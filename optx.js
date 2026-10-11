(function (global) {
  'use strict';

  const BASE45_ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:';
  const BASE45_INDEX = Object.fromEntries(Array.from(BASE45_ALPHABET, (char, index) => [char, index]));
  const CRC_TABLE = new Uint32Array(256);

  for (let i = 0; i < 256; i++) {
    let value = i;
    for (let bit = 0; bit < 8; bit++) value = (value >>> 1) ^ ((value & 1) ? 0xedb88320 : 0);
    CRC_TABLE[i] = value >>> 0;
  }

  const GF256 = (() => {
    const exp = new Uint8Array(512);
    const log = new Uint8Array(256);
    let value = 1;
    for (let i = 0; i < 255; i++) {
      exp[i] = value;
      log[value] = i;
      value <<= 1;
      if (value & 0x100) value ^= 0x11d;
    }
    for (let i = 255; i < exp.length; i++) exp[i] = exp[i - 255];
    return { exp, log };
  })();

  function gfMul(a, b) {
    if (!a || !b) return 0;
    return GF256.exp[GF256.log[a] + GF256.log[b]];
  }

  function gfInv(value) {
    if (!value) throw new Error('Sıfırın GF256 tersi yoktur.');
    return GF256.exp[255 - GF256.log[value]];
  }

  function encodeBase45(bytes) {
    let output = '';
    for (let i = 0; i < bytes.length; i += 2) {
      if (i + 1 < bytes.length) {
        let value = bytes[i] * 256 + bytes[i + 1];
        output += BASE45_ALPHABET[value % 45];
        value = Math.floor(value / 45);
        output += BASE45_ALPHABET[value % 45];
        output += BASE45_ALPHABET[Math.floor(value / 45)];
      } else {
        const value = bytes[i];
        output += BASE45_ALPHABET[value % 45];
        output += BASE45_ALPHABET[Math.floor(value / 45)];
      }
    }
    return output;
  }

  function decodeBase45(text) {
    const output = [];
    for (let i = 0; i < text.length;) {
      const remaining = text.length - i;
      if (remaining === 1) throw new Error('Geçersiz Base45 uzunluğu.');
      const a = BASE45_INDEX[text[i]];
      const b = BASE45_INDEX[text[i + 1]];
      if (a === undefined || b === undefined) throw new Error('Geçersiz Base45 karakteri.');
      if (remaining >= 3) {
        const c = BASE45_INDEX[text[i + 2]];
        if (c === undefined) throw new Error('Geçersiz Base45 karakteri.');
        const value = a + b * 45 + c * 2025;
        if (value > 0xffff) throw new Error('Geçersiz Base45 değeri.');
        output.push(value >>> 8, value & 255);
        i += 3;
      } else {
        const value = a + b * 45;
        if (value > 255) throw new Error('Geçersiz Base45 değeri.');
        output.push(value);
        i += 2;
      }
    }
    return new Uint8Array(output);
  }

  function crc32(bytes) {
    let crc = 0xffffffff;
    for (const byte of bytes) crc = (crc >>> 8) ^ CRC_TABLE[(crc ^ byte) & 255];
    return (crc ^ 0xffffffff) >>> 0;
  }

  function fixedBase36(value, width) {
    if (!Number.isSafeInteger(value) || value < 0) throw new Error('Geçersiz sayısal başlık alanı.');
    const encoded = value.toString(36).toUpperCase();
    if (encoded.length > width) throw new Error('Aktarım, protokol başlığına sığmayacak kadar büyük.');
    return encoded.padStart(width, '0');
  }

  function parseBase36(value) {
    if (!/^[0-9A-Z]+$/.test(value)) return NaN;
    return Number.parseInt(value, 36);
  }

  function rowForSymbol(symbolIndex, dataCount, parityCount) {
    if (symbolIndex < 0 || symbolIndex >= dataCount + parityCount) return null;
    const row = new Uint8Array(dataCount);
    if (symbolIndex < dataCount) {
      row[symbolIndex] = 1;
      return row;
    }

    // [I; C] biçimindeki Cauchy matrisi, herhangi dataCount satırdan
    // geri kurulabilen sistematik bir MDS kodu verir.
    const x = symbolIndex - dataCount;
    for (let column = 0; column < dataCount; column++) {
      const denominator = x ^ (parityCount + column);
      row[column] = gfInv(denominator);
    }
    return row;
  }

  function invertMatrix(source) {
    const size = source.length;
    const matrix = source.map((row, rowIndex) => {
      const extended = new Uint8Array(size * 2);
      extended.set(row, 0);
      extended[size + rowIndex] = 1;
      return extended;
    });

    for (let column = 0; column < size; column++) {
      let pivot = column;
      while (pivot < size && matrix[pivot][column] === 0) pivot++;
      if (pivot === size) return null;
      if (pivot !== column) [matrix[pivot], matrix[column]] = [matrix[column], matrix[pivot]];

      const inverse = gfInv(matrix[column][column]);
      for (let i = 0; i < size * 2; i++) matrix[column][i] = gfMul(matrix[column][i], inverse);

      for (let row = 0; row < size; row++) {
        if (row === column) continue;
        const factor = matrix[row][column];
        if (!factor) continue;
        for (let i = 0; i < size * 2; i++) matrix[row][i] ^= gfMul(factor, matrix[column][i]);
      }
    }
    return matrix.map(row => row.slice(size));
  }

  function encodeGroup(source, offset, dataCount, parityCount, chunkSize) {
    if (dataCount + parityCount > 255) throw new Error('Bir hata düzeltme grubu 255 sembolü aşamaz.');
    const data = Array.from({ length: dataCount }, (_, index) => {
      const block = new Uint8Array(chunkSize);
      block.set(source.subarray(offset + index * chunkSize, offset + (index + 1) * chunkSize));
      return block;
    });
    const parity = Array.from({ length: parityCount }, () => new Uint8Array(chunkSize));

    for (let parityIndex = 0; parityIndex < parityCount; parityIndex++) {
      const row = rowForSymbol(dataCount + parityIndex, dataCount, parityCount);
      const target = parity[parityIndex];
      for (let dataIndex = 0; dataIndex < dataCount; dataIndex++) {
        const coefficient = row[dataIndex];
        const block = data[dataIndex];
        if (!coefficient) continue;
        for (let byteIndex = 0; byteIndex < chunkSize; byteIndex++) {
          target[byteIndex] ^= gfMul(coefficient, block[byteIndex]);
        }
      }
    }
    return data.concat(parity);
  }

  function recoverGroup(symbols, dataCount, parityCount, chunkSize) {
    const selected = Array.from(symbols.entries())
      .filter(([index, bytes]) => Number.isInteger(index) && index >= 0 && index < dataCount + parityCount && bytes.length === chunkSize)
      .slice(0, dataCount);
    if (selected.length < dataCount) return null;

    const inverse = invertMatrix(selected.map(([index]) => rowForSymbol(index, dataCount, parityCount)));
    if (!inverse) return null;
    const recovered = Array.from({ length: dataCount }, () => new Uint8Array(chunkSize));

    for (let outputIndex = 0; outputIndex < dataCount; outputIndex++) {
      for (let inputIndex = 0; inputIndex < dataCount; inputIndex++) {
        const coefficient = inverse[outputIndex][inputIndex];
        const block = selected[inputIndex][1];
        if (!coefficient) continue;
        for (let byteIndex = 0; byteIndex < chunkSize; byteIndex++) {
          recovered[outputIndex][byteIndex] ^= gfMul(coefficient, block[byteIndex]);
        }
      }
    }
    return recovered;
  }

  function makeDataFrame(fileId, groupIndex, symbolIndex, payload) {
    return 'O2D' + fileId + fixedBase36(groupIndex, 3) + fixedBase36(symbolIndex, 2) + fixedBase36(crc32(payload), 7) + encodeBase45(payload);
  }

  function parseDataFrame(raw) {
    if (typeof raw !== 'string' || !raw.startsWith('O2D') || raw.length < 29) return null;
    const fileId = raw.slice(3, 15);
    const groupIndex = parseBase36(raw.slice(15, 18));
    const symbolIndex = parseBase36(raw.slice(18, 20));
    const expectedCrc = parseBase36(raw.slice(20, 27));
    if (![groupIndex, symbolIndex, expectedCrc].every(Number.isSafeInteger)) return null;
    try {
      const payload = decodeBase45(raw.slice(27));
      if (crc32(payload) !== expectedCrc) return null;
      return { fileId, groupIndex, symbolIndex, payload };
    } catch (_) {
      return null;
    }
  }

  function makeMetaFrame(fileId, metadata) {
    return 'O2M' + fileId + encodeBase45(new TextEncoder().encode(JSON.stringify(metadata)));
  }

  function parseMetaFrame(raw) {
    if (typeof raw !== 'string' || !raw.startsWith('O2M') || raw.length < 17) return null;
    try {
      const fileId = raw.slice(3, 15);
      const metadata = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(decodeBase45(raw.slice(15))));
      return { fileId, metadata };
    } catch (_) {
      return null;
    }
  }

  global.Optx2 = Object.freeze({
    encodeBase45,
    decodeBase45,
    crc32,
    fixedBase36,
    encodeGroup,
    recoverGroup,
    makeDataFrame,
    parseDataFrame,
    makeMetaFrame,
    parseMetaFrame
  });
})(window);
