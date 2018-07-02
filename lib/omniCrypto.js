const fs = require('fs-extra');
const plist = require('plist');
const assert = require('assert');
const crypto = require('crypto');

const fileMagic = Buffer.from('OmniFileEncryption\0\0');

const slotType = {
  'None'                : 0, // Trailing padding
  'ActiveAESWRAP'       : 1, // (Obsolete) Currently-active AESWRAP key
  'RetiredAESWRAP'      : 2, // (Obsolete) Old AESWRAP key used after rollover
  'ActiveAES_CTR_HMAC'  : 3, // Currently-active CTR+HMAC key
  'RetiredAES_CTR_HMAC' : 4, // Old key used after rollover
  'PlaintextMask'       : 5, // Filename patterns which should not be encrypted
  'RetiredPlaintextMask': 6, // Filename patterns which have legacy unencrypted entries
};

// a: Buffer, length: 8
// b: number
function xor64(a, b) {
  const tmp = b;
  b = Buffer.alloc(8);
  b.writeUInt32BE(tmp >> 8, 0);
  b.writeUInt32BE(tmp & 0xFFFFFFFF, 4);

  const result = Buffer.alloc(8);
  for (let i = 0; i < a.length; i++) {
    result[i] = a[i] ^ b[i];
  }
  return result;
}

function _unwrap_core(wrappingKey, a, r) {
  const decryptor = crypto.createDecipheriv("aes-128-ecb", wrappingKey, '');
  decryptor.setAutoPadding(false);
  const n = r.length;
  for (let j = 5; 0 <= j; j--) {
    for (let i = n - 1; 0 <= i; i--) {
      const atr = Buffer.concat([xor64(a, (n * j) + i + 1), r[i]], 16);
      const b = decryptor.update(atr);
      a = b.slice(0, 8);
      r[i] = b.slice(8);
    }
  }
  return [a, r];
}

function aesKeyUnwrap(wrappingKey, wrappedKey) {
  assert(24 <= wrappedKey.length, 'The wrapped key must be at least 24 bytes');
  assert(wrappedKey.length % 8 === 0, 'The wrapped key must be a multiple of 8 bytes');
  assert([16, 24, 32].includes(wrappingKey.length), 'The wrapping key must be a valid AES key length');

  const aiv = Buffer.from('a6'.repeat(8), 'hex');
  let r = [];
  for (let i = 0; i < wrappedKey.length; i += 8) {
    r.push(wrappedKey.slice(i, i + 8));
  }

  let a = r.shift();
  [a, r] = _unwrap_core(wrappingKey, a, r);
  if (!a.equals(aiv)) {
    new Error('Invalid Unwrap');
  }

  return Buffer.concat(r);
}

class EncryptedFileHelper {
  constructor(keyMaterial) {
    // File format constants.
    this.SegIVLen = 12;     // Four bytes less than blocksize (see CTR mode for why)
    this.SegMACLen = 20;    // Arbitrary, but fixed
    this.SegPageSize = 65536;
    this.FileMACPrefix = Buffer.from('\x01'); // Fixed prefix for file HMAC

    this.aeskey = keyMaterial.slice(0, 16);
    this.hmackey = keyMaterial.slice(16, 32);
  }

  // Yield a sequence of tuples describing the locations of the encrypted segments.
  * segmentRanges(seg0start, segNend) {
    const encryptedHdrSize = this.SegIVLen + this.SegMACLen;
    let idx = 0;
    let position = seg0start;
    while (true) {
      assert(position + encryptedHdrSize < segNend);
      if (segNend < position + encryptedHdrSize + this.SegPageSize) {
        // Partial trailing page.
        yield [idx, position, segNend - (position + encryptedHdrSize)];
        break;
      } else {
        // Full page.
        yield [idx, position, this.SegPageSize];
        position += encryptedHdrSize + this.SegPageSize;
        idx += 1;
      }
    }
  }

  // Check the file's integrity
  async checkHMAC(fd, segmentStart, segmentEnd, fileHMAC) {
    const fileHash = crypto.createHmac('sha256', this.hmackey);
    let filePosition;
    fileHash.update(this.FileMACPrefix);
    for (const [segmentIndex, startPosition, dataLength] of this.segmentRanges(segmentStart, segmentEnd)) {
      const segmentIV = Buffer.alloc(this.SegIVLen);
      const segmentMAC = Buffer.alloc(this.SegMACLen);
      filePosition = startPosition;
      await fs.read(fd, segmentIV, 0, segmentIV.length, filePosition);
      filePosition += segmentIV.length;
      await fs.read(fd, segmentMAC, 0, segmentMAC.length, filePosition);
      filePosition += segmentMAC.length;
      const segmentHash = crypto.createHmac('sha256', this.hmackey);
      segmentHash.update(segmentIV);
      const indexBuffer = Buffer.alloc(4);
      indexBuffer.writeUInt32BE(segmentIndex, 0);
      segmentHash.update(indexBuffer);
      const buffer = Buffer.alloc(dataLength);
      await fs.read(fd, buffer, 0, buffer.length, filePosition);
      segmentHash.update(buffer);

      // Verify the segment's own MAC against the segment data
      const computed = segmentHash.digest();
      assert(segmentMAC.equals(computed.slice(0, this.SegMACLen)));
      fileHash.update(segmentMAC);
    }
    const computed = fileHash.digest();
    assert(computed.equals(fileHMAC));
  }

  // Decrypt the file
  async decrypt(fd, segmentStart, segmentEnd) {
    const result = [];
    for (const [, startPosition, dataLength] of this.segmentRanges(segmentStart, segmentEnd)) {
      // Read the segment's IV and set up the decryption context
      const segmentIV = Buffer.alloc(16);
      await fs.read(fd, segmentIV, 0, this.SegIVLen, startPosition);
      const decryptor = crypto.createDecipheriv('aes-128-ctr', this.aeskey, segmentIV);

      // Decrypt the segment
      const buffer = Buffer.alloc(dataLength);
      await fs.read(fd, buffer, 0 , dataLength, startPosition + this.SegIVLen + this.SegMACLen);
      result.push(decryptor.update(buffer));
      const trailing = decryptor.final();
      if (0 < trailing.length) {
        result.push(trailing);
      }
    }
    return Buffer.concat(result);
  }
}

class DocumentKey {
  constructor(secrets, unwrappingKey) {
    this.secrets = null;
    let unwrapped;
    if (secrets) {
      if (!unwrappingKey) {
        unwrapped = secrets;
      } else {
        unwrapped = aesKeyUnwrap(unwrappingKey, secrets);
      }
      this.parseSecrets(unwrapped);
    }
  }

  parseSecrets(unwrapped) {
    function Slot(tp, id, content) {
      const result = [];
      result.push(tp, id, content);
      result._fields = ['tp', 'id', 'content'];
      Object.assign(result, {tp, id, content});
      return result;
    }
    const secrets = [];
    let idx = 0;
    while(idx !== unwrapped.length) {
      const slotType = unwrapped[idx];
      if(slotType === 0) {
        break;
      }
      const slotLength = 4 * unwrapped[idx+1];
      const slotId = unwrapped.readUInt16BE(idx + 2);
      const slotData = unwrapped.slice(idx + 4, idx + 4 + slotLength);
      secrets.push(new Slot(slotType, slotId, slotData));
      idx = idx + 4 + slotLength;
    }
    this.secrets = secrets;
  }

  static async parseMetadata(metadataPath) {
    const xml = await fs.readFile(metadataPath, 'utf8');

    const metadata = plist.parse(xml);
    assert(metadata[0] instanceof Object);
    return metadata[0];
  }

  static async usePassphrase(metadata, passphrase) {
    assert(metadata.method === 'password');
    assert(metadata.algorithm === 'PBKDF2; aes128-wrap');

    // Ideally, we should also normalize (NFC) and stringprep the passphrase before converting it to utf-8
    // As Node uses utf8 as default, It does not need converting.
    const passPhraseBytes = passphrase;
    return await new Promise((resolve, reject) => {
      crypto.pbkdf2(passPhraseBytes, metadata.salt, metadata.rounds, 16, 'sha1',
          (err, derivedKey) => {
            if (err) reject(err);
            resolve(derivedKey);
          });
    });
  }

  * applicablePolicySlots(filename) {
    for (const slot of this.secrets) {
      if ([slotType['PlaintextMask'], slotType['RetiredPlaintextMask']].includes(slot.tp)) {
        if (filename.endsWith(slot.content.toString().replace(/\0*$/, ''))) {
          yield slot;
        }
      }
    }
  }

  // Return an object which decrypts a file, given that file's key information. Used by decrypt_file().
  getDecryptor(info) {
    // The beginning of the key information is the key identifier.
    const keyId = info.readUInt16BE(0);
    // Find matching key identifier(s).
    const slots = this.secrets.filter(secret => secret.id === keyId);
    assert(slots.length === 1, 'Should have exactly one matching entry');
    const slot = slots[0];
    if ([slotType['ActiveAES_CTR_HMAC'], slotType['RetiredAES_CTR_HMAC']].includes(slot.tp)) {
      assert(info.length === 2, 'No per-file info for these key types');
      return new EncryptedFileHelper(slot.content);
    } else if ([slotType['ActiveAESWRAP'], slotType['RetiredAESWRAP']].includes(slot.tp)) {
      const wrappedKey = info.slice(2);
      assert(wrappedKey.length % 8 === 0, 'AESWRAPped info');
      const unwrapped = aesKeyUnwrap(slot.content, wrappedKey);
      return new EncryptedFileHelper(unwrapped);
    } else {
      throw new Error(`Unknown keyslot type: ${slot.tp}`);
    }
  }

  async decryptFile(filename) {
    let canReadPlainText = null;
    for(const slot of this.applicablePolicySlots(filename)) {
      if (slot.tp === slotType['PlaintextMask']) {
        canReadPlainText = 'expected';
      } else if (slot.tp === slotType['RetiredPlaintextMask']) {
        canReadPlainText = 'temporarily allowed';
      }
    }

    const magic = Buffer.alloc(fileMagic.length);
    const fd = await fs.open(filename, 'r');
    const stat = await fs.fstat(fd);
    await fs.read(fd, magic, 0, fileMagic.length, null);
    if (!magic.equals(fileMagic)) {
      if (canReadPlainText && !magic.includes('crypt')) {
        console.log('not encrypted');
      } else {
        throw new Error('Incorrect file magic, or unencrypted file');
      }
    }

    // Read the key information.
    let infoLength = Buffer.alloc(2);
    await fs.read(fd, infoLength, 0, 2, null);
    infoLength = infoLength.readUInt16BE(0);
    const info = Buffer.alloc(infoLength);
    await fs.read(fd, info, 0, infoLength, null);

    // Skip & check padding.
    const offset = magic.length + 2 + infoLength;
    const paddingLength = (16 - (offset % 16)) % 16;
    const padding = Buffer.alloc(paddingLength);
    await fs.read(fd, padding, 0, paddingLength, null);
    assert(padding.equals(Buffer.from('\0'.repeat(paddingLength))));

    // Look up file key
    const decryptor = this.getDecryptor(info);

    // The rest of the file is the encrypted segments followed by the file HMAC.
    const seg0start = fileMagic.length + 2 + infoLength + paddingLength;
    const segNend = stat.size - 32;
    const fileHMAC = Buffer.alloc(32);
    await fs.read(fd, fileHMAC, 0, 32, segNend);

    // Check the MACs
    await decryptor.checkHMAC(fd ,seg0start, segNend, fileHMAC);
    return await decryptor.decrypt(fd, seg0start, segNend);
  }
}

async function decrypt(phrase, metadataPath, encryptedFilePath) {
  const encryptionMetadata = await DocumentKey.parseMetadata(metadataPath);
  const metadataKey = await DocumentKey.usePassphrase(encryptionMetadata, phrase);
  const docKey = new DocumentKey(encryptionMetadata.key, metadataKey);
  return await docKey.decryptFile(encryptedFilePath);
}

module.exports = {
  decrypt
};
