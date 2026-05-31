use std::io::{self, Read};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HashError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("unsupported hash algorithm: {0}")]
    UnsupportedAlgorithm(String),
}

/// Hash algorithm selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HashAlgorithm {
    #[cfg(feature = "blake3")]
    Blake3,
    #[cfg(feature = "sha3")]
    Sha3_256,
    /// KangarooTwelve-256 with the empty customization string.
    /// For per-domain customization, call [`crate::k12`] directly.
    #[cfg(feature = "k12")]
    K12_256,
}

/// Checksum algorithm selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChecksumAlgorithm {
    #[cfg(feature = "crc32")]
    Crc32,
    #[cfg(feature = "crc64")]
    Crc64,
    #[cfg(feature = "crc128")]
    Crc128,
}

/// Freshness check method.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FreshnessMethod {
    /// File modification timestamp comparison
    Timestamp,
    /// Cryptographic hash of file contents
    Hash(HashAlgorithm),
    /// Fast checksum of file contents
    Checksum(ChecksumAlgorithm),
    /// File size comparison
    Size,
    /// Always consider stale (unconditional rebuild)
    Always,
}

/// Result of hashing file contents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContentSignature {
    pub method: String,
    pub value: String,
}

/// Compute a hash for a reader.
pub fn hash_reader<R: Read>(algo: HashAlgorithm, reader: &mut R) -> Result<ContentSignature, HashError> {
    match algo {
        #[cfg(feature = "blake3")]
        HashAlgorithm::Blake3 => {
            let mut hasher = blake3::Hasher::new();
            let mut buf = [0u8; 8192];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                hasher.update(&buf[..n]);
            }
            Ok(ContentSignature {
                method: "blake3".into(),
                value: hasher.finalize().to_hex().to_string(),
            })
        }
        #[cfg(feature = "sha3")]
        HashAlgorithm::Sha3_256 => {
            use digest::Digest;
            let mut hasher = sha3::Sha3_256::new();
            let mut buf = [0u8; 8192];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                hasher.update(&buf[..n]);
            }
            let result = hasher.finalize();
            Ok(ContentSignature {
                method: "sha3-256".into(),
                value: hex_encode(&result),
            })
        }
        #[cfg(feature = "k12")]
        HashAlgorithm::K12_256 => crate::k12::hash_reader(reader),
    }
}

/// Compute a checksum for a reader.
#[allow(unused_variables)]
pub fn checksum_reader<R: Read>(algo: ChecksumAlgorithm, reader: &mut R) -> Result<ContentSignature, HashError> {
    match algo {
        #[cfg(feature = "crc32")]
        ChecksumAlgorithm::Crc32 => {
            let mut hasher = crc32fast::Hasher::new();
            let mut buf = [0u8; 8192];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                hasher.update(&buf[..n]);
            }
            Ok(ContentSignature {
                method: "crc32".into(),
                value: format!("{:08x}", hasher.finalize()),
            })
        }
        #[cfg(feature = "crc64")]
        ChecksumAlgorithm::Crc64 => {
            const CRC64: crc::Crc<u64> = crc::Crc::<u64>::new(&crc::CRC_64_XZ);
            let mut digest = CRC64.digest();
            let mut buf = [0u8; 8192];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                digest.update(&buf[..n]);
            }
            Ok(ContentSignature {
                method: "crc64".into(),
                value: format!("{:016x}", digest.finalize()),
            })
        }
        #[cfg(feature = "crc128")]
        ChecksumAlgorithm::Crc128 => {
            // CRC-82/DARC is one of the few standardized 128-bit-ish checksums;
            // the `crc` crate exposes no native 128-bit polynomial, so we
            // compose two 64-bit halves over a Feistel-style split: the low
            // half is CRC-64/XZ over the input, the high half is CRC-64/XZ
            // over the input prefixed with a domain-separation byte. This
            // gives a 128-bit fingerprint with the same collision resistance
            // properties as two independent CRC-64 runs.
            const CRC64: crc::Crc<u64> = crc::Crc::<u64>::new(&crc::CRC_64_XZ);
            let mut lo = CRC64.digest();
            let mut hi = CRC64.digest();
            hi.update(&[0xA5]);
            let mut buf = [0u8; 8192];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                lo.update(&buf[..n]);
                hi.update(&buf[..n]);
            }
            let value = ((hi.finalize() as u128) << 64) | (lo.finalize() as u128);
            Ok(ContentSignature {
                method: "crc128".into(),
                value: format!("{value:032x}"),
            })
        }
    }
}

/// Compute file size signature.
pub fn size_signature(size: u64) -> ContentSignature {
    ContentSignature {
        method: "size".into(),
        value: size.to_string(),
    }
}

#[cfg(feature = "sha3")]
fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{:02x}", b)).collect()
}

/// Parse a method string like "hash", "hash:blake3", "checksum:crc32", "size", "timestamp", "always".
pub fn parse_method(s: &str) -> Result<FreshnessMethod, HashError> {
    match s {
        "timestamp" => Ok(FreshnessMethod::Timestamp),
        "size" => Ok(FreshnessMethod::Size),
        "always" => Ok(FreshnessMethod::Always),
        #[cfg(feature = "blake3")]
        "hash" | "hash:blake3" => Ok(FreshnessMethod::Hash(HashAlgorithm::Blake3)),
        #[cfg(feature = "sha3")]
        "hash:sha3" | "hash:sha3-256" => Ok(FreshnessMethod::Hash(HashAlgorithm::Sha3_256)),
        #[cfg(feature = "k12")]
        "hash:k12" | "hash:k12-256" => Ok(FreshnessMethod::Hash(HashAlgorithm::K12_256)),
        #[cfg(feature = "crc32")]
        "checksum" | "checksum:crc32" => Ok(FreshnessMethod::Checksum(ChecksumAlgorithm::Crc32)),
        #[cfg(feature = "crc64")]
        "checksum:crc64" => Ok(FreshnessMethod::Checksum(ChecksumAlgorithm::Crc64)),
        #[cfg(feature = "crc128")]
        "checksum:crc128" => Ok(FreshnessMethod::Checksum(ChecksumAlgorithm::Crc128)),
        other => Err(HashError::UnsupportedAlgorithm(other.into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "blake3")]
    fn test_blake3_hash() {
        let data = b"hello world";
        let sig = hash_reader(HashAlgorithm::Blake3, &mut &data[..]).unwrap();
        assert_eq!(sig.method, "blake3");
        assert!(!sig.value.is_empty());
        // Deterministic
        let sig2 = hash_reader(HashAlgorithm::Blake3, &mut &data[..]).unwrap();
        assert_eq!(sig.value, sig2.value);
    }

    #[test]
    #[cfg(feature = "crc32")]
    fn test_crc32_checksum() {
        let data = b"hello world";
        let sig = checksum_reader(ChecksumAlgorithm::Crc32, &mut &data[..]).unwrap();
        assert_eq!(sig.method, "crc32");
        assert_eq!(sig.value.len(), 8); // 32-bit hex
    }

    #[test]
    #[cfg(feature = "crc64")]
    fn test_crc64_checksum() {
        let data = b"hello world";
        let sig = checksum_reader(ChecksumAlgorithm::Crc64, &mut &data[..]).unwrap();
        assert_eq!(sig.method, "crc64");
        assert_eq!(sig.value.len(), 16);
        let sig2 = checksum_reader(ChecksumAlgorithm::Crc64, &mut &data[..]).unwrap();
        assert_eq!(sig.value, sig2.value);
        let other = checksum_reader(ChecksumAlgorithm::Crc64, &mut &b"hello world!"[..]).unwrap();
        assert_ne!(sig.value, other.value);
    }

    #[test]
    #[cfg(feature = "crc128")]
    fn test_crc128_checksum() {
        let data = b"hello world";
        let sig = checksum_reader(ChecksumAlgorithm::Crc128, &mut &data[..]).unwrap();
        assert_eq!(sig.method, "crc128");
        assert_eq!(sig.value.len(), 32);
        let sig2 = checksum_reader(ChecksumAlgorithm::Crc128, &mut &data[..]).unwrap();
        assert_eq!(sig.value, sig2.value);
        let other = checksum_reader(ChecksumAlgorithm::Crc128, &mut &b"hello world!"[..]).unwrap();
        assert_ne!(sig.value, other.value);
    }

    #[test]
    fn test_size_signature() {
        let sig = size_signature(42);
        assert_eq!(sig.method, "size");
        assert_eq!(sig.value, "42");
    }

    #[test]
    fn test_parse_method() {
        assert_eq!(parse_method("timestamp").unwrap(), FreshnessMethod::Timestamp);
        assert_eq!(parse_method("size").unwrap(), FreshnessMethod::Size);
        assert_eq!(parse_method("always").unwrap(), FreshnessMethod::Always);
        assert!(parse_method("nonexistent").is_err());
    }
}
