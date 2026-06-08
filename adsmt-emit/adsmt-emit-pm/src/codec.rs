//! Redistributable package archive + pluggable compression codec.
//!
//! A built package's `contents/` directory (== the build's
//! `$pkgdir`) is packed into a `tar` archive and then compressed by
//! a [`Codec`], producing `<name>.tar.<ext>` (default
//! `<name>.tar.zst`).
//!
//! The codec is pluggable so the in-development **bzip4** compressor
//! (`~/bzip4`, a BWT-family codec) can slot in later as a
//! `Bzip4Codec` (via its `bzip4-core` crate or the `bzip4-cli`
//! binary) without touching the packaging logic. Today only
//! [`ZstdCodec`] is wired.

use std::io;
use std::path::Path;

/// A pluggable compression codec for the package archive.
pub trait Codec {
    /// The extension after `.tar.`, e.g. `"zst"` or `"bz4"`.
    fn extension(&self) -> &str;
    /// Compress `data`.
    fn compress(&self, data: &[u8]) -> io::Result<Vec<u8>>;
    /// Decompress `data`.
    fn decompress(&self, data: &[u8]) -> io::Result<Vec<u8>>;
}

/// The default codec: zstandard.
pub struct ZstdCodec {
    /// Compression level (zstd: 1..=22).
    pub level: i32,
}

impl Default for ZstdCodec {
    fn default() -> Self {
        ZstdCodec { level: 19 }
    }
}

impl Codec for ZstdCodec {
    fn extension(&self) -> &str {
        "zst"
    }
    fn compress(&self, data: &[u8]) -> io::Result<Vec<u8>> {
        zstd::stream::encode_all(data, self.level)
    }
    fn decompress(&self, data: &[u8]) -> io::Result<Vec<u8>> {
        zstd::stream::decode_all(data)
    }
}

/// Resolve a codec by its `.tar.<ext>` extension. Returns `None`
/// for an unknown extension (e.g. `bz4` until the Bzip4Codec lands).
pub fn codec_for_extension(ext: &str) -> Option<Box<dyn Codec>> {
    match ext {
        "zst" => Some(Box::new(ZstdCodec::default())),
        _ => None,
    }
}

/// Pack a directory tree into a `tar` archive, sorted by path for
/// reproducibility.
pub fn tar_dir(dir: &Path) -> io::Result<Vec<u8>> {
    let mut files = Vec::new();
    crate::store::collect_files(dir, dir, &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let mut builder = tar::Builder::new(Vec::new());
    for (rel, abs) in &files {
        let bytes = std::fs::read(abs)?;
        let mut header = tar::Header::new_gnu();
        header.set_size(bytes.len() as u64);
        header.set_mode(0o644);
        header.set_mtime(0);
        header.set_cksum();
        builder.append_data(&mut header, rel, &bytes[..])?;
    }
    builder.into_inner()
}

/// Pack a directory into a compressed redistributable archive.
pub fn pack_dir(dir: &Path, codec: &dyn Codec) -> io::Result<Vec<u8>> {
    let tar = tar_dir(dir)?;
    codec.compress(&tar)
}

/// Unpack a compressed archive into `dest`.
pub fn unpack_into(archive: &[u8], codec: &dyn Codec, dest: &Path) -> io::Result<()> {
    let tar = codec.decompress(archive)?;
    let mut ar = tar::Archive::new(&tar[..]);
    ar.unpack(dest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zstd_roundtrips_bytes() {
        let codec = ZstdCodec::default();
        let data = b"the quick brown fox".repeat(100);
        let packed = codec.compress(&data).unwrap();
        assert!(packed.len() < data.len());
        assert_eq!(codec.decompress(&packed).unwrap(), data);
        assert_eq!(codec.extension(), "zst");
    }

    #[test]
    fn pack_unpack_directory_roundtrip() {
        let tmp = tempfile::tempdir().unwrap();
        let src = tmp.path().join("pkg");
        std::fs::create_dir_all(src.join("lib")).unwrap();
        std::fs::write(src.join("emitter.wasm"), b"\0asm\x01\0\0\0").unwrap();
        std::fs::write(src.join("lib/data.bin"), b"aux-data").unwrap();

        let codec = ZstdCodec::default();
        let archive = pack_dir(&src, &codec).unwrap();

        let out = tmp.path().join("out");
        unpack_into(&archive, &codec, &out).unwrap();
        assert_eq!(std::fs::read(out.join("emitter.wasm")).unwrap(), b"\0asm\x01\0\0\0");
        assert_eq!(std::fs::read(out.join("lib/data.bin")).unwrap(), b"aux-data");
    }

    #[test]
    fn unknown_extension_has_no_codec() {
        assert!(codec_for_extension("zst").is_some());
        assert!(codec_for_extension("bz4").is_none());
    }
}
