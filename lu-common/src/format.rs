use serde::Serialize;
use std::io::{self, Write};
use thiserror::Error;

/// Supported output formats for logicutils CLI protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    /// Line-oriented plain text (default)
    Plain,
    /// One JSON object per line (JSONL)
    Json,
    /// Tab-separated values with header
    Tsv,
    /// Comma-separated values with header
    Csv,
    /// TOML
    Toml,
    /// Shell-eval compatible `KEY=value` pairs
    Shell,
}

#[derive(Debug, Error)]
pub enum FormatError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("JSON serialization error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("CSV serialization error: {0}")]
    Csv(#[from] csv::Error),
    #[error("TOML serialization error: {0}")]
    Toml(#[from] toml::ser::Error),
}

impl OutputFormat {
    pub fn from_str_loose(s: &str) -> Option<Self> {
        match s.to_ascii_lowercase().as_str() {
            "plain" | "text" => Some(Self::Plain),
            "json" | "jsonl" => Some(Self::Json),
            "tsv" => Some(Self::Tsv),
            "csv" => Some(Self::Csv),
            "toml" => Some(Self::Toml),
            "shell" | "sh" | "eval" => Some(Self::Shell),
            _ => None,
        }
    }
}

/// A record with named string fields, suitable for all output formats.
#[derive(Debug, Clone, Serialize)]
pub struct Record {
    fields: Vec<(String, String)>,
}

impl Record {
    pub fn new() -> Self {
        Self { fields: Vec::new() }
    }

    pub fn field(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.fields.push((key.into(), value.into()));
        self
    }

    pub fn keys(&self) -> impl Iterator<Item = &str> {
        self.fields.iter().map(|(k, _)| k.as_str())
    }

    pub fn values(&self) -> impl Iterator<Item = &str> {
        self.fields.iter().map(|(_, v)| v.as_str())
    }

    pub fn get(&self, key: &str) -> Option<&str> {
        self.fields
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }
}

impl Default for Record {
    fn default() -> Self {
        Self::new()
    }
}

/// Writer that emits records in the chosen format.
pub struct FormatWriter<W: Write> {
    writer: W,
    format: OutputFormat,
    header_written: bool,
    header_keys: Vec<String>,
}

impl<W: Write> FormatWriter<W> {
    pub fn new(writer: W, format: OutputFormat) -> Self {
        Self {
            writer,
            format,
            header_written: false,
            header_keys: Vec::new(),
        }
    }

    pub fn write_record(&mut self, record: &Record) -> Result<(), FormatError> {
        match self.format {
            OutputFormat::Plain => {
                let line: Vec<&str> = record.values().collect();
                writeln!(self.writer, "{}", line.join("\t"))?;
            }
            OutputFormat::Json => {
                let map: serde_json::Map<String, serde_json::Value> = record
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), serde_json::Value::String(v.clone())))
                    .collect();
                serde_json::to_writer(&mut self.writer, &map)?;
                writeln!(self.writer)?;
            }
            OutputFormat::Tsv => {
                if !self.header_written {
                    self.header_keys = record.keys().map(String::from).collect();
                    writeln!(self.writer, "{}", self.header_keys.join("\t"))?;
                    self.header_written = true;
                }
                let vals: Vec<&str> = record.values().collect();
                writeln!(self.writer, "{}", vals.join("\t"))?;
            }
            OutputFormat::Csv => {
                if !self.header_written {
                    self.header_keys = record.keys().map(String::from).collect();
                    let mut wtr = csv::WriterBuilder::new()
                        .has_headers(false)
                        .from_writer(Vec::new());
                    wtr.write_record(&self.header_keys)?;
                    let data = wtr.into_inner().map_err(|e| e.into_error())?;
                    self.writer.write_all(&data)?;
                    self.header_written = true;
                }
                let vals: Vec<&str> = record.values().collect();
                let mut wtr = csv::WriterBuilder::new()
                    .has_headers(false)
                    .from_writer(Vec::new());
                wtr.write_record(&vals)?;
                let data = wtr.into_inner().map_err(|e| e.into_error())?;
                self.writer.write_all(&data)?;
            }
            OutputFormat::Toml => {
                let map: toml::map::Map<String, toml::Value> = record
                    .fields
                    .iter()
                    .map(|(k, v)| (k.clone(), toml::Value::String(v.clone())))
                    .collect();
                let s = toml::to_string(&map)?;
                write!(self.writer, "{}", s)?;
            }
            OutputFormat::Shell => {
                for (k, v) in &record.fields {
                    // Shell-safe: single-quote the value, escaping embedded single quotes
                    let escaped = v.replace('\'', "'\\''");
                    write!(self.writer, "{}='{}' ", k, escaped)?;
                }
                writeln!(self.writer)?;
            }
        }
        Ok(())
    }

    pub fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_record() -> Record {
        Record::new()
            .field("file", "main.c")
            .field("method", "blake3")
            .field("value", "abc123")
    }

    #[test]
    fn test_plain_output() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Plain);
        w.write_record(&sample_record()).unwrap();
        assert_eq!(String::from_utf8(buf).unwrap(), "main.c\tblake3\tabc123\n");
    }

    #[test]
    fn test_json_output() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Json);
        w.write_record(&sample_record()).unwrap();
        let s = String::from_utf8(buf).unwrap();
        let v: serde_json::Value = serde_json::from_str(s.trim()).unwrap();
        assert_eq!(v["file"], "main.c");
        assert_eq!(v["method"], "blake3");
    }

    #[test]
    fn test_tsv_output() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Tsv);
        w.write_record(&sample_record()).unwrap();
        let s = String::from_utf8(buf).unwrap();
        let lines: Vec<&str> = s.lines().collect();
        assert_eq!(lines[0], "file\tmethod\tvalue");
        assert_eq!(lines[1], "main.c\tblake3\tabc123");
    }

    #[test]
    fn test_csv_output() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Csv);
        w.write_record(&sample_record()).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("file,method,value"));
        assert!(s.contains("main.c,blake3,abc123"));
    }

    #[test]
    fn test_shell_output() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Shell);
        w.write_record(&sample_record()).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("file='main.c'"));
        assert!(s.contains("method='blake3'"));
    }

    #[test]
    fn test_shell_escaping() {
        let mut buf = Vec::new();
        let mut w = FormatWriter::new(&mut buf, OutputFormat::Shell);
        let rec = Record::new().field("name", "it's a test");
        w.write_record(&rec).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("name='it'\\''s a test'"));
    }
}
