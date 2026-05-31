/// Standard exit codes for logicutils CLI protocol.
///
/// All logicutils utilities follow this convention:
/// - 0: success / true / fresh / match found
/// - 1: failure / false / stale / no match
/// - 2: usage or runtime error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ExitCode {
    Success = 0,
    Failure = 1,
    Error = 2,
}

impl ExitCode {
    pub fn as_i32(self) -> i32 {
        self as i32
    }
}

impl From<ExitCode> for std::process::ExitCode {
    fn from(code: ExitCode) -> Self {
        std::process::ExitCode::from(code as u8)
    }
}

impl From<bool> for ExitCode {
    fn from(b: bool) -> Self {
        if b { ExitCode::Success } else { ExitCode::Failure }
    }
}
