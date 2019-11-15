/// Testing utilities needed by multiple modules of this crate

use crate::serialization::Level;
use quickcheck_derive::Arbitrary;


/// QuickCheck-friendly variant of log::Record
#[derive(Arbitrary, Clone, Debug)]
pub struct ArbitraryRecord {
    message: String,
    level: Level,
    target: String,
    module_path: Option<String>,
    file: Option<String>,
    line: Option<u32>
}

impl ArbitraryRecord {
    /// Turn this into a log::Record, process it, and return the result
    ///
    /// We can't return the Record due to fmt::Arguments lifetime issues.
    pub fn process<R>(self, action: impl FnOnce(log::Record) -> R) -> R {
        action(
            log::Record::builder()
                .args(format_args!("{}", self.message))
                .level(self.level.into())
                .target(&self.target)
                .module_path(self.module_path.as_ref().map(String::as_ref))
                .file(self.file.as_ref().map(String::as_ref))
                // Zero line numbers don't exist and we exploit this
                .line(self.line.filter(|&line| line != 0))
                // TODO: Support key_values
                .build()
        )
    }
}