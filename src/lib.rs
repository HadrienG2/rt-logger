#[allow(deprecated)]
use abomonation::{Abomonation, unsafe_abomonate};

use std::io::{Result as IOResult, Write};


// Mirrors log::Level, must be kept in sync with it
#[derive(Clone, Copy)]
enum Level {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

unsafe impl Abomonation for Level {}

impl From<log::Level> for Level {
    fn from(l: log::Level) -> Self {
        match l {
            log::Level::Error => Level::Error,
            log::Level::Warn => Level::Warn,
            log::Level::Info => Level::Info,
            log::Level::Debug => Level::Debug,
            log::Level::Trace => Level::Trace,
        }
    }
}

impl Into<log::Level> for Level {
    fn into(self) -> log::Level {
        match self {
            Level::Error => log::Level::Error,
            Level::Warn => log::Level::Warn,
            Level::Info => log::Level::Info,
            Level::Debug => log::Level::Debug,
            Level::Trace => log::Level::Trace,
        }
    }
}


// Mirrors log::Record, must be kept in sync with it
struct RecordWithoutArgs<'a> {
    level: Level,
    target: &'a str,
    // NOTE: args cannot be abomonated and must be serialized separately
    module_path: Option<&'a str>,
    file: Option<&'a str>,
    line: Option<u32>,
    // FIXME: Support key_values
}

// FIXME: Fix abomonation_derive so that I can use it
unsafe_abomonate!{ RecordWithoutArgs<'_> : level,
                                           target,
                                           module_path,
                                           file,
                                           line }


// Serialize a log::Record.
//
// # Safety
//
// This function uses `abomonation::encode` and shares all of its safety issues.
//
// TODO: Add tests
pub unsafe fn encode_log<W: Write>(record: &log::Record, mut write: W) -> IOResult<()> {
    // Determine the size of the formatted log message
    use std::fmt::Write as FmtWrite;
    struct BytesCounter(usize);
    impl FmtWrite for BytesCounter {
        fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
            self.0 += s.len();
            Ok(())
        }
    }
    let mut ctr = BytesCounter(0);
    ctr.write_fmt(*record.args()).expect("Infaillible by design");
    let msg_size: usize = ctr.0;

    // Push the log message's size, then the log message itself
    abomonation::encode(&msg_size, &mut write)?;
    write.write_fmt(*record.args())?;

    // Extract the other record parameters into a struct
    let record_wo_args = RecordWithoutArgs {
        level: record.level().into(),
        target: record.target(),
        module_path: record.module_path(),
        file: record.file(),
        line: record.line(),
        // FIXME: Support key_values
    };

    // Push the other record parameters
    abomonation::encode(&record_wo_args, &mut write)
}


// De-serialize a log::Record, process it and returns the results.
//
// I would like to simply return the log::Record, but the fact that it contains
// an fmt::Arguments means that it cannot leave the stack frame that it
// originates from, and must be processed immediately.
//
// # Safety
//
// This function uses `abomonation::decode` and shares all of its safety issues.
//
// TODO: Add tests
pub unsafe fn decode_and_process_log<'a, R>(
    bytes: &'a mut [u8],
    mut process: impl FnMut(&log::Record) -> R
) -> Option<(R, &'a mut [u8])> {
    // Retrieve message size, abort if input buffer is obviously too small
    let (msg_size, bytes) = abomonation::decode::<usize>(bytes)?;
    if *msg_size > bytes.len() { return None; }

    // Retrieve message
    let (msg_bytes, bytes) = bytes.split_at_mut(*msg_size);
    let msg = std::str::from_utf8_unchecked(msg_bytes);

    // Retrieve remaining fields, reconstruct record, and process it
    let (record_wo_args, bytes) = abomonation::decode::<RecordWithoutArgs>(bytes)?;
    let result = process(
        &log::Record::builder()
                     .args(format_args!("{}", msg))
                     .level(record_wo_args.level.into())
                     .target(record_wo_args.target)
                     .module_path(record_wo_args.module_path)
                     .file(record_wo_args.file)
                     .line(record_wo_args.line)
                     // FIXME: Support key_values
                     .build()
    );

    // Return the processing results, and remaining bytes
    Some((result, bytes))
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}