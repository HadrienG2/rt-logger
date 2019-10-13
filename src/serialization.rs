//! Facilities for serializing and deserializing log::Record
//!
//! This implements the most minimal serialization that will possibly allow
//! transferring a log::Record across threads, aka abomonation. As a result, the
//! serialization is not properly type-checked, and is therefore unsafe.

use abomonation::{Entomb, Exhume};

#[cfg(test)]
use quickcheck_derive::Arbitrary;

use std::{
    fmt,
    io::{Result as IOResult, Write},
    ptr::NonNull,
};


/// A log::Level clone on which I can derive traits
//
// NOTE: Mirrors log::Level, must be kept in sync with it
//
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Clone, Copy, Debug)]
enum Level {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

// FIXME: Derive this, rather than implementing it manually
unsafe impl Entomb for Level {}
unsafe impl Exhume<'_> for Level {}

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


/// A log::Record clone (w/o args) on which I can derive traits
//
// NOTE: Mirrors log::Record, must be kept in sync with it
//
struct RecordWithoutArgs<'a> {
    level: Level,
    target: &'a str,
    // NOTE: args cannot be abomonated and must be serialized separately
    module_path: Option<&'a str>,
    file: Option<&'a str>,
    line: Option<u32>,
    // FIXME: Support key_values
}

// FIXME: Derive this, rather than implementing it manually
unsafe impl Entomb for RecordWithoutArgs<'_> {
    unsafe fn entomb<W: Write>(&self, write: &mut W) -> IOResult<()> {
        Level::entomb(&self.level, write)?;
        <&str>::entomb(&self.target, write)?;
        <Option<&str>>::entomb(&self.module_path, write)?;
        <Option<&str>>::entomb(&self.file, write)?;
        <Option<u32>>::entomb(&self.line, write)
    }

    fn extent(&self) -> usize {
        Level::extent(&self.level)
        + <&str>::extent(&self.target)
        + <Option<&str>>::extent(&self.module_path)
        + <Option<&str>>::extent(&self.file)
        + <Option<u32>>::extent(&self.line)
    }
}
//
unsafe impl<'de> Exhume<'de> for RecordWithoutArgs<'de> {
    unsafe fn exhume(self_: NonNull<Self>, mut bytes: &'de mut [u8]) -> Option<&'de mut [u8]> {
        bytes = Level::exhume(From::from(&mut (*self_.as_ptr()).level), bytes)?;
        bytes = <&str>::exhume(From::from(&mut (*self_.as_ptr()).target), bytes)?;
        bytes = <Option<&str>>::exhume(From::from(&mut (*self_.as_ptr()).module_path), bytes)?;
        bytes = <Option<&str>>::exhume(From::from(&mut (*self_.as_ptr()).file), bytes)?;
        <Option<u32>>::exhume(From::from(&mut (*self_.as_ptr()).line), bytes)
    }
}

/// Separate the fmt::Arguments from the rest of a log::Record
///
/// fmt::Arguments is too opaque to be serializable, therefore it must be
/// handled specially by printing it to the output data stream.
///
fn split_log_args<'a>(record: &log::Record<'a>) -> (fmt::Arguments<'a>,
                                                    RecordWithoutArgs<'a>) {
    let record_wo_args = RecordWithoutArgs {
        level: record.level().into(),
        target: record.target(),
        module_path: record.module_path(),
        file: record.file(),
        line: record.line(),
        // FIXME: Support key_values
    };
    (*record.args(), record_wo_args)
}

/// Tell how many bytes would be generated by printing an fmt::Arguments
///
/// We need this both to get advance knowledge of the serialized record size and
/// to emit the string length before the string in the output data stream.
///
fn args_str_len(args: fmt::Arguments<'_>) -> usize {
    use fmt::Write as FmtWrite;
    struct BytesCounter(usize);
    impl FmtWrite for BytesCounter {
        fn write_str(&mut self, s: &str) -> Result<(), std::fmt::Error> {
            self.0 += s.len();
            Ok(())
        }
    }
    let mut ctr = BytesCounter(0);
    ctr.write_fmt(args).expect("Infaillible by design");
    ctr.0
}

/// Serialize a log::Record.
///
/// # Safety
///
/// This function uses `abomonation::encode` and inherits its safety issues.
///
pub unsafe fn encode_log<W: Write>(record: &log::Record, mut write: W) -> IOResult<()> {
    // Isolate the fmt::Arguments from the input record
    let (record_args, record_wo_args) = split_log_args(record);

    // Push the log message's size, then the log message itself
    abomonation::encode::<usize, _>(&args_str_len(record_args), &mut write)?;
    write.write_fmt(record_args)?;

    // Push the other record parameters
    abomonation::encode::<RecordWithoutArgs, _>(&record_wo_args, &mut write)
}


/// De-serialize a log::Record, process it, and returns the results
///
/// We can't return the log::Record due to fmt::Arguments lifetime issues.
///
/// Will return None if the serialized data is invalid (buffer too short).
/// Otherwise, will return the results along with unused bytes from input.
///
/// # Safety
///
/// This function uses `abomonation::decode` and inherits its safety issues.
///
pub unsafe fn decode_and_process_log<'a, R>(
    bytes: &'a mut [u8],
    mut process: impl FnMut(&log::Record) -> R
) -> Option<(R, &'a mut [u8])> {
    // Retrieve message size, abort if input buffer is too small
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

/// Report the number of bytes required to serialize a log::Record
pub fn measure_log(record: &log::Record) -> usize {
    let (record_args, record_wo_args) = split_log_args(record);
    let message_len = args_str_len(record_args);
    abomonation::measure::<usize>(&message_len)
        + message_len
        + abomonation::measure::<RecordWithoutArgs>(&record_wo_args)
}


#[cfg(test)]
mod tests {
    use quickcheck_derive::Arbitrary;
    use quickcheck_macros::quickcheck;

    /// quickcheck-friendly variant of log::Record
    #[derive(Arbitrary, Clone, Debug)]
    struct ArbitraryRecord {
        message: String,
        level: super::Level,
        target: String,
        module_path: Option<String>,
        file: Option<String>,
        line: Option<u32>
    }

    impl ArbitraryRecord {
        /// Turn this into a log::Record, process it, and return the result
        ///
        /// We can't return the Record due to fmt::Arguments lifetime issues.
        ///
        fn process<R>(self, action: impl FnOnce(log::Record) -> R) -> R {
            action(
                log::Record::builder()
                    .args(format_args!("{}", self.message))
                    .level(self.level.into())
                    .target(&self.target)
                    .module_path(self.module_path.as_ref().map(String::as_ref))
                    .file(self.file.as_ref().map(String::as_ref))
                    .line(self.line)
                    // FIXME: Support key_values
                    .build()
            )
        }
    }

    #[quickcheck]
    /// Check that we can go from log::Record to bytes and back
    fn round_trip(record: ArbitraryRecord) {
        // Get a random log::Record
        record.process(|record| {
            // Serialize it into a Vec of bytes
            let mut v = Vec::new();
            unsafe { super::encode_log(&record, &mut v) }
                .expect("Failed to serialize log::Record");

            // Check that the serialization produced as many bytes as expected
            assert_eq!(v.len(), super::measure_log(&record),
                       "Serialized record is not as long as expected");

            // Deserialize it...
            let ((), remaining_bytes) = unsafe {
                super::decode_and_process_log(&mut v[..], |record2| {
                    // ...and check that the output log::Record is similar
                    // (our criteria being having the same Debug representation)
                    assert_eq!(format!("{:?}", record),
                               format!("{:?}", record2),
                               "Deserialized log::Record doesn't match")
                })
            }.expect("Failed to deserialize log::Record");

            // Make sure that there are no leftover bytes
            assert_eq!(remaining_bytes.len(), 0,
                       "Unexpected leftover bytes after deserialization");
        })
    }
}
