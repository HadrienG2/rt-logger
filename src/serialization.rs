//! Facilities for serializing and deserializing log::Record
//!
//! This implements the most minimal serialization that will possibly allow
//! transferring a log::Record across threads, aka abomonation. As a result, the
//! serialization is not properly type-checked, and is therefore unsafe. The
//! intent is to provide a safe API on top of that.
//!
//! We do not use serde because...
//! - By itself, Serde does not guarantee real-time safety. In fact, the default
//!   implementation of Serializer::collect_str(), which is used when
//!   serializing `fmt::Arguments`, is RT-unsafe because it allocates a String.
//! - There does not seem to be particular interest in addressing this from
//!   popular Serde serializers, even performance-oriented ones like bincode
//!   (see https://github.com/servo/bincode/issues/172 )
//! - Complex serde serializers with features like schema evolution are overkill
//!   for our intra-process use case and likely to bring performance down,
//!   whereas we aim to enable logging on RT threads with a tight time budget.

use abomonation::Entomb;
use abomonation_derive::{Abomonation};

#[cfg(test)]
use quickcheck_derive::Arbitrary;

use std::{
    fmt,
    num::NonZeroU32,
    io::{Result as IOResult, Write},
};


/// A log::Level clone on which I can derive traits
///
/// This definition mirrors `log::Level` and must be kept in sync with it.
///
/// # Safety
///
/// This struct must have no uninitialized padding bytes in order to avoid
/// triggering UB in `abomonation::encode`. Until that UB issue is resolved,
/// which will require core Rust changes and may therefore take a long while,
/// please preserve this property while extending this struct for support of
/// future `log` versions and features.
///
/// For now, that property is guaranteed for free by `Level` being a
/// member-less enum with repr(usize) (usize is needed for RecordWithoutArgs).
//
// TODO: Once the padding bytes issue is resolved, remove this space-inefficient
//       repr and implement the language-level padding bytes UB fix instead.
#[cfg_attr(test, derive(Arbitrary))]
#[derive(Abomonation, Clone, Copy, Debug)]
#[repr(usize)]
pub enum Level {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

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
///
/// `fmt::Arguments` cannot be serialized by abomonation, and must be printed as
/// a string after the serialized RecordWithoutArgs. We only take note of the
/// length of that string in RecordWithoutArgs so that we can later deserialize
/// the string.
///
/// This struct mirrors `log::Record`, and should be kept in sync with it as
/// `log::Record` evolves. For example, it should follow the impeding
/// stabilization of structured logging in `log` by providing a way to serialize
/// that information too.
///
/// # Safety
///
/// This struct must have no uninitialized padding bytes in order to avoid
/// triggering UB in `abomonation::encode`. Until that UB issue is resolved,
/// which will require core Rust changes and may therefore take a long while,
/// please preserve this property while extending this struct for support of
/// future `log` versions and features.
///
/// Proving absence of padding bytes may only be done for a specific pointer
/// width. So far, this has been done for 16-bit, 32-bit, 64-bit and 128-bit
/// architectures, which covers all architectures that Rust supports currently
/// and is expected to support for the foreseeable future. If a proof has not
/// been provided for your architecture, the RecordWithoutArgs type will not be
/// available, in which case you are welcome to do the proof and submit a patch.
//
// TODO: Once the padding bytes issue is resolved, remove the repr(C) and manual
//       padding and implement the language-level padding bytes UB fix instead.
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32",
          target_pointer_width = "64", target_pointer_width = "128"))]
#[derive(Abomonation)]
#[repr(C)]  // Used for padding byte avoidance through fine data layout control
struct RecordWithoutArgs<'a> {      // === PROOF OF ABSENCE OF PADDING BYTES ===
    level: Level,                   // repr = usize, no padding because on top
    target: &'a str,                // repr = 2*usize, no padding btw same type
    args_len: usize,                // repr = usize, no padding btw same type
    module_path: Option<&'a str>,   // repr = 2*usize due to null ref opt,
                                    //                no padding btw same type
    file: Option<&'a str>,          // repr = 2*usize due to null ref opt,
                                    //                no padding btw same type
    line: Option<NonZeroU32>,       // repr = u32 due to NonZeroU32 opt, and
                                    //            u32 <= usize on 32/64-bit
                                    //            CPUs, so no padding expected.
                                    //            Also happens to works for
                                    //            16-bit CPUs, because
                                    //            8*16-bit above = 4*32-bit, so
                                    //            we'd stay aligned on 32-bit
                                    //            through the fields above.
    #[cfg(target_pointer_width="64")]
    __padding1: u32,                // Needed so that struct size is multiple of
                                    // align on 64-bit platforms.
    #[cfg(target_pointer_width="128")]
    __padding2: u64,                // Needed so that size is multiple of align
                                    // on 128-bit platforms (yes, those might be
                                    // on the future horizon, e.g. RISC-V has
                                    // defined an instruction set for that...).
                                    //
                                    // + No data recursively serialized by
                                    //   abomonation (via the &str refs) has
                                    //   padding bytes, since UTF-8 has align=1.
    // TODO: Support key_values, bearing in mind the above constraints
}

/// Separate the fmt::Arguments from the rest of a log::Record
///
/// fmt::Arguments is too opaque to be serializable, therefore it must be
/// handled specially by printing it to the output data stream.
fn split_log_args<'a>(record: &log::Record<'a>) -> (fmt::Arguments<'a>,
                                                    RecordWithoutArgs<'a>) {
    let record_wo_args = RecordWithoutArgs {
        level: record.level().into(),
        target: record.target(),
        args_len: args_str_len(*record.args()),
        module_path: record.module_path(),
        file: record.file(),
        line: record.line().map(|line| {
            NonZeroU32::new(line).expect("Line numbers should be 1-based")
        }),
        #[cfg(target_pointer_width="64")]
        __padding1: 0,
        #[cfg(target_pointer_width="128")]
        __padding2: 0,
        // TODO: Support key_values
    };
    (*record.args(), record_wo_args)
}

/// Tell how many bytes would be generated by printing an fmt::Arguments
///
/// We need this both to get advance knowledge of the serialized record size and
/// to emit the string length before the string in the output data stream.
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

/// Serialize a log::Record
pub fn encode_log<W: Write>(record: &log::Record, mut write: W) -> IOResult<()> {
    // Isolate the fmt::Arguments from the input record
    let (record_args, record_wo_args) = split_log_args(record);

    // Push everything but the fmt::Arguments. This includes the length of the
    // formatted fmt::Arguments, which we'll use during decoding.
    //
    // This is safe because we have checked that `RecordWithoutArgs` does not
    // contain padding bytes, which is the only known source of UB in
    // `abomonation::encode`.
    unsafe {
        abomonation::encode::<RecordWithoutArgs, _>(&record_wo_args, &mut write)?;
    }

    // Print the fmt::Arguments as an UTF-8 string at the end.
    write.write_fmt(record_args)
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
/// This function should only be used on bytes that were produced by
/// `encode_log()` _from the same build of this library_. Passing arbitrary
/// bytes to it can result in undefined behavior such as null references or
/// invalid UTF-8 in an &str. And different builds of this library (e.g. from
/// different CPU architectures, with different compiler settings...) may not
/// agree on the data format which serialized bytes should have.
///
/// In addition, input bytes must be aligned on a `log_alignment()` boundary, or
/// else you'll get misaligned pointer UB (possible consequences of which
/// include mangled data and instant "invalid operation" program crashes).
pub unsafe fn decode_and_process_log<'a, R>(
    bytes: &'a mut [u8],
    process: impl FnOnce(&log::Record) -> R
) -> Option<(R, &'a mut [u8])> {
    // Retrieve everything but the fmt::Arguments.
    let (record_wo_args, bytes) = abomonation::decode::<RecordWithoutArgs>(bytes)?;

    // Retrieve the fmt::Arguments string, abort if input buffer is too small
    if record_wo_args.args_len > bytes.len() { return None; }
    let (msg_bytes, bytes) = bytes.split_at_mut(record_wo_args.args_len);
    let msg = std::str::from_utf8_unchecked(msg_bytes);

    // Reconstruct a log::Record and process it
    let result = process(
        &log::Record::builder()
                     .args(format_args!("{}", msg))
                     .level(record_wo_args.level.into())
                     .target(record_wo_args.target)
                     .module_path(record_wo_args.module_path)
                     .file(record_wo_args.file)
                     .line(record_wo_args.line.map(u32::from))
                     // TODO: Support key_values
                     .build()
    );

    // Return the processing results, and remaining bytes
    Some((result, bytes))
}

/// Report the number of bytes required to serialize a log::Record
pub fn measure_log(record: &log::Record) -> usize {
    let (_record_args, record_wo_args) = split_log_args(record);
    abomonation::measure::<RecordWithoutArgs>(&record_wo_args)
        + record_wo_args.args_len
}

/// Report the memory alignment of a serialized log::Record
pub fn log_alignment() -> usize {
    // The fact that we print `fmt::Arguments` as an UTF-8 string after the
    // serialized `RecordWithoutArgs` does not add to the alignment requirements
    // because an UTF-8 string is byte-aligned, which is the weakest alignment.
    <RecordWithoutArgs as Entomb>::alignment()
}


#[cfg(test)]
mod tests {
    use abomonation::align::AlignedBytes;
    use crate::tests::ArbitraryRecord;
    use quickcheck_macros::quickcheck;
    use std::mem::size_of;
    use super::RecordWithoutArgs;

    #[test]
    fn no_record_wo_args_padding() {
        // Since it is currently UB to send a data structure with uninitialized
        // padding bytes to abomonation, we rely on the fact that
        // RecordWithoutArgs does not have padding bytes for safety.
        //
        // We manually proved that above, but manual proofs can be wrong, so
        // let's add a layer of automatic verification.
        assert_eq!(size_of::<RecordWithoutArgs>(),
                   size_of::<usize>()          // level: Level is repr(usize)
                       + 2*size_of::<usize>()  // target: &str is two usizes
                       + size_of::<usize>()    // args_len: usize
                       + 2*size_of::<usize>()  // module_path: Option<&str>
                                               // == &str due to null ref opt
                       + 2*size_of::<usize>()  // file: Option<&str>, cf above
                       + size_of::<u32>()      // line: u32
                       + if cfg!(target_pointer_width="64")  // __padding1: u32
                         { size_of::<u32>() } else { 0 }
                       + if cfg!(target_pointer_width="128")  // __padding2: u64
                         { size_of::<u64>() } else { 0 }
                  );
    }

    #[quickcheck]
    /// Check that we can go from log::Record to bytes and back
    fn round_trip(record: ArbitraryRecord) {
        // Get a random log::Record
        record.process(|record| {
            // Serialize it into a Vec of bytes
            let mut bytes = Vec::new();
            super::encode_log(&record, &mut bytes)
                 .expect("Failed to serialize log::Record");

            // Check that the serialization produced as many bytes as expected
            assert_eq!(bytes.len(), super::measure_log(&record),
                       "Serialized record is not as long as expected");

            // Check that the serialized data has no padding bytes. This should
            // be the case since UTF-8 strings are just initialized bytes with
            // alignment 1... but hey, better check anyway.
            //
            // The fact that RecordWithoutArgs itself does not have padding
            // bytes is checked in the separate no_record_wo_args_padding test.
            assert_eq!(bytes.len(),
                       size_of::<RecordWithoutArgs>()
                           + record.target().len()
                           + record.module_path().map(&str::len).unwrap_or(0)
                           + record.file().map(&str::len).unwrap_or(0)
                           + super::args_str_len(*record.args()));

            // Deserialize it...
            let mut bytes = AlignedBytes::<RecordWithoutArgs>::new(&mut bytes[..]);
            let ((), remaining_bytes) = unsafe {
                super::decode_and_process_log(&mut bytes, |record2| {
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


/// Performance benchmarks
///
/// These benchmarks masquerading as tests are a stopgap solution until
/// benchmarking lands in Stable Rust. They should be compiled in release mode,
/// and run with only one OS thread. In addition, the default behaviour of
/// swallowing test output should obviously be suppressed.
///
/// TL;DR: cargo test --release -- --ignored --nocapture --test-threads=1
///
/// TODO: Switch to standard Rust benchmarks once they are stable
///
#[cfg(test)]
mod benchmarks {
    use abomonation::align::AlignedBytes;
    use crate::bench;
    use super::RecordWithoutArgs;

    const NUM_BENCH_ITERS: u32 = 50_000_000;

    /// Benchmark for minimal serialization overhead
    #[test]
    #[ignore]
    fn min_serialize() {
        bench_serialize(&bench::min_record());
    }

    /// Benchmark for minimal deserialization overhead
    #[test]
    #[ignore]
    fn min_deserialize() {
        bench_deserialize(&bench::min_record());
    }

    /// Benchmark for args serialization overhead
    #[test]
    #[ignore]
    fn args_serialize() {
        bench_serialize(&bench::args_record());
    }

    /// Benchmark for args deserialization overhead
    #[test]
    #[ignore]
    fn args_deserialize() {
        bench_deserialize(&bench::args_record());
    }

    /// Benchmark for target serialization overhead
    #[test]
    #[ignore]
    fn target_serialize() {
        bench_serialize(&bench::target_record());
    }

    /// Benchmark for target deserialization overhead
    #[test]
    #[ignore]
    fn target_deserialize() {
        bench_deserialize(&bench::target_record());
    }

    /// Generic microbenchmark for serialization overhead
    fn bench_serialize(record: &log::Record) {
        // Prepare storage for serializing the log
        let expected_size = super::measure_log(&record);
        let mut bytes = Vec::with_capacity(expected_size);

        // Benchmark log serialization
        testbench::benchmark(NUM_BENCH_ITERS, || {
            bytes.clear();
            super::encode_log(&record, &mut bytes).unwrap();
            assert_eq!(bytes.len(), expected_size);
        });
    }

    /// Generic microbenchmark for deserialization overhead
    fn bench_deserialize(record: &log::Record) {
        // Serialize the log
        let mut bytes = Vec::with_capacity(super::measure_log(&record));
        super::encode_log(&record, &mut bytes).unwrap();
        let mut bytes = AlignedBytes::<RecordWithoutArgs>::new(&mut bytes);

        // Benchmark log deserialization
        testbench::benchmark(NUM_BENCH_ITERS, || {
            unsafe {
                super::decode_and_process_log(&mut bytes, bench::ignore_log)
            }.unwrap();
        });
    }
}
