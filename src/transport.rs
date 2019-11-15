//! Facilities for transporting serialized `log::Record`s from real-time threads
//! to a non-real-time logging thread.

use crate::serialization;

use crossbeam_channel::{self, Receiver, Sender, TryRecvError, TrySendError};

use std::{
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    num::NonZeroUsize,
};


/// Fixed-size log storage block size
///
/// This should be large enough for storing any realistic log record. Ideally,
/// I would like not to impose this, instead letting you use the LogStorageBlock
/// size that's right for your application, but that requires const generics...
//
// FIXME: Remove hard limit on log size by allowing variable-sized log entries.
//        But this will require a custom lock-free MPSC channel type...
const LOG_STORAGE_BLOCK_SIZE: usize = 1024;

/// Byte storage that's aligned on a `serialization::log_alignment()` boundary.
///
/// Unfortunately, as of current Rust, this definition must be kept in sync with
/// that of `serialization::log_alignment()` by hand, and using a rather
/// unpleasant syntax. Fortunately, there is a test making sure that the two
/// definitions are in sync on your machine. Hopefully things will get better
/// with new language versions and future library evolutions.
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32",
          target_pointer_width = "64", target_pointer_width = "128"))]
#[cfg_attr(target_pointer_width = "16", repr(align(4)))]
#[cfg_attr(target_pointer_width = "32", repr(align(4)))]
#[cfg_attr(target_pointer_width = "64", repr(align(8)))]
#[cfg_attr(target_pointer_width = "128", repr(align(16)))]
struct LogStorageBlock([u8; LOG_STORAGE_BLOCK_SIZE]);


/// Mechanism to send logs to a logging thread
//
// TODO: Try to make a channel which actually supports variable-sized logs...
pub struct LogSender {
    /// Bounded lock-free channel for log storage blocks
    sender: Sender<LogStorageBlock>,

    /// Counter of dropped log entries
    dropped: Arc<AtomicUsize>,
}

impl LogSender {
    /// Attempt to send a log record on this channel without blocking
    ///
    /// This method has mostly the same semantics as the eponymous method of
    /// `std::mpsc::SyncSender`, but with the extra perk that the log record's
    /// recipient (aka the logging thread) will be notified if a log cannot be
    /// sent because the channel is full.
    ///
    /// The recommended error handling pattern is to accept the fact that the
    /// log record is lost and either panic or move on.
    pub fn try_send<'a>(&self, log: log::Record<'a>)
                       -> Result<(), TrySendError<log::Record<'a>>> {
        // Serialize the log
        let mut storage_block = LogStorageBlock([0; LOG_STORAGE_BLOCK_SIZE]);
        serialization::encode_log(&log, &mut storage_block.0[..])
            .expect("Log size exceeded current LOG_STORAGE_BLOCK_SIZE limit");

        // Try to send it to the logging thread
        match self.sender.try_send(storage_block) {
            Ok(()) => Ok(()),
            Err(TrySendError::Full(_)) => {
                // Count "channel full" errors
                self.dropped.fetch_add(1, Ordering::Relaxed);
                Err(TrySendError::Full(log))
            }
            Err(TrySendError::Disconnected(_)) =>
                Err(TrySendError::Disconnected(log)),
        }
    }

    // NOTE: No synchronous send() method is exposed, as it is always a mistake
    //       to use such a method on real-time threads.
}


/// Mechanism to process logs in a logging thread
//
// TODO: Try to make a channel which actually supports variable-sized logs...
pub struct LogReceiver {
    /// Bounded lock-free channel for log storage blocks
    receiver: Receiver<LogStorageBlock>,

    /// Counter of dropped log entries
    dropped: Arc<AtomicUsize>,
}

/// Events to be processed by the logging thread
#[derive(Debug)]
pub enum LogEvent<'a> {
    /// A new log was received and should be emitted
    Log(&'a log::Record<'a>),

    /// Some logs were dropped because the log channel capacity was exhausted
    DroppedLogs(usize),
}

impl LogReceiver {
    /// Attempt to process an incoming log without blocking.
    ///
    /// This has mostly the same semantics as `mpsc::Receiver::try_recv`, but
    /// due to the weird semantics of `std::fmt::Arguments` the log cannot
    /// the function that deserialized it and must be processed in-place via a
    /// callback. Don't worry, we'll send you the result back.
    pub fn try_process<R>(&self, callback: impl FnOnce(LogEvent) -> R)
                         -> Result<R, TryRecvError> {
        // Check for dropped logs
        if let Some(dropped) = self.check_dropped_logs() {
            return Ok(callback(LogEvent::DroppedLogs(dropped.into())));
        }

        // We already check for this in unit tests, but the user may not run
        // them for his CPU architecture, so having an extra layer of
        // defense-in-depth in debug builds is a good idea.
        debug_assert_eq!(std::mem::align_of::<LogStorageBlock>(),
                         crate::serialization::log_alignment(),
                         "Log storage block alignment went out of sync with \
                          log serialization, please re-synchronize them");

        // Try to fetch a log
        let mut storage_block = self.receiver.try_recv()?;

        // If successful, deserialize and process it
        //
        // This is safe because the API of `log_channel` presents mixing and
        // matching one build of `LogSender` with another build of `LogReceiver`
        // and alignment is taken care of by the LogStorageBlock newtype.
        Ok(unsafe {
            serialization::decode_and_process_log(
                &mut storage_block.0[..],
                |log| callback(LogEvent::Log(log))
            )
        }.expect("Failed to decode a serialized log").0)
    }

    /// Check for log buffer overruns and reset log overrun counter
    fn check_dropped_logs(&self) -> Option<NonZeroUsize> {
        // Avoid expensive atomic RMW operations unless necessary
        if self.dropped.load(Ordering::Relaxed) != 0 {
            NonZeroUsize::new(self.dropped.swap(0, Ordering::Relaxed))
        } else {
            None
        }
    }

    // FIXME: Implement other mpsc::Receiver methods
}


/// Create a channel for passing logs between threads
///
/// General-purpose memory allocators are not real-time safe, therefore for our
/// purpose we must use a bounded-capacity channel that allocates all storage at
/// initialization time.
///
/// The capacity is given in bytes of storage, since that's the unit that makes
/// most sense for variable-sized log entries. Once the channel is full, it will
/// start dropping log entries, which will be reported by the logger thread. You
/// should obviously strive to avoid this event by using sufficiently
/// high-capacity log channels and making sure your logging thread can drain the
/// channel faster than the real-time threads are filling it.
//
// TODO: Eliminate the need for storage blocks or signal it here
pub fn log_channel(capacity: usize) -> (LogSender, LogReceiver) {
    let num_blocks =
        capacity / LOG_STORAGE_BLOCK_SIZE
        + if capacity % LOG_STORAGE_BLOCK_SIZE != 0 { 1 } else { 0 }; 

    let (sender, receiver) = crossbeam_channel::bounded(num_blocks);
    let dropped = Arc::new(AtomicUsize::new(0));

    let log_sender = LogSender {
        sender,
        dropped: dropped.clone(),
    };
    let log_receiver = LogReceiver { receiver, dropped };
    (log_sender, log_receiver)
}


#[cfg(test)]
mod tests {
    use crate::{
        serialization,
        tests::ArbitraryRecord,
    };
    use quickcheck_macros::quickcheck;
    use std::num::NonZeroUsize;
    use super::{LogEvent, LogStorageBlock, LOG_STORAGE_BLOCK_SIZE};

    #[test]
    fn storage_block_alignment() {
        assert_eq!(std::mem::align_of::<LogStorageBlock>(),
                   crate::serialization::log_alignment(),
                   "Log storage block alignment went out of sync with \
                    log serialization, please re-synchronize them");
    }

    #[quickcheck]
    /// Check that we can go from log::Record to bytes and back
    fn round_trip(record: ArbitraryRecord) {
        // Make a log channel
        // FIXME: No implementation details, please
        let (sender, receiver) = super::log_channel(LOG_STORAGE_BLOCK_SIZE);

        // Number of dropped logs should be initially zero
        assert_eq!(receiver.check_dropped_logs(), NonZeroUsize::new(0),
                   "A newly created channel should have no dropped log");

        // Get a random log::Record
        record.process(|record| {
            // Ignore excessively large logs
            if serialization::measure_log(&record) > LOG_STORAGE_BLOCK_SIZE {
                return;
            }

            // Push the log through the channel
            sender.try_send(record.clone())
                  .expect("Failed to send a log::Record");

            // Try to push another log. This should fail and be reported on the
            // receiver's side.
            sender.try_send(record.clone())
                  .expect_err("A log channel with a capacity of 1 should only \
                               have room for one log record");
            receiver.try_process(|event| {
                if let LogEvent::DroppedLogs(dropped) = event {
                    assert_eq!(dropped, 1, "Should report one dropped log");
                } else {
                    panic!("Dropped logs should be reported");
                }
            }).expect("One dropped log should be reported");

            // Try to get the original log back...
            receiver.try_process(|event| {
                if let LogEvent::Log(record2) = event {
                    // ...and check that the output log::Record is similar
                    // (our criteria being having the same Debug representation)
                    assert_eq!(format!("{:?}", record),
                               format!("{:?}", record2),
                               "Retrieved log::Record doesn't match");
                } else {
                    panic!("No dropped log should be reported here");
                }
            }).expect("Failed to retrieve log::Record");
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
    use crate::bench;
    use super::{LogEvent, LOG_STORAGE_BLOCK_SIZE};

    // WARNING: Running these benchmarks with a high iteration count is highly
    //          memory intensive, you may want to do stats on multiple runs.
    const NUM_SEND_RECV_ITERS: u32 = 2_000_000;

    const NUM_ROUND_TRIP_ITERS: u32 = 5_000_000;

    /// Benchmark for minimal log emission overhead
    #[test]
    #[ignore]
    fn min_send() {
        bench_send(&bench::min_record());
    }

    /// Benchmark for minimal log reception overhead
    #[test]
    #[ignore]
    fn min_recv() {
        bench_recv(&bench::min_record());
    }

    /// Benchmark for minimal log emission+reception round-trip overhead
    #[test]
    #[ignore]
    fn min_round_trip() {
        bench_round_trip(&bench::min_record());
    }

    /// Benchmark for args log emission overhead
    #[test]
    #[ignore]
    fn args_send() {
        bench_send(&bench::args_record());
    }

    /// Benchmark for args log reception overhead
    #[test]
    #[ignore]
    fn args_recv() {
        bench_recv(&bench::args_record());
    }

    /// Benchmark for args log emission+reception round-trip overhead
    #[test]
    #[ignore]
    fn args_round_trip() {
        bench_round_trip(&bench::args_record());
    }

    /// Benchmark for target log emission overhead
    #[test]
    #[ignore]
    fn target_send() {
        bench_send(&bench::target_record());
    }

    /// Benchmark for target log reception overhead
    #[test]
    #[ignore]
    fn target_recv() {
        bench_recv(&bench::target_record());
    }

    /// Benchmark for target log emission+reception round-trip overhead
    #[test]
    #[ignore]
    fn target_round_trip() {
        bench_round_trip(&bench::target_record());
    }

    /// Generic microbenchmark for log emission overhead
    fn bench_send(record: &log::Record) {
        // Prepare a channel for sending the logs
        // FIXME: No implementation details, please
        let capacity = LOG_STORAGE_BLOCK_SIZE * (NUM_SEND_RECV_ITERS as usize);
        let (sender, _receiver) = super::log_channel(capacity);

        // Benchmark log emission
        testbench::benchmark(NUM_SEND_RECV_ITERS, || {
            sender.try_send(record.clone()).unwrap();
        });
    }

    /// Generic microbenchmark for log reception overhead
    fn bench_recv(record: &log::Record) {
        // Prepare a channel full of logs
        // FIXME: No implementation details, please
        let capacity = LOG_STORAGE_BLOCK_SIZE * (NUM_SEND_RECV_ITERS as usize);
        let (sender, receiver) = super::log_channel(capacity);
        for _ in 0..NUM_SEND_RECV_ITERS {
            sender.try_send(record.clone()).unwrap();
        }

        // Benchmark log reception
        testbench::benchmark(NUM_SEND_RECV_ITERS, || {
            receiver.try_process(ignore_event).unwrap();
        });
    }

    /// Generic microbenchmark for log emission+reception round-trip
    ///
    /// We normally prefer to microbenchmark individual operations, but in this
    /// particular case that makes our benchmark unrealistically
    /// memory-intensive, so it's good to have another benchmark with a more
    /// realistic cache footprint as a point of comparison.
    fn bench_round_trip(record: &log::Record) {
        // Prepare a channel for holding the logs
        // FIXME: No implementation details, please
        let (sender, receiver) = super::log_channel(LOG_STORAGE_BLOCK_SIZE);

        // Benchmark log emission+reception round-trip
        testbench::benchmark(NUM_ROUND_TRIP_ITERS, || {
            sender.try_send(record.clone()).unwrap();
            receiver.try_process(ignore_event).unwrap();
        });
    }

    /// A non-optimizable ~no-op for log reception benchmarks
    #[inline(never)]
    pub fn ignore_event(event: LogEvent) {
        // Even with inline(never), it's more prudent to do _something_ with the
        // parameter, just to make sure the compiler doesn't add some sort of
        // "does not make meaningful use of parameter" metadata to the function.
        if let LogEvent::Log(record) = event {
            assert_eq!(record.level(), log::Level::Error);
        }
    }
}
