//! Benchmarking utilities needed by multiple modules of this crate

/// Generate a big string literal
macro_rules! long_string {
    () => {"This is a long string, you can use it to benchmark specific \
           parts of the log record (de)serialization process. The string \
           is long enough to offset the overhead of any other field of the \
           log record. Sadly, we can't just use an &'static str because \
           the std::fmt machinery truly, positively wants a string \
           literal, but hopefully you won't mind this somewhat unorthodox \
           use of macros, everything-looks-like-a-nail style... But \
           now, seriously, if your logs are getting longer than this \
           string, you may really want to consider shrinking them!"}
}

/// Produce a minimal log record for benchmarking fixed codec overheads
pub fn min_record() -> log::Record<'static> {
    log::Record::builder()
        .args(format_args!(""))
        .level(log::Level::Error)
        .target(&"")
        .module_path(None)
        .file(None)
        .line(None)
        // TODO: Support key_values
        .build()
}

/// Produce a log record with big args for benchmarking fmt::Arguments
/// (de)serialization overhead
pub fn args_record() -> log::Record<'static> {
    log::Record::builder()
        .args(format_args!(long_string!()))
        .level(log::Level::Error)
        .target(&"")
        .module_path(None)
        .file(None)
        .line(None)
        // TODO: Support key_values
        .build()
}

/// Produce a log record with a big target for benchmarking string
/// (de)serialization overhead
pub fn target_record() -> log::Record<'static> {
    log::Record::builder()
        .args(format_args!(""))
        .level(log::Level::Error)
        .target(&long_string!())
        .module_path(None)
        .file(None)
        .line(None)
        // TODO: Support key_values
        .build()
}
