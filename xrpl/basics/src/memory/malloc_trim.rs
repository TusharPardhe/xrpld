//! Compatibility surface for `xrpl/basics/MallocTrim.h`.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MallocTrimReport {
    pub supported: bool,
    pub trim_result: i32,
    pub rss_before_kb: i64,
    pub rss_after_kb: i64,
    pub duration_us: i64,
    pub minflt_delta: i64,
    pub majflt_delta: i64,
}

impl Default for MallocTrimReport {
    fn default() -> Self {
        Self {
            supported: false,
            trim_result: -1,
            rss_before_kb: -1,
            rss_after_kb: -1,
            duration_us: -1,
            minflt_delta: -1,
            majflt_delta: -1,
        }
    }
}

impl MallocTrimReport {
    pub fn delta_kb(&self) -> i64 {
        if self.rss_before_kb < 0 || self.rss_after_kb < 0 {
            return 0;
        }
        self.rss_after_kb - self.rss_before_kb
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JemallocStats {
    pub allocated_bytes: usize,
    pub active_bytes: usize,
    pub metadata_bytes: usize,
    pub mapped_bytes: usize,
    pub resident_bytes: usize,
    pub retained_bytes: usize,
    pub arenas: u32,
}

/// Return a refreshed snapshot of the allocator used by every Quaxar runtime
/// host. `None` means this build does not install the TikV jemalloc allocator
/// or the allocator rejected a required control query.
pub fn jemalloc_stats() -> Option<JemallocStats> {
    #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
    {
        let mut old_epoch = 0_u64;
        let mut old_epoch_len = std::mem::size_of_val(&old_epoch);
        let mut new_epoch = 1_u64;
        let epoch_result = unsafe {
            tikv_jemalloc_sys::mallctl(
                c"epoch".as_ptr(),
                (&mut old_epoch as *mut u64).cast(),
                &mut old_epoch_len,
                (&mut new_epoch as *mut u64).cast(),
                std::mem::size_of_val(&new_epoch),
            )
        };
        if epoch_result != 0 {
            return None;
        }

        let mut arenas = 0_u32;
        let mut arenas_len = std::mem::size_of_val(&arenas);
        let arenas_result = unsafe {
            tikv_jemalloc_sys::mallctl(
                c"arenas.narenas".as_ptr(),
                (&mut arenas as *mut u32).cast(),
                &mut arenas_len,
                std::ptr::null_mut(),
                0,
            )
        };
        if arenas_result != 0 {
            return None;
        }

        return Some(JemallocStats {
            allocated_bytes: read_jemalloc_usize(c"stats.allocated")?,
            active_bytes: read_jemalloc_usize(c"stats.active")?,
            metadata_bytes: read_jemalloc_usize(c"stats.metadata")?,
            mapped_bytes: read_jemalloc_usize(c"stats.mapped")?,
            resident_bytes: read_jemalloc_usize(c"stats.resident")?,
            retained_bytes: read_jemalloc_usize(c"stats.retained")?,
            arenas,
        });
    }

    #[cfg(not(all(feature = "jemalloc", not(target_env = "msvc"))))]
    None
}

#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
fn read_jemalloc_usize(name: &std::ffi::CStr) -> Option<usize> {
    let mut value = 0_usize;
    let mut value_len = std::mem::size_of_val(&value);
    let result = unsafe {
        tikv_jemalloc_sys::mallctl(
            name.as_ptr(),
            (&mut value as *mut usize).cast(),
            &mut value_len,
            std::ptr::null_mut(),
            0,
        )
    };
    (result == 0).then_some(value)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NullMallocTrimLogger;

pub trait MallocTrimLogger: Send + Sync + 'static {
    fn debug(&self, message: &str);
}

impl MallocTrimLogger for NullMallocTrimLogger {
    fn debug(&self, _message: &str) {}
}

pub fn malloc_trim(tag: &str, logger: &dyn MallocTrimLogger) -> MallocTrimReport {
    #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
    {
        return measured_trim(tag, "jemalloc", logger, purge_jemalloc_arenas);
    }

    #[cfg(all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu"))]
    {
        return measured_trim(tag, "glibc", logger, || unsafe { libc::malloc_trim(0) });
    }

    #[allow(unreachable_code)]
    {
        logger.debug(&format!(
            "allocator trim not supported on this platform (tag={tag})"
        ));
        MallocTrimReport::default()
    }
}

#[cfg(any(
    all(feature = "jemalloc", not(target_env = "msvc")),
    all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu")
))]
fn measured_trim(
    tag: &str,
    allocator: &str,
    logger: &dyn MallocTrimLogger,
    trim: impl FnOnce() -> i32,
) -> MallocTrimReport {
    let rss_before_kb = read_statm_rss_kb();
    let ru_before = read_thread_rusage();
    let start = std::time::Instant::now();
    let trim_result = trim();
    let duration_us = start.elapsed().as_micros() as i64;
    let rss_after_kb = read_statm_rss_kb();
    let ru_after = read_thread_rusage();

    let report = MallocTrimReport {
        supported: true,
        trim_result,
        rss_before_kb,
        rss_after_kb,
        duration_us,
        minflt_delta: ru_after
            .as_ref()
            .zip(ru_before.as_ref())
            .map(|(after, before)| after.ru_minflt - before.ru_minflt)
            .unwrap_or(-1),
        majflt_delta: ru_after
            .as_ref()
            .zip(ru_before.as_ref())
            .map(|(after, before)| after.ru_majflt - before.ru_majflt)
            .unwrap_or(-1),
    };

    logger.debug(&format!(
        "allocator_trim allocator={allocator} tag={tag} result={} rss_before={}kB rss_after={}kB delta={}kB duration_us={}",
        report.trim_result,
        report.rss_before_kb,
        report.rss_after_kb,
        report.delta_kb(),
        report.duration_us
    ));
    report
}

/// Purge every automatically created jemalloc arena. Quaxar allocates and
/// releases full SHAMap acquisition graphs across worker threads, so purging
/// only the housekeeping thread's arena would leave most free extents resident.
#[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
fn purge_jemalloc_arenas() -> i32 {
    let mut narenas = 0_u32;
    let mut narenas_len = std::mem::size_of_val(&narenas);
    let read_result = unsafe {
        tikv_jemalloc_sys::mallctl(
            c"arenas.narenas".as_ptr(),
            (&mut narenas as *mut u32).cast(),
            &mut narenas_len,
            std::ptr::null_mut(),
            0,
        )
    };
    if read_result != 0 {
        return read_result;
    }

    let mut first_error = 0;
    for arena in 0..narenas {
        let command = std::ffi::CString::new(format!("arena.{arena}.purge"))
            .expect("jemalloc arena purge command contains no NUL");
        let result = unsafe {
            tikv_jemalloc_sys::mallctl(
                command.as_ptr(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                0,
            )
        };
        if result != 0 && first_error == 0 {
            first_error = result;
        }
    }
    first_error
}

#[cfg(any(
    all(feature = "jemalloc", not(target_env = "msvc")),
    all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu")
))]
fn read_statm_rss_kb() -> i64 {
    #[cfg(target_os = "linux")]
    {
        let Ok(statm) = std::fs::read_to_string("/proc/self/statm") else {
            return -1;
        };
        let mut fields = statm.split_whitespace();
        let _size = fields.next();
        let Some(resident) = fields.next() else {
            return -1;
        };
        let Ok(resident_pages) = resident.parse::<i64>() else {
            return -1;
        };
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        if page_size <= 0 {
            return -1;
        }
        return resident_pages * page_size / 1024;
    }

    #[cfg(not(target_os = "linux"))]
    -1
}

#[cfg(any(
    all(feature = "jemalloc", not(target_env = "msvc")),
    all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu")
))]
fn read_thread_rusage() -> Option<libc::rusage> {
    #[cfg(target_os = "linux")]
    {
        let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
        let result = unsafe { libc::getrusage(libc::RUSAGE_THREAD, usage.as_mut_ptr()) };
        if result == 0 {
            return Some(unsafe { usage.assume_init() });
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{MallocTrimLogger, NullMallocTrimLogger, jemalloc_stats, malloc_trim};
    use std::sync::Mutex;

    #[derive(Debug, Default)]
    struct RecordingLogger {
        entries: Mutex<Vec<String>>,
    }

    impl MallocTrimLogger for RecordingLogger {
        fn debug(&self, message: &str) {
            self.entries
                .lock()
                .expect("logger mutex poisoned")
                .push(message.to_owned());
        }
    }

    #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
    #[test]
    fn jemalloc_statistics_refresh_and_report_consistent_totals() {
        let stats = jemalloc_stats().expect("jemalloc statistics");
        assert!(stats.allocated_bytes > 0);
        assert!(stats.active_bytes >= stats.allocated_bytes);
        assert!(stats.resident_bytes >= stats.active_bytes);
        assert!(stats.mapped_bytes >= stats.active_bytes);
        assert!(stats.arenas > 0);
    }
    #[test]
    fn malloc_trim_reports_support_state_and_logs() {
        let logger = RecordingLogger::default();
        let report = malloc_trim("test", &logger);
        #[cfg(any(
            all(feature = "jemalloc", not(target_env = "msvc")),
            all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu")
        ))]
        assert!(report.supported);
        #[cfg(not(any(
            all(feature = "jemalloc", not(target_env = "msvc")),
            all(not(feature = "jemalloc"), target_os = "linux", target_env = "gnu")
        )))]
        assert!(!report.supported);
        #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
        {
            assert_eq!(report.trim_result, 0);
            assert!(
                logger
                    .entries
                    .lock()
                    .expect("logger mutex poisoned")
                    .iter()
                    .any(|entry| entry.contains("allocator=jemalloc"))
            );
        }
        assert!(
            !logger
                .entries
                .lock()
                .expect("logger mutex poisoned")
                .is_empty()
        );

        let null_logger = NullMallocTrimLogger;
        let _ = malloc_trim("null", &null_logger);
    }
}
