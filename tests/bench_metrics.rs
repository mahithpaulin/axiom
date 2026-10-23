use axiom::bench::{peak_rss_kb, rss_kb};

#[test]
fn peak_rss_is_not_below_current_rss() {
    // Read the point sample first. VmHWM is monotonic, so a later read can
    // only be higher; the reverse order compares a stale peak with a newer
    // RSS and flakes under the parallel test harness.
    let current = rss_kb();
    let peak = peak_rss_kb();
    assert!(
        peak >= current,
        "VmHWM must be at least the current VmRSS (peak={peak} kB, current={current} kB)"
    );
}
