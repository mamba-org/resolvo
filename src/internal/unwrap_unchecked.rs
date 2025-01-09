#[track_caller]
pub unsafe fn debug_expect_unchecked<T>(opt: Option<T>, msg: &str) -> T {
    #[cfg(debug_assertions)]
    {
        opt.expect(msg)
    }
    #[cfg(not(debug_assertions))]
    {
        opt.unwrap_unchecked()
    }
}
