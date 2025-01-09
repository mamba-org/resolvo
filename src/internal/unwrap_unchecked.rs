/// An unsafe method that unwraps an option without checking if it is `None` in
/// release mode but does check the value in debug mode.
#[track_caller]
pub unsafe fn debug_expect_unchecked<T>(opt: Option<T>, _msg: &str) -> T {
    #[cfg(debug_assertions)]
    {
        opt.expect(_msg)
    }
    #[cfg(not(debug_assertions))]
    {
        opt.unwrap_unchecked()
    }
}
