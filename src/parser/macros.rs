#[cfg(test)]
#[macro_use]
macro_rules! test_parse {
    ($parser: ident, $src: expr) => {{
        let res = $parser($src);
        nom_trace::print_trace!();
        let (rem, res) = res.unwrap();
        assert!(
            rem.is_empty(),
            "non-empty remainder: \"{}\", parsed: {:?}",
            rem,
            res
        );
        res
    }};
}
