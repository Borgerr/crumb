use assert_cmd::Command;
use std::{io::Write, str};
use tempfile::{NamedTempFile, TempDir};

fn return_exitcode(source: &str) -> i32 {
    let tmpdir = TempDir::new().unwrap();
    let mut tmpsource = NamedTempFile::with_suffix_in(r".c", tmpdir.path()).unwrap();
    write!(tmpsource, "{}", source).unwrap();
    let source_name = tmpsource.path().to_str().unwrap();

    let compile_res_vec = Command::cargo_bin(env!("CARGO_PKG_NAME"))
        .unwrap()
        .arg(source_name)
        .ok()
        .unwrap()
        .stdout;
    let compile_res_str = str::from_utf8(&compile_res_vec).unwrap();
    assert!(!compile_res_str.starts_with("(!)"));

    let binary_name = source_name.strip_suffix(r".c").unwrap();

    match Command::new(binary_name).ok() {
        Ok(out) => out.status.code().unwrap(),
        Err(e) => e.as_output().unwrap().status.code().unwrap(),
    }
}

macro_rules! basic_mainret {
    ($name:tt, $str:expr, $res:expr) => {
        #[test]
        fn $name() {
            let source_code: &str = &format!("int main(void) {{ return {}; }}", $str);
            let expected_bytes: i8 = $res; // voodoo done as unary - cannot be done on a u8. IAFM.
            assert_eq!((expected_bytes as u8) as i32, return_exitcode(source_code));
        }
    };
}

basic_mainret!(return_basic_neg_mainret, "-2", -2);
basic_mainret!(return_basic_cmp_mainret, "~2", !2);
basic_mainret!(return_negneg_mainret, "-(-2)", -(-2));
basic_mainret!(return_cmpcmp_mainret, "~(~2)", !(!2));
basic_mainret!(return_cmpneg_mainret, "~(-2)", !(-2));
basic_mainret!(return_triplecmp_mainret, "~(~(~2))", !(!(!2)));
basic_mainret!(return_tripleneg_mainret, "-(-(-2))", -(-(-2)));
basic_mainret!(return_negcmpneg_mainret, "-(~(-2))", -(!(-2)));
basic_mainret!(return_quadneg_mainret, "-(-(-(-2)))", -(-(-(-2))));
basic_mainret!(return_quadcmp_mainret, "~(~(~(~2)))", !(!(!(!2))));
