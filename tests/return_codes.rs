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

basic_mainret!(return_basic_neg_two, "-2", -2);
basic_mainret!(return_basic_cmp_two, "~2", !2);
basic_mainret!(return_negneg_two, "-(-2)", -(-2));
basic_mainret!(return_cmpcmp_two, "~(~2)", !(!2));
basic_mainret!(return_cmpneg_two, "~(-2)", !(-2));
basic_mainret!(return_triplecmp_two, "~(~(~2))", !(!(!2)));
basic_mainret!(return_tripleneg_two, "-(-(-2))", -(-(-2)));
basic_mainret!(return_negcmpneg_two, "-(~(-2))", -(!(-2)));
basic_mainret!(return_quadneg_two, "-(-(-(-2)))", -(-(-(-2))));
basic_mainret!(return_quadcmp_two, "~(~(~(~2)))", !(!(!(!2))));
basic_mainret!(return_cmpnegcmpneg_two, "~(-(~(-2)))", !(-(!(-2))));

basic_mainret!(return_basic_neg_three, "-3", -3);
basic_mainret!(return_basic_cmp_three, "~3", !3);
basic_mainret!(return_negneg_three, "-(-3)", -(-3));
basic_mainret!(return_cmpcmp_three, "~(~3)", !(!3));
basic_mainret!(return_cmpneg_three, "~(-3)", !(-3));
basic_mainret!(return_triplecmp_three, "~(~(~3))", !(!(!3)));
basic_mainret!(return_tripleneg_three, "-(-(-3))", -(-(-3)));
basic_mainret!(return_negcmpneg_three, "-(~(-3))", -(!(-3)));
basic_mainret!(return_quadneg_three, "-(-(-(-3)))", -(-(-(-3))));
basic_mainret!(return_quadcmp_three, "~(~(~(~3)))", !(!(!(!3))));
basic_mainret!(return_cmpnegcmpneg_three, "~(-(~(-3)))", !(-(!(-3))));

basic_mainret!(return_one_plus_one, "1 + 1", 1 + 1);
basic_mainret!(return_one_minus_one, "1 - 1", 1 - 1);
basic_mainret!(return_two_times_three, "2 * 3", 2 * 3);
basic_mainret!(return_one_plus_two_times_three, "1 + 2 * 3", 1 + 2 * 3);
basic_mainret!(return_four_div_two, "4 / 2", 4 / 2);
basic_mainret!(
    return_one_times_two_minus_three_times_parens_four_plus_five,
    "1 * 2 - 3 * (4 + 5)",
    1 * 2 - 3 * (4 + 5)
);
basic_mainret!(
    return_unary_and_binary,
    "-(1 + 1) * ~(4 - 5)",
    -(1 + 1) * !(4 - 5)
);
