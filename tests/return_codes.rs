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

fn logical_op(left: u8, right: u8, op: fn(u8, u8) -> bool) -> i8 {
    if op(left, right) {
        1
    } else {
        0
    }
}
fn logical_and(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| (l != 0) && (r != 0))
}
fn logical_or(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| (l != 0) || (r != 0))
}
fn logical_lt(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l < r)
}
fn logical_gt(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l > r)
}
fn logical_lte(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l <= r)
}
fn logical_gte(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l >= r)
}
fn logical_eq(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l == r)
}
fn logical_neq(left: u8, right: u8) -> i8 {
    logical_op(left, right, |l: u8, r: u8| l != r)
}

// this is really dumb but I love it
trait EqZero {
    fn eqzero(&self) -> i8; // i8 again for ease of use
}
impl EqZero for u8 {
    fn eqzero(&self) -> i8 {
        if *self != 0 {
            0
        } else {
            1
        }
    }
}
impl EqZero for i8 {
    fn eqzero(&self) -> i8 {
        if *self != 0 {
            0
        } else {
            1
        }
    }
}
impl EqZero for i32 {
    fn eqzero(&self) -> i8 {
        if *self != 0 {
            0
        } else {
            1
        }
    }
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

basic_mainret!(return_zero_and_127, "0 & 127", 0 & 127);
basic_mainret!(return_zero_or_127, "0 | 127", 0 | 127);
basic_mainret!(return_xor_self, "42 ^ 42", 42 ^ 42);
basic_mainret!(
    return_big_bitwise_guy,
    "1 ^ 2 & 3 | (4 | 5)",
    1 ^ 2 & 3 | (4 | 5)
);
basic_mainret!(
    return_one_plus_two_or_two_plus_one,
    "1 + 2 | 2 + 1",
    1 + 2 | 2 + 1
);

basic_mainret!(return_lognot_one, "!1", 1.eqzero());
basic_mainret!(return_lognot_zero, "!0", 0.eqzero());
basic_mainret!(return_lognot_lognot_one, "!!1", 1.eqzero().eqzero());
basic_mainret!(return_lognot_lognot_zero, "!!0", 0.eqzero().eqzero());
basic_mainret!(return_one_logand_two, "1 && 2", logical_and(1, 2));
basic_mainret!(return_one_logor_two, "1 || 2", logical_or(1, 2));
basic_mainret!(return_one_logeq_two, "1 == 2", logical_eq(1, 2));
basic_mainret!(return_one_logeq_one, "1 == 1", logical_eq(1, 1));
basic_mainret!(return_one_logneq_two, "1 != 2", logical_neq(1, 2));
basic_mainret!(return_one_loggt_two, "1 > 2", logical_gt(1, 2));
basic_mainret!(return_one_loglt_two, "1 < 2", logical_lt(1, 2));
basic_mainret!(return_one_loglte_two, "1 <= 2", logical_lte(1, 2));
basic_mainret!(return_one_loggte_two, "1 >= 2", logical_gte(1, 2));
