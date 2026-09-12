use crate::int_abi;
use protocol::{MPTAmount, XRPAmount};

pub struct Report {
    pub checks: usize,
}

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Sub,
    Mul,
    Neg,
}

impl Operation {
    fn wrapped(self, left: i64, right: i64) -> i64 {
        match self {
            Self::Add => left.wrapping_add(right),
            Self::Sub => left.wrapping_sub(right),
            Self::Mul => left.wrapping_mul(right),
            Self::Neg => left.wrapping_neg(),
        }
    }
}

fn mpt_value(op: Operation, left: i64, right: i64) -> i64 {
    match op {
        Operation::Add => (MPTAmount::from(left) + MPTAmount::from(right)).value(),
        Operation::Sub => (MPTAmount::from(left) - MPTAmount::from(right)).value(),
        _ => unreachable!("only MPT add/sub operators are exported here"),
    }
}

fn xrp_value(left: i64, right: i64) -> i64 {
    (XRPAmount::from(left) * right).drops()
}

fn neg_value(value: i64) -> i64 {
    (-MPTAmount::from(value)).value()
}

fn mpt(opcode: u8, op: Operation, left: i64, right: i64, report: &mut Report) {
    let lean = int_abi::direct(opcode, left, right);
    assert_eq!(lean, op.wrapped(left, right), "Lean IntAmount wraps");
    assert_eq!(lean, mpt_value(op, left, right), "MPTAmount wraps");
    report.checks += 1;
}

fn xrp(left: i64, right: i64, report: &mut Report) {
    let lean = int_abi::direct(4, left, right);
    assert_eq!(
        lean,
        Operation::Mul.wrapped(left, right),
        "Lean IntAmount wraps"
    );
    assert_eq!(lean, xrp_value(left, right), "XRPAmount wraps");
    report.checks += 1;
}

fn neg(value: i64, report: &mut Report) {
    let lean = int_abi::direct(3, value, 0);
    assert_eq!(
        lean,
        Operation::Neg.wrapped(value, 0),
        "Lean IntAmount wraps"
    );
    assert_eq!(lean, neg_value(value), "MPTAmount wraps");
    report.checks += 1;
}

pub fn run(min: i64, max: i64, values: &[i64]) -> Report {
    let mut report = Report { checks: 0 };
    for (left, right) in [
        (0, 0),
        (1, -1),
        (7, 3),
        (-7, 3),
        (max, 1),
        (min, -1),
        (min, min),
    ] {
        mpt(1, Operation::Add, left, right, &mut report);
        mpt(2, Operation::Sub, left, right, &mut report);
        mpt(5, Operation::Add, left, right, &mut report);
        mpt(6, Operation::Sub, left, right, &mut report);
        xrp(left, right, &mut report);
    }
    for &value in values {
        neg(value, &mut report);
    }
    assert_eq!(report.checks, 44);
    report
}
