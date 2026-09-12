use std::{cmp::Ordering, fmt};

use basics::number::NumberParts as RuntimeNumber;

use super::IOUAmount;

impl PartialOrd for IOUAmount {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IOUAmount {
    fn cmp(&self, other: &Self) -> Ordering {
        RuntimeNumber::from(*self).compare(RuntimeNumber::from(*other))
    }
}

impl fmt::Display for IOUAmount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        RuntimeNumber::from(*self).fmt(f)
    }
}
