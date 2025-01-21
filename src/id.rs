use std::cmp::Ordering;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    site: u64,
    seq: u64,
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.site, self.seq)
    }
}

impl Id {
    pub const fn new(site: u64, seq: u64) -> Self {
        Self { site, seq }
    }
}

impl PartialOrd for Id {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Id {
    fn cmp(&self, other: &Self) -> Ordering {
        self.seq
            .cmp(&other.seq)
            .then_with(|| self.site.cmp(&other.site))
    }
}
