use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, PartialEq, Eq)]
pub struct Clock {
    inner: BTreeMap<u64, u64>,
}

impl Clock {
    pub const fn new() -> Self {
        Self {
            inner: BTreeMap::new(),
        }
    }

    #[inline]
    pub fn increment(&mut self, site: u64) {
        *self.inner.entry(site).or_default() += 1;
    }

    #[inline]
    pub fn delta_for(&self, site: u64) -> ClockDelta {
        let counter = self.inner.get(&site).copied().unwrap_or_default();
        ClockDelta::new(site, counter)
    }

    #[inline]
    pub fn sum(&self) -> u64 {
        self.inner.values().sum()
    }
}

impl PartialOrd for Clock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut less = false;
        let mut greater = false;

        let all_sites: BTreeSet<_> = self.inner.keys().chain(other.inner.keys()).collect();
        for &site in &all_sites {
            let self_counter = *self.inner.get(site).unwrap_or(&0);
            let other_counter = *other.inner.get(site).unwrap_or(&0);

            match self_counter.cmp(&other_counter) {
                Ordering::Less => less = true,
                Ordering::Greater => greater = true,
                Ordering::Equal => {}
            }

            if less && greater {
                break;
            }
        }

        match (less, greater) {
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => Some(Ordering::Equal),
            (true, true) => None,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct ClockDelta {
    site: u64,
    counter: u64,
}

impl ClockDelta {
    #[inline]
    pub fn new(site: u64, counter: u64) -> Self {
        Self { site, counter }
    }
}

pub trait Merge<T> {
    fn merge(&mut self, other: &T);
}

impl Merge<Clock> for Clock {
    fn merge(&mut self, other: &Clock) {
        for (&site, &other_counter) in &other.inner {
            let entry = self.inner.entry(site).or_insert(0);
            if *entry < other_counter {
                *entry = other_counter;
            }
        }
    }
}

impl Merge<ClockDelta> for Clock {
    #[inline]
    fn merge(&mut self, delta: &ClockDelta) {
        let entry = self.inner.entry(delta.site).or_insert(0);
        if *entry < delta.counter {
            *entry = delta.counter;
        }
    }
}

impl std::fmt::Debug for Clock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Clock(")?;
        let mut first = true;
        for (site, counter) in &self.inner {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}:{}", site, counter)?;
        }
        write!(f, ")")
    }
}

impl std::fmt::Debug for ClockDelta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ClockDelta({}:{})", self.site, self.counter)
    }
}
