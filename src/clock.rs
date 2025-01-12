use std::cmp::Ordering;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clock {
    clock: BTreeMap<u64, u64>,
    sum: u64,
}

impl Clock {
    pub fn new() -> Self {
        Self {
            clock: BTreeMap::new(),
            sum: 0,
        }
    }

    pub fn increment(&mut self, site: u64) {
        *self.clock.entry(site).or_insert(0) += 1;
        self.sum += 1;
    }

    pub fn merge(&mut self, other: &Self) {
        for (&site, &counter) in &other.clock {
            let entry = self.clock.entry(site).or_insert(0);
            if *entry < counter {
                self.sum += entry.abs_diff(counter);
                *entry = counter;
            }
        }
    }

    pub fn sum(&self) -> u64 {
        self.sum
    }
}

impl PartialOrd for Clock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut less = false;
        let mut greater = false;

        for (&site, &self_counter) in self.clock.iter().chain(other.clock.iter()) {
            let other_counter = other.clock.get(&site).cloned().unwrap_or(0);

            if self_counter < other_counter {
                less = true;
            } else if self_counter > other_counter {
                greater = true;
            }
        }

        match (less, greater) {
            (true, true) => None,
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => Some(Ordering::Equal),
        }
    }
}

impl Ord for Clock {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}
