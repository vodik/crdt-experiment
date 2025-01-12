use crate::clock::Clock;
use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    pub site: u64,
    pub seq: u64,
}

impl Id {
    pub fn new(site: u64, clock: &Clock) -> Self {
        let seq = clock.sum();
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operation<T> {
    clock: Clock,
    op: Op<T>,
}

impl<T> Operation<T> {
    pub fn insert(clock: Clock, insert_id: Id, left_id: Option<Id>, value: T) -> Self {
        Self {
            clock,
            op: Op::Insert(InsertOp {
                insert_id,
                left_id,
                value,
            }),
        }
    }

    pub fn update(clock: Clock, insert_id: Id, new_version_id: Id, new_value: T) -> Self {
        Self {
            clock,
            op: Op::Update(UpdateOp {
                insert_id,
                new_version_id,
                new_value,
            }),
        }
    }

    pub fn delete(clock: Clock, insert_id: Id, new_version_id: Id) -> Self {
        Self {
            clock,
            op: Op::Delete(DeleteOp {
                insert_id,
                new_version_id,
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op<T> {
    Insert(InsertOp<T>),
    Update(UpdateOp<T>),
    Delete(DeleteOp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertOp<T> {
    insert_id: Id,
    left_id: Option<Id>,
    value: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpdateOp<T> {
    insert_id: Id,
    new_version_id: Id,
    new_value: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeleteOp {
    insert_id: Id,
    new_version_id: Id,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Entry<T> {
    insert_id: Id,
    version_id: Id,
    next: Option<Id>,
    // FIXME: Store tombstone as a flag so delete can be undone
    value: Option<T>,
}

impl<T> Entry<T> {
    fn new(insert_id: Id, value: T) -> Self {
        let version_id = insert_id.clone();
        Self {
            insert_id,
            version_id,
            next: None,
            value: Some(value),
        }
    }

    fn is_tombstone(&self) -> bool {
        self.value.is_none()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rga<T> {
    site: u64,
    clock: Clock,
    head: Option<Id>,
    map: HashMap<Id, Entry<T>>,
}

impl<T> Rga<T>
where
    T: Clone,
{
    pub fn new(site: u64) -> Self {
        let clock = Clock::new();
        Self {
            site,
            clock,
            head: None,
            map: HashMap::new(),
        }
    }

    fn next_id(&mut self) -> Id {
        self.clock.increment(self.site);
        Id::new(self.site, &self.clock)
    }

    pub fn insert(&mut self, index: usize, value: T) -> Operation<T> {
        let left_id = index
            .checked_sub(1)
            .and_then(|index| self.find_id_by_index(index));

        let insert_id = self.next_id();
        self.insert_left_of(left_id, insert_id, value.clone());
        Operation::insert(self.clock.clone(), insert_id, left_id, value)
    }

    pub fn push(&mut self, value: T) -> Operation<T> {
        // FIXME: optimize
        let idx = self.iter().count();
        self.insert(idx, value)
    }

    pub fn update<F>(&mut self, index: usize, f: F) -> Option<Operation<T>>
    where
        F: FnOnce(&mut T),
    {
        let id = self.find_id_by_index(index)?;
        let entry = self.map.get_mut(&id)?;
        f(entry.value.as_mut()?);

        let new_version_id = self.next_id();
        let entry = self.map.get_mut(&id).unwrap();
        entry.version_id = new_version_id;

        Some(Operation::update(
            self.clock.clone(),
            id,
            new_version_id,
            entry.value.clone().unwrap(),
        ))
    }

    pub fn delete(&mut self, index: usize) -> Option<Operation<T>> {
        let id = self.find_id_by_index(index)?;
        let entry = self.map.get(&id)?;
        if entry.is_tombstone() {
            return None;
        }

        let new_version_id = self.next_id();
        let entry = self.map.get_mut(&id)?;
        entry.value = None;
        entry.version_id = new_version_id;

        Some(Operation::delete(self.clock.clone(), id, new_version_id))
    }

    pub fn apply(&mut self, op: Operation<T>) {
        self.clock.merge(&op.clock);
        match op.op {
            Op::Insert(iop) => self.remote_insert(iop),
            Op::Update(uop) => self.remote_update(uop),
            Op::Delete(dop) => self.remote_delete(dop),
        }
    }

    fn remote_insert(&mut self, iop: InsertOp<T>) {
        if !self.map.contains_key(&iop.insert_id) {
            self.insert_left_of(iop.left_id, iop.insert_id, iop.value);
        }
    }

    fn remote_update(&mut self, uop: UpdateOp<T>) {
        if let Some(entry) = self.map.get_mut(&uop.insert_id) {
            if uop.new_version_id > entry.version_id {
                entry.version_id = uop.new_version_id;
                entry.value = Some(uop.new_value);
            }
        }
    }

    fn remote_delete(&mut self, dop: DeleteOp) {
        if let Some(entry) = self.map.get_mut(&dop.insert_id) {
            if dop.new_version_id > entry.version_id {
                entry.version_id = dop.new_version_id;
                entry.value = None;
            }
        }
    }

    fn insert_left_of(&mut self, left_id: Option<Id>, insert_id: Id, value: T) {
        let mut new_entry = Entry::new(insert_id, value);

        if left_id.is_none() {
            new_entry.next = self.head;
            self.head = Some(insert_id);
        } else {
            let mut cur_id = left_id.unwrap();
            loop {
                let cur = self.map.get(&cur_id).unwrap();
                match cur.next {
                    Some(next_id) if next_id > insert_id => {
                        cur_id = next_id;
                    }
                    _ => break,
                }
            }

            let cur_entry = self.map.get_mut(&cur_id).unwrap();
            let old_right = cur_entry.next;
            new_entry.next = old_right;
            cur_entry.next = Some(insert_id);
        }

        self.map.insert(insert_id, new_entry);
    }

    fn find_id_by_index(&self, mut index: usize) -> Option<Id> {
        let mut pos = self.head;
        let mut latest_id = None;

        while let Some(id) = pos {
            let entry = self
                .map
                .get(&id)
                .expect("Broken pointer in the RGA linked structure");

            latest_id = Some(id);
            pos = entry.next;

            if !entry.is_tombstone() {
                if index == 0 {
                    return latest_id;
                }
                index -= 1;
            }
        }

        latest_id
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        RgaIter {
            map: &self.map,
            current: self.head,
        }
    }
}

struct RgaIter<'a, T> {
    map: &'a HashMap<Id, Entry<T>>,
    current: Option<Id>,
}

impl<'a, T> Iterator for RgaIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(id) = self.current {
            let entry = self.map.get(&id)?;
            self.current = entry.next;
            if let Some(value) = &entry.value {
                return Some(value);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use std::ops::Range;
    use test_strategy::proptest;

    #[test]
    fn test_local_inserts_by_index() {
        let mut rga1 = Rga::new(1);
        let insert_a = rga1.insert(0, "A");
        let insert_b = rga1.insert(1, "B");
        let insert_x = rga1.insert(1, "X");

        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"B"]);

        let mut rga2 = Rga::new(2);
        for op in [&insert_a, &insert_b, &insert_x] {
            rga2.apply(op.clone());
        }
        let vals: Vec<_> = rga2.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"B"]);

        let mut rga3 = Rga::new(3);
        for op in [insert_a, insert_x, insert_b] {
            rga3.apply(op);
        }
        let vals: Vec<_> = rga3.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"B"]);
    }

    #[test]
    fn test_push() {
        let mut rga1 = Rga::new(1);
        let insert_a = rga1.push("A");
        let insert_b = rga1.push("B");
        let insert_c = rga1.push("C");
        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"A", &"B", &"C"]);

        let mut rga2 = Rga::new(2);
        for op in [insert_a, insert_b, insert_c] {
            rga2.apply(op);
        }
        let vals2: Vec<_> = rga2.iter().collect();
        assert_eq!(vals2, vec![&"A", &"B", &"C"]);
    }

    #[test]
    fn test_local_insert_update_delete_by_index() {
        let mut rga1 = Rga::new(1);
        let insert_a = rga1.insert(0, "A");
        let insert_b = rga1.insert(1, "B");
        let insert_x = rga1.insert(1, "X");

        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"B"]);

        let update_b = rga1.update(2, |val| *val = "B2").unwrap();

        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"B2"]);

        let delete_x = rga1.delete(1).unwrap();

        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"A", &"B2"]);

        let mut rga2 = Rga::new(2);
        for op in [insert_a, insert_b, insert_x, update_b, delete_x] {
            rga2.apply(op);
        }
        let vals4: Vec<_> = rga2.iter().collect();
        assert_eq!(vals4, vec![&"A", &"B2"]);
    }

    #[test]
    fn test_last_write_wins() {
        let mut rga1 = Rga::new(1);
        let insert_x = rga1.insert(0, "X");
        let update_x1 = rga1.update(0, |val| *val = "X1").unwrap();
        let update_x2 = rga1.update(0, |val| *val = "X2").unwrap();

        let mut rga2 = Rga::new(2);
        for op in [&insert_x, &update_x1, &update_x2] {
            rga2.apply(op.clone());
        }
        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"X2"]);

        let mut rga2 = Rga::new(2);
        for op in [insert_x, update_x2, update_x1] {
            rga2.apply(op);
        }
        let vals: Vec<_> = rga1.iter().collect();
        assert_eq!(vals, vec![&"X2"]);
    }

    #[test]
    fn test_update_delete_precedence() {
        let mut rga1 = Rga::new(1);
        let insert_x = rga1.insert(0, "X");
        let update_x = rga1.update(0, |val| *val = "X1").unwrap();
        let delete_x = rga1.delete(0).unwrap();

        let mut rga2 = Rga::new(2);
        for op in [&insert_x, &update_x, &delete_x] {
            rga2.apply(op.clone());
        }
        let vals: Vec<_> = rga1.iter().collect();
        assert!(vals.is_empty());

        let mut rga2 = Rga::new(2);
        for op in [insert_x, delete_x, update_x] {
            rga2.apply(op);
        }
        let vals: Vec<_> = rga1.iter().collect();
        assert!(vals.is_empty());
    }

    #[test]
    fn test_concurrent_inserts() {
        let mut rga5 = Rga::new(5);
        let insert_a = rga5.insert(0, "A");
        let insert_x = rga5.insert(1, "X");

        let mut rga1 = Rga::new(1);
        rga1.apply(insert_a.clone());
        let insert_y = rga1.insert(1, "Y");

        let mut rga3 = Rga::new(3);
        for op in [&insert_a, &insert_x, &insert_y] {
            rga3.apply(op.clone());
        }
        let vals: Vec<_> = rga3.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"Y"]);

        let mut rga3 = Rga::new(3);
        for op in [insert_a, insert_y, insert_x] {
            rga3.apply(op);
        }
        let vals: Vec<_> = rga3.iter().collect();
        assert_eq!(vals, vec![&"A", &"X", &"Y"]);
    }

    #[derive(Debug)]
    enum Op<T> {
        Insert(usize, T),
        Replace(usize, T),
        Delete(usize),
    }

    fn ops<T: Arbitrary>(range: Range<usize>) -> impl Strategy<Value = Op<T>> {
        prop_oneof![
            (range.clone(), any::<T>()).prop_map(|(index, value)| Op::Insert(index, value)),
            (range.clone(), any::<T>()).prop_map(|(index, value)| Op::Replace(index, value)),
            range.prop_map(|index| Op::Delete(index)),
        ]
    }

    #[proptest]
    fn test_replica_convergence(
        #[strategy(vec(any::<u8>(), 10..200))] seed: Vec<u8>,
        #[strategy(vec(vec(ops(0..#seed.len()), 1..30), 2..100))] plan: Vec<Vec<Op<u8>>>,
    ) {
        let base_rga = {
            let mut rga = Rga::new(0);
            for value in &seed {
                rga.push(*value);
            }
            rga
        };

        // Create n replicas of the base RGA.
        let mut replicas: Vec<_> = plan
            .iter()
            .enumerate()
            .map(|(replica_id, _)| {
                let mut replica = base_rga.clone();
                replica.site = replica_id as u64 + 1;
                replica
            })
            .collect();

        // On each replica RGA, apply m operations.
        // Afterwards, broadcast all operations to every other replica.
        let mut broadcast_queue = vec![];
        for (replica_id, ops) in plan.iter().enumerate() {
            let replica: &mut Rga<u8> = &mut replicas[replica_id];
            broadcast_queue.clear();

            for op in ops {
                match op {
                    Op::Insert(index, value) => {
                        let operation = replica.insert(*index, value.clone());
                        broadcast_queue.push(operation);
                    }
                    Op::Replace(index, value) => {
                        if let Some(operation) = replica.update(*index, |v| *v = value.clone()) {
                            broadcast_queue.push(operation);
                        }
                    }
                    Op::Delete(index) => {
                        if let Some(operation) = replica.delete(*index) {
                            broadcast_queue.push(operation);
                        }
                    }
                }
            }

            // eprintln!("replica {}:", replica.site);
            // for operation in &broadcast_queue {
            //     eprintln!("-> {:?}", &operation);
            // }

            for replica in replicas.iter_mut() {
                if replica.site == replica_id as u64 + 1 {
                    continue;
                }

                for operation in &broadcast_queue {
                    replica.apply(operation.clone());
                }
            }
        }

        // Check that each of the n replicas have a consistent view of the list.
        let reference_vals: Vec<_> = replicas[0].iter().cloned().collect();
        // eprintln!("\n--- {:?}", seed);
        // eprintln!("+++ {:?}", reference_vals);
        // eprintln!("===============");

        for replica in &replicas[1..] {
            let vals: Vec<_> = replica.iter().cloned().collect();
            prop_assert_eq!(&vals, &reference_vals);
        }
    }
}
