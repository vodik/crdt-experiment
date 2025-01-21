use crate::clock::{Clock, ClockDelta, Merge};
use crate::id::Id;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InsertOp<T> {
    id: Id,
    left_id: Option<Id>,
    value: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpdateOp<T> {
    id: Id,
    update_id: Id,
    new_value: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeleteOp {
    id: Id,
    delete_id: Id,
}

impl<T> Op<T> {
    fn insert(id: Id, left_id: Option<Id>, value: T) -> Self {
        Self::Insert(InsertOp { id, left_id, value })
    }

    fn update(id: Id, update_id: Id, new_value: T) -> Self {
        Self::Update(UpdateOp {
            id,
            update_id,
            new_value,
        })
    }

    fn delete(id: Id, delete_id: Id) -> Self {
        Self::Delete(DeleteOp { id, delete_id })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op<T> {
    Insert(InsertOp<T>),
    Update(UpdateOp<T>),
    Delete(DeleteOp),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Operation<T> {
    op: Op<T>,
    when: ClockDelta,
}

impl<T> Operation<T> {
    pub fn new(op: Op<T>, clock: ClockDelta) -> Self {
        Self { op, when: clock }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry<T> {
    pub id: Id,
    pub version_id: Id,
    pub next: Option<Id>,
    // FIXME: Store tombstone as a flag so delete can be undone
    pub value: Option<T>,
}

impl<T> Entry<T> {
    fn new(id: Id, value: T) -> Self {
        Self {
            id,
            version_id: id,
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
        Self {
            site,
            clock: Clock::new(),
            head: None,
            map: HashMap::new(),
        }
    }

    pub fn replicate(&self, site: u64) -> Self {
        let mut other = self.clone();
        other.site = site;
        other
    }

    fn next_id(&mut self) -> Id {
        self.clock.increment(self.site);
        Id::new(self.site, self.clock.sum())
    }

    pub fn insert(&mut self, index: usize, value: T) -> Operation<T> {
        let left_id = index
            .checked_sub(1)
            .and_then(|index| self.find_id_by_index(index));

        let id = self.next_id();
        self.insert_right_of(left_id, id, value.clone());
        Operation::new(
            Op::insert(id, left_id, value),
            self.clock.delta_for(self.site),
        )
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

        let update_id = self.next_id();
        let entry = self.map.get_mut(&id).unwrap();
        entry.version_id = update_id;

        Some(Operation::new(
            Op::update(id, update_id, entry.value.clone().unwrap()),
            self.clock.delta_for(self.site),
        ))
    }

    pub fn delete(&mut self, index: usize) -> Option<Operation<T>> {
        let id = self.find_id_by_index(index)?;
        let entry = self.map.get(&id)?;
        if entry.is_tombstone() {
            return None;
        }

        let delete_id = self.next_id();
        let entry = self.map.get_mut(&id)?;
        entry.value = None;
        entry.version_id = delete_id;

        Some(Operation::new(
            Op::delete(id, delete_id),
            self.clock.delta_for(self.site),
        ))
    }

    pub fn apply(&mut self, op: Operation<T>) {
        self.clock.merge(&op.when);
        match op.op {
            Op::Insert(iop) => self.remote_insert(iop),
            Op::Update(uop) => self.remote_update(uop),
            Op::Delete(dop) => self.remote_delete(dop),
        }
    }

    fn remote_insert(&mut self, iop: InsertOp<T>) {
        if !self.map.contains_key(&iop.id) {
            let left_id = self.probe_forward(iop.left_id, iop.id);
            self.insert_right_of(left_id, iop.id, iop.value);
        }
    }

    fn remote_update(&mut self, uop: UpdateOp<T>) {
        if let Some(entry) = self.map.get_mut(&uop.id) {
            if uop.update_id > entry.version_id {
                entry.version_id = uop.update_id;
                entry.value = Some(uop.new_value);
            }
        }
    }

    fn remote_delete(&mut self, dop: DeleteOp) {
        if let Some(entry) = self.map.get_mut(&dop.id) {
            if dop.delete_id > entry.version_id {
                entry.version_id = dop.delete_id;
                entry.value = None;
            }
        }
    }

    fn insert_right_of(&mut self, left_id: Option<Id>, id: Id, value: T) {
        let mut new_entry = Entry::new(id, value);

        match left_id {
            None => self.head = Some(id),
            Some(left_id) => {
                let cur_entry = self.map.get_mut(&left_id).expect("broken pointer");
                new_entry.next = std::mem::replace(&mut cur_entry.next, Some(id));
            }
        }

        self.map.insert(id, new_entry);
    }

    fn probe_forward(&self, current_id: Option<Id>, id: Id) -> Option<Id> {
        let Some(mut cur) = current_id else {
            return None;
        };

        loop {
            let entry = self.map.get(&cur).expect("broken pointer");
            match entry.next {
                Some(next_id) if next_id > id => cur = next_id,
                _ => break Some(cur),
            }
        }
    }

    fn find_id_by_index(&self, mut index: usize) -> Option<Id> {
        let mut pos = self.head;
        let mut latest_id = None;

        while let Some(id) = pos {
            let entry = self.map.get(&id).expect("broken pointer");

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

        let original_vals: Vec<_> = rga1.iter().collect();
        assert_eq!(original_vals, vec![&"A", &"B", &"C"]);

        let mut rga2 = Rga::new(2);
        for op in [insert_a, insert_b, insert_c] {
            rga2.apply(op);
        }
        let vals2: Vec<_> = rga2.iter().collect();
        assert_eq!(vals2, original_vals);
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
        #[strategy(vec(any::<u8>(), 10..20))] seed: Vec<u8>,
        #[strategy(vec(vec(ops(0..#seed.len()), 1..10), 2..30))] plan: Vec<Vec<Op<u8>>>,
    ) {
        let base_rga = {
            let mut rga = Rga::new(50);
            for &value in &seed {
                rga.push(value);
            }
            rga
        };

        // Create n replicas of the base RGA.
        let mut replicas: Vec<_> = plan
            .iter()
            .enumerate()
            .map(|(replica_id, _)| base_rga.replicate(replica_id as u64))
            .collect();

        // On each replica RGA, apply m operations.
        // Afterwards, broadcast all operations to every other replica.
        let mut broadcast_queue = vec![];
        for (replica_id, ops) in plan.iter().enumerate() {
            let replica: &mut Rga<u8> = &mut replicas[replica_id];
            broadcast_queue.clear();

            for op in ops {
                let operation = match op {
                    Op::Insert(index, value) => Some(replica.insert(*index, value.clone())),
                    Op::Replace(index, value) => replica.update(*index, |v| *v = value.clone()),
                    Op::Delete(index) => replica.delete(*index),
                };
                broadcast_queue.extend(operation);
            }

            for replica in replicas.iter_mut() {
                for operation in &broadcast_queue {
                    replica.apply(operation.clone());
                }
            }
        }

        // Check that each of the n replicas have a consistent view of the list.
        let reference_vals: Vec<_> = replicas[0].iter().collect();
        for replica in &replicas[1..] {
            let vals: Vec<_> = replica.iter().collect();
            prop_assert_eq!(&vals, &reference_vals);
        }
    }
}
