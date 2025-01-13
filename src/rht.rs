use std::cmp::Ordering;
use std::collections::{hash_map, HashMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    pub site: u64,
    pub seq: u64,
}

impl Id {
    pub fn new(site: u64, seq: u64) -> Self {
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
pub enum Operation<K, V> {
    Put(PutOp<K, V>),
    Delete(DeleteOp<K>),
}

impl<K, V> Operation<K, V>
where
    K: Clone,
{
    pub fn put(key: K, version_id: Id, value: V) -> Self {
        Self::Put(PutOp {
            key,
            version_id,
            value,
        })
    }

    pub fn delete(key: K, version_id: Id) -> Self {
        Self::Delete(DeleteOp { key, version_id })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PutOp<K, V> {
    key: K,
    version_id: Id,
    value: V,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeleteOp<K> {
    key: K,
    version_id: Id,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Entry<V> {
    version_id: Id,
    value: Option<V>,
}

impl<V> Entry<V> {
    fn new(version_id: Id, value: V) -> Self {
        Self {
            version_id,
            value: Some(value),
        }
    }

    fn is_tombstone(&self) -> bool {
        self.value.is_none()
    }
}

#[derive(Debug, Clone)]
pub struct Rht<K, V> {
    site: u64,
    seq: u64,
    map: HashMap<K, Entry<V>>,
}

impl<K, V> Rht<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    pub fn new(site: u64) -> Self {
        Self {
            site,
            seq: 0,
            map: HashMap::new(),
        }
    }

    fn next_id(&mut self) -> Id {
        self.seq += 1;
        Id::new(self.site, self.seq)
    }

    pub fn put(&mut self, key: K, value: V) -> Operation<K, V> {
        let version_id = self.next_id();
        self.map
            .insert(key.clone(), Entry::new(version_id, value.clone()));
        Operation::put(key, version_id, value)
    }

    pub fn update<F>(&mut self, key: K, f: F) -> Option<Operation<K, V>>
    where
        F: FnOnce(&mut V),
    {
        let entry = self.map.get_mut(&key)?;
        f(entry.value.as_mut()?);

        let new_version_id = self.next_id();
        let entry = self.map.get_mut(&key).unwrap();
        entry.version_id = new_version_id;

        Some(Operation::put(
            key.clone(),
            new_version_id,
            entry.value.clone().unwrap(),
        ))
    }

    pub fn delete(&mut self, key: K) -> Option<Operation<K, V>> {
        let entry = self.map.get(&key)?;
        if entry.is_tombstone() {
            return None;
        }

        let version_id = self.next_id();
        let entry = self.map.get_mut(&key)?;
        entry.version_id = version_id;
        entry.value = None;

        Some(Operation::delete(key, version_id))
    }

    pub fn apply(&mut self, op: Operation<K, V>) {
        let updated = match op {
            Operation::Put(pop) => self.remote_put(pop),
            Operation::Delete(dop) => self.remote_delete(dop),
        };

        if updated {
            self.seq += 1;
        }
    }

    fn remote_put(&mut self, pop: PutOp<K, V>) -> bool {
        let entry = self.map.entry(pop.key.clone());
        match entry {
            hash_map::Entry::Occupied(mut entry) => {
                let entry = entry.get_mut();
                if pop.version_id > entry.version_id {
                    entry.version_id = pop.version_id;
                    entry.value = Some(pop.value);
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(Entry {
                    version_id: pop.version_id,
                    value: Some(pop.value),
                });
            }
        }
        true
    }

    fn remote_delete(&mut self, dop: DeleteOp<K>) -> bool {
        let entry = self.map.entry(dop.key.clone()).or_insert_with(|| Entry {
            version_id: dop.version_id,
            value: None,
        });

        if dop.version_id > entry.version_id {
            entry.version_id = dop.version_id;
            entry.value = None;
            return true;
        }
        false
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let entry = self.map.get(key)?;
        entry.value.as_ref()
    }

    pub fn contains_key(&self, key: &K) -> bool {
        match self.map.get(key) {
            Some(entry) => !entry.is_tombstone(),
            None => false,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|pair| pair.0)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|pair| pair.1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.map
            .iter()
            .filter_map(|(k, e)| e.value.as_ref().map(|value| (k, value)))
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
    fn test_local_puts() {
        let mut rht1 = Rht::new(1);
        let put_a = rht1.put("key1", "A".to_string());
        let put_b = rht1.put("key2", "B".to_string());
        let put_c = rht1.put("key3", "C".to_string());

        assert_eq!(rht1.get(&"key1"), Some(&"A".to_string()));
        assert_eq!(rht1.get(&"key2"), Some(&"B".to_string()));
        assert_eq!(rht1.get(&"key3"), Some(&"C".to_string()));

        let mut rht2 = Rht::new(2);
        for op in [put_a, put_b, put_c] {
            rht2.apply(op);
        }

        assert_eq!(rht2.get(&"key1"), Some(&"A".to_string()));
        assert_eq!(rht2.get(&"key2"), Some(&"B".to_string()));
        assert_eq!(rht2.get(&"key3"), Some(&"C".to_string()));
    }

    #[test]
    fn test_updates_and_deletes() {
        let mut rht1 = Rht::new(1);
        let put_a = rht1.put("key1", "A".to_string());
        let put_b = rht1.put("key2", "B".to_string());

        assert_eq!(rht1.get(&"key1"), Some(&"A".to_string()));
        assert_eq!(rht1.get(&"key2"), Some(&"B".to_string()));

        let update_a = rht1.update("key1", |v| *v = "A1".to_string()).unwrap();
        assert_eq!(rht1.get(&"key1"), Some(&"A1".to_string()));

        let delete_b = rht1.delete("key2").unwrap();
        assert_eq!(rht1.get(&"key2"), None);

        let mut rht2 = Rht::new(2);
        for op in [put_a, put_b, update_a, delete_b] {
            rht2.apply(op);
        }

        assert_eq!(rht2.get(&"key1"), Some(&"A1".to_string()));
        assert_eq!(rht2.get(&"key2"), None);
    }

    #[test]
    fn test_concurrent_puts_last_write_wins() {
        let mut rht1 = Rht::new(1);
        let put_a1 = rht1.put("key", "A1".to_string());

        let mut rht2 = Rht::new(2);
        let put_a2 = rht2.put("key", "A2".to_string());

        rht1.apply(put_a2.clone());
        rht2.apply(put_a1.clone());

        assert_eq!(rht1.get(&"key"), Some(&"A2".to_string()));
        assert_eq!(rht2.get(&"key"), Some(&"A2".to_string()));

        let mut rht3 = Rht::new(3);
        for op in [&put_a1, &put_a2] {
            rht3.apply(op.clone());
        }

        assert_eq!(rht3.get(&"key"), Some(&"A2".to_string()));
        assert_eq!(rht3.get(&"key"), Some(&"A2".to_string()));

        let mut rht4 = Rht::new(4);
        for op in [put_a2, put_a1] {
            rht4.apply(op);
        }

        assert_eq!(rht4.get(&"key"), Some(&"A2".to_string()));
        assert_eq!(rht4.get(&"key"), Some(&"A2".to_string()));
    }

    #[derive(Debug)]
    enum Op<V> {
        Put(usize, V),
        Delete(usize),
    }

    fn ops<V: Arbitrary>(range: Range<usize>) -> impl Strategy<Value = Op<V>> {
        prop_oneof![
            (range.clone(), any::<V>()).prop_map(|(key, value)| Op::Put(key, value)),
            range.prop_map(|key| Op::Delete(key)),
        ]
    }

    #[proptest]
    fn test_replica_convergence(
        #[strategy(vec(any::<u8>(), 10..200))] seed: Vec<u8>,
        #[strategy(vec(vec(ops(0..#seed.len()), 1..30), 2..100))] plan: Vec<Vec<Op<u8>>>,
    ) {
        let base_rht = {
            let mut rht = Rht::new(0);
            for (index, &value) in seed.iter().enumerate() {
                rht.put(index, value);
            }
            rht
        };
        let baseline_vals: HashMap<_, _> = base_rht.iter().collect();

        // Create n replicas of the base RHT.
        let mut replicas: Vec<_> = plan
            .iter()
            .enumerate()
            .map(|(replica_id, _)| {
                let mut replica = base_rht.clone();
                replica.site = replica_id as u64 + 1;
                replica
            })
            .collect();

        // On each replica RHT, apply m operations.
        // Afterwards, broadcast all operations to every other replica.
        let mut broadcast_queue = vec![];
        for (replica_id, ops) in plan.iter().enumerate() {
            let replica: &mut Rht<usize, u8> = &mut replicas[replica_id];
            broadcast_queue.clear();

            for op in ops {
                match op {
                    Op::Put(key, value) => {
                        let operation = replica.put(*key, value.clone());
                        broadcast_queue.push(operation);
                    }
                    Op::Delete(key) => {
                        if let Some(operation) = replica.delete(*key) {
                            broadcast_queue.push(operation);
                        }
                    }
                }
            }

            eprintln!("replica {}:", replica.site);
            for operation in &broadcast_queue {
                eprintln!("-> {:?}", &operation);
            }

            for replica in replicas.iter_mut() {
                for operation in &broadcast_queue {
                    replica.apply(operation.clone());
                }
            }
        }

        // Check that each of the n replicas have a consistent view of the list.
        let reference_vals: HashMap<_, _> = replicas[0].iter().collect();
        eprintln!("\n--- {:?}", baseline_vals);
        eprintln!("+++ {:?}", reference_vals);
        eprintln!("===============");

        for replica in &replicas[1..] {
            let vals: HashMap<_, _> = replica.iter().collect();
            prop_assert_eq!(&vals, &reference_vals);
        }
    }
}
