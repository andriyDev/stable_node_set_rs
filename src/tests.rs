use std::collections::HashMap;

use rand::{seq::SliceRandom, SeedableRng};

use super::{NodeHandle, NodeSet};

#[test]
fn tree_order_is_correct() {
  let mut set = NodeSet::default();
  assert!(set.insert(9).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![9]);
  assert_avl_invariant(&set);
  assert!(set.insert(2).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![2, 9]);
  assert_avl_invariant(&set);
  assert!(set.insert(5).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![2, 5, 9]);
  assert_avl_invariant(&set);
  assert!(set.insert(1).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 2, 5, 9]);
  assert_avl_invariant(&set);
  assert!(set.insert(3).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3, 5, 9]);
  assert_avl_invariant(&set);
  assert!(set.insert(10).is_some());
  assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3, 5, 9, 10]);
  assert_avl_invariant(&set);
  assert!(set.insert(7).is_some());
  assert_eq!(
    set.iter().copied().collect::<Vec<_>>(),
    vec![1, 2, 3, 5, 7, 9, 10]
  );
  assert_avl_invariant(&set);
}

#[test]
fn returns_none_for_element_already_in_set() {
  let mut set = NodeSet::default();
  assert!(set.insert(7).is_some());
  assert!(set.insert(7).is_none());
  assert!(set.insert(7).is_none());
  assert!(set.insert(2).is_some());
  assert!(set.insert(7).is_none());
  assert!(set.insert(2).is_none());
  assert!(set.insert(5).is_some());
  assert!(set.insert(7).is_none());
  assert!(set.insert(5).is_none());
  assert!(set.insert(2).is_none());
}

fn is_ordered<T: PartialOrd + Ord>(mut iter: impl Iterator<Item = T>) -> bool {
  let mut previous = match iter.next() {
    None => return true,
    Some(previous) => previous,
  };
  for value in iter {
    match previous.cmp(&value) {
      std::cmp::Ordering::Less => {}
      _ => return false,
    }
    previous = value;
  }
  true
}

fn assert_avl_invariant<T>(set: &NodeSet<T>) {
  let mut tree_heights = HashMap::new();
  fn compute_height<T>(
    set: &NodeSet<T>,
    node_handle: NodeHandle,
    tree_heights: &mut HashMap<NodeHandle, u32>,
  ) {
    let node = set.get_node(node_handle);
    let mut left_height = 0;
    if let Some(left) = node.left {
      compute_height(set, left, tree_heights);
      left_height = tree_heights[&left];
    }
    let mut right_height = 0;
    if let Some(right) = node.right {
      compute_height(set, right, tree_heights);
      right_height = tree_heights[&right];
    }
    tree_heights.insert(node_handle, right_height.max(left_height) + 1);
  }

  if let Some(root_node) = set.root_node {
    compute_height(set, root_node, &mut tree_heights);
  }
  for node in set.nodes.values() {
    let mut left_height = 0;
    if let Some(left) = node.left {
      left_height = tree_heights[&left];
    }
    let mut right_height = 0;
    if let Some(right) = node.right {
      right_height = tree_heights[&right];
    }
    let expected_balance = right_height as i32 - left_height as i32;
    assert_eq!(
      node.balance_factor,
      expected_balance as _,
      "Set let={}",
      set.len()
    );
    assert!(
      -1 <= node.balance_factor && node.balance_factor <= 1,
      "Balance factor {} is out of range [-1,1]",
      node.balance_factor
    );
  }
}

#[test]
fn randomized_tree_is_ordered_and_satisfies_avl_invariant_after_inserts_and_deletes(
) {
  let mut rng = rand::prelude::StdRng::seed_from_u64(1337);

  let mut values = (0..1000).collect::<Vec<_>>();
  values.shuffle(&mut rng);

  let mut set = NodeSet::default();
  let mut handles = Vec::new();
  for value in values {
    handles.push(set.insert(value).expect("all values are unique"));
    assert!(is_ordered(set.iter()));
    assert_avl_invariant(&set);
  }

  handles.shuffle(&mut rng);

  for handle in handles {
    set.remove(handle);
    assert!(is_ordered(set.iter()));
    assert_eq!(set.len(), set.iter().count());
    assert_avl_invariant(&set);
  }
}
