#![doc = include_str!("../README.md")]

use slotmap::{DefaultKey, SlotMap};
use std::fmt::Debug;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeHandle(DefaultKey);

pub struct NodeSet<T> {
  nodes: SlotMap<DefaultKey, Node<T>>,
  root_node: Option<NodeHandle>,
}

struct Node<T> {
  value: T,
  balance_factor: i8,
  parent: Option<NodeHandle>,
  left: Option<NodeHandle>,
  right: Option<NodeHandle>,
}

impl<T> Node<T> {
  fn child(&self, direction: Direction) -> &Option<NodeHandle> {
    match direction {
      Direction::Left => &self.left,
      Direction::Right => &self.right,
    }
  }

  fn child_mut(&mut self, direction: Direction) -> &mut Option<NodeHandle> {
    match direction {
      Direction::Left => &mut self.left,
      Direction::Right => &mut self.right,
    }
  }

  fn which_child(&self, child_handle: NodeHandle) -> Direction {
    match self.left {
      None => Direction::Right,
      Some(left) => {
        if left == child_handle {
          Direction::Left
        } else {
          Direction::Right
        }
      }
    }
  }
}

impl<T> Default for NodeSet<T> {
  fn default() -> Self {
    Self::new()
  }
}

pub struct NodeSetIterator<'set, T> {
  set: &'set NodeSet<T>,
  node_handle: Option<NodeHandle>,
}

impl<'set, T> Iterator for NodeSetIterator<'set, T> {
  type Item = &'set T;

  fn next(&mut self) -> Option<Self::Item> {
    self.node_handle = match self.node_handle {
      None => self.set.first(),
      Some(node_handle) => self.set.next_handle(node_handle),
    };
    self.node_handle.map(|node_handle| &self.set.get_node(node_handle).value)
  }
}

impl<'set, T> IntoIterator for &'set NodeSet<T> {
  type Item = &'set T;

  type IntoIter = NodeSetIterator<'set, T>;

  fn into_iter(self) -> Self::IntoIter {
    Self::IntoIter { set: self, node_handle: None }
  }
}

impl<T> NodeSet<T> {
  pub fn new() -> Self {
    Self { nodes: SlotMap::new(), root_node: None }
  }

  pub fn len(&self) -> usize {
    self.nodes.len()
  }

  pub fn iter(&self) -> impl Iterator<Item = &T> {
    self.into_iter()
  }

  pub fn get_value(&self, node_handle: NodeHandle) -> Option<&T> {
    self.nodes.get(node_handle.0).map(|node| &node.value)
  }

  // Gets the handle of the first value in the set.
  pub fn first(&self) -> Option<NodeHandle> {
    self.root_node.map(|root_node| {
      self.direction_most_in_subtree(root_node, Direction::Left)
    })
  }

  // Finds the handle of value before `node_handle`.
  pub fn previous_handle(&self, node_handle: NodeHandle) -> Option<NodeHandle> {
    let node = self.nodes.get(node_handle.0)?;
    match node.left {
      Some(left) => {
        Some(self.direction_most_in_subtree(left, Direction::Right))
      }
      None => {
        let mut child = node_handle;
        let mut parent = node.parent;
        while let Some(parent_handle) = parent {
          let parent_node = self.get_node(parent_handle);
          if let Direction::Right = parent_node.which_child(child) {
            break;
          }
          child = parent_handle;
          parent = parent_node.parent;
        }

        parent
      }
    }
  }

  // Finds the handle of value after `node_handle`.
  pub fn next_handle(&self, node_handle: NodeHandle) -> Option<NodeHandle> {
    let node = self.nodes.get(node_handle.0)?;
    match node.right {
      Some(right) => {
        Some(self.direction_most_in_subtree(right, Direction::Left))
      }
      None => {
        let mut child = node_handle;
        let mut parent = node.parent;
        while let Some(parent_handle) = parent {
          let parent_node = self.get_node(parent_handle);
          if let Direction::Left = parent_node.which_child(child) {
            break;
          }
          child = parent_handle;
          parent = parent_node.parent;
        }

        parent
      }
    }
  }

  fn get_node(&self, handle: NodeHandle) -> &Node<T> {
    self.nodes.get(handle.0).unwrap()
  }

  fn get_node_mut(&mut self, handle: NodeHandle) -> &mut Node<T> {
    self.nodes.get_mut(handle.0).unwrap()
  }

  fn rotate_left(&mut self, node_handle: NodeHandle) {
    let parent = self.get_node(node_handle).parent;
    let new_root = self.get_node(node_handle).child(Direction::Right).expect(
      "If we are doing a left rotation, there must be a node to the right.",
    );
    let rebased_subtree = *self.get_node(new_root).child(Direction::Left);

    // Make parent point to the new root.
    match parent {
      None => self.root_node = Some(new_root),
      Some(parent) => {
        let parent = self.get_node_mut(parent);
        *parent.child_mut(parent.which_child(node_handle)) = Some(new_root);
      }
    }

    let new_root_node = self.get_node_mut(new_root);
    // Assign the parent of the new_root.
    new_root_node.parent = parent;
    // Make the old root a child of `new_root`.
    *new_root_node.child_mut(Direction::Left) = Some(node_handle);

    let old_root_node = self.get_node_mut(node_handle);
    // Set the parent of the old root to be the new root.
    old_root_node.parent = Some(new_root);
    // Make the rebased subtree a child of the old root.
    *old_root_node.child_mut(Direction::Right) = rebased_subtree;

    // Update the parent of the rebased subtree.
    if let Some(rebased_subtree) = rebased_subtree {
      self.get_node_mut(rebased_subtree).parent = Some(node_handle);
    }

    let new_root_node = self.get_node_mut(new_root);
    if new_root_node.balance_factor == 0 {
      // Only happens on deletion. The rebased subtree had the same height
      // as its (previous) sibling.
      new_root_node.balance_factor = -1;
      let old_root_node = self.get_node_mut(node_handle);
      old_root_node.balance_factor = 1;
    } else {
      new_root_node.balance_factor = 0;
      let old_root_node = self.get_node_mut(node_handle);
      old_root_node.balance_factor = 0
    }
  }

  fn rotate_right(&mut self, node_handle: NodeHandle) {
    let parent = self.get_node(node_handle).parent;
    let new_root = self.get_node(node_handle).child(Direction::Left).expect(
      "If we are doing a right rotation, there must be a node to the left.",
    );
    let rebased_subtree = *self.get_node(new_root).child(Direction::Right);

    // Make parent point to the new root.
    match parent {
      None => self.root_node = Some(new_root),
      Some(parent) => {
        let parent = self.get_node_mut(parent);
        *parent.child_mut(parent.which_child(node_handle)) = Some(new_root);
      }
    }

    let new_root_node = self.get_node_mut(new_root);
    // Assign the parent of the new_root.
    new_root_node.parent = parent;
    // Make the old root a child of `new_root`.
    *new_root_node.child_mut(Direction::Right) = Some(node_handle);

    let old_root_node = self.get_node_mut(node_handle);
    // Set the parent of the old root to be the new root.
    old_root_node.parent = Some(new_root);
    // Make the rebased subtree a child of the old root.
    *old_root_node.child_mut(Direction::Left) = rebased_subtree;

    // Update the parent of the rebased subtree.
    if let Some(rebased_subtree) = rebased_subtree {
      self.get_node_mut(rebased_subtree).parent = Some(node_handle);
    }

    let new_root_node = self.get_node_mut(new_root);
    if new_root_node.balance_factor == 0 {
      // Only happens on deletion. The rebased subtree had the same height
      // as its (previous) sibling.
      new_root_node.balance_factor = 1;
      let old_root_node = self.get_node_mut(node_handle);
      old_root_node.balance_factor = -1;
    } else {
      new_root_node.balance_factor = 0;
      let old_root_node = self.get_node_mut(node_handle);
      old_root_node.balance_factor = 0
    }
  }

  fn rotate_right_left(&mut self, node_handle: NodeHandle) {
    let parent = self.get_node(node_handle).parent;
    let new_left_child = node_handle;
    let new_right_child = self
            .get_node(node_handle)
            .child(Direction::Right)
            .expect("If we are doing a right-left rotation, there must be a node to the right.");
    let new_root = self.get_node(new_right_child).child(Direction::Left).expect("If we are doing a right-left rotation, these must be a node to the left of the right child");
    let new_root_node = self.get_node_mut(new_root);
    let rebased_left_child = *new_root_node.child(Direction::Left);
    let rebased_right_child = *new_root_node.child(Direction::Right);

    new_root_node.parent = parent;
    new_root_node.left = Some(new_left_child);
    new_root_node.right = Some(new_right_child);
    // Make parent point to the new root.
    match parent {
      None => self.root_node = Some(new_root),
      Some(parent) => {
        let parent = self.get_node_mut(parent);
        *parent.child_mut(parent.which_child(node_handle)) = Some(new_root);
      }
    }

    let new_left_node = self.get_node_mut(new_left_child);
    new_left_node.parent = Some(new_root);
    new_left_node.right = rebased_left_child;
    if let Some(rebased_left_child) = rebased_left_child {
      self.get_node_mut(rebased_left_child).parent = Some(new_left_child);
    }

    let new_right_node = self.get_node_mut(new_right_child);
    new_right_node.parent = Some(new_root);
    new_right_node.left = rebased_right_child;
    if let Some(rebased_right_child) = rebased_right_child {
      self.get_node_mut(rebased_right_child).parent = Some(new_right_child);
    }

    match self.get_node(new_root).balance_factor.cmp(&0) {
      std::cmp::Ordering::Equal => {
        // Only happens on deletion. The rebased left and right subtrees
        // had the same height.
        self.get_node_mut(new_left_child).balance_factor = 0;
        self.get_node_mut(new_right_child).balance_factor = 0;
      }
      std::cmp::Ordering::Greater => {
        self.get_node_mut(new_left_child).balance_factor = -1;
        self.get_node_mut(new_right_child).balance_factor = 0;
      }
      std::cmp::Ordering::Less => {
        self.get_node_mut(new_left_child).balance_factor = 0;
        self.get_node_mut(new_right_child).balance_factor = 1;
      }
    };
    self.get_node_mut(new_root).balance_factor = 0;
  }

  fn rotate_left_right(&mut self, node_handle: NodeHandle) {
    let parent = self.get_node(node_handle).parent;
    let new_right_child = node_handle;
    let new_left_child = self
            .get_node(node_handle)
            .child(Direction::Left)
            .expect("If we are doing a left-right rotation, there must be a node to the left.");
    let new_root = self.get_node(new_left_child).child(Direction::Right).expect("If we are doing a left-right rotation, these must be a node to the right of the left child");
    let new_root_node = self.get_node_mut(new_root);
    let rebased_left_child = *new_root_node.child(Direction::Left);
    let rebased_right_child = *new_root_node.child(Direction::Right);

    new_root_node.parent = parent;
    new_root_node.left = Some(new_left_child);
    new_root_node.right = Some(new_right_child);
    // Make parent point to the new root.
    match parent {
      None => self.root_node = Some(new_root),
      Some(parent) => {
        let parent = self.get_node_mut(parent);
        *parent.child_mut(parent.which_child(node_handle)) = Some(new_root);
      }
    }

    let new_left_node = self.get_node_mut(new_left_child);
    new_left_node.parent = Some(new_root);
    new_left_node.right = rebased_left_child;
    if let Some(rebased_left_child) = rebased_left_child {
      self.get_node_mut(rebased_left_child).parent = Some(new_left_child);
    }

    let new_right_node = self.get_node_mut(new_right_child);
    new_right_node.parent = Some(new_root);
    new_right_node.left = rebased_right_child;
    if let Some(rebased_right_child) = rebased_right_child {
      self.get_node_mut(rebased_right_child).parent = Some(new_right_child);
    }

    match self.get_node(new_root).balance_factor.cmp(&0) {
      std::cmp::Ordering::Equal => {
        // Only happens on deletion. The rebased left and right subtrees
        // had the same height.
        self.get_node_mut(new_left_child).balance_factor = 0;
        self.get_node_mut(new_right_child).balance_factor = 0;
      }
      // TODO
      std::cmp::Ordering::Greater => {
        self.get_node_mut(new_left_child).balance_factor = -1;
        self.get_node_mut(new_right_child).balance_factor = 0;
      }
      std::cmp::Ordering::Less => {
        self.get_node_mut(new_left_child).balance_factor = 0;
        self.get_node_mut(new_right_child).balance_factor = 1;
      }
    };
    self.get_node_mut(new_root).balance_factor = 0;
  }

  /// Finds the node in `subtree` furthest in `direction`.
  fn direction_most_in_subtree(
    &self,
    subtree: NodeHandle,
    direction: Direction,
  ) -> NodeHandle {
    let subtree_node = self.nodes.get(subtree.0).unwrap();
    let next = match direction {
      Direction::Left => subtree_node.left,
      Direction::Right => subtree_node.right,
    };

    match next {
      None => subtree,
      Some(next) => self.direction_most_in_subtree(next, direction),
    }
  }

  fn rebalance_insert(
    &mut self,
    new_node: NodeHandle,
    initial_parent: NodeHandle,
  ) {
    let new_node_direction =
      self.get_node(initial_parent).which_child(new_node);
    let mut parent_and_child = Some((initial_parent, new_node_direction));
    let get_parent_and_child = |set: &Self, old_parent| {
      set.get_node(old_parent).parent.map(|new_parent| {
        (new_parent, set.get_node(new_parent).which_child(old_parent))
      })
    };

    while let Some((parent_handle, child_direction)) = parent_and_child {
      let parent_node = self.get_node_mut(parent_handle);
      match (parent_node.balance_factor.cmp(&0), child_direction) {
        (std::cmp::Ordering::Equal, Direction::Right) => {
          parent_node.balance_factor = 1;
          parent_and_child = get_parent_and_child(self, parent_handle);
        }
        (std::cmp::Ordering::Equal, Direction::Left) => {
          parent_node.balance_factor = -1;
          parent_and_child = get_parent_and_child(self, parent_handle);
        }
        (std::cmp::Ordering::Less, Direction::Right) => {
          parent_node.balance_factor = 0;
          break;
        }
        (std::cmp::Ordering::Greater, Direction::Left) => {
          parent_node.balance_factor = 0;
          break;
        }
        (std::cmp::Ordering::Greater, Direction::Right) => {
          // The parent is right-heavy and a node was inserted on the right
          // subtree.
          let right_child = parent_node.right.expect(
            "The node is right-heavy, so there must be a node to the right.",
          );
          let child_node = self.get_node(right_child);
          if child_node.balance_factor < 0 {
            // The child is left-heavy, so do a double rotation.
            self.rotate_right_left(parent_handle);
          } else {
            self.rotate_left(parent_handle);
          }
          break;
        }
        (std::cmp::Ordering::Less, Direction::Left) => {
          // The parent is left-heavy and a node was inserted on the left
          // subtree.
          let left_child = parent_node.left.expect(
            "The node is left-heavy, so there must be a node to the left.",
          );
          let child_node = self.get_node(left_child);
          if child_node.balance_factor > 0 {
            // The child is right-heavy, so do a double rotation.
            self.rotate_left_right(parent_handle);
          } else {
            self.rotate_right(parent_handle);
          }
          break;
        }
      }
    }
  }

  fn rebalance_delete(
    &mut self,
    initial_parent: NodeHandle,
    deleted_direction: Direction,
  ) {
    let mut parent_and_child = Some((initial_parent, deleted_direction));
    let get_parent_and_child = |set: &Self, old_parent| {
      set.get_node(old_parent).parent.map(|new_parent| {
        (new_parent, set.get_node(new_parent).which_child(old_parent))
      })
    };

    while let Some((parent_handle, child_direction)) = parent_and_child {
      let parent_node = self.get_node_mut(parent_handle);
      match (parent_node.balance_factor.cmp(&0), child_direction) {
        (std::cmp::Ordering::Equal, Direction::Left) => {
          parent_node.balance_factor = 1;
          break;
        }
        (std::cmp::Ordering::Equal, Direction::Right) => {
          parent_node.balance_factor = -1;
          break;
        }
        (std::cmp::Ordering::Less, Direction::Left) => {
          parent_node.balance_factor = 0;
          parent_and_child = get_parent_and_child(self, parent_handle);
        }
        (std::cmp::Ordering::Greater, Direction::Right) => {
          parent_node.balance_factor = 0;
          parent_and_child = get_parent_and_child(self, parent_handle);
        }
        (std::cmp::Ordering::Greater, Direction::Left) => {
          // The parent is right-heavy and a node was deleted on the left
          // subtree.
          let right_child = parent_node.right.expect(
            "The node is right-heavy, so there must be a node to the right.",
          );
          // Update the parent and direction in case we don't break out of the
          // loop.
          parent_and_child = get_parent_and_child(self, parent_handle);
          let balance_factor = self.get_node(right_child).balance_factor;
          if balance_factor < 0 {
            // The child is left-heavy, so do a double rotation.
            self.rotate_right_left(parent_handle);
          } else {
            self.rotate_left(parent_handle);
          }
          if balance_factor == 0 {
            break;
          }
        }
        (std::cmp::Ordering::Less, Direction::Right) => {
          // The parent is left-heavy and a node was deleted on the right
          // subtree.
          let left_child = parent_node.left.expect(
            "The node is left-heavy, so there must be a node to the left.",
          );
          // Update the parent and direction in case we don't break out of the
          // loop.
          parent_and_child = get_parent_and_child(self, parent_handle);
          let balance_factor = self.get_node(left_child).balance_factor;
          if balance_factor > 0 {
            // The child is right-heavy, so do a double rotation.
            self.rotate_left_right(parent_handle);
          } else {
            self.rotate_right(parent_handle);
          }
          if balance_factor == 0 {
            break;
          }
        }
      }
    }
  }
}

/// The result of looking for a value in the set.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FoundHandle {
  // The value is in the set, and its handle is returned.
  Found(NodeHandle),
  // The set is empty - the value is not in the set.
  SetEmpty,
  // The set does not contain the value and the handle of the value before it
  // is provided. This is equivalent to `MissingWithNextHandle`. Both are
  // provided so users can know which direction to search.
  MissingWithPreviousHandle(NodeHandle),
  // The set does not contain the value and the handle of the value after it
  // is provided. This is equivalent to `MissingWithPreviousHandle`. Both are
  // provided so users can know which direction to search.
  MissingWithNextHandle(NodeHandle),
}

impl<T: PartialOrd + Ord> NodeSet<T> {
  /// Finds the slot in `node_handle`s subtree that `value` should be placed
  /// in. Returns `Ok` if `value` is not in the set, and `Err` if the value is
  /// already in the set.
  fn find_slot(
    &self,
    node_handle: NodeHandle,
    value: &T,
  ) -> Result<(NodeHandle, Direction), NodeHandle> {
    let node = self.nodes.get(node_handle.0).unwrap();
    match value.cmp(&node.value) {
      std::cmp::Ordering::Equal => Err(node_handle),
      std::cmp::Ordering::Less => match node.left {
        None => Ok((node_handle, Direction::Left)),
        Some(left) => self.find_slot(left, value),
      },
      std::cmp::Ordering::Greater => match node.right {
        None => Ok((node_handle, Direction::Right)),
        Some(right) => self.find_slot(right, value),
      },
    }
  }

  /// Looks for `value` in the set.
  pub fn find_handle(&mut self, value: &T) -> FoundHandle {
    let Some(root_node) = self.root_node else {
      return FoundHandle::SetEmpty;
    };
    match self.find_slot(root_node, value) {
      Err(node_handle) => FoundHandle::Found(node_handle),
      Ok((node_handle, Direction::Left)) => {
        FoundHandle::MissingWithNextHandle(node_handle)
      }
      Ok((node_handle, Direction::Right)) => {
        FoundHandle::MissingWithPreviousHandle(node_handle)
      }
    }
  }

  pub fn insert(&mut self, value: T) -> Option<NodeHandle> {
    let mut new_node =
      Node { value, balance_factor: 0, parent: None, left: None, right: None };
    match self.root_node {
      None => {
        let new_handle = NodeHandle(self.nodes.insert(new_node));
        self.root_node = Some(new_handle);
        Some(new_handle)
      }
      Some(root_node) => {
        let (parent, direction) =
          self.find_slot(root_node, &new_node.value).ok()?;

        new_node.parent = Some(parent);
        let new_handle = NodeHandle(self.nodes.insert(new_node));

        *self.get_node_mut(parent).child_mut(direction) = Some(new_handle);

        self.rebalance_insert(new_handle, parent);
        Some(new_handle)
      }
    }
  }

  pub fn remove(&mut self, node_handle: NodeHandle) -> Option<T> {
    let node = self.nodes.get(node_handle.0)?;
    match (node.left, node.right) {
      (None, None) => {
        let parent = node.parent;
        let node = self.nodes.remove(node_handle.0)?;
        match parent {
          None => self.root_node = None,
          Some(parent) => {
            let parent_node = self.get_node_mut(parent);
            let direction = parent_node.which_child(node_handle);
            *parent_node.child_mut(direction) = None;

            self.nodes.remove(node_handle.0);
            self.rebalance_delete(parent, direction);
          }
        }
        Some(node.value)
      }
      (Some(left), None) => {
        let parent = node.parent;
        let node = self.nodes.remove(node_handle.0)?;
        self.get_node_mut(left).parent = parent;
        match parent {
          None => self.root_node = Some(left),
          Some(parent) => {
            let parent_node = self.get_node_mut(parent);
            let direction = parent_node.which_child(node_handle);
            *parent_node.child_mut(direction) = Some(left);
            self.rebalance_delete(parent, direction);
          }
        }
        Some(node.value)
      }
      (None, Some(right)) => {
        let parent = node.parent;
        let node = self.nodes.remove(node_handle.0)?;
        self.get_node_mut(right).parent = parent;
        match parent {
          None => self.root_node = Some(right),
          Some(parent) => {
            let parent_node = self.get_node_mut(parent);
            let direction = parent_node.which_child(node_handle);
            *parent_node.child_mut(direction) = Some(right);
            self.rebalance_delete(parent, direction);
          }
        }
        Some(node.value)
      }
      (Some(left), Some(right)) => {
        let node_parent = node.parent;
        let node_balance = node.balance_factor;

        let replacement_node_handle = self.next_handle(node_handle).expect(
          "The node has a right child, so there is at least one next handle.",
        );

        let node = self.nodes.remove(node_handle.0)?;

        self.get_node_mut(left).parent = Some(replacement_node_handle);

        let replacement_node = self.get_node_mut(replacement_node_handle);
        // replacement_node.left is None since it is the next handle.
        let replacement_node_right = replacement_node.right;
        let replacement_node_parent = replacement_node.parent.expect("the next handle is a child of the right subtree, so at the least, node_handle is the parent.");

        replacement_node.balance_factor = node_balance;
        replacement_node.left = Some(left);
        replacement_node.parent = node_parent;
        match node_parent {
          None => self.root_node = Some(replacement_node_handle),
          Some(parent) => {
            let parent_node = self.get_node_mut(parent);
            let direction = parent_node.which_child(node_handle);
            *parent_node.child_mut(direction) = Some(replacement_node_handle);
          }
        }

        if replacement_node_handle == right {
          self.rebalance_delete(replacement_node_handle, Direction::Right);
          return Some(node.value);
        }
        self.get_node_mut(replacement_node_handle).right = Some(right);
        self.get_node_mut(right).parent = Some(replacement_node_handle);
        self.get_node_mut(replacement_node_parent).left =
          replacement_node_right;
        if let Some(replacement_node_right) = replacement_node_right {
          self.get_node_mut(replacement_node_right).parent =
            Some(replacement_node_parent);
        }
        self.rebalance_delete(replacement_node_parent, Direction::Left);
        Some(node.value)
      }
    }
  }
}

#[derive(Clone, Copy)]
enum Direction {
  Left,
  Right,
}

#[cfg(test)]
mod tests;
