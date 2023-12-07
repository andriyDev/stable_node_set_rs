# stable_node_set

A crate for an ordered set with handles to values.

## Should I use a stable node set?

Probably not. You should only use this when:

1) You need a set.
2) You need the values to be ordered (e.g., for iteration, or determining the
previous or next value of another value).
3) One of these two:
  a) You need a stable handle to the value.
  b) You need to find the next/previous value of another value in the set.

The last requirement is the most restrictive. This means you can't search for
your value (perhaps it gets too expensive, or the order is unstable), or you
need to be able to get the next and previous values (which is not common).

## Example

```rust
use stable_node_set::{NodeSet, NodeHandle};

fn main() {
  let mut node_set = NodeSet::new();

  let handle_1 = node_set.insert(1).unwrap();
  let handle_2 = node_set.insert(2).unwrap();
  let handle_3 = node_set.insert(3).unwrap();

  assert_eq!(node_set.remove(handle_1).unwrap(), 1);
  assert_eq!(node_set.remove(handle_2).unwrap(), 2);
  assert_eq!(node_set.remove(handle_3).unwrap(), 3);
}
```

## License

License under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
