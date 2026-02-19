/-
  Core Tree inductive type definition.
  A depth-indexed persistent binary merkle tree.
-/
import LeanMilhouse.Hash
import LeanMilhouse.Packable

/-- A depth-indexed persistent binary merkle tree.

    - `α` is the value type stored at leaves.
    - `n : Nat` is the depth (number of levels above the leaves).

    The `Packable α` instance determines how many values are packed into each
    leaf. The packing factor is enforced at the type level: `packedLeaf` always
    holds exactly `packingFactor` values.

    The depth index statically guarantees that the tree is balanced:
    a `node` always has two children of equal depth.

    **Leaf-type invariant**: A well-formed tree uses exactly one kind of depth-0
    node, determined by `packingFactor`:
    - `packingFactor = 1` → only `leaf` (never `packedLeaf`)
    - `packingFactor > 1` → only `packedLeaf` (never `leaf`)
    `zero` is permitted at any depth in either regime. -/
inductive Tree (α : Type) [p : Packable α] : Nat → Type where
  /-- A single value at a leaf position (depth 0). -/
  | leaf (hash : Thunk Hash) (value : α) : Tree α 0
  /-- Multiple small values packed into one leaf (depth 0).
      The vector length is exactly `Packable.packingFactor`. -/
  | packedLeaf (hash : Thunk Hash) (values : Vector α p.packingFactor) : Tree α 0
  /-- Internal node with two children of equal depth. -/
  | node (hash : Thunk Hash) (left right : Tree α n) : Tree α (n + 1)
  /-- Empty subtree representing `2^n` default values.
      Its hash is `MerkleHash.zeroHash n`. -/
  | zero : Tree α n
