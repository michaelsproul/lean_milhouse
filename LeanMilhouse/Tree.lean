/-
  Core Tree inductive type definition.
  A depth-indexed persistent binary merkle tree.
-/
import LeanMilhouse.Hash

/-- A depth-indexed persistent binary merkle tree.

    - `α` is the value type stored at leaves.
    - `n : Nat` is the depth (number of levels above the leaves).

    The depth index statically guarantees that the tree is balanced:
    a `node` always has two children of equal depth. -/
inductive Tree (α : Type) : Nat → Type where
  /-- A single value at a leaf position (depth 0). -/
  | leaf (hash : Thunk Hash) (value : α) : Tree α 0
  /-- Multiple small values packed into one leaf (depth 0).
      The number of values `k` is typically `Packable.packingFactor`. -/
  | packedLeaf (hash : Thunk Hash) (values : Vector α k) : Tree α 0
  /-- Internal node with two children of equal depth. -/
  | node (hash : Thunk Hash) (left right : Tree α n) : Tree α (n + 1)
  /-- Empty subtree representing `2^n` default values.
      Its hash is `MerkleHash.zeroHash n`. -/
  | zero : Tree α n
