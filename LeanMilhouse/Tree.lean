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
    holds exactly `packingFactor` values (including the `packingFactor = 1` case).

    The depth index statically guarantees that the tree is balanced:
    a `node` always has two children of equal depth.
    `zero` is permitted at any depth. -/
inductive Tree (α : Type) [p : Packable α] : Nat → Type where
  /-- Packed leaf holding exactly `packingFactor` values (depth 0). -/
  | packedLeaf (hash : Thunk Hash) (values : Vector α p.packingFactor) : Tree α 0
  /-- Internal node with two children of equal depth. -/
  | node (hash : Thunk Hash) (left right : Tree α n) : Tree α (n + 1)
  /-- Empty subtree representing `2^n` default values.
      Its hash is `MerkleHash.zeroHash n`. -/
  | zero : Tree α n
