/-
  Core Tree inductive type definition.
  A depth-indexed persistent binary merkle tree.
-/
import LeanMilhouse.Hash
import LeanMilhouse.Packable

/-- A depth-indexed persistent binary merkle tree modelling a growable prefix list.

    - `α` is the value type stored at leaves.
    - `n : Nat` is the depth (number of levels above the leaves).

    The `Packable α` instance determines the maximum number of values packed into
    each leaf (`packingFactor`). A `packedLeaf` holds a `Vector α k` where
    `k ≤ packingFactor`, allowing variable-length leaves for the prefix model.

    The depth index statically guarantees that the tree is balanced:
    a `node` always has two children of equal depth.
    `zero` is permitted at any depth and represents an empty subtree. -/
inductive Tree (α : Type) [p : Packable α] : Nat → Type where
  /-- Packed leaf holding up to `packingFactor` values (depth 0). -/
  | packedLeaf (hash : Thunk Hash) (values : Vector α k) (hk : k ≤ p.packingFactor) : Tree α 0
  /-- Internal node with two children of equal depth. -/
  | node (hash : Thunk Hash) (left right : Tree α n) : Tree α (n + 1)
  /-- Empty subtree (no values). Its hash is `MerkleHash.zeroHash n`. -/
  | zero : Tree α n
