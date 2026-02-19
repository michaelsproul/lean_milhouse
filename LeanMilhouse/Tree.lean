/-
  Core Tree inductive type definition.
  A depth-indexed persistent binary merkle tree.
-/
import LeanMilhouse.Hash

/-- A depth-indexed persistent binary merkle tree.

    - `α` is the value type stored at leaves.
    - `pf : Nat` is the packing factor (number of values per leaf).
    - `n : Nat` is the depth (number of levels above the leaves).

    The depth index statically guarantees that the tree is balanced:
    a `node` always has two children of equal depth. The packing factor
    is enforced at the type level: `packedLeaf` always holds exactly `pf` values.

    **Leaf-type invariant**: A well-formed tree uses exactly one kind of depth-0
    node, determined by `pf`:
    - `pf = 1` → only `leaf` (never `packedLeaf`)
    - `pf > 1` → only `packedLeaf` (never `leaf`)
    `zero` is permitted at any depth in either regime. -/
inductive Tree (α : Type) (pf : Nat) : Nat → Type where
  /-- A single value at a leaf position (depth 0). -/
  | leaf (hash : Thunk Hash) (value : α) : Tree α pf 0
  /-- Multiple small values packed into one leaf (depth 0).
      The vector length is exactly the packing factor `pf`. -/
  | packedLeaf (hash : Thunk Hash) (values : Vector α pf) : Tree α pf 0
  /-- Internal node with two children of equal depth. -/
  | node (hash : Thunk Hash) (left right : Tree α pf n) : Tree α pf (n + 1)
  /-- Empty subtree representing `2^n` default values.
      Its hash is `MerkleHash.zeroHash n`. -/
  | zero : Tree α pf n
