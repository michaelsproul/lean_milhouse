/-
  Tree.set: functional update of a single element via path-copying.
  Corresponds to `with_updated_leaf` in Rust milhouse.
-/
import LeanMilhouse.Tree
import LeanMilhouse.Packable

namespace Tree

/-- Placeholder hash thunk for newly created/modified nodes.
    The real hash should be recomputed via `treeHash`. -/
private def invalidHash : Thunk Hash := Thunk.mk fun _ => default

private theorem pow_succ_mul (n pf : Nat) :
    2 ^ (n + 1) * pf = 2 ^ n * pf + 2 ^ n * pf := by
  have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [Nat.pow_succ]; omega
  rw [this, Nat.add_mul]

/-- Set the value at index `i` in the tree, returning a new tree via path-copying.

    The index space is `Fin (2^n * packingFactor)` where `n` is the tree depth
    and `packingFactor` determines how many values are packed into each leaf.
    At each internal node, the upper bits of the index determine whether to
    descend left (0) or right (1). At a packed leaf, the lower bits select
    the position within the packed vector.

    Only nodes along the root-to-leaf path are newly allocated; sibling subtrees
    are shared (persistent data structure).

    `zero` nodes are expanded on demand: a `zero` at depth `n+1` becomes a `node`
    with two `zero` children, and the update recurses into the appropriate side.
    At depth `0`, a `zero` becomes either a `leaf` (when `packingFactor = 1`) or
    a `packedLeaf` (when `packingFactor > 1`).

    **Leaf-type invariant**: This function preserves the invariant that a tree
    uses only `leaf` when `packingFactor = 1` and only `packedLeaf` when
    `packingFactor > 1`. The `packedLeaf` vector size is enforced by the type.

    Hash thunks in newly created nodes are invalidated (set to a placeholder).
    Use `treeHash` to recompute the correct merkle root after updates. -/
def set [Inhabited α] [p : Packable α] : {n : Nat} → Tree α n → Fin (2 ^ n * p.packingFactor) → α → Tree α n
  | 0, .leaf _ _, _, v =>
    .leaf invalidHash v
  | 0, .packedLeaf _ values, i, v =>
    if h : i.val < values.size then
      .packedLeaf invalidHash (values.set i.val v h)
    else
      .packedLeaf invalidHash values
  | 0, .zero, i, v =>
    if p.packingFactor == 1 then
      .leaf invalidHash v
    else
      let defaults := Vector.replicate p.packingFactor default
      .packedLeaf invalidHash (defaults.set i.val v (by omega))
  | n + 1, .node _ left right, i, v =>
    if h : i.val < 2 ^ n * p.packingFactor then
      .node invalidHash (set left ⟨i.val, h⟩ v) right
    else
      .node invalidHash left (set right ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor
        have := i.isLt
        omega⟩ v)
  | n + 1, .zero, i, v =>
    if h : i.val < 2 ^ n * p.packingFactor then
      .node invalidHash (set .zero ⟨i.val, h⟩ v) .zero
    else
      .node invalidHash .zero (set .zero ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor
        have := i.isLt
        omega⟩ v)

end Tree
