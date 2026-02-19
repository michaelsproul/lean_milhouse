/-
  Tree.set: functional update of a single element via path-copying.
  No-op for out-of-bounds indices and zero nodes.
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

    The index space is `Fin (2^n * packingFactor)` where `n` is the tree depth.
    For a packed leaf, updates the value if the index is within the leaf's current
    size; otherwise returns the tree unchanged (no-op for OOB).
    For `zero` nodes, returns `.zero` (no-op; use `push` to grow the tree).

    Only nodes along the root-to-leaf path are newly allocated; sibling subtrees
    are shared (persistent data structure). -/
def set [p : Packable α] : {n : Nat} → Tree α n → Fin (2 ^ n * p.packingFactor) → α → Tree α n
  | 0, .packedLeaf hash values hk, i, v =>
    if h : i.val < values.size then
      .packedLeaf invalidHash (values.set i.val v (by omega)) hk
    else
      .packedLeaf hash values hk
  | 0, .zero, _, _ => .zero
  | n + 1, .node _ left right, i, v =>
    if h : i.val < 2 ^ n * p.packingFactor then
      .node invalidHash (set left ⟨i.val, h⟩ v) right
    else
      .node invalidHash left (set right ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor
        have := i.isLt
        omega⟩ v)
  | _ + 1, .zero, _, _ => .zero

end Tree
