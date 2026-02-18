/-
  Tree.set: functional update of a single element via path-copying.
  Corresponds to `with_updated_leaf` in Rust milhouse.
-/
import LeanMilhouse.Tree

namespace Tree

/-- Placeholder hash thunk for newly created/modified nodes.
    The real hash should be recomputed via `treeHash`. -/
private def invalidHash : Thunk Hash := Thunk.mk fun _ => default

/-- Set the value at index `i` in the tree, returning a new tree via path-copying.

    Corresponds to `with_updated_leaf` in Rust milhouse. At each internal node,
    the high bit of the index determines whether to descend left (0) or right (1).
    Only nodes along the root-to-leaf path are newly allocated; sibling subtrees
    are shared (persistent data structure).

    `zero` nodes are expanded on demand: a `zero` at depth `n+1` becomes a `node`
    with two `zero` children, and the update recurses into the appropriate side.

    Hash thunks in newly created nodes are invalidated (set to a placeholder).
    Use `treeHash` to recompute the correct merkle root after updates. -/
def set : {n : Nat} → Tree α n → Fin (2 ^ n) → α → Tree α n
  | 0, .leaf _ _, _, v => .leaf invalidHash v
  | 0, .packedLeaf _ _, _, v => .leaf invalidHash v
  | 0, .zero, _, v => .leaf invalidHash v
  | n + 1, .node _ left right, i, v =>
    if h : i.val < 2 ^ n then
      .node invalidHash (left.set ⟨i.val, h⟩ v) right
    else
      .node invalidHash left (right.set ⟨i.val - 2 ^ n, by omega⟩ v)
  | n + 1, .zero, i, v =>
    if h : i.val < 2 ^ n then
      .node invalidHash (Tree.zero.set ⟨i.val, h⟩ v) .zero
    else
      .node invalidHash .zero (Tree.zero.set ⟨i.val - 2 ^ n, by omega⟩ v)

end Tree
