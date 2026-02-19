/-
  Tree.push: append a value to the next available position.
  Fills left subtrees before right, maintaining the prefix invariant.
-/
import LeanMilhouse.Tree
import LeanMilhouse.Tree.Length
import LeanMilhouse.Packable

namespace Tree

/-- Placeholder hash thunk for newly created/modified nodes. -/
private def invalidHash : Thunk Hash := Thunk.mk fun _ => default

/-- Append a value to the tree at the next available position.

    The tree is filled left-to-right: at a node, push goes left if the left
    subtree is not yet full, otherwise right. At a packed leaf, the value is
    appended if there is room. At a `zero` node, a new subtree is created.

    If the tree is already at full capacity, this is a no-op.
    Use `push_length` (with `t.length < capacity`) to prove the length increases. -/
def push [p : Packable α] : {n : Nat} → Tree α n → α → Tree α n
  | 0, .packedLeaf hash values hk, v =>
    if h : values.size < p.packingFactor then
      .packedLeaf invalidHash (values.push v) (by dsimp [Vector.size] at h; omega)
    else
      .packedLeaf hash values hk
  | 0, .zero, v =>
    .packedLeaf invalidHash #v[v] (by have := p.packingFactor_pos; omega)
  | n + 1, .node _ left right, v =>
    if left.length < 2 ^ n * p.packingFactor then
      .node invalidHash (push left v) right
    else
      .node invalidHash left (push right v)
  | n + 1, .zero, v =>
    .node invalidHash (push .zero v) .zero

end Tree
