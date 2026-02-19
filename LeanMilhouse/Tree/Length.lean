/-
  Tree.length: total number of occupied positions in the tree.
-/
import LeanMilhouse.Tree
import LeanMilhouse.Packable

namespace Tree

/-- The total number of occupied positions in the tree.
    For a well-formed tree modelling a prefix list, this equals the list length. -/
def length [p : Packable α] : {n : Nat} → Tree α n → Nat
  | 0, .packedLeaf _ values _ => values.size
  | _, .zero => 0
  | _ + 1, .node _ left right => left.length + right.length

end Tree
