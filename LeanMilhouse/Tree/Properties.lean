/-
  Proofs of key correctness properties for Tree get/set operations.
-/
import LeanMilhouse.Tree.Get
import LeanMilhouse.Tree.Set

namespace Tree

theorem get_set_same [Inhabited α] [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    (t.set i v).get i = v
  | 0, .leaf _ _, _, v => by simp [set, get]
  | 0, .packedLeaf _ values, i, v => by simp [set, get]
  | 0, .zero, i, v => by
    simp only [set]
    split
    · simp [get]
    · simp [get]
  | n + 1, .node _ left right, i, v => by
    simp only [set]
    split
    · rename_i h
      simp only [get, h, ↓reduceDIte]
      exact get_set_same left ⟨i.val, h⟩ v
    · rename_i h
      simp only [get]
      split
      · rename_i h'
        exact absurd h' (by omega)
      · exact get_set_same right _ v
  | n + 1, .zero, i, v => by
    simp only [set]
    split
    · rename_i h
      simp only [get, h, ↓reduceDIte]
      exact get_set_same .zero ⟨i.val, h⟩ v
    · rename_i h
      simp only [get]
      split
      · rename_i h'
        exact absurd h' (by omega)
      · exact get_set_same .zero _ v

end Tree
