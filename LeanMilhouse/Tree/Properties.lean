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
  | 0, .packedLeaf _ values, i, v => by
    simp only [set]
    have hsize : values.size = p.packingFactor := by simp [Vector.size]
    have hi : i.val < values.size := by omega
    split
    · rename_i h
      simp only [get, h, ↓reduceDIte]
      simp
    · rename_i h
      exact absurd hi h
  | 0, .zero, i, v => by
    simp only [set]
    split
    · simp [get]
    · rename_i hpf
      simp only [get]
      have hsize : ((Vector.replicate p.packingFactor default).set i.val v (by omega)).size
        = p.packingFactor := by simp [Vector.size]
      split
      · simp
      · rename_i h
        exact absurd (by omega : i.val < _) h
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
