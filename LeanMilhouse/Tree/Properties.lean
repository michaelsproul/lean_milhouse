/-
  Proofs of key correctness properties for Tree get/set operations.
-/
import LeanMilhouse.Tree.Get
import LeanMilhouse.Tree.Set

namespace Tree

@[simp] theorem get_zero [Inhabited α] [p : Packable α] {n : Nat}
    (i : Fin (2 ^ n * p.packingFactor)) :
    (.zero : Tree α n).get i = (default : α) := by
  cases n <;> simp [get]

theorem get_set_same [Inhabited α] [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    (t.set i v).get i = v
  | 0, .packedLeaf _ values, i, v => by simp [set, get]
  | 0, .zero, i, v => by simp [set, get]
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

theorem get_set_other [Inhabited α] [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i j : Fin (2 ^ n * p.packingFactor)) (v : α),
    i ≠ j → (t.set i v).get j = t.get j
  -- packedLeaf: Vector.set at different index is identity
  | 0, .packedLeaf _ values, i, j, v, hij => by
    simp only [set, get]
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hne]
  -- zero at depth 0: expands to packedLeaf, then vector lemmas
  | 0, .zero, i, j, v, hij => by
    simp only [set, get]
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hne]
  -- node: recurse into matching subtree, other subtree unaffected
  | n + 1, .node _ left right, i, j, v, hij => by
    simp only [set]
    split
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte]
        exact get_set_other left ⟨i.val, hi⟩ ⟨j.val, hj⟩ v
          (by intro heq
              have h := Fin.ext_iff.mp heq
              exact hij (Fin.ext h))
      · simp only [get, hj, ↓reduceDIte]
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte]
      · simp only [get, hj, ↓reduceDIte]
        exact get_set_other right _ _ v
          (by intro heq
              have h := Fin.ext_iff.mp heq; simp at h
              exact hij (Fin.ext (by omega)))
  -- zero at depth n+1: expand and recurse, using get_zero for default
  | n + 1, .zero, i, j, v, hij => by
    simp only [set]
    split
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte]
        rw [get_set_other .zero ⟨i.val, hi⟩ ⟨j.val, hj⟩ v
          (by intro heq
              have h := Fin.ext_iff.mp heq
              exact hij (Fin.ext h)),
          get_zero]
      · simp only [get, hj, ↓reduceDIte, get_zero]
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte, get_zero]
      · simp only [get, hj, ↓reduceDIte]
        rw [get_set_other .zero _ _ v
          (by intro heq
              have h := Fin.ext_iff.mp heq; simp at h
              exact hij (Fin.ext (by omega))),
          get_zero]

end Tree
