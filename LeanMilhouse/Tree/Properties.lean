/-
  Properties and correctness proofs for Tree operations.
-/
import LeanMilhouse.Tree.Get
import LeanMilhouse.Tree.Set
import LeanMilhouse.Tree.Length
import LeanMilhouse.Tree.Push

namespace Tree

private theorem pow_succ_mul (n pf : Nat) :
    2 ^ (n + 1) * pf = 2 ^ n * pf + 2 ^ n * pf := by
  have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [Nat.pow_succ]; omega
  rw [this, Nat.add_mul]

private theorem capacity_pos [p : Packable α] (n : Nat) :
    0 < 2 ^ n * p.packingFactor :=
  Nat.mul_pos (by have := @Nat.one_le_two_pow n; omega) p.packingFactor_pos

def WellFormed [p : Packable α] : {n : Nat} → Tree α n → Prop
  | _, .zero => True
  | 0, .packedLeaf _ _ _ => True
  | n + 1, .node _ left right =>
    left.WellFormed ∧ right.WellFormed ∧
    (right.length > 0 → left.length = 2 ^ n * p.packingFactor)

@[simp] theorem get_zero [p : Packable α] {n : Nat}
    (i : Fin (2 ^ n * p.packingFactor)) :
    (.zero : Tree α n).get i = none := by
  cases n <;> simp [get]

@[simp] theorem length_zero [p : Packable α] {n : Nat} :
    (.zero : Tree α n).length = 0 := by
  cases n <;> simp [length]

theorem length_le_capacity [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n), t.length ≤ 2 ^ n * p.packingFactor
  | 0, .packedLeaf _ values hk => by
    show values.size ≤ 2 ^ 0 * p.packingFactor
    simp [Vector.size, Nat.pow_zero]; exact hk
  | 0, .zero => by simp [length]
  | n + 1, .node _ left right => by
    simp only [length]
    have := length_le_capacity left
    have := length_le_capacity right
    have := pow_succ_mul n p.packingFactor; omega
  | _ + 1, .zero => by simp [length]

private theorem packed_lt_pf [p : Packable α] {k : Nat} {values : Vector α k}
    {hk : k ≤ p.packingFactor} {hash : Thunk Hash}
    (h : (Tree.packedLeaf hash values hk : Tree α 0).length < 2 ^ 0 * p.packingFactor) :
    values.size < p.packingFactor := by
  dsimp only [length, Vector.size] at h
  simp only [Nat.pow_zero, Nat.one_mul] at h; exact h

-- ============================================================

theorem set_length [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    (t.set i v).length = t.length
  | 0, .packedLeaf _ values hk, i, v => by
    simp only [set]; split <;> simp [length]
  | 0, .zero, _, _ => rfl
  | n + 1, .node _ left right, i, v => by
    simp only [set]; split
    · rename_i h; simp only [length]
      have := set_length left ⟨i.val, h⟩ v; omega
    · rename_i h; simp only [length]
      have := set_length right ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor; have := i.isLt; omega⟩ v; omega
  | _ + 1, .zero, _, _ => rfl

-- ============================================================

theorem get_set_other [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i j : Fin (2 ^ n * p.packingFactor)) (v : α),
    i ≠ j → (t.set i v).get j = t.get j
  | 0, .packedLeaf _ values hk, i, j, v, hij => by
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [set]; split
    · by_cases hj : j.val < values.size
      · simp only [get, show j.val < (values.set i.val v (by omega)).size from hj,
                    ↓reduceDIte]
        congr 1; simp [hne]
      · simp only [get, show ¬(j.val < (values.set i.val v (by omega)).size) from hj,
                    ↓reduceDIte]
    · rfl
  | 0, .zero, _, _, _, _ => rfl
  | n + 1, .node _ left right, i, j, v, hij => by
    simp only [set]; split
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte]
        exact get_set_other left ⟨i.val, hi⟩ ⟨j.val, hj⟩ v
          (by intro heq
              have h := congrArg (fun (x : Fin (2 ^ n * p.packingFactor)) => x.val) heq
              simpa using hij (Fin.ext h))
      · simp only [get, hj, ↓reduceDIte]
    · rename_i hi
      by_cases hj : j.val < 2 ^ n * p.packingFactor
      · simp only [get, hj, ↓reduceDIte]
      · simp only [get, hj, ↓reduceDIte]
        exact get_set_other right _ _ v
          (by intro heq
              have h := congrArg (fun (x : Fin (2 ^ n * p.packingFactor)) => x.val) heq
              simp at h; exact hij (Fin.ext (by omega)))
  | _ + 1, .zero, _, _, _, _ => rfl

-- ============================================================

theorem get_set_same [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    t.WellFormed → i.val < t.length → (t.set i v).get i = some v
  | 0, .packedLeaf _ values hk, i, v, _, h_lt => by
    simp only [length] at h_lt
    simp only [set]; split
    · simp only [get]; split
      · congr 1; simp
      · rename_i h; exact absurd h_lt h
    · rename_i h; exact absurd h_lt h
  | 0, .zero, _, _, _, h_lt => by simp [length] at h_lt
  | n + 1, .node _ left right, i, v, hwf, h_lt => by
    obtain ⟨hwf_l, hwf_r, hprefix⟩ := hwf
    simp only [length] at h_lt
    simp only [set]; split
    · rename_i h
      simp only [get, h, ↓reduceDIte]
      have h_lt_left : i.val < left.length := by
        by_cases hr : right.length > 0
        · have := hprefix hr; omega
        · omega
      exact get_set_same left ⟨i.val, h⟩ v hwf_l h_lt_left
    · rename_i h
      simp only [get]; split
      · rename_i h'; exact absurd h' (by omega)
      · have h_lt_right : i.val - 2 ^ n * p.packingFactor < right.length := by
          have : right.length > 0 := by have := length_le_capacity left; omega
          have := hprefix this; omega
        exact get_set_same right _ v hwf_r h_lt_right
  | _ + 1, .zero, _, _, _, h_lt => by simp [length] at h_lt

-- ============================================================

theorem set_wellFormed [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    t.WellFormed → (t.set i v).WellFormed
  | 0, .packedLeaf _ _ _, _, _, _ => by simp only [set]; split <;> trivial
  | 0, .zero, _, _, _ => by simp [set, WellFormed]
  | n + 1, .node _ left right, i, v, hwf => by
    obtain ⟨hwf_l, hwf_r, hprefix⟩ := hwf
    simp only [set]; split
    · exact ⟨set_wellFormed left _ v hwf_l, hwf_r, by
        intro hr; rw [set_length]; exact hprefix hr⟩
    · refine ⟨hwf_l, set_wellFormed right _ v hwf_r, fun hr => ?_⟩
      apply hprefix; rwa [set_length] at hr
  | _ + 1, .zero, _, _, _ => by simp [set, WellFormed]

-- ============================================================

theorem push_length [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (v : α),
    t.length < 2 ^ n * p.packingFactor →
    (t.push v).length = t.length + 1
  | 0, .packedLeaf _ values hk, v, h_cap => by
    have h_room := packed_lt_pf h_cap
    simp only [push, h_room, ↓reduceDIte, length, Vector.size]
  | 0, .zero, _, _ => by simp [push, length, Vector.size]
  | n + 1, .node _ left right, v, h_cap => by
    simp only [length] at h_cap; simp only [push]; split
    · rename_i h_left; simp only [length]
      rw [push_length left v h_left]; omega
    · rename_i h_left; simp only [length]
      have h_left_full : left.length = 2 ^ n * p.packingFactor := by
        have := length_le_capacity left; omega
      have h_right_cap : right.length < 2 ^ n * p.packingFactor := by
        have := pow_succ_mul n p.packingFactor; omega
      rw [push_length right v h_right_cap]; omega
  | n + 1, .zero, _, _ => by
    simp only [push, length]
    rw [push_length (.zero : Tree α n) _ (by rw [length_zero]; exact capacity_pos n)]
    rw [length_zero]

-- ============================================================

theorem push_wellFormed [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (v : α),
    t.WellFormed → t.length < 2 ^ n * p.packingFactor →
    (t.push v).WellFormed
  | 0, .packedLeaf _ _ _, _, _, _ => by simp only [push]; split <;> trivial
  | 0, .zero, _, _, _ => trivial
  | n + 1, .node _ left right, v, hwf, h_cap => by
    obtain ⟨hwf_l, hwf_r, hprefix⟩ := hwf
    simp only [length] at h_cap; simp only [push]; split
    · rename_i h_left
      exact ⟨push_wellFormed left v hwf_l h_left, hwf_r, by
        intro hr; rw [push_length left v h_left]; have := hprefix hr; omega⟩
    · rename_i h_left
      have h_left_full : left.length = 2 ^ n * p.packingFactor := by
        have := length_le_capacity left; omega
      have h_right_cap : right.length < 2 ^ n * p.packingFactor := by
        have := pow_succ_mul n p.packingFactor; omega
      exact ⟨hwf_l, push_wellFormed right v hwf_r h_right_cap, fun _ => h_left_full⟩
  | n + 1, .zero, _, _, _ => by
    simp only [push, WellFormed, length_zero]
    exact ⟨push_wellFormed .zero _ trivial (by rw [length_zero]; exact capacity_pos n),
           trivial, fun h => by simp at h⟩

-- ============================================================

theorem get_push_last [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (v : α)
    (h_cap : t.length < 2 ^ n * p.packingFactor),
    t.WellFormed →
    (t.push v).get ⟨t.length, by have := length_le_capacity t; omega⟩ = some v
  | 0, .packedLeaf _ values hk, v, h_cap, _ => by
    have h_room := packed_lt_pf h_cap
    simp only [push, h_room, ↓reduceDIte, get, length]
    have h1 : values.size < (values.push v).size := by dsimp [Vector.size]; omega
    simp only [h1, ↓reduceDIte]
    congr 1
    rw [Vector.getElem_push]
    simp only [show ¬(values.size < values.size) from Nat.lt_irrefl _, ↓reduceDIte]
  | 0, .zero, v, _, _ => by simp [push, get, Vector.size]
  | n + 1, .node _ left right, v, h_cap, hwf => by
    obtain ⟨hwf_l, hwf_r, hprefix⟩ := hwf
    simp only [length] at h_cap ⊢; simp only [push]; split
    · rename_i h_left
      simp only [get]
      by_cases h_idx : left.length + right.length < 2 ^ n * p.packingFactor
      · -- index goes left, push goes left
        simp only [h_idx, ↓reduceDIte]
        have h_right_zero : right.length = 0 := by
          by_cases hr : right.length > 0
          · have := hprefix hr; omega
          · omega
        -- Rewrite ⟨left.length + right.length, _⟩ to ⟨left.length, _⟩
        have : (left.push v).get ⟨left.length + right.length, h_idx⟩ =
               (left.push v).get ⟨left.length, by omega⟩ := by
          congr 1; ext; simp; omega
        rw [this]
        exact get_push_last left v h_left hwf_l
      · -- index goes right but push goes left → impossible
        have : right.length > 0 := by
          have := length_le_capacity left; omega
        have := hprefix this; omega
    · rename_i h_left
      have h_left_cap := length_le_capacity left
      have h_left_full : left.length = 2 ^ n * p.packingFactor := by omega
      have h_right_cap : right.length < 2 ^ n * p.packingFactor := by
        have := pow_succ_mul n p.packingFactor; omega
      simp only [get]
      by_cases h_idx : left.length + right.length < 2 ^ n * p.packingFactor
      · omega  -- impossible: left full + right anything ≥ cap
      · -- index goes right, push goes right
        simp only [h_idx, ↓reduceDIte]
        -- Rewrite shifted index to right.length
        have : (right.push v).get
                 ⟨left.length + right.length - 2 ^ n * p.packingFactor, by
                    have := pow_succ_mul n p.packingFactor; omega⟩ =
               (right.push v).get ⟨right.length, by omega⟩ := by
          congr 1; ext; simp; omega
        rw [this]
        exact get_push_last right v h_right_cap hwf_r
  | n + 1, .zero, v, _, _ => by
    simp only [push, length]
    simp only [get]
    have h_lt : (0 : Nat) < 2 ^ n * p.packingFactor := capacity_pos n
    simp only [h_lt, ↓reduceDIte]
    -- Rewrite ⟨0, _⟩ to ⟨(.zero : Tree α n).length, _⟩
    have : ((.zero : Tree α n).push v).get ⟨0, h_lt⟩ =
           ((.zero : Tree α n).push v).get
             ⟨(.zero : Tree α n).length, by simp; exact h_lt⟩ := by
      congr 1; ext; simp
    rw [this]
    exact get_push_last (.zero : Tree α n) v (by rw [length_zero]; exact h_lt) trivial

-- ============================================================

theorem get_push_other [p : Packable α] :
    ∀ {n : Nat} (t : Tree α n) (i : Fin (2 ^ n * p.packingFactor)) (v : α),
    t.WellFormed → i.val < t.length →
    (t.push v).get i = t.get i
  | 0, .packedLeaf _ values hk, i, v, _, h_lt => by
    simp only [length] at h_lt; simp only [push]; split
    · simp only [get]
      have h1 : i.val < (values.push v).size := by dsimp [Vector.size] at h_lt ⊢; omega
      simp only [h1, ↓reduceDIte, h_lt, ↓reduceDIte]
      congr 1; rw [Vector.getElem_push]; simp only [h_lt, ↓reduceDIte]
    · rfl
  | 0, .zero, _, _, _, h_lt => by simp [length] at h_lt
  | n + 1, .node _ left right, i, v, hwf, h_lt => by
    obtain ⟨hwf_l, hwf_r, hprefix⟩ := hwf
    simp only [length] at h_lt; simp only [push]; split
    · rename_i h_left
      simp only [get]; split
      · rename_i hi
        have : i.val < left.length := by
          by_cases hr : right.length > 0
          · have := hprefix hr; omega
          · omega
        exact get_push_other left ⟨i.val, hi⟩ v hwf_l this
      · rfl  -- i right, push left → unchanged
    · rename_i h_left
      simp only [get]; split
      · rfl  -- i left, push right → unchanged
      · rename_i hi
        have h_left_full : left.length = 2 ^ n * p.packingFactor := by
          have := length_le_capacity left; omega
        have h_lt_right : i.val - 2 ^ n * p.packingFactor < right.length := by
          have : right.length > 0 := by omega
          have := hprefix this; omega
        exact get_push_other right _ v hwf_r h_lt_right
  | _ + 1, .zero, _, _, _, h_lt => by simp [length] at h_lt

end Tree
