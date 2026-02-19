/-
  Tree.get: index-based access with packing support.
  Returns `Option α`: `some v` for occupied positions, `none` for unoccupied.
  Corresponds to `get_recursive` in Rust milhouse.
-/
import LeanMilhouse.Tree
import LeanMilhouse.Packable

namespace Tree

private theorem pow_succ_mul (n pf : Nat) :
    2 ^ (n + 1) * pf = 2 ^ n * pf + 2 ^ n * pf := by
  have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [Nat.pow_succ]; omega
  rw [this, Nat.add_mul]

/-- Get the value at index `i` in the tree, returning `Option α`.

    The index space is `Fin (2^n * packingFactor)` where `n` is the tree depth
    and `packingFactor` determines the maximum number of values packed into each
    leaf. The upper `n` bits of the index navigate the binary tree; the lower
    bits select within a packed leaf.

    Returns `none` for `zero` nodes and for out-of-bounds positions within a
    variable-length packed leaf. -/
def get [p : Packable α] : {n : Nat} → Tree α n → Fin (2 ^ n * p.packingFactor) → Option α
  | 0, .packedLeaf _ values _, i =>
    if h : i.val < values.size then some values[i.val] else none
  | 0, .zero, _ => none
  | n + 1, .node _ left right, i =>
    if h : i.val < 2 ^ n * p.packingFactor then
      get left ⟨i.val, h⟩
    else
      get right ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor
        have := i.isLt
        omega⟩
  | _ + 1, .zero, _ => none

end Tree
