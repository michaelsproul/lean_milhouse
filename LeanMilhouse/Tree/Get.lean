/-
  Tree.get: index-based access with packing support.
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

/-- Get the value at index `i` in the tree.

    The index space is `Fin (2^n * packingFactor)` where `n` is the tree depth
    and `packingFactor` determines how many values are packed into each leaf.
    The upper `n` bits of the index navigate the binary tree; the lower
    `packingDepth` bits select within a packed leaf.

    `zero` nodes return the `default` (inhabited) value.
    A `leaf` (single value, depth 0) returns its value regardless of the
    packing index — this is a degenerate case that shouldn't occur in
    well-formed trees with `packingFactor > 1`.
    Corresponds to `get_recursive` in Rust milhouse. -/
def get [Inhabited α] [p : Packable α] : {n : Nat} → Tree α n → Fin (2 ^ n * p.packingFactor) → α
  | 0, .leaf _ v, _ => v
  | 0, .packedLeaf _ values, i =>
    if h : i.val < values.size then values[i.val] else default
  | 0, .zero, _ => default
  | n + 1, .node _ left right, i =>
    if h : i.val < 2 ^ n * p.packingFactor then
      get left ⟨i.val, h⟩
    else
      get right ⟨i.val - 2 ^ n * p.packingFactor, by
        have := pow_succ_mul n p.packingFactor
        have := i.isLt
        omega⟩
  | _ + 1, .zero, _ => default

end Tree
