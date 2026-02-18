/-
  Packable typeclass for types that can be packed into merkle tree leaves.
  The packing factor determines how many values fit in a single 32-byte leaf.
-/

/-- Typeclass for types that can be packed into merkle tree leaves.
    `packingFactor` must be a positive power of 2. -/
class Packable (α : Type) where
  packingFactor : Nat
  packingFactor_pos : packingFactor > 0
  packingFactor_pow2 : ∃ k, packingFactor = 2 ^ k

/-- The packing depth is log2 of the packing factor. This determines how many
    levels of the tree are "absorbed" into a packed leaf. -/
def Packable.packingDepth [p : Packable α] : Nat :=
  Nat.log2 p.packingFactor

/-- UInt64: 4 values × 8 bytes = 32 bytes per leaf. -/
instance : Packable UInt64 where
  packingFactor := 4
  packingFactor_pos := by omega
  packingFactor_pow2 := ⟨2, by omega⟩

/-- UInt32: 8 values × 4 bytes = 32 bytes per leaf. -/
instance : Packable UInt32 where
  packingFactor := 8
  packingFactor_pos := by omega
  packingFactor_pow2 := ⟨3, by omega⟩

/-- Default packing factor of 1 for complex types (no packing). -/
instance : Packable UInt8 where
  packingFactor := 32
  packingFactor_pos := by omega
  packingFactor_pow2 := ⟨5, by omega⟩
