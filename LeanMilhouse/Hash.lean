/-
  Hash opaque type, MerkleHash typeclass, and CollisionResistant extension.
-/

/-- Abstract hash type. We use `axiom` so that proofs cannot depend on
    any concrete hash representation. -/
axiom Hash : Type

/-- `Hash` is inhabited (needed for `Thunk Hash`, default values, etc.). -/
axiom Hash.inhabited : Inhabited Hash
noncomputable instance : Inhabited Hash := Hash.inhabited

/-- Typeclass providing the merkle hashing operations for a value type `α`. -/
class MerkleHash (α : Type) where
  /-- Hash a single leaf value. -/
  hashLeaf : α → Hash
  /-- Hash a packed vector of values. -/
  hashPacked : {k : Nat} → Vector α k → Hash
  /-- Combine two child hashes into a parent hash. -/
  hashCombine : Hash → Hash → Hash
  /-- The canonical hash for an empty (zero) subtree at a given depth. -/
  zeroHash : (depth : Nat) → Hash

/-- Extension of `MerkleHash` that axiomatizes collision resistance.
    This is the standard cryptographic assumption needed for merkle tree
    correctness proofs. -/
class CollisionResistant (α : Type) extends MerkleHash α where
  combine_injective : ∀ {a b c d : Hash},
    hashCombine a b = hashCombine c d → a = c ∧ b = d
  leaf_injective : ∀ {a b : α},
    hashLeaf a = hashLeaf b → a = b
