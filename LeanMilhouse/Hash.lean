/-
  Hash opaque type, MerkleHash typeclass, and CollisionResistant extension.
-/

/-- A 256-bit hash, represented as four 64-bit words.
    The concrete representation makes all tree operations computable.
    Proofs stay abstract by going through the `MerkleHash` typeclass interface,
    never inspecting these fields directly. -/
structure Hash where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Inhabited, BEq, DecidableEq, Repr

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
