# Milhouse → Lean Port: Plan

## Overview

Port the core `Tree<T>` type from [sigp/milhouse](https://github.com/sigp/milhouse) (Rust) into Lean 4,
with a focus on **formal verification** of key properties.

Milhouse is a persistent binary merkle tree library used in Ethereum consensus (Lighthouse client).
The Rust implementation has four tree variants: `Leaf`, `PackedLeaf`, `Node`, and `Zero`, with
`Arc`-based structural sharing, lazy hash caching, and batch update support.

---

## Design Decisions

### 1. Primary Goal: Formal Verification

We prioritize **provability** over performance. The Lean implementation serves as a verified
reference specification. We may diverge from the Rust structure where it aids proof ergonomics.

### 2. Depth-Indexed Dependent Type

The `Tree` type is indexed by its depth as a natural number:

```
Tree α n
```

where `α` is the value type and `n : Nat` is the depth. This gives us:
- **Static guarantee of balanced trees**: A `Node` combines two subtrees of equal depth.
- **Depth consistency enforced by the type checker**: No runtime depth-mismatch bugs.
- **Structural induction on depth** for proofs.

The Rust version passes depth as a runtime parameter. Our approach is strictly stronger.

### 3. Abstract Hash Type with Collision Resistance Axiom

Define an opaque `Hash` type and a `MerkleHash` typeclass:

```lean
opaque Hash : Type

class MerkleHash (α : Type) where
  hashLeaf : α → Hash
  hashPacked : Vector α k → Hash
  hashCombine : Hash → Hash → Hash
  zeroHash : (depth : Nat) → Hash
```

Provide a `CollisionResistant` extension class that axiomatizes injectivity:

```lean
class CollisionResistant extends MerkleHash α where
  combine_injective : hashCombine a b = hashCombine c d → a = c ∧ b = d
  leaf_injective : hashLeaf a = hashLeaf b → a = b
```

This lets proofs assume collision resistance (standard cryptographic assumption) without
committing to a concrete hash algorithm. A real SHA256 instance can be plugged in later.

### 4. Packable Typeclass

Model the packing factor as a typeclass on the value type, mirroring Rust's `TreeHash` trait:

```lean
class Packable (α : Type) where
  packingFactor : Nat
  packingFactor_pos : packingFactor > 0
  packingFactor_pow2 : ∃ k, packingFactor = 2 ^ k
```

Instances:
- `Packable UInt64` with `packingFactor = 4` (4 × 8 bytes = 32 bytes)
- `Packable UInt32` with `packingFactor = 8`
- Default `packingFactor = 1` for complex types (equivalent to plain `Leaf`)

The packing depth is derived: `packingDepth = Nat.log2 packingFactor`.

### 5. Thunk-Based Lazy Hash Caching

Use Lean's `Thunk` type for lazy hash computation:

```lean
inductive Tree (α : Type) : Nat → Type where
  | leaf (hash : Thunk Hash) (value : α) : Tree α 0
  | packedLeaf (hash : Thunk Hash) (values : Vector α k) : Tree α 0
  | node (hash : Thunk Hash) (left right : Tree α n) : Tree α (n + 1)
  | zero : Tree α n
```

- `Thunk Hash` delays hash computation until forced, mirroring the Rust `RwLock<Hash256>`
  pattern without mutable state.
- `zero` carries no hash — its hash is `zeroHash depth`, computed from a lookup table.
- On tree mutation (path-copying), new nodes get fresh thunks that will recompute.

**Note for proofs**: `Thunk` is opaque at the value level but we can reason about the
*computed* hash via a `treeHash` function that ignores cached values and computes structurally.
Proofs will primarily use `treeHash`, not the cached thunks.

### 6. Include PackedLeaf

Include all four variants from the start. `PackedLeaf` stores up to `packingFactor` values
in a single node at depth 0. When `packingFactor = 1`, `packedLeaf` and `leaf` are equivalent
(we may unify them or keep both for clarity).

The packing factor affects index routing: the lowest `packingDepth` bits of an index select
within the packed vector, while higher bits navigate the tree.

### 7. Priority Proofs: Get/Set Roundtrip

The first theorems to prove:

```lean
-- Reading back a written value
theorem get_set_same (t : Tree α n) (i : Fin (2^n)) (v : α) :
    (t.set i v).get i = v

-- Writing doesn't affect other indices
theorem get_set_other (t : Tree α n) (i j : Fin (2^n)) (v : α) (h : i ≠ j) :
    (t.set i v).get j = t.get j
```

These are the fundamental correctness properties of any array-like structure.

---

## Module Structure

```
LeanMilhouse/
  Hash.lean          -- Hash opaque type, MerkleHash class, CollisionResistant class
  Packable.lean      -- Packable typeclass, instances for UInt64, UInt32, etc.
  Tree.lean          -- Tree inductive type definition
  Tree/
    Basic.lean       -- Tree constructors, helpers, smart constructors
    Get.lean         -- get : Tree α n → Fin (2^n) → α
    Set.lean         -- set : Tree α n → Fin (2^n) → α → Tree α n
    Hash.lean        -- treeHash : Tree α n → Hash (the pure, structural hash function)
    Zero.lean        -- Zero hash table, properties of zero trees
    Properties.lean  -- Proofs: get/set roundtrip, hash consistency, structural invariants
```

---

## Tree Type Definition (Detailed)

```lean
inductive Tree (α : Type) [MerkleHash α] : Nat → Type where
  | leaf (hash : Thunk Hash) (value : α) : Tree α 0
  | packedLeaf (hash : Thunk Hash) (values : Vector α k) : Tree α 0
  | node (hash : Thunk Hash) (left : Tree α n) (right : Tree α n) : Tree α (n + 1)
  | zero : Tree α n
```

### Variant Semantics

| Variant      | Depth | Meaning |
|-------------|-------|---------|
| `leaf`       | 0     | Single value at a leaf position |
| `packedLeaf` | 0    | Multiple small values packed into one leaf |
| `node`       | n+1   | Internal node with two children of depth n |
| `zero`       | any n | Empty subtree — represents `2^n` default values |

### Key Operations (Signatures)

```lean
-- Access element at index
def Tree.get [MerkleHash α] [Packable α] : Tree α n → Fin (2^n) → α

-- Update element at index (returns new tree via path-copying)
def Tree.set [MerkleHash α] [Packable α] : Tree α n → Fin (2^n) → α → Tree α n

-- Compute the merkle hash (pure, structural — ignores cached thunks)
def Tree.treeHash [MerkleHash α] : Tree α n → Hash

-- Construct a tree from a list of values
def Tree.ofList [MerkleHash α] [Packable α] [Inhabited α] : List α → (n : Nat) → Tree α n

-- Convert tree to list of all values
def Tree.toList [MerkleHash α] [Packable α] [Inhabited α] : Tree α n → List α
```

---

## Implementation Phases

### Phase 1: Core Types
- [ ] `Hash.lean` — Hash type, MerkleHash class, CollisionResistant
- [ ] `Packable.lean` — Packable class with basic instances
- [ ] `Tree.lean` — The inductive type definition

### Phase 2: Core Operations
- [ ] `Tree/Get.lean` — Index-based access with packing support
- [ ] `Tree/Set.lean` — Functional update via path-copying
- [ ] `Tree/Zero.lean` — Zero tree construction and properties
- [ ] `Tree/Basic.lean` — Helpers, decidable equality, repr

### Phase 3: Hashing
- [ ] `Tree/Hash.lean` — Pure `treeHash` function, hash recomputation on set

### Phase 4: Proofs
- [ ] `Tree/Properties.lean` — get/set roundtrip theorems
- [ ] Additional structural invariant proofs

### Phase 5: Future Work (not in initial scope)
- [ ] `List` / `Vector` wrappers with length tracking
- [ ] `Interface` layer with buffered updates
- [ ] `rebase` / `intra_rebase` for structural deduplication
- [ ] Builder (bottom-up O(n) construction)
- [ ] Concrete SHA256 `MerkleHash` instance

---

## Open Questions / Risks

1. **Thunk in proofs**: Lean's `Thunk` is implemented via `Unit → α` under the hood.
   We need to verify we can reason past it for proof purposes, or we may need a custom
   lazy wrapper with an extraction axiom.

2. **PackedLeaf index arithmetic**: Routing indices through packed leaves requires
   dividing the index space. With dependent types this interacts with `Fin` arithmetic.
   May require careful lemma development.

3. **Universe polymorphism**: `Hash` being opaque means we need to decide its universe.
   Keeping everything in `Type` (Type 0) should suffice for now.

4. **Default values for `zero`**: `Zero` represents empty subtrees. `get` on a `zero` node
   needs to return a default value. Options:
   - Require `Inhabited α` (simple, standard)
   - Require `Default α` (custom class with a specific "zero value")
   - Return `Option α` (changes the API)

   **Decision**: Use `Inhabited α` for simplicity. The default value represents the
   "empty" or "uninitialized" state, matching Ethereum's zero-initialization semantics.

5. **Packing factor as type parameter vs runtime value**: The current design uses a
   typeclass, meaning `packingFactor` is determined by the type `α`. If we ever need
   different packing for the same type in different contexts, we'd need to refactor.
   This matches Rust's design and should be fine.

---

## Comparison with Rust Milhouse

| Aspect | Rust (milhouse) | Lean (this port) |
|--------|----------------|------------------|
| Depth tracking | Runtime parameter | Type-level index |
| Structural sharing | `Arc<Tree>` | Lean runtime sharing (automatic) |
| Hash caching | `RwLock<Hash256>` (interior mutability) | `Thunk Hash` (lazy evaluation) |
| Mutation model | Path-copying + `Arc` | Pure functional (path-copying implicit) |
| Parallelism | Rayon for hash computation | Not applicable (pure/sequential) |
| Packing | `TreeHash` trait | `Packable` typeclass |
| Batch updates | `UpdateMap` + selective recursion | Not in initial scope |
| Verification | None (tested) | Formal proofs in Lean |
