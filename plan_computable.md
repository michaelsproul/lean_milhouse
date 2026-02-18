# Plan: Make LeanMilhouse Fully Computable

## Problem

`Tree.set` (and all future operations) are `noncomputable` because `Hash` is an
`axiom`. Lean's code generator cannot produce executable code for anything that
depends on an axiom-introduced type. The dependency chain is:

    axiom Hash → axiom Hash.inhabited → noncomputable Inhabited Hash
      → noncomputable default : Hash → noncomputable invalidHash
        → noncomputable Tree.set

## Key Insight

The axiom-based `Hash` was chosen so proofs wouldn't depend on a specific hash
algorithm. But we can achieve the **same proof abstraction** without axioms:

- Make `Hash` a **concrete structure** (computable).
- Keep `MerkleHash` as a **typeclass** providing the hash operations.
- Proofs that quantify over `[MerkleHash α]` are already generic — they work
  for *any* instance, regardless of `Hash`'s concrete representation.
- `CollisionResistant` stays as a typeclass extension — proofs assume it as a
  constraint, never need to inspect `Hash` internals.

The proofs never touch `Hash`'s fields directly. They go through the `MerkleHash`
interface. So making `Hash` concrete costs us nothing in proof generality.

## Change: Replace `axiom Hash` with `structure Hash`

Replace the two axioms and noncomputable instance in `Hash.lean`:

```lean
-- BEFORE (noncomputable)
axiom Hash : Type
axiom Hash.inhabited : Inhabited Hash
noncomputable instance : Inhabited Hash := Hash.inhabited
```

With a concrete 256-bit hash (four 64-bit words, matching SHA256/Keccak output):

```lean
-- AFTER (computable)
structure Hash where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Inhabited, BEq, DecidableEq, Repr
```

This gives us:
- `Inhabited Hash` — derived, computable (default is all zeros)
- `BEq Hash` — derived, computable
- `DecidableEq Hash` — derived, computable
- `Repr Hash` — derived, for debugging/display

### Why 4×UInt64?

- Exactly 256 bits = 32 bytes, matching real Ethereum hash sizes.
- Fixed-size, no length proofs needed (unlike `ByteArray`).
- All field types are `Inhabited`, `BEq`, `DecidableEq` — so derivation works.
- Efficient: UInt64 operations are native.

The specific representation doesn't matter for proofs — they go through
`MerkleHash.hashCombine` etc., never through `Hash.w0`.

## Downstream effects

### Tree/Set.lean

Remove all `noncomputable` annotations:

```lean
-- BEFORE
private noncomputable def invalidHash : Thunk Hash := ...
noncomputable def set : ...

-- AFTER
private def invalidHash : Thunk Hash := ...
def set : ...
```

No logic changes needed. `default : Hash` now computes to
`⟨0, 0, 0, 0⟩` instead of being stuck on an axiom.

### MerkleHash / CollisionResistant (no changes)

These are typeclasses — they already work with any concrete `Hash`. The class
fields (`hashLeaf`, `hashCombine`, etc.) are abstract operations provided by
instances. Making `Hash` concrete doesn't affect them.

### Tree.lean (no changes)

The `Tree` inductive uses `Thunk Hash` in constructors. `Thunk Hash` is
computable as long as `Hash` is — which it now is.

### Packable.lean (no changes)

No dependency on `Hash`.

## Files to modify

1. **`LeanMilhouse/Hash.lean`** — Replace axioms with structure, remove
   noncomputable instance. ~10 lines changed.
2. **`LeanMilhouse/Tree/Set.lean`** — Remove `noncomputable` from
   `invalidHash` and `set`. 2 keywords removed.

## What this preserves

- All `MerkleHash` / `CollisionResistant` typeclass proofs remain valid.
- `get_set_same` / `get_set_other` theorem statements are unchanged.
- The `Tree` type definition is unchanged.
- Future `treeHash` function will also be computable (it uses `MerkleHash`
  methods, which are computable when a concrete instance is provided).

## What this enables

- `#eval` on tree operations (build trees, set values, inspect results).
- Compiled executable that actually runs tree operations.
- Test harnesses that exercise the code at runtime.
- A concrete `MerkleHash` instance (e.g., wrapping a SHA256 FFI) can be
  plugged in and executed.
