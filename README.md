# Verified Clifford Equivalence in Lean 4

A Lean 4 + Mathlib formalisation of a decision procedure for Clifford circuit equivalence
in the phase-free symplectic setting. Clifford circuits over `{H, S, CNOT}` act on
phase-free Paulis `(x, z) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`; the action is 𝔽₂-linear, so two circuits act the
same on all 4ⁿ Paulis iff they agree on the `2n` basis Paulis `X i`, `Z i`. A Boolean
checker based on this is proved sound and complete.

**Status:** All main theorems are proved, with no `sorry`. They depend only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main theorems

| | Theorem | Statement | File |
|---|---|---|---|
| (a) | `act_preserves_omega`, `run_preserves_omega` | Every well-formed gate and circuit preserves the symplectic form, i.e. commutation relations | [Symplectic.lean](CliffordEquiv/Symplectic.lean) |
| (b) | `act_add`, `run_add` | The action of every gate and circuit is additive (𝔽₂-linear) | [Linear.lean](CliffordEquiv/Linear.lean) |
| (b) | `run_eq_of_basis` | Circuits that agree on every basis Pauli agree on every Pauli | [Linear.lean](CliffordEquiv/Linear.lean) |
| (c) | `check_sound`, `check_complete`, `check_iff` | `check c₁ c₂ = true` ↔ `∀ p, run c₁ p = run c₂ p` | [Checker.lean](CliffordEquiv/Checker.lean) |

## Example

Soundness turns a run of the checker into a theorem about every Pauli
([Examples.lean](CliffordEquiv/Examples.lean)):

```lean
/-- SWAP built two ways. -/
example : ∀ p : SPauli 2,
    run [CNOT 0 1, CNOT 1 0, CNOT 0 1] p = run [CNOT 1 0, CNOT 0 1, CNOT 1 0] p :=
  check_sound _ _ (by decide)
```

Also verified: `H H = I`, `CNOT CNOT = I`, and conjugating by `H ⊗ H` reverses a CNOT.

## Scope

- **Phase-free only.** Equal action means equal up to a Pauli correction and global phase,
  not up to global phase alone. For example, `S S = Z` acts trivially here, and the checker
  accepts it against the empty circuit.
- **Model, not matrices.** The gate update rules (`act`) are definitions, matching
  conjugation by the H, S and CNOT matrices on paper; that correspondence is not proved in Lean.
- **Well-formedness.** Theorem (a) needs `CNOT a b` to have `a ≠ b`; linearity and the
  checker's correctness hold for all circuits.

## Layout

```
CliffordEquiv/
  Pauli.lean       SPauli, addition, basis X i / Z i, symplectic form omega
  Gate.lean        CGate {H, S, CNOT}, WellFormed, act
  Circuit.lean     Circuit, run
  Symplectic.lean  theorem (a)
  Linear.lean      theorem (b) and the basis argument
  Checker.lean     theorem (c): check, soundness, completeness
  Examples.lean    demo identities and #eval sanity checks
WORKLOG.md         summary table, then a detailed section per entry
```

## Build

Requires [elan](https://github.com/leanprover/elan). The Lean toolchain is pinned in
`lean-toolchain` (`v4.36.0-rc1`), Mathlib is pinned to tag `v4.36.0-rc1` in `lakefile.toml`,
and `lake-manifest.json` records the exact revisions.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check that a theorem has no unfinished proofs, add this to a file that imports
`CliffordEquiv`. The output should not include `sorryAx`.

```lean
#print axioms CliffordEquiv.check_iff
```
