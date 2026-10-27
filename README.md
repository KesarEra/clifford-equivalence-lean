# Verified Clifford Equivalence in Lean 4

A Lean 4 + Mathlib formalisation of a decision procedure for Clifford circuit equivalence
in the phase-free symplectic setting: Clifford circuits over `{H, S, CNOT}` act on
phase-free Paulis `(x, z) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`, and two circuits have the same action iff they
agree on the `2n` basis Paulis.

**Status:** week 1 — definitions and theorem statements compile; proofs are `sorry`.

## Main theorems

| Theorem | File | Status |
|---|---|---|
| (a) `act_preserves_omega`: well-formed gates preserve the symplectic form | [Symplectic.lean](CliffordEquiv/Symplectic.lean) | `sorry` |
| (b) `run_add`: the circuit action is additive (𝔽₂-linear) | [Linear.lean](CliffordEquiv/Linear.lean) | `sorry` |
| (c) `check_iff`: the basis checker is sound and complete | [Checker.lean](CliffordEquiv/Checker.lean) | `sorry` |

Demo identities (`HH = I`, `CNOT·CNOT = I`, SWAP two ways, `H`-conjugation reverses CNOT)
are in [Examples.lean](CliffordEquiv/Examples.lean).

**Scope:** only the phase-free action is verified. Equal actions means equal up to a Pauli
correction and global phase, *not* up to global phase alone (e.g. `S S = Z` acts trivially).

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
`lean-toolchain` (`v4.36.0-rc1`) and Mathlib is pinned to tag `v4.36.0-rc1` in `lakefile.toml`.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check a theorem's axioms (should not include `sorryAx` once proved):

```lean
#print axioms CliffordEquiv.check_iff
```
