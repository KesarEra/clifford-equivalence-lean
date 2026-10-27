import Mathlib

/-!
# Phase-free Paulis in symplectic form

An `n`-qubit Pauli, ignoring its sign/phase, is a pair of bit vectors `(x, z) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`.
Qubit `i` carries `I, X, Z, Y` according to `(x i, z i) = (0,0), (1,0), (0,1), (1,1)`.

Two Paulis commute iff their symplectic form `omega` is `0`.
-/

open BigOperators

namespace CliffordEquiv

/-- Phase-free Pauli on `n` qubits in symplectic form. -/
@[ext]
structure SPauli (n : ℕ) where
  x : Fin n → ZMod 2
  z : Fin n → ZMod 2

namespace SPauli

variable {n : ℕ}

instance : DecidableEq (SPauli n) := fun p q =>
  decidable_of_iff (p.x = q.x ∧ p.z = q.z) (by
    constructor
    · rintro ⟨hx, hz⟩; exact SPauli.ext hx hz
    · rintro rfl; exact ⟨rfl, rfl⟩)

/-- Pointwise addition (multiplication of Paulis up to phase). -/
instance : Add (SPauli n) := ⟨fun p q => ⟨p.x + q.x, p.z + q.z⟩⟩

/-- The identity Pauli. -/
instance : Zero (SPauli n) := ⟨⟨0, 0⟩⟩

@[simp] lemma add_x (p q : SPauli n) : (p + q).x = p.x + q.x := rfl
@[simp] lemma add_z (p q : SPauli n) : (p + q).z = p.z + q.z := rfl
@[simp] lemma zero_x : (0 : SPauli n).x = 0 := rfl
@[simp] lemma zero_z : (0 : SPauli n).z = 0 := rfl

-- TODO (week 3): it may be convenient to upgrade this to `AddCommGroup` and
-- `Module (ZMod 2)` so that `Finset.sum` works for the basis decomposition.

/-- Single-qubit label of qubit `i`: one of `I`, `X`, `Z`, `Y`. -/
def label (p : SPauli n) (i : Fin n) : Char :=
  match decide (p.x i = 1), decide (p.z i = 1) with
  | false, false => 'I'
  | true,  false => 'X'
  | false, true  => 'Z'
  | true,  true  => 'Y'

/-- Prints e.g. `XIZY`, qubit 0 first. -/
instance : Repr (SPauli n) :=
  ⟨fun p _ => String.ofList ((List.finRange n).map p.label)⟩

/-- Basis Pauli `X` on qubit `i`. -/
def X (i : Fin n) : SPauli n := ⟨Pi.single i 1, 0⟩

/-- Basis Pauli `Z` on qubit `i`. -/
def Z (i : Fin n) : SPauli n := ⟨0, Pi.single i 1⟩

end SPauli

/-- Symplectic form: `∑ᵢ (xᵢ z'ᵢ + zᵢ x'ᵢ)`. It is `0` iff the Paulis commute. -/
def omega {n : ℕ} (p q : SPauli n) : ZMod 2 :=
  ∑ i, (p.x i * q.z i + p.z i * q.x i)

end CliffordEquiv
