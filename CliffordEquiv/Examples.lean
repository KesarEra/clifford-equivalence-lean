import CliffordEquiv.Checker

/-!
# Demo identities (plan §6.2)

Each is proved by running the checker (`decide`) and applying `check_sound`.
-/

namespace CliffordEquiv

open CGate SPauli

-- Sanity checks: H swaps X and Z; CNOT 0 1 maps X⊗I to X⊗X.
#eval run [H 0] (X 0 : SPauli 1)
#eval run [CNOT 0 1] (X 0 : SPauli 2)

/-- `H H = id`. -/
example : ∀ p : SPauli 1, run [H 0, H 0] p = run [] p :=
  check_sound _ _ (by decide)

/-- `CNOT CNOT = id`. -/
example : ∀ p : SPauli 2, run [CNOT 0 1, CNOT 0 1] p = run [] p :=
  check_sound _ _ (by decide)

/-- SWAP built two ways. -/
example : ∀ p : SPauli 2,
    run [CNOT 0 1, CNOT 1 0, CNOT 0 1] p = run [CNOT 1 0, CNOT 0 1, CNOT 1 0] p :=
  check_sound _ _ (by decide)

/-- Conjugating by `H ⊗ H` reverses a CNOT. -/
example : ∀ p : SPauli 2,
    run [H 0, H 1, CNOT 0 1, H 0, H 1] p = run [CNOT 1 0] p :=
  check_sound _ _ (by decide)

/-- Limitation (plan §6.1): `S S = Z` acts trivially here, though it is not the identity. -/
example : ∀ p : SPauli 1, run [S 0, S 0] p = run [] p :=
  check_sound _ _ (by decide)

end CliffordEquiv
