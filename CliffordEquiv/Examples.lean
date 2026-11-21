import CliffordEquiv.Checker

/-!
# Demo identities

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

/-- Limitation of the phase-free setting: `S S = Z` acts trivially here, though it is not the
identity. -/
example : ∀ p : SPauli 1, run [S 0, S 0] p = run [] p :=
  check_sound _ _ (by decide)

#eval act (H 0) (X 0 : SPauli 1)          -- Z
#eval act (S 0) (X 0 : SPauli 1)          -- Y
#eval act (CNOT 0 1) (Z 1 : SPauli 2)     -- ZZ
#eval act (H 1) (X 0 + Z 1 : SPauli 2)    -- XX  (X⊗Z, then H on qubit 1 turns Z into X)

end CliffordEquiv
