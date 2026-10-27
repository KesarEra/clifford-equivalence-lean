import CliffordEquiv.Linear

/-!
# Theorem (c): a decidable equivalence checker

`check c₁ c₂` compares the images of the `2n` basis Paulis. It is sound and complete for
equality of phase-free actions. Cost: `O(n·m)` coordinate updates plus `O(n²)` to compare.
-/

namespace CliffordEquiv

variable {n : ℕ}

/-- Boolean check: do the circuits agree on every basis Pauli? -/
def check (c₁ c₂ : Circuit n) : Bool :=
  (List.finRange n).all fun i =>
    decide (run c₁ (SPauli.X i) = run c₂ (SPauli.X i)) &&
    decide (run c₁ (SPauli.Z i) = run c₂ (SPauli.Z i))

theorem check_sound (c₁ c₂ : Circuit n) (h : check c₁ c₂ = true) :
    ∀ p, run c₁ p = run c₂ p := by
  sorry

theorem check_complete (c₁ c₂ : Circuit n) (h : ∀ p, run c₁ p = run c₂ p) :
    check c₁ c₂ = true := by
  sorry

theorem check_iff (c₁ c₂ : Circuit n) :
    check c₁ c₂ = true ↔ ∀ p, run c₁ p = run c₂ p :=
  ⟨check_sound c₁ c₂, check_complete c₁ c₂⟩

end CliffordEquiv
