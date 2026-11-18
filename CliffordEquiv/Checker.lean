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
    unfold check at h
    rw [List.all_eq_true] at h
    have hi : ∀ i, run c₁ (SPauli.X i) = run c₂ (SPauli.X i)
              ∧ run c₁ (SPauli.Z i) = run c₂ (SPauli.Z i) := by
      intro i
      have hb := h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb
    apply run_eq_of_basis
    · intro i
      exact (hi i).1
    · intro i
      exact (hi i).2

theorem check_complete (c₁ c₂ : Circuit n) (h : ∀ p, run c₁ p = run c₂ p) :
    check c₁ c₂ = true := by
    unfold check
    rw [List.all_eq_true]
    intro i _
    rw [h (SPauli.X i), h (SPauli.Z i)] -- Also can be achieved with: simp [h]
    simp

theorem check_iff (c₁ c₂ : Circuit n) :
    check c₁ c₂ = true ↔ ∀ p, run c₁ p = run c₂ p :=
  ⟨check_sound c₁ c₂, check_complete c₁ c₂⟩

end CliffordEquiv
