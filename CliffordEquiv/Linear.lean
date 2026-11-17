import CliffordEquiv.Circuit

/-!
# Theorem (b): the action is additive (𝔽₂-linear)

So a circuit's action is determined by its images of the `2n` basis Paulis `X i`, `Z i`.
Note additivity does not need well-formedness.
-/

namespace CliffordEquiv

variable {n : ℕ}

theorem act_add (g : CGate n) (p q : SPauli n) :
    act g (p + q) = act g p + act g q := by
    cases g with
    | H a =>
      ext i
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
        split_ifs
        · rfl
        · rfl
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
        split_ifs
        · rfl
        · rfl
    | S a =>
      ext i
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
        split_ifs
        · ring
        · rfl
    | CNOT a b =>
      ext i
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
        split_ifs
        · ring
        rfl
      · simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]
        split_ifs
        · ring
        · rfl

theorem run_add (c : Circuit n) (p q : SPauli n) :
    run c (p + q) = run c p + run c q := by
    induction c generalizing p q with
    | nil => rfl
    | cons g gs ih =>
      simp only [run_cons]
      rw [act_add]
      rw [ih]

/-- If two circuits agree on every basis Pauli, they agree on every Pauli. -/
theorem run_eq_of_basis (c₁ c₂ : Circuit n)
    (hX : ∀ i, run c₁ (SPauli.X i) = run c₂ (SPauli.X i))
    (hZ : ∀ i, run c₁ (SPauli.Z i) = run c₂ (SPauli.Z i)) :
    ∀ p, run c₁ p = run c₂ p := by
  sorry

end CliffordEquiv
