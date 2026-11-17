import CliffordEquiv.Circuit

/-!
# Theorem (a): gates preserve the symplectic form

Plan §6.3: `H` and `S` are per-coordinate identities lifted with `Finset.sum_congr`;
`CNOT` needs the `a` and `b` terms split out of the sum (`Finset.add_sum_erase`, using `a ≠ b`).
-/

namespace CliffordEquiv

variable {n : ℕ}

theorem act_H_preserves_omega (a : Fin n) (p q : SPauli n) :
    omega (act (.H a) p) (act (.H a) q) = omega p q := by
    unfold omega
    apply Finset.sum_congr rfl
    intro i _
    simp only [act]
    split_ifs with h
    · ring
    · rfl

theorem act_S_preserves_omega (a : Fin n) (p q : SPauli n) :
    omega (act (.S a) p) (act (.S a) q) = omega p q := by
    unfold omega
    apply Finset.sum_congr rfl
    intro i _
    simp only [act]
    split_ifs with h
    · generalize p.x i = px, p.z i = pz, q.x i = qx, q.z i = qz
      revert px pz qx qz
      decide
    · rfl

theorem act_CNOT_preserves_omega (a b : Fin n) (hab : a ≠ b) (p q : SPauli n) :
    omega (act (.CNOT a b) p) (act (.CNOT a b) q) = omega p q := by
  sorry

/-- Every well-formed gate preserves the symplectic form (commutation relations). -/
theorem act_preserves_omega (g : CGate n) (hg : g.WellFormed) (p q : SPauli n) :
    omega (act g p) (act g q) = omega p q := by
  sorry

/-- Every well-formed circuit preserves the symplectic form. -/
theorem run_preserves_omega (c : Circuit n) (hc : c.WellFormed) (p q : SPauli n) :
    omega (run c p) (run c q) = omega p q := by
  sorry

end CliffordEquiv
