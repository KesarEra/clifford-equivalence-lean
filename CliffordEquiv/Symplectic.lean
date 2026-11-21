import CliffordEquiv.Circuit

/-!
# Theorem (a): gates preserve the symplectic form

`H` and `S` leave every term of the sum unchanged, so they reduce to one qubit with
`Finset.sum_congr`. `CNOT` changes the terms at qubits `a` and `b`, each by the same amount `K`;
summing gives `omega p q + K + K`, which equals `omega p q` in `ZMod 2` (this needs `a ≠ b`).
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
    unfold omega
    have key : ∀ i,
        (act (CGate.CNOT a b) p).x i * (act (CGate.CNOT a b) q).z i
          + (act (CGate.CNOT a b) p).z i * (act (CGate.CNOT a b) q).x i
        = (p.x i * q.z i + p.z i * q.x i)                           -- old term
          + (if i = a then p.x a * q.z b + p.z b * q.x a else 0)    -- + K at qubit a
          + (if i = b then p.x a * q.z b + p.z b * q.x a else 0)    -- + K at qubit b
          := by
          intro i
          simp only [act]
          split_ifs with hb ha ha
          · exfalso
            apply hab
            rw [← ha]
            exact hb
          · rw [hb]
            ring
          · rw [ha]
            ring
          · ring
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    generalize ∑ x, (p.x x * q.z x + p.z x * q.x x) = s
    generalize (p.x a * q.z b + p.z b * q.x a) = k
    revert s k
    decide

/-- Every well-formed gate preserves the symplectic form (commutation relations). -/
theorem act_preserves_omega (g : CGate n) (hg : g.WellFormed) (p q : SPauli n) :
    omega (act g p) (act g q) = omega p q := by
    cases g with
    | H a => exact act_H_preserves_omega a p q
    | S a => exact act_S_preserves_omega a p q
    | CNOT a b => exact act_CNOT_preserves_omega a b hg p q

/-- Every well-formed circuit preserves the symplectic form. -/
theorem run_preserves_omega (c : Circuit n) (hc : c.WellFormed) (p q : SPauli n) :
    omega (run c p) (run c q) = omega p q := by
    induction c generalizing p q with
    | nil => rfl
    | cons g gs ih =>
      simp only [run_cons]
      rw [ih]
      · exact act_preserves_omega g (hc g (by simp)) p q
      · intro g' hg'
        exact hc g' (by simp [hg'])

end CliffordEquiv
