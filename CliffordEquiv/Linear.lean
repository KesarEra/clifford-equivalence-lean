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

lemma act_zero (g : CGate n) : act g 0 = 0 := by
    cases g <;> ext i <;> simp [act]

lemma run_zero (c : Circuit n) : run c 0 = 0 := by
    induction c with
    | nil => rfl
    | cons g gs ih =>
      simp only [run_cons, act_zero]
      exact ih

/-- `p` with every qubit outside `s` reset to `I`. -/
def SPauli.restrict (p : SPauli n) (s : Finset (Fin n)) : SPauli n :=
  ⟨fun i => if i ∈ s then p.x i else 0,
   fun i => if i ∈ s then p.z i else 0⟩

/-- Only qubit `j` of `p`; every other qubit is `I`. -/
def SPauli.single (p : SPauli n) (j : Fin n) : SPauli n :=
  ⟨fun i => if i = j then p.x i else 0,
   fun i => if i = j then p.z i else 0⟩

lemma restrict_empty (p : SPauli n) : p.restrict ∅ = 0 := by
  ext i <;> simp [SPauli.restrict]

lemma restrict_univ (p : SPauli n) : p.restrict Finset.univ = p := by
  ext i <;> simp [SPauli.restrict]

lemma restrict_insert (p : SPauli n) (j : Fin n) (s : Finset (Fin n)) (hj : j ∉ s) :
    p.restrict (insert j s) = p.restrict s + p.single j := by
  ext i
  · simp only [SPauli.restrict, SPauli.single, SPauli.add_x, Pi.add_apply, Finset.mem_insert]
    by_cases h : i = j
    · rw [h]
      simp [hj]
    · simp [h]
  · simp only [SPauli.restrict, SPauli.single, SPauli.add_z, Pi.add_apply, Finset.mem_insert]
    by_cases h : i = j
    · rw [h]
      simp [hj]
    · simp [h]

lemma zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v
  decide

lemma single_eq (p : SPauli n) (j : Fin n) :
    p.single j = (if p.x j = 1 then SPauli.X j else 0) + (if p.z j = 1 then SPauli.Z j else 0) := by
    rcases zmod2_cases (p.x j) with hx | hx <;> rcases zmod2_cases (p.z j) with hz | hz
    all_goals simp only [hx, hz]
    all_goals
      ext i <;> by_cases h : i = j <;> simp [SPauli.single, SPauli.X, SPauli.Z, h, hx, hz]

/-- If two circuits agree on every basis Pauli, they agree on every Pauli. -/
theorem run_eq_of_basis (c₁ c₂ : Circuit n)
    (hX : ∀ i, run c₁ (SPauli.X i) = run c₂ (SPauli.X i))
    (hZ : ∀ i, run c₁ (SPauli.Z i) = run c₂ (SPauli.Z i)) :
    ∀ p, run c₁ p = run c₂ p := by
    intro p
    have hsingle : ∀ j, run c₁ (p.single j) = run c₂ (p.single j) := by
      intro j
      rw [single_eq, run_add, run_add]
      split_ifs
      all_goals simp [hX, hZ, run_zero]
    have key : ∀ s : Finset (Fin n), run c₁ (p.restrict s) = run c₂ (p.restrict s) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [restrict_empty, run_zero, run_zero]
      | insert j s hj ih =>
        rw [restrict_insert p j s hj, run_add, run_add, ih, hsingle]
    rw [← restrict_univ p]
    exact key Finset.univ

end CliffordEquiv
