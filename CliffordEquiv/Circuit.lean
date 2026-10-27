import CliffordEquiv.Gate

/-!
# Circuits

A circuit is a list of gates, applied left to right.
-/

namespace CliffordEquiv

/-- A circuit is a list of gates; the head is applied first. -/
abbrev Circuit (n : ℕ) := List (CGate n)

namespace Circuit

variable {n : ℕ}

/-- Every gate in the circuit is well formed. -/
def WellFormed (c : Circuit n) : Prop := ∀ g ∈ c, g.WellFormed

end Circuit

/-- Apply the gates of a circuit in order. -/
def run {n : ℕ} : Circuit n → SPauli n → SPauli n
  | [], p => p
  | g :: gs, p => run gs (act g p)

@[simp] lemma run_nil {n : ℕ} (p : SPauli n) : run [] p = p := rfl
@[simp] lemma run_cons {n : ℕ} (g : CGate n) (gs : Circuit n) (p : SPauli n) :
    run (g :: gs) p = run gs (act g p) := rfl

end CliffordEquiv
