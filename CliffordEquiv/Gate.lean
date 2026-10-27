import CliffordEquiv.Pauli

/-!
# Clifford gates and their action on Paulis

The generating set `{H, S, CNOT}` acting by conjugation on phase-free Paulis.
-/

namespace CliffordEquiv

/-- The Clifford gate set `{H, S, CNOT}` on `n` qubits. `CNOT a b` has control `a`, target `b`. -/
inductive CGate (n : ℕ) where
  | H (a : Fin n)
  | S (a : Fin n)
  | CNOT (a b : Fin n)
  deriving DecidableEq, Repr

namespace CGate

variable {n : ℕ}

/-- A gate is well formed if a `CNOT` has distinct control and target. -/
def WellFormed : CGate n → Prop
  | .CNOT a b => a ≠ b
  | _ => True

instance : DecidablePred (WellFormed (n := n)) := fun g => by
  cases g <;> unfold WellFormed <;> infer_instance

end CGate

open CGate in
/-- Conjugation action of a gate on a phase-free Pauli. -/
def act {n : ℕ} : CGate n → SPauli n → SPauli n
  | .H a, p =>
    { x := fun i => if i = a then p.z i else p.x i,
      z := fun i => if i = a then p.x i else p.z i }
  | .S a, p =>
    { x := p.x,
      z := fun i => if i = a then p.z i + p.x i else p.z i }
  | .CNOT a b, p =>
    { x := fun i => if i = b then p.x i + p.x a else p.x i,
      z := fun i => if i = a then p.z i + p.z b else p.z i }

end CliffordEquiv
