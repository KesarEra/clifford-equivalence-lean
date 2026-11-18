# Worklog

| Date | Hours | Brief description |
|---|---|---|
| 2026-10-27 | 1.5 | Created the git repo and Lean + Mathlib project, pinned to `v4.36.0-rc1`. Statements compile with `sorry`; demo identities pass `decide`. [Details](#2026-10-27-repo-and-project-setup) |
| 2026-11-16 | 2 | Proved `act_add` (each gate's action respects addition of Paulis): the first theorem without `sorry`. Added `#eval` gate checks to `Examples.lean`. [Details](#2026-11-16-proved-act_add) |
| 2026-11-17 | 0.5 | Proved `run_add` (a whole circuit respects addition of Paulis), by induction on the circuit. [Details](#2026-11-17-proved-run_add) |
| 2026-11-17 | 1.5 | Proved that H and S preserve the symplectic form (`act_H_preserves_omega`, `act_S_preserves_omega`). Background on commutation and the symplectic form. [Details](#2026-11-17-proved-h-and-s-preserve-the-symplectic-form) |
| 2026-11-17 | 2 | Proved that CNOT preserves the symplectic form (`act_CNOT_preserves_omega`), the hardest of the gate lemmas. [Details](#2026-11-17-proved-cnot-preserves-the-symplectic-form) |
| 2026-11-18 | 1 | Proved `act_preserves_omega` and `run_preserves_omega`: every well-formed gate and circuit preserves the symplectic form. Theorem (a) is complete; `Symplectic.lean` has no `sorry`. [Details](#2026-11-18-completed-theorem-a-symplectic-preservation) |
| 2026-11-18 | 2 | Proved checker completeness (`check_complete`) and soundness (`check_sound`, assuming `run_eq_of_basis`). Background on what soundness and completeness mean here. [Details](#2026-11-18-proved-checker-soundness-and-completeness) |

---

## 2026-10-27: Repo and project setup

**How it was created:** `lake +leanprover-community/mathlib4:lean-toolchain init CliffordEquiv math`.
Running it with Mathlib's own toolchain keeps the Lean and Mathlib versions matched. It also ran
`git init` and downloaded the prebuilt Mathlib cache.

**Pinned versions:** Lean `v4.36.0-rc1` (in `lean-toolchain`) and Mathlib tag `v4.36.0-rc1` (in
`lakefile.toml`). `lake-manifest.json` records the exact commits; commit it and don't run
`lake update` mid-project.

**How to build:**

```sh
lake exe cache get   # only needed on a fresh clone: downloads prebuilt Mathlib
lake build
```

To check whether a theorem still depends on `sorry`, add `#print axioms CliffordEquiv.check_iff`
to a file; `sorryAx` in the output means it does.

**Changes from the template:**
- Turned off Mathlib's copyright-header linter in `lakefile.toml`
  (`weak.linter.style.header = false`). It expects Mathlib's own copyright header in every file
  and warned on all of them.
- Deleted the `update.yml` GitHub workflow, which bumps Mathlib automatically and would break the pinning.
  Also deleted `create-release.yml`. Kept `lean_action_ci.yml`, which builds the project on every push.

**Expected build output:**
- `declaration uses 'sorry'` on every unproved theorem.
- A warning that `Pauli.lean` imports Mathlib without the new `module` system. It is harmless; ignore it.
- `#eval` output `Z` and `XX` from `Examples.lean` (H maps X to Z; CNOT 0→1 maps X⊗I to X⊗X).

**Lean files:** the plan's §6.2 skeleton is split into `Pauli`, `Gate`, `Circuit`, then one file
per main theorem (`Symplectic`, `Linear`, `Checker`), and `Examples`. Things I added beyond the plan:
- `SPauli` prints readably (e.g. `XIZY`), so `#eval` is useful.
- Basis Paulis `SPauli.X i` / `SPauli.Z i`.
- A comment in `Pauli.lean` suggesting an `AddCommGroup` instance for the week-3 basis sums.

**Demo identities:** proved as `check_sound _ _ (by decide)`. The checker already computes and
passes on all five, but they are only fully verified once `check_sound` is proved.

**Not done yet:**
- No commit.
- No `LICENSE` (week 5; Apache-2.0 would match Mathlib).
- No GitHub remote.

## 2026-11-16: Proved act_add

**What it says:** `act g (p + q) = act g p + act g q`. Applying a gate to a product of Paulis
(addition of bit vectors) is the same as applying it to each and multiplying. In matrix terms,
U(PQ)U† = (UPU†)(UQU†).

**How the proof works** (`CliffordEquiv/Linear.lean`):
1. `cases g with | H a => … | S a => … | CNOT a b => …` gives one case per gate.
2. `ext i` turns equality of two Paulis into two goals: the `x` parts agree at every qubit `i`,
   and the `z` parts agree at every `i`.
3. `simp only [act, SPauli.add_x, SPauli.add_z, Pi.add_apply]` unfolds the gate rule and the
   addition, leaving goals with `if i = a then … else …`.
4. `split_ifs` splits into the case where `i` is the qubit the gate touches and the case where it isn't.
5. Close each case with `rfl` (both sides identical) or `ring` (equal after rearranging).

**What I learned:**
- Without `ext i` first, `simp only` gets stuck: the goal compares whole Paulis
  (`{ x := …, z := … }`), and the addition lemmas only apply to a single component.
- `rfl` only works when both sides are literally the same; `ring` handles reordering and brackets.
- If `simp only` already closes a goal (S doesn't change `x`), a following `split_ifs` errors with "no goals".
- Lean 4 is indentation-sensitive: lines under a case or a `·` bullet must be indented further than it.
- Background: what H, S and CNOT do as matrices, the two-bits-per-qubit Pauli representation, and
  why the gate rules in `act` are what conjugation gives (N&C 10.5.1–10.5.2).

**Next:** `run_add`, by induction on the circuit.

## 2026-11-17: Proved run_add

**What it says:** `run c (p + q) = run c p + run c q`. `act_add` showed one gate respects
addition; this extends it to any circuit.

**How the proof works** (`CliffordEquiv/Linear.lean`): induction on the list of gates.
1. `induction c generalizing p q with | nil => … | cons g gs ih => …`.
2. Base case (empty circuit): `rfl`, since `run [] x` is `x` by definition.
3. Inductive step: `simp only [run_cons]` unfolds `run (g :: gs) x` to `run gs (act g x)` in all
   three places; `rw [act_add]` splits `act g (p + q)`; `rw [ih]` finishes.

**What I learned:**
- Induction on a list works like induction on ℕ: a case for the empty list `[]` and a case for
  `g :: gs` (first gate `g`, remaining gates `gs`), with the induction hypothesis `ih` about `gs`.
- `generalizing p q` makes `ih` hold for *all* Paulis, not just the original `p` and `q`. It's
  needed because the step uses `ih` on `act g p` and `act g q`. Without it, `rw [ih]` fails to
  find `run gs (p + q)` in the goal.
- `rw [h]` replaces the left side of `h` with its right side, but only for the first match it
  finds; `simp only [h]` rewrites every match. `rw` closes the goal automatically once both sides are identical.

**Next:** `act_H_preserves_omega`, the first proof about a sum (`∑`).

## 2026-11-17: Proved H and S preserve the symplectic form

**What it says:** `omega (act g p) (act g q) = omega p q` for `g = H a` and `g = S a`: these
gates don't change whether two Paulis commute.

**Background:** two Paulis commute or anticommute. Per qubit, `x·z′ + z·x′` counts the
"clashes" (a bit flip in one where the other has a phase flip); over many qubits each clash
contributes a minus sign, so only the parity matters. That parity is `omega`, a sum mod 2:
0 = commute, 1 = anticommute. Conjugation by any gate preserves commutation, which is why these
lemmas should hold.

**How the proofs work** (`CliffordEquiv/Symplectic.lean`):
1. `unfold omega` exposes the sum `∑ i, …`.
2. `apply Finset.sum_congr rfl` reduces "the sums are equal" to "each term is equal".
3. `intro i _` picks an arbitrary qubit; `simp only [act]` unfolds the gate rule.
4. `split_ifs with h`: is `i` the qubit the gate acts on?
   - H, `i = a`: the two products are swapped, so `ring`. Otherwise `rfl`.
   - S, `i = a`: the two sides differ by `2·x·x′`, zero only because 1 + 1 = 0 in `ZMod 2`, so
     `ring` fails. `generalize` the four values to variables, `revert` them, and `decide` checks
     all 16 cases. Otherwise `rfl`.

**What I learned:**
- `Finset.sum_congr`: equal terms give equal sums. `apply` reduces a goal to a lemma's hypotheses.
- `ring` only uses facts true in every ring; it doesn't know 2 = 0 in `ZMod 2`. `ring_nf` shows what's left over.
- "Make it finite, then `decide`": `generalize` replaces expressions with variables, `revert`
  turns them into a `∀`, and `decide` checks every case of a finite type.

**Next:** `act_CNOT_preserves_omega`. Individual terms change for CNOT, so the proof works with
the whole sum: the changes at qubits `a` and `b` are both `+ K`, and K + K = 0.

## 2026-11-17: Proved CNOT preserves the symplectic form

**Why it's harder than H and S:** CNOT (control `a`, target `b`) changes individual terms of the
sum, so per-term equality fails. Working out new − old by hand for each qubit:
- qubit `a` (z gets `+ z b`): new term = old term + K;
- qubit `b` (x gets `+ x a`): new term = old term + K;
- every other qubit: unchanged;

where K = `p.x a * q.z b + p.z b * q.x a`. The extra is the same at `a` and `b` because it comes
from the *other* qubit leaking in. So the sum gains K + K = 0. This needs `a ≠ b`.

**How the proof works** (`CliffordEquiv/Symplectic.lean`), written top-down:
1. `have key : ∀ i, new term = old term + (if i = a then K else 0) + (if i = b then K else 0)`.
   Proof: `split_ifs` gives four cases. `i = a` and `i = b` together is impossible
   (`exfalso`, `apply hab`, then show `a = b`); the other three are `rw` then `ring`.
2. `rw [Finset.sum_congr rfl (fun i _ => key i)]` rewrites every term using `key`.
3. `Finset.sum_add_distrib` (twice) splits into three sums.
4. `Finset.sum_ite_eq'` (twice) collapses each `if`-sum to K, leaving old sum + K + K.
5. `generalize` the sum and K, `revert`, `decide`.

**What I learned:**
- When only a few terms of a sum change, write each term as old + (extra only at that qubit),
  using `if i = a then … else 0`; Mathlib's `Finset.sum_ite_eq'` sums that shape.
- `have name : statement := by …` proves a helper fact inside a proof. Writing the outline
  first, with `sorry` for the helper, then filling it in, keeps a long proof manageable.
- Impossible cases: `exfalso` turns the goal into `False`; `apply hab` (with `hab : a ≠ b`)
  reduces it to proving `a = b`. `rw [← h]` rewrites right to left.
- Passing a proof directly to a lemma (`Finset.sum_congr rfl (fun i _ => key i)`) as an
  alternative to `apply`.

**Next:** `act_preserves_omega` (cases on the gate, using the three lemmas) and
`run_preserves_omega` (induction on the circuit).

## 2026-11-18: Completed theorem (a), symplectic preservation

**What it says:** every well-formed gate (`act_preserves_omega`) and every well-formed circuit
(`run_preserves_omega`) preserves `omega`, i.e. commutation relations. With the three gate
lemmas, `Symplectic.lean` now has no `sorry`.

**How the proofs work** (`CliffordEquiv/Symplectic.lean`):
- `act_preserves_omega`: `cases g`, then `exact` the matching gate lemma. For CNOT, `hg` is
  passed as the `a ≠ b` proof.
- `run_preserves_omega`: induction on the circuit, `generalizing p q` as in `run_add`.
  `simp only [run_cons]`, then `rw [ih]`, which leaves two goals: the first gate preserves
  `omega` (`act_preserves_omega`) and the rest of the circuit is well formed.

**What I learned:**
- A theorem can be used like a function: `act_H_preserves_omega a p q` is a proof of that
  statement for those arguments, and `exact` closes the goal with it.
- Lean unfolds definitions when checking types: `(CGate.CNOT a b).WellFormed` is defined as
  `a ≠ b`, so `hg` can be passed where `a ≠ b` is expected.
- If a hypothesis depends on the variable being inducted on (`hc` on `c`), Lean adds it to the
  induction hypothesis: `ih : Circuit.WellFormed gs → …`.
- `rw` with a conditional equation leaves the condition as an extra goal.
- `by simp` (or `by simp [h]`) proves simple list-membership facts such as `g ∈ g :: gs`.

**Next:** theorem (c): `run_eq_of_basis` (agreement on basis Paulis implies agreement
everywhere), then `check_sound` and `check_complete`.

## 2026-11-18: Proved checker soundness and completeness

**What they say:** `check c₁ c₂` tests only the 2n basis Paulis, instead of all 4ⁿ.
- **Completeness** (`check_complete`): if the circuits agree on every Pauli, `check` says `true`
  (no false negatives).
- **Soundness** (`check_sound`): if `check` says `true`, the circuits agree on every Pauli (no
  false positives).
- Together (`check_iff`): `check = true` ↔ the circuits are equivalent. Both are needed: a
  checker that always says `false` is sound, and one that always says `true` is complete.

**Why one is easy and the other hard:** completeness only *specialises* (agreeing on all Paulis
includes the basis ones) and would hold for any functions. Soundness *generalises* from 2n tests
to 4ⁿ inputs, which is only true because circuits are additive (`run_add`) and every Pauli is a
sum of basis Paulis. That argument is `run_eq_of_basis`, the last `sorry`; `check_sound` is fully
verified once it's proved, and so are the demo identities (proof by reflection: `by decide`
runs the checker, `check_sound` turns the result into a theorem).

**How the proofs work** (`CliffordEquiv/Checker.lean`):
- `check_complete`: `unfold check`, `rw [List.all_eq_true]` (turns "`all` is true" into "for
  every qubit"), `intro i _`, rewrite with `h` at `X i` and `Z i`, then `simp`.
- `check_sound`: the same unpacking applied to the hypothesis (`unfold check at h`,
  `rw [...] at h`); a `have` turns it into plain equations, using `h i (List.mem_finRange i)`
  and `simp only [Bool.and_eq_true, decide_eq_true_eq] at hb`; then `apply run_eq_of_basis`
  leaves two goals, closed with `(hx i).1` and `(hx i).2`.

**What I learned:**
- `Bool` (computed `true`/`false`) vs `Prop` (statements to prove); `decide P` turns a
  decidable proposition into a `Bool`.
- `at h` makes a tactic work on a hypothesis instead of the goal.
- Applying a `∀ x ∈ list, …` hypothesis to a value and a membership proof.
- `∧` ("and"); `.1` and `.2` take its two parts.
- A `sorry`'d lemma can be used in other proofs; they become fully proved once it is.
- `have … :=` needs `by` before tactic lines; without it Lean reports `Unknown identifier`.

**Next:** `run_eq_of_basis`, in four stages, starting with `act_zero` and `run_zero`.
