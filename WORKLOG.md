# Worklog

| Date | Hours | Brief description |
|---|---|---|
| 2026-10-27 | 1.5 | Created the git repo and Lean + Mathlib project, pinned to `v4.36.0-rc1`. Statements compile with `sorry`; demo identities pass `decide`. [Details](#2026-10-27-repo-and-project-setup) |
| 2026-11-16 | 2 | Proved `act_add` (each gate's action respects addition of Paulis): the first theorem without `sorry`. Added `#eval` gate checks to `Examples.lean`. [Details](#2026-11-16-proved-act_add) |
| 2026-11-17 | 0.5 | Proved `run_add` (a whole circuit respects addition of Paulis), by induction on the circuit. [Details](#2026-11-17-proved-run_add) |

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
