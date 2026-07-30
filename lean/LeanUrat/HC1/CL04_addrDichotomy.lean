/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.CL04_addrDichotomy — address vocabulary + the dichotomy-(4) probe (BP5 CL-04)

**Unit CL-04** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.1 (R-b)
displays (3)-(4); risk R-3). Pre-adjudication probe: countermodel-first for the (R-b)
repair candidate of C6. Runs with no prerequisites; its report INFORMS the CL-02
statement-repair adjudication (Asvin queue Q3). CL-05 (the dichotomy prover) NEVER
launches without this probe's report.

**Part 1 (defs (3), compiled here, review-flagged as new statement vocabulary).**
Addresses are bounded slot vectors with the top slot pinned to the block:
`Addr T b := { s : Fin (K+1) → ℕ // (∀ r : Fin K, s r.castSucc < slotBound r) ∧
s (last K) = b }`; `aligned T γ s := ∃ n : ℤ, γ − Σ_r s_r·κ_r = n` (ℤ-alignment);
`attainable T γ s := 0 ≤ γ − Σ_r s_r·κ_r` (the p-adic level l exists in ℕ). These
re-type the note's "every height in γ's slot tree is attainable" over ADDRESSES —
ScratchC6's diagnosis of the D-10 mistype (the missing addresses at shallow heights
would need l < 0: they are not coordinates, so C6's per-coordinate ∀ cannot see them).

**Part 2 (the probe, sorry slot).** Repaired conjunct 2′ of display (4) claims
`card 𝔸(b,γ) = card F_{K+1} ⟺ every aligned address at (b,γ) is attainable`.
The ⟸ leg needs a counting identity NOT in the corpus (real new mathematics:
aDim = Σ_{aligned attainable addresses} dim_{F_p}(digit line)). CHARGE: search for an
instance where ALL aligned addresses are attainable yet `card 𝔸 < card F_{K+1}`.
Candidate mechanism (risk R-3): the digit lines are F_Q-lines, F_Q ⊊ K_top — exactly
ScratchC6's `card ≤ |F₂| < |F₄|` deficiency, WHICH MAY SURVIVE the address re-typing;
check whether (4)'s RHS must instead read "attainable ∧ digit lines full", i.e.
whether the note ties fullness to `[F_Q : F_p]·#addresses = [F_{K+1} : F_p]`.

**Prediction status (NOT sealed either way — that is the point of the probe).** The
blueprint records genuine uncertainty: at ScratchC6's own shallow instance the
dichotomy (4) SURVIVES (the address s₀ = 1 is aligned, κ₀ = 1, but unattainable at
γ = 0, so (4)'s RHS correctly FAILS there), and the counting heuristic
`#aligned·[F_Q:F_p] = [F_{K+1}:F_p]` holds there (2·1 = 2) — but no general argument
exists in the corpus. Outcomes: (a) a concrete countermodel sketch (→ CL-02 falls
back to R-a with the probe on record); (b) "no obstruction found" + the exact
counting identity CL-05 must prove.

**Deps.** DefsTower (`slotBound`, `kappa`), DefsCar (`levelSet`, `alphabet`). Output
feeds CL-02; deliverable = this file green + the probe report (countermodel sketch or
counting-identity spec).

**E-phase resolutions recorded.**
* Displays (3) are transcribed verbatim (sums over ALL r : Fin (K+1) — the top slot
  contributes b·κ_K, matching `ht c = l + Σ_r slot_r·κ_r`); no helper name is banked
  (the Q-6 lesson: nothing beyond the blueprint's three defs).
* The probe existential carries the `Nonempty` guard (the fenced C6 and any repaired
  form quantify over nonempty level sets) and uses `<` (the blueprint's "yet card 𝔸 <
  card F_{K+1}"; strictly stronger than the ≠ needed to refute (4)⟸).
* The probe's ambient is fixed at the standard gate instance (p = 2,
  F = GaloisField 2 2); the blueprint does not pin it — if the mechanism survey finds
  an obstruction only at another ambient, the prover reports BLOCKED-with-artifact and
  the retarget goes through the orchestrator.

difficulty: hard-fable. hyp: none. PERMITTED OUTCOME: BLOCKED + mechanism-survey
report in lieu of a proof of the probe existential.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

namespace Tower

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (T : Tower p F)

/-- **Address** (display (3)): a bounded slot vector in block b — inner slots bounded
by the key-degree ratios, top slot pinned to b. Unlike a `Coord`, an address carries
NO p-adic level l: it names a height class `Σ_r s_r·κ_r + ℕ`, and a coordinate over it
exists iff `γ − Σ_r s_r·κ_r ∈ ℕ` (aligned ∧ attainable below). -/
def Addr (b : ℕ) : Type :=
  { s : Fin (T.K + 1) → ℕ //
    (∀ r : Fin T.K, s r.castSucc < T.slotBound r) ∧ s (Fin.last T.K) = b }

/-- **ℤ-alignment** (display (3)): γ sits on the address's height lattice —
`γ − Σ_r s_r·κ_r` is an integer (possibly negative: alignment does NOT imply a
coordinate exists). -/
def aligned (γ : ℚ) {b : ℕ} (s : T.Addr b) : Prop :=
  ∃ n : ℤ, γ - ∑ r, (s.1 r : ℚ) * T.kappa r = (n : ℚ)

/-- **Attainability** (display (3)): the p-adic level exists in ℕ —
`0 ≤ γ − Σ_r s_r·κ_r`. Aligned ∧ attainable ⟺ some coordinate of block b at height γ
has slot vector s. -/
def attainable (γ : ℚ) {b : ℕ} (s : T.Addr b) : Prop :=
  0 ≤ γ - ∑ r, (s.1 r : ℚ) * T.kappa r

end Tower

/-- **The CL-04 probe** (countermodel attempt against display (4)'s ⟸ leg): a tower,
block, and height with a NONEMPTY level set where every aligned address is attainable
yet the alphabet is strictly smaller than the top residue field. A proof of this
existential REFUTES the (R-b) repaired dichotomy and sends CL-02 to the (R-a)
fallback; a mechanism survey finding no such instance (BLOCKED outcome, report
required) names the counting identity CL-05 must prove. -/
theorem CL04_dichotomy_probe :
    ∃ (T : Tower 2 (GaloisField 2 2)) (b : ℕ) (γ : ℚ),
      (T.levelSet b γ).Nonempty ∧
      (∀ s : T.Addr b, T.aligned γ s → T.attainable γ s) ∧
      Nat.card ↥(T.alphabet b γ) < Nat.card ↥(T.stg (Fin.last T.K)).K := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL04_dichotomy_probe
