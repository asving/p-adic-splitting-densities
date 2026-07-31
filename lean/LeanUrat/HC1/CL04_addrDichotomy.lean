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

## PROBE REPORT (gate executed 2026-07-30) — outcome (b): NO OBSTRUCTION FOUND;
## the probe existential is believed FALSE for EVERY tower term; display (4) SURVIVES

**Verdict: STALLED-STATEMENT-SURVIVES.** The countermodel attempt terminated with a
math-level proof that no legal `Tower` admits the R-3 deficiency, plus a sealed numeric
sweep (`verification/cl04_addr_equidistribution_probe.py`, predictions sealed in header
before first run; 43,427 slot data incl. the gcd-defect strata, exit 0). The `sorry`
below stays banked as the open probe slot — its disposition (delete / quarantine-with-
record on R-b ratification) is CL-02's, per the fence discipline. NOTHING negation-
shaped is landed (the fenced `C6_alphabetCard` sorry is live; no-coexistence ruling).

**Mechanism reduction.** For any tower, block, height with nonempty level set:
* each digit line `y ↦ typComposite b γ (Pi.single c y)` is an ADDITIVE map with
  subgroup image of card ≤ |F_Q| (additivity: digLift residual sums via `hRadd`, weight
  jumps kill only the `y' = −y` diagonal via `w_jump`); so card 𝔸 ≤ |F_Q|^N with
  N := #(level set) = #(aligned ∧ attainable addresses) — the coordinate ↔ address
  bijection `(l, s) ↔ s, l = γ − Σ s_r·κ_r`;
* card F_{K+1} = |F_Q|^{∏ g}: `TransitionData.child_field : σ'.K = σ.nextField zbar`
  with `TransHyp.hirr ψ` + `hroot` pins each increment's residue growth to EXACTLY g
  (z̄'s minimal polynomial is ψ); `IsRecentering` keeps K; base pin `K = FQ`;
* the lines are full and jointly independent (line fullness: weight-detection at the
  piece index, exactly `C6_attain_automatic`'s display (0) applied to digit
  differences; joint independence: distinct level-set coordinates have distinct
  BOUNDED slot vectors, and iterated key developments are slot-min ORTHOGONAL —
  `hK1`/`K1At` at each stage's own key, descended to the top scale through `hStretch`/
  the ScratchC6 `stretch_chain` — so no cross-slot cancellation can raise the weight),
  giving card 𝔸 = |F_Q|^N exactly.
Hence (4)'s ⟸ leg fails at an all-attainable class IFF that class holds FEWER than
∏ g aligned addresses, and the whole probe reduces to slot combinatorics.

**The equidistribution theorem (CI-1, the counting identity's core — kills the
countermodel).** For every legal slot datum (stages r = 0..K storing (e_r, h_r) with
`Stage.hcop : gcd e_r h_r = 1`, `he`/`hh`; increments with `slotBound k = e_k·g_{k+1}`
— forced by `child_key` + `IsStandardLift`'s degree, L3_liftMonic; recenterings with
`slotBound = 1`, `e = 1` forced by `IsRecentering`), writing d_r := e_0···e_r:

    for EVERY class ρ ∈ ℚ/ℤ:  #{s : inner slots, Σ_r s_r·h_r/d_r ≡ ρ (mod ℤ)}
      = ∏ g   if ρ ∈ ⟨1/d_{K−1}⟩,   0 otherwise.

Proof (elementary, uses ONLY hcop — no I-aug/steeper-chain): peel slot 0. The walk
`s₀·h₀/e₀ mod ℤ`, s₀ < e₀·g₁, covers the subgroup ⟨1/e₀⟩ uniformly g₁ times
(gcd(h₀,e₀) = 1); conditioning on the tail reduces the fiber count to the SAME problem
mod ⟨1/e₀⟩ for the shifted tower (multiply by e₀), and induction closes. So every
achieved class of block b holds EXACTLY ∏ g = [F_{K+1} : F_Q] aligned addresses: the
digit-line deficiency (|F_Q| per line) is EXACTLY compensated by the address count —
the note's shallow heuristic `#aligned·[F_Q:F_p] = [F_{K+1}:F_p]` is a theorem, and
(4) needs NO extra "digit lines full" conjunct on its RHS.

**What CL-05 must prove (the ⟸-leg spec, all from existing stage laws + CI-1):**
* CI-1 (above; new Lean content, elementary induction on slots);
* CI-2 line structure: each level-set digit line is an injective additive hom image,
  card = |F_Q| (`hRadd`/`w_jump`/weight detection; ScratchC6 toolkit);
* CI-3 joint independence: `aDim b γ = N·[F_Q:F_p]` via slot-min orthogonality
  (`hK1` + `hStretch` recursion; T8's step lemma is the shape);
* CI-4 card bridge: `Nat.card F_{K+1} = |F_Q|^{∏g}` (child_field/hirr/hroot chain +
  `C6_cardK_bridge`'s char pin).
Assembly: all aligned attainable ⟹ N = ∏g (CI-1) ⟹ card 𝔸 = |F_Q|^{∏g} = card F_{K+1};
⟹-leg contrapositive: an unattainable aligned address drops N' < ∏g ⟹
card 𝔸 ≤ |F_Q|^{N'} < card F_{K+1} (needs only CI-1 + the CI-2 upper bound).

**Fence consequence (Q-1/CL-02).** R-b's display (4) survives its countermodel-first
gate with the counting identity now specified from existing laws; per the /goal
decision rule this supports ratifying R-b (it alone keeps the MOVES 2160–2165
dichotomy formal). CL-05's launch condition (this report) is satisfied.

## DATED NOTE (2026-07-31, item-18 execution — M1 hygiene). The C6 fence
## transition EXECUTED: `C6_alphabetCard` was repaired with the named
## `Tower.cleanThreshold b γ := ∀ s : T.Addr b, T.aligned γ s → T.attainable γ s`
## hypothesis guarding conjunct 2 (the hypothesis-guard form of the ratified
## "independence/clean-threshold" repair — this file's Part-1 vocabulary is now
## statement-consumed there), and the compiled `Tshallow` countermodel landed in
## CL01c against the frozen `C6_stmt_pre_repair` copy. THIS file's banked probe
## slot `CL04_dichotomy_probe` (below) is UNCHANGED: it targets display (4)'s ⟸
## leg (an existential believed FALSE for every tower — the probe report above),
## NOT the pre- or post-repair C6 statement; its sorry stays banked as the open
## probe slot pending CL-05 (whose ⟸-leg proof would refute it constructively:
## no such instance can exist once CI-1..CI-4 are proved).
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
