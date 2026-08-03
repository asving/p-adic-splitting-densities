/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.Scaffold.HDischarge.H1.GlueRun

/-!
# HC2/DefsPrime — the σ.wPrev-keyed PRIMED MIRRORS (P0 APPLICATION unit; campaign date 2026-08-08, wallclock 2026-08-03)

**THE APPLICATION (additive new-definition route).**  Decided by Claude under the
2026-08-03 delegation (ledger `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, commit
b70a452, decision 1): the ACCEPTED FGMN transcription-scale repair
(`lean/notes/openmath/FGMN_REDERIVATION_2026-08-08.md`, ACCEPTED at REVISION 10 — the
compiled `SideReads` clauses (i)/(ii) DOUBLE-SCALE the stride weight: their window
functional `ν.e * ν.σ.w (B j) + j * ν.h` keys the coefficient weight at the node
stage's OWN graded scale, where the print — FGMN Thm 4.2 / Def 3.16 / eq (13),
provenance-pinned — keys it at the PARENT valuation) is applied here as NEW
definitions, leaving every compiled name byte-untouched:

* `SideReads'` — the compiled `SideReads` (HC2/Defs.lean:280–314) with EXACTLY the
  three token substitutions `ν.σ.w` → `ν.σ.wPrev` at the clause-(i)/(ii) functional
  sites (Defs.lean:285/287/292); clauses (iii)–(vi) code-identical.
* `ReadsOf'`, `TruncRunFrom'`, `FTiedTruncLanding'`/`ftie_extends'`,
  `DIterJunctionSupplier'` — the run/glue mirrors, each transcribed per the DITERSUP
  displays (`lean/notes/openmath/DITERSUP_STMT_2026-08-08.md` §S1/§S2): the compiled
  originals with the primed names substituted, nothing else.

**THE σ.wPrev IDENTIFICATION** (the application charter's verification item): the
parent-valuation accessor IS the `Stage` field `wPrev` (`Moves/Defs.lean`, DEF-4:
"the PARENT valuation `w_prev` (the previous stage's `w`, extended to `A`); at the
base it is the Gauss valuation. Coefficient positions/weights are read against it.").
The compiled `SideReads` clause (ii) residual leg ALREADY consumes `ν.σ.wPrev` in its
T-exponent — the repair moves the window functional onto the accessor the residual
leg always used.  At every compiled positive instance on file (U31 base read, HK25
e = 1 seam) `w = wPrev` pointwise on the consumed carrier, so the primed and compiled
definitions agree there; they diverge exactly at genuinely graded e ≥ 2 junction
frames (FGMN §S2).

**HONEST GATING (nothing is discharged here).**  Definitions only: no gate fires; the
one theorem (`ftie_extends'`) is the transcription-trivial chain constructor.  The
DITERSUP gates J1–J3b remain note-side displays — landing these definitions UNBLOCKS
them (they become statable against compiled names) but discharges NOTHING.  The
byte-frozen record is UNTOUCHED: `SideReads`, `ReadsOf`, `TruncRunFrom`,
`FTiedTruncLanding`/`ftie_extends`, `DIterJunctionSupplier`, and every JuncForge/D0
theorem (`juncforge_no_e2_junction`, `juncforge_deep_wall`,
`juncforge_junc_bundle_false`, `juncforge_D0_instanceFalse`,
`juncforge_gate_hbundle_false`, `juncforge_gluePacket_false`) keep their exact
compiled meanings as statements about the OLD clause — the FGMN REVISION-10
acceptance list (c) retained-semantics fixed point.  The change-set's completeness is
adjudicated ON THE DIFF plus a dedicated POST-APPLICATION HOSTILE PASS (FGMN
REVISION-9 cut) — that pass is OWED, not performed by this unit.

**TRUST BOUNDARY.**  Every declaration below is a NEW-statement site: definitions are
where errors hide; each is FLAGGED FOR STATEMENT REVIEW (the post-application hostile
pass + semantic-guardian discipline).  In-definition comments are pointers, not
byte-copies of the originals' comments; the CODE of every unchanged clause is
transcribed identically.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- **`SideReads'` — the σ.wPrev-keyed per-read clause bundle** (the ACCEPTED FGMN
repair, applied additively; DITERSUP §S1 display).  The compiled `SideReads`
(HC2/Defs.lean:280–314) with EXACTLY three token substitutions: the clause-(i)/(ii)
window functional reads `ν.e * ν.σ.wPrev (B j) + j * ν.h` — the coefficient weight at
the PARENT valuation (FGMN eq (13): the polygon ordinate is µᵢ₋₁(aₛφᵢˢ); Thm 4.2 glues
it to the graded residual side), replacing the compiled `ν.σ.w` at
Defs.lean:285/287/292, which double-scales the stride weight at graded (σ.e ≥ 2)
junction stages (σ.w = e·σ.wPrev on the coefficient carrier there).  Clauses
(iii)–(vi) are code-identical to the compiled originals: the ANCHOR/ORDER clause
stays at the GRADED scale `σ.R` (Thm 4.2's H_µ(g) — the `juncforge_clauseIII_derivable`
fixed point), and the clause-(ii) residual leg keeps the `σ.wPrev` T-exponent it
always had.  σ.wPrev identification: `Stage.wPrev`, DEF-4 (module docstring).
STATEMENT-REVIEW FLAG (trust boundary): new-statement site; review owed at the
post-application hostile pass.  Nothing binds this definition yet; the byte-frozen
JuncForge/D0 theorems bind `SideReads` and keep their exact compiled meanings. -/
def SideReads' {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p]) : Prop :=
  -- (i) SIDE — window functional at the PARENT scale (FGMN eq (13) / Thm 4.2)
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ)) ∧  -- token 1 (was ν.σ.w, Defs.lean:285)
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →  -- token 2 (was ν.σ.w, Defs.lean:287)
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)) ∧
  -- (ii) DIGITS — functional-equality leg at the PARENT scale
  (∀ k : ℕ, k ≤ ν.wSide / ν.e → ν.pat k ≠ 0 →
      B (ν.s0 + ν.e * k) ≠ 0 ∧
      (ν.e : ℤ) * ν.σ.wPrev (B (ν.s0 + ν.e * k)) + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ)  -- token 3 (was ν.σ.w, Defs.lean:292)
        = ν.gam ∧
      ν.σ.R (B (ν.s0 + ν.e * k)) = LaurentPolynomial.C (ν.pat k) *
        LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (B (ν.s0 + ν.e * k)))) ∧
  -- (iii) ANCHOR/ORDER — code-identical to `SideReads` (Defs.lean:296–298; the graded-scale
  -- fixed point `juncforge_clauseIII_derivable`)
  (HasAnchorK (ν.σ.R (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j)) ν.a ν.Ranch ∧
   OrdPsiPoly ν.ψ ν.Ranch ν.μ) ∧
  -- (iv) DESCENT WITNESS — code-identical (Defs.lean:299–300)
  LandingKey ν Φnext ∧
  -- (v) LIFTS + ROOT NORMALIZATION — code-identical (Defs.lean:301–302)
  (ν.lift = (polOM p F).liftOf ν ∧ ((ν.zbar : Fˣ) : F) = canonRoot ν) ∧
  -- (vi) VERTEX READ-OFF — code-identical (Defs.lean:303–314; the N-4 sign-off clause)
  (∀ (Bh : ℕ → Polynomial ℤ_[p]) (Nh : ℕ),
      IsDevelopment Φnext (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) Bh Nh →
      ν.σ.digPrime ν.zbar (Bh ν.μ) = ν.vtx)

/-- **`ReadsOf'` — the σ.wPrev-keyed run predicate** (DITERSUP §S2 display): the
compiled `ReadsOf` (HC2/Defs.lean:320–327) with `SideReads` → `SideReads'`, nothing
else.  STATEMENT-REVIEW FLAG (trust boundary): new-statement site; review owed at the
post-application hostile pass.  `ReadsOf` itself is byte-untouched; every compiled
consumer (U19–U25 projections, V9, GlueRun) still binds the OLD predicate. -/
def ReadsOf' (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (f : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ HistoryCoherent H ∧
  ∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      SideReads' (H.nodes[i]'hi) B Nd Φnext

end LeanUrat.MovesJ
