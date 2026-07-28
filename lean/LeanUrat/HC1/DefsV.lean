/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild

/-!
# HC1/DefsV — the V′ kernel Defs layer (blueprint §10, unit V0; ADDITIVE — no
accepted statement touched)

**Provenance.** `HC1_LEAN_BLUEPRINT_2026-07-28.md` §10 ("THE V′ KERNEL — the
read-functional carry algebra in the aligned frame"), unit V0.  The ONE design
behind the three hard residuals (S9w-(i), S9a's hS6a strip, HC2's
`K1_readVertexPin_nonrec`): the D.1(e) residual pack rebuilt at a NEW
(e★, h★, s★, t★)-position law over an existing stage's data —

  (†)  wV(f) := min_j ( e★·σ.w(B_j) + j·h★ )              (the read functional)
       RV(f) := Σ_{j minimizing} C(φ(slot-j digit)) · T(j·s★ − t★·σ.w(B_j))

* REGRADE instance (K1-nonrec): P = σ.Φ (the SAME key), (e★,h★) = the RECORDED
  READ pair, φ = identity on ↥σ.K.  **NOTE THE REUSE: wV at the same key IS
  `childW σ σ.Φ e★ h★` — no new functional is defined here.**
* DESCENT instance (S9w): P = Φ̂, (e★,h★) = th's (e′,h′), φ = z̄-evaluation —
  carried by the EXISTING `ChildResData`/`ChildResLaws` (DefsChild); V8's units.

FINDING 3 (why `ReadFrame` is a PARTIAL pack, not a `Stage`): the regraded
frame's coefficient weights under wVPrev = σ.w lie in σ.e·ℤ (hStretch), so
`Stage.hS6b`'s quantifier "∀ ν > wPrev Φ" (the D.9(b) cofinite range) is
UNSATISFIABLE at a regrade for σ.e > 1.  Hence NO hS6b, NO hvalgrp, NO
reps/Tvec — everything the D.5/D.8 reruns consume and nothing more.

POST-V5 NOTE: `ReadFrame.hS6a` is transcribed in the CURRENT `Stage.hS6a` form,
which since the V5 sign-off (2026-07-28) is the FIXED-POINT COSET form (∃ base
before ∀ orbit scalar; MOVES 1964–1971, 2431–2435).  V6(a) fills it: regrade
scalars are PRESERVED (no z̄ enters at the same level), so the parent's coset
bases transport verbatim.

Falsifiability: every pin is an equation against existing objects; wrong
positions break V2's hRmul at the first product.  Definitions only — no
theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The read pair** (blueprint §10 V0): a legal (e★, h★, s★, t★) regrade index over
the stage σ — lowest terms + Bézout + the (P2) pin + the read-form (I-aug)
STEEPNESS `e★·σ.h < h★` (D.4, MOVES 2219–2220 "λ > w(Φ)" at the stage scale; on
the HC2 side extracted from `HistoryCoherent`'s slope law + strict steepening —
`h_{i+1} > h_i·e_{i+1}·e_i·g_i ≥ e_{i+1}·h_i`, V9's short lemma). -/
def ReadPair (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Prop :=
  1 ≤ estar ∧ 1 ≤ hstar ∧ Nat.gcd estar hstar = 1 ∧
    (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1 ∧
    (estar = 1 → tstar = 0) ∧
    (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ)

/-- **The regrade carrier** (blueprint §10 V0), mirroring `ChildResData`: a residual
function on all of A for the regrade index (e★, h★, s★, t★) AT THE SAME KEY σ.Φ,
carrying the two pins —
* the key pin `Rv σ.Φ = T s★` (slot-1 arithmetic `1·s★ − t★·σ.w 1 = s★`);
* the S5-shape pin: scalars PRESERVED from the frame residual, positions RE-FORCED
  at the new pair (`−t★·σ.w B` — the (S5) position law at (e★, h★), MOVES 1960–1963). -/
structure ReadResData (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
  /-- the regrade residual function on all of A -/
  Rv : Polynomial ℤ_[p] → LaurentPolynomial ↥σ.K
  /-- the key pin `Rv(Φ) = z^{s★}` (D.3(b) at the regrade) -/
  hRPhi : Rv σ.Φ = LaurentPolynomial.T sstar
  /-- the S5-shape pin: SAME scalar as the frame digit, position re-forced at the
  new pair — the (S5) position law `−t★·σ.w B` (MOVES 1960–1963) -/
  hS5 : ∀ B, B ≠ 0 → inC σ.Φ B →
      ∃ c : (↥σ.K)ˣ,
        σ.R B = LaurentPolynomial.C (c : ↥σ.K) *
            LaurentPolynomial.T (- σ.t * σ.wPrev B) ∧
        Rv B = LaurentPolynomial.C (c : ↥σ.K) *
            LaurentPolynomial.T (- tstar * σ.w B)

/-- **The regrade law pack** (blueprint §10 V0): the D.1(e) laws of a regrade carrier
w.r.t. the read functional `childW σ σ.Φ e★ h★` — the SAME seven conjuncts as
`ChildResLaws` (hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg), at the regrade
instance of (†). -/
def ReadResLaws {σ : Stage p F} {estar hstar : ℕ} {sstar tstar : ℤ}
    (D : ReadResData σ estar hstar sstar tstar) : Prop :=
  (D.Rv 0 = 0) ∧
  (∀ f, f ≠ 0 → D.Rv f ≠ 0) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rv (f * g) = D.Rv f * D.Rv g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
      childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f →
      D.Rv (f + g) = D.Rv f + D.Rv g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
      D.Rv (f + g) = D.Rv f) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ σ.Φ estar hstar f = childW σ σ.Φ estar hstar g →
      childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar (f + g) →
      D.Rv f + D.Rv g = 0) ∧
  (∀ f, D.Rv (-f) = - D.Rv f)

/-- **The read frame** (blueprint §10 V0, Finding 3): the PARTIAL stage pack of the
regrade — a lawful carrier + the wV laws (hwmul/hwult/hwΦ/hK1-at-Φ/hStretch) +
hS6a in the current (post-V5 coset) `Stage.hS6a` form — everything the D.5/D.8
reruns (V3/V4) consume; **NO hS6b** (unsatisfiable at regrades for σ.e > 1,
Finding 3), NO hvalgrp, NO reps/Tvec. -/
structure ReadFrame (σ : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) : Type u where
  /-- the lawful regrade carrier -/
  D : ReadResData σ estar hstar sstar tstar
  /-- the carrier is lawful (V2's content) -/
  laws : ReadResLaws D
  /-- wV is multiplicative (V1's content) -/
  hwmul : ∀ f g, f ≠ 0 → g ≠ 0 →
      childW σ σ.Φ estar hstar (f * g)
        = childW σ σ.Φ estar hstar f + childW σ σ.Φ estar hstar g
  /-- wV is ultrametric -/
  hwult : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      min (childW σ σ.Φ estar hstar f) (childW σ σ.Φ estar hstar g)
        ≤ childW σ σ.Φ estar hstar (f + g)
  /-- the key's read weight is h★ (slot-1 arithmetic) -/
  hwPhi : childW σ σ.Φ estar hstar σ.Φ = (hstar : ℤ)
  /-- Lemma K1 at the frame's own key, in the read grading -/
  hK1 : K1At (childW σ σ.Φ estar hstar) σ.Φ ((hstar : ℤ))
  /-- the regrade stretch: wV = e★·σ.w on the coefficient space C_Φ -/
  hStretch : ∀ B, B ≠ 0 → inC σ.Φ B →
      childW σ σ.Φ estar hstar B = (estar : ℤ) * σ.w B
  /-- (S6a) at the regrade, in the post-V5 fixed-point coset form (weights read
  against wVPrev = σ.w, i.e. over `childWeightSet σ σ.Φ`); filled by V6(a) —
  regrade scalars are PRESERVED, so the parent's coset bases transport. -/
  hS6a : ∀ ν : ℤ, ν ∈ childWeightSet σ σ.Φ →
      ∃ b : (↥σ.K)ˣ, ∀ c : (↥σ.K)ˣ, ((c : ↥σ.K) : F) ∈ σ.FQ →
        ∃ B, B ≠ 0 ∧ inC σ.Φ B ∧ σ.w B = ν ∧
          D.Rv B = LaurentPolynomial.C ((c * b : (↥σ.K)ˣ) : ↥σ.K) *
            LaurentPolynomial.T (- tstar * ν)

end LeanUrat.HC1
