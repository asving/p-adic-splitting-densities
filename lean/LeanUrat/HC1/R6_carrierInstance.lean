/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R5_EQ2Pass

/-!
# HC1.R6_carrierInstance — the instantiation deliverable at δ = 1

moves_ref: MOVESR blueprint D4(a) "instantiation from the OM engine is HC-1's
declared deliverable" + campaign §1 HC-2. deps: T6, C1–C4, R1–R4. The LST/TYP/DOM
LEGS of `CStatements` hold for the tower's real carrier; the jets/counting legs
(thmCa/thmCb/C05/C1/C15) are NOT claimed: they need the JetSetup bridge —
**HC-2's seam**, recorded. difficulty: medium (assembly).
hyp: `TowerRealizable` (§5).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open LeanUrat.Moves
open scoped Classical

/-- OBSTRUCTION KERNEL 2a (machine-checked, escalation pass 2026-07-28): the REAL
slot coefficient is definitionally BLIND to off-block digits — `T.slotCoeff b`
reads `y` only on `{c | T.blk c = b}`, so perturbing `y` at an off-block
coordinate leaves it unchanged. -/
private theorem realSlot_offBlock_blind {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (T : Tower p F) (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ)
    (c_off : T.Coord) (hoff : T.blk c_off ≠ b) (d : ↥(T.stg 0).FQ) :
    T.slotCoeff b (y + Pi.single c_off d) = T.slotCoeff b y := by
  unfold Tower.slotCoeff
  apply finsum_mem_congr rfl
  intro c hc
  have hne : c ≠ c_off := fun h => hoff (h ▸ hc)
  simp [hne]

/-- OBSTRUCTION KERNEL 2b (machine-checked, escalation pass 2026-07-28): ANY
carrier pack whose `slotCoeff H b` is blind to some off-block coordinate `c_off`
(as the real one is, kernel 2a) and which satisfies `LSTStmt'` is REFUTED at every
windowed `b` carrying one nonzero slot value whose weight-height lies strictly
above `ht c_off`: leg (i-b)'s minimality clause `∀ c, y c ≠ 0 → ht c₀ ≤ ht c` is
UNRESTRICTED in `c` (R1 dropped T4/C1's `hsupp : ∀ c, y c ≠ 0 → blk c = b`), so it
reaches the off-block digit. -/
private theorem LSTib_offBlock_pincer {p : ℕ} [Fact p.Prime] (K : CarrierPackR p)
    (hlst : LSTStmt' p K) (H : K.Hist) (b : ℕ) (hwin : K.window H b)
    (y : K.Coord → K.Digit) (hy : K.slotCoeff H b y ≠ 0)
    (c_off : K.Coord) (d : K.Digit) (hd : y c_off + d ≠ 0)
    (hblind : K.slotCoeff H b (y + Pi.single c_off d) = K.slotCoeff H b y)
    (hlow : ∀ c₀ : K.Coord, K.G.w (K.slotCoeff H b y) = (K.ht H c₀ : WithTop ℚ) →
      K.ht H c_off < K.ht H c₀) : False := by
  obtain ⟨c₀, _hc₀ne, hc₀w, hc₀min⟩ :=
    (hlst H).2.1 b hwin (y + Pi.single c_off d) (by rw [hblind]; exact hy)
  rw [hblind] at hc₀w
  have hoffne : ((y + Pi.single c_off d : K.Coord → K.Digit)) c_off ≠ 0 := by
    simpa [Pi.single_eq_same] using hd
  exact absurd (hc₀min c_off hoffne) (not_le.mpr (hlow c₀ hc₀w))

/-- Unit R6 (`hc1_carrier_legs`): for every realizable tower there is a carrier
pack whose graded pieces are the tower's REAL pieces (`grQ` — the non-vacuity
pin) satisfying the LST, TYP, and DOM statement defs. -/
theorem R6_carrierInstance {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) :
    ∃ K : CarrierPackR p,
      (∀ γ : ℚ, K.G.Gr γ = T.grQ γ) ∧
      LSTStmt' p K ∧ TYPStmt' p K ∧ DOMStmt' p K := by
  -- ============================================================================
  -- HARD-CORE OBSTRUCTION — SHARPENED AT ESCALATION (pass 2, 2026-07-28; the two
  -- machine-checked kernels are the private theorems above). R6 is NOT honestly
  -- closable from the current corpus, and — CORRECTING pass 1's record — it does
  -- NOT unblock when C2(b) closes: the R-layer statement defs themselves carry two
  -- quantifier-scope transcription bugs relative to the C-layer forms they were
  -- meant to abstract. Statement repairs are fence-gated (sign-off required), so
  -- STOP is forced. The pass-1 Gr-pin fact remains true (dischargeable via
  -- `T.carrier (T6_carrierLaws T).2`).
  --
  -- [2026-07-30 verify-2 fold-in — DEPENDENCY STATUS CORRECTION. The pass-2
  -- record below is kept verbatim as history, but its dependency claims are
  -- SUPERSEDED at HEAD: `C2_TYPa` (including its conjunct-(b) carry wall,
  -- closed in-file) and `T4_slotMinHt` are both PROVED, Lean-core footprint
  -- (compiled `#print axioms` check 2026-07-30; the old pointer "C2(b) open at
  -- `C2_TYPa.lean:102`" was stale — post-golf, :102 lands in an unrelated
  -- private lemma). Consequence for the queued A17 statement-repair
  -- adjudication: every "(dep-sorry)" tag in the POSITIVE FINDING below is
  -- pass-2-era; the documented post-repair assembly now carries ZERO
  -- dep-sorries, so post-repair R6 would be fully closable. DEFECT 1 and
  -- DEFECT 2 themselves re-verified accurate at this fold-in; the :130 sorry
  -- correctly stands pending the fence-gated statement repairs.]
  --
  -- DEFECT 1 (R1 `LSTStmt'` leg (i-b) — REFUTED for every content-bearing pack;
  -- machine-checked kernels `realSlot_offBlock_blind` + `LSTib_offBlock_pincer`).
  -- (i-b) dropped T4/C1's support hypothesis `∀ c, y c ≠ 0 → blk c = b`, so its
  -- minimality clause quantifies over ALL coordinates. Any `slotCoeff H b` that is
  -- blind to off-block digits (the real one is, definitionally — kernel 2a; and any
  -- honest-(i-c)/TYP-additive pack must be, since `inγ`-invisibility of off-block
  -- singles follows from (i-c) at `x := 0` plus `inγ_detects`) is refuted by
  -- `y' := y* + Pi.single c_off d` at any windowed b, whenever some off-block
  -- coordinate sits at height strictly below w(slot y*) — e.g. the height-0
  -- coordinate (l = 0, slots ≡ 0, block 0) against any windowed b ≥ 1 (kernel 2b).
  -- No `window : Hist → ℕ → Prop` choice rescues this (the killer varies y, not b);
  -- only `window ≡ False` (vacuating (i-b)/(i-c)) or `slotCoeff ≡ 0` survive —
  -- both violate the repo's `sorry`-free ≠ non-vacuous invariant.
  -- REPAIR (fence, sign-off): reinstate in (i-b) exactly T4/C1's hypothesis
  --   `(∀ c, y c ≠ 0 → K.blk H c = b) →` (optionally also C1's finite-support arg).
  --
  -- DEFECT 2 (R2 `TYPStmt'` conjunct 1 vs the polynomial-Coeff real pack — REFUTED
  -- independently of the carry lemma, correcting pass 1's "unblocks when C2(b)
  -- closes"). Conjunct 1 is unconditional in x, y, but `T.inGr γ'` sends
  -- below-weight elements to 0 (the dif-condition) while `inγ_detects` forces a
  -- nonzero value at exact weight: for single-coordinate tuples x, y at heights
  -- γ₁ < γ' (both weights attained per T4's form), w(slot(x+y)) = γ₁ < γ' gives
  -- LHS = 0 ≠ 0 + inγ γ'(slot y) = RHS. Cross-strata failure — no carry involved.
  -- So C2(b) is NECESSARY (its per-coordinate core is conjunct 1 at equal heights)
  -- but NOT SUFFICIENT for the intended `K.G := T.carrier` instantiation.
  --
  -- POSITIVE FINDING (the honest unblock route, verified leg-by-leg at this pass):
  -- take Coeff := the lattice-supported graded expansion
  --   {B : ∀ γ : ℚ, T.grQ γ // ∀ γ, B γ ≠ 0 → ∃ n : ℕ, γ = n / strTop}
  -- (heights lie on (1/strTop)·ℕ since e ≥ 1 and e_r·str_r ∣ strTop), with
  -- w := least-populated-level (Nat.find; kills/detects/w_add are elementary),
  -- inγ γ := evaluation (UNCONDITIONALLY additive — the four `GradedCarrierR` laws
  -- hold with Gr := T.grQ, keeping the non-vacuity pin), and
  -- slotCoeff H b y := (γ ↦ T.inGr γ (T.slotCoeff b (y restricted to lvl b γ))) —
  -- the MOVES 3795–3807 display itself. Then conjunct 1 reduces componentwise to
  -- EXACTLY C2(b) (dep-sorry), (i-c) is definitional, (i-a) follows from T3 (the
  -- MonoNZ guard discharges via `hmonic`), (ii)/(iii)/DOM are C4/rl-definitional,
  -- conjunct 2 closes with aDim := Nat.log p (card) since the pieces are p-torsion
  -- (T3 at mono (l=1, slots≡0) gives w(C p) = strTop > 0) — and (i-b), AFTER the
  -- Defect-1 repair, transports from T4 (dep-sorry) via a two-level contradiction.
  -- So post-repair R6 = an assembly carrying the T4 + C2(b) dep-sorries, exactly
  -- the §4.6-style ledger pattern; no new mathematics beyond the C2(b) wall.
  -- [2026-07-30: T4 + C2(b) both since PROVED Lean-core — see the fold-in note
  -- above; the post-repair assembly carries zero dep-sorries at HEAD.]
  --
  -- Hence: STOP. Deliverables = the two kernels above + the two repair specs.
  -- Vacuous witnesses (Hist := Empty, window ≡ False, slotCoeff ≡ 0) remain
  -- statement-legal and remain FORBIDDEN by the honesty invariant.
  -- ============================================================================
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.R6_carrierInstance
