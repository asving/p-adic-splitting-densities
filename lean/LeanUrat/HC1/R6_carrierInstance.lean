/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R5_EQ2Pass
import LeanUrat.HC1.CL07_heightLattice
import LeanUrat.HC1.CL08_latticeExp
import LeanUrat.HC1.CL14_packEslotMin
import LeanUrat.HC1.CL15a_packEmonoWeight
import LeanUrat.HC1.CL15b_packErestrictExt
import LeanUrat.HC1.CL15c_packEfloorId
import LeanUrat.HC1.CL15d_packEavoid
import LeanUrat.HC1.CL16_packEtyp1
import LeanUrat.HC1.CL17_packEtyp2
import LeanUrat.HC1.CL18_packEdom

/-!
# HC1.R6_carrierInstance — the instantiation deliverable at δ = 1 (PROVED 2026-07-31)

moves_ref: MOVESR blueprint D4(a) "instantiation from the OM engine is HC-1's
declared deliverable" + campaign §1 HC-2. deps: T6, C1–C4, R1–R4, and the BP5
CL-07/08/14/15a–d/16/17/18 graded-expansion units. The LST/TYP/DOM LEGS of
`CStatements` hold for the tower's real carrier; the jets/counting legs
(thmCa/thmCb/C05/C1/C15) are NOT claimed: they need the JetSetup bridge —
**HC-2's seam**, recorded. difficulty: medium (assembly). hyp: `TowerRealizable`.

## CL-06 / A17 EXECUTION RECORD (Asvin queue items 6 + 19, sign-off 2026-07-31)

* **DEFECT 1 repaired (statement fence, VARIANT A ratified — BP5 §3.2 display (6),
  Q-3 adjudication 2026-07-30).** `LSTStmt'` leg (i-b) (R1) reinstates T4/C1's
  hypothesis row `(Function.support y).Finite → (∀ c, y c ≠ 0 → K.blk H c = b) →`.
  The pre-repair text is FROZEN below as `LSTStmt_pre_A17'` (R-7 kernel-freezing
  pattern) and kernels 2a/2b are retyped against the frozen copy, so the
  machine-checked refutation record stays compilable and can never be read as a
  refutation of the repaired live statement.
* **DEFECT 2 scoping record (NO statement change).** `TYPStmt'`, `DOMStmt'`, and
  `SecB1Stmt'` texts are UNCHANGED. TYP conjunct 1's refutation at the
  polynomial-Coeff pack (cross-strata tuples, the pass-2 record below) was an
  INSTANCE-choice defect: the repair is the graded-expansion pack (CL-08/CL-09),
  whose evaluation is unconditionally additive — never a weakening of the R2 text.
* **The discharge (queue item 19, this file's theorem).** `R6_carrierInstance` is
  PROVED at the graded-expansion pack: `G := gradedExpCarrier T` (CL-08), so the
  Gr-pin `∀ γ, K.G.Gr γ = T.grQ γ` holds by `rfl` — the non-vacuity clause. The
  legs fold back from the proved unfolded units: (i-a) CL-15a, (i-b) CL-14 (the
  NCL spine CL-10→CL-27/CL-11→CL-12→CL-13 underneath), (i-c) CL-15b, (ii) CL-15c,
  (iii) CL-15d, TYP CL-16/CL-17, DOM CL-18 — via the `wE` least-populated-level
  spec (`r6_wE_eq`) and CL-07's height lattice. UNIVERSE GLUE (the CL-09 pin,
  resolved statement-neutrally): `CarrierPackR.Digit : Type` while `↥FQ : Type u`;
  the statement (over `{F : Type*}`, untouched) is discharged with
  `Digit := Shrink.{0} ↥FQ` (finite ⇒ `Small.{0}`), digits read through the
  additive equivalence `Shrink.addEquiv` — at `F : Type` this pack is CL-09's
  `packE T rl` up to that equivalence (CL-09 untouched, kept as the Type-gate
  display-(8) literal).

## HISTORY — the pass-2 obstruction record (relocated VERBATIM from the proof
## body at the CL-06 execution; its "sorry stands" conclusion is SUPERSEDED by
## the repair + discharge above)

HARD-CORE OBSTRUCTION — SHARPENED AT ESCALATION (pass 2, 2026-07-28; the two
machine-checked kernels are the private theorems below). R6 is NOT honestly
closable from the current corpus, and — CORRECTING pass 1's record — it does
NOT unblock when C2(b) closes: the R-layer statement defs themselves carry two
quantifier-scope transcription bugs relative to the C-layer forms they were
meant to abstract. Statement repairs are fence-gated (sign-off required), so
STOP is forced. The pass-1 Gr-pin fact remains true (dischargeable via
`T.carrier (T6_carrierLaws T).2`).

[2026-07-30 verify-2 fold-in — DEPENDENCY STATUS CORRECTION. The pass-2
record below is kept verbatim as history, but its dependency claims are
SUPERSEDED at HEAD: `C2_TYPa` (including its conjunct-(b) carry wall,
closed in-file) and `T4_slotMinHt` are both PROVED, Lean-core footprint
(compiled `#print axioms` check 2026-07-30; the old pointer "C2(b) open at
`C2_TYPa.lean:102`" was stale — post-golf, :102 lands in an unrelated
private lemma). Consequence for the queued A17 statement-repair
adjudication: every "(dep-sorry)" tag in the POSITIVE FINDING below is
pass-2-era; the documented post-repair assembly now carries ZERO
dep-sorries, so post-repair R6 would be fully closable. DEFECT 1 and
DEFECT 2 themselves re-verified accurate at this fold-in; the :130 sorry
correctly stands pending the fence-gated statement repairs.]

DEFECT 1 (R1 `LSTStmt'` leg (i-b) — REFUTED for every content-bearing pack;
machine-checked kernels `realSlot_offBlock_blind` + `LSTib_offBlock_pincer`).
(i-b) dropped T4/C1's support hypothesis `∀ c, y c ≠ 0 → blk c = b`, so its
minimality clause quantifies over ALL coordinates. Any `slotCoeff H b` that is
blind to off-block digits (the real one is, definitionally — kernel 2a; and any
honest-(i-c)/TYP-additive pack must be, since `inγ`-invisibility of off-block
singles follows from (i-c) at `x := 0` plus `inγ_detects`) is refuted by
`y' := y* + Pi.single c_off d` at any windowed b, whenever some off-block
coordinate sits at height strictly below w(slot y*) — e.g. the height-0
coordinate (l = 0, slots ≡ 0, block 0) against any windowed b ≥ 1 (kernel 2b).
No `window : Hist → ℕ → Prop` choice rescues this (the killer varies y, not b);
only `window ≡ False` (vacuating (i-b)/(i-c)) or `slotCoeff ≡ 0` survive —
both violate the repo's `sorry`-free ≠ non-vacuous invariant.
REPAIR (fence, sign-off): reinstate in (i-b) exactly T4/C1's hypothesis
  `(∀ c, y c ≠ 0 → K.blk H c = b) →` (optionally also C1's finite-support arg).
[EXECUTED 2026-07-31, VARIANT A: both rows — see the execution record above.]

DEFECT 2 (R2 `TYPStmt'` conjunct 1 vs the polynomial-Coeff real pack — REFUTED
independently of the carry lemma, correcting pass 1's "unblocks when C2(b)
closes"). Conjunct 1 is unconditional in x, y, but `T.inGr γ'` sends
below-weight elements to 0 (the dif-condition) while `inγ_detects` forces a
nonzero value at exact weight: for single-coordinate tuples x, y at heights
γ₁ < γ' (both weights attained per T4's form), w(slot(x+y)) = γ₁ < γ' gives
LHS = 0 ≠ 0 + inγ γ'(slot y) = RHS. Cross-strata failure — no carry involved.
So C2(b) is NECESSARY (its per-coordinate core is conjunct 1 at equal heights)
but NOT SUFFICIENT for the intended `K.G := T.carrier` instantiation.

POSITIVE FINDING (the honest unblock route, verified leg-by-leg at this pass):
take Coeff := the lattice-supported graded expansion
  {B : ∀ γ : ℚ, T.grQ γ // ∀ γ, B γ ≠ 0 → ∃ n : ℕ, γ = n / strTop}
(heights lie on (1/strTop)·ℕ since e ≥ 1 and e_r·str_r ∣ strTop), with
w := least-populated-level (Nat.find; kills/detects/w_add are elementary),
inγ γ := evaluation (UNCONDITIONALLY additive — the four `GradedCarrierR` laws
hold with Gr := T.grQ, keeping the non-vacuity pin), and
slotCoeff H b y := (γ ↦ T.inGr γ (T.slotCoeff b (y restricted to lvl b γ))) —
the MOVES 3795–3807 display itself. Then conjunct 1 reduces componentwise to
EXACTLY C2(b) (dep-sorry), (i-c) is definitional, (i-a) follows from T3 (the
MonoNZ guard discharges via `hmonic`), (ii)/(iii)/DOM are C4/rl-definitional,
conjunct 2 closes with aDim := Nat.log p (card) since the pieces are p-torsion
(T3 at mono (l=1, slots≡0) gives w(C p) = strTop > 0) — and (i-b), AFTER the
Defect-1 repair, transports from T4 (dep-sorry) via a two-level contradiction.
So post-repair R6 = an assembly carrying the T4 + C2(b) dep-sorries, exactly
the §4.6-style ledger pattern; no new mathematics beyond the C2(b) wall.
[2026-07-30: T4 + C2(b) both since PROVED Lean-core — see the fold-in note
above; the post-repair assembly carries zero dep-sorries at HEAD.]

Hence: STOP. Deliverables = the two kernels above + the two repair specs.
Vacuous witnesses (Hist := Empty, window ≡ False, slotCoeff ≡ 0) remain
statement-legal and remain FORBIDDEN by the honesty invariant.
[END OF THE RELOCATED PASS-2 RECORD.]
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open LeanUrat.Moves
open scoped Classical

/-- **FROZEN PRE-A17 STATEMENT COPY** (R-7 kernel-freezing pattern; CL-06 execution,
2026-07-31, M1 hygiene): the VERBATIM pre-repair `LSTStmt'` text, whose leg (i-b)
LACKS T4/C1's hypothesis row (the R1 rev-4 transcription bug, DEFECT 1). Kernel 2b
below refutes THIS form and only this form; the live `LSTStmt'` (repaired at CL-06,
VARIANT A) is NOT refuted — it is DISCHARGED at the graded-expansion pack by
`R6_carrierInstance` below. -/
private def LSTStmt_pre_A17' (p : ℕ) [Fact p.Prime] (K : CarrierPackR p) : Prop :=
  ∀ H : K.Hist,
    (∀ c : K.Coord, K.G.w (K.mono H c) = (K.ht H c : WithTop ℚ)) ∧
    (∀ b : ℕ, K.window H b → ∀ y : K.Coord → K.Digit, K.slotCoeff H b y ≠ 0 →
      ∃ c₀ : K.Coord, y c₀ ≠ 0 ∧ K.G.w (K.slotCoeff H b y) = (K.ht H c₀ : WithTop ℚ) ∧
        ∀ c : K.Coord, y c ≠ 0 → K.ht H c₀ ≤ K.ht H c) ∧
    (∀ b : ℕ, K.window H b → ∀ (γ : ℚ) (x y : K.Coord → K.Digit),
      (∀ c ∈ K.lvl H b γ, x c = y c) →
      (∀ c : K.Coord, K.blk H c = b → K.ht H c < γ → x c = 0 ∧ y c = 0) →
      K.G.inγ γ (K.slotCoeff H b x) = K.G.inγ γ (K.slotCoeff H b y)) ∧
    (∀ b : ℕ, K.floorB H b = (K.lines H (K.kIdx H)).at (K.blockEdge H b)) ∧
    (∀ (b : ℕ) (γ' : ℚ), K.floorB H b < γ' →
      ∀ c ∈ K.lvl H b γ', ¬ (K.blk H c = b ∧ K.ht H c ≤ K.floorB H b))

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

/-- OBSTRUCTION KERNEL 2b (machine-checked, escalation pass 2026-07-28; RETYPED at
the CL-06 execution 2026-07-31 against the FROZEN pre-repair copy `LSTStmt_pre_A17'`
— dated M1-hygiene note: this kernel refutes the PRE-REPAIR (i-b), the form WITHOUT
the T4/C1 hypothesis row; it does NOT touch the repaired live `LSTStmt'`): ANY
carrier pack whose `slotCoeff H b` is blind to some off-block coordinate `c_off`
(as the real one is, kernel 2a) and which satisfies pre-A17 `LSTStmt'` is REFUTED at
every windowed `b` carrying one nonzero slot value whose weight-height lies strictly
above `ht c_off`: the pre-repair leg (i-b)'s minimality clause
`∀ c, y c ≠ 0 → ht c₀ ≤ ht c` is UNRESTRICTED in `c` (R1 dropped T4/C1's
`hsupp : ∀ c, y c ≠ 0 → blk c = b`), so it reaches the off-block digit. -/
private theorem LSTib_offBlock_pincer {p : ℕ} [Fact p.Prime] (K : CarrierPackR p)
    (hlst : LSTStmt_pre_A17' p K) (H : K.Hist) (b : ℕ) (hwin : K.window H b)
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

/-! ## The assembly pack (CL-19 glue): the graded expansion at `Type`-shrunk digits

`CarrierPackR.Digit : Type` while `↥(T.stg 0).FQ : Type u` follows the ambient `F`
(the CL-09 universe pin). The R6 statement is over `{F : Type*}` and is untouched,
so the pack takes `Digit := Shrink.{0} ↥FQ` (`Finite ⇒ Countable ⇒ Small.{0}`) and
reads digits through the additive equivalence `Shrink.addEquiv`. Everything else is
display (8) verbatim (CL-09's `packE`, which stays as the `F : Type` literal). -/

section Assembly

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open Polynomial

/-- The additive digit equivalence `Shrink ↥FQ ≃+ ↥FQ` (the universe glue). -/
private noncomputable def r6_dEq (T : Tower p F) :
    Shrink.{0} ↥(T.stg 0).FQ ≃+ ↥(T.stg 0).FQ := Shrink.addEquiv

private lemma r6_dEq_ne_zero (T : Tower p F) (d : Shrink.{0} ↥(T.stg 0).FQ) :
    r6_dEq T d ≠ 0 ↔ d ≠ 0 := by
  constructor
  · intro h hd
    exact h (by rw [hd, map_zero])
  · intro h hd
    exact h ((r6_dEq T).injective (by rw [hd, map_zero]))

/-- strTop positivity (copy of the CL07/CL08/CL09 private toolkit). -/
private lemma r6_strTop_pos (T : Tower p F) : 0 < T.strTop := by
  have haux : ∀ n : ℕ, 0 < T.strAux n := by
    intro n
    induction n with
    | zero => norm_num [Tower.strAux]
    | succ k ih =>
      rw [Tower.strAux]
      apply Nat.mul_pos ih
      split
      · exact (T.stg _).he
      · exact Nat.one_pos
  rw [Tower.strTop, Tower.str]
  exact Nat.mul_pos (haux _) (T.stg (Fin.last T.K)).he

/-- `digLift 0 = 0` (copy of the CL09/CL14 private). -/
private lemma r6_digLift_zero (T : Tower p F) : T.digLift (0 : ↥(T.stg 0).FQ) = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, -, -, hR⟩
  apply (T.stg 0).hRne B hB0
  rw [hR]
  have h0 : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := Subtype.ext (by simp)
  rw [h0, map_zero, zero_mul]

/-- The slot coefficient of an everywhere-zero digit assignment vanishes
(copy of the CL14 private). -/
private lemma r6_slotCoeff_zero (T : Tower p F) (b : ℕ) (z : T.Coord → ↥(T.stg 0).FQ)
    (hz : ∀ c, z c = 0) : T.slotCoeff b z = 0 := by
  rw [Tower.slotCoeff]
  apply finsum_mem_of_eqOn_zero
  intro c _
  show T.digLift (z c) * T.mono c = (0 : Polynomial ℤ_[p])
  rw [hz c, r6_digLift_zero T, zero_mul]

/-- `inGr γ 0 = 0` (copy of the CL09 private). -/
private lemma r6_inGr_zero (T : Tower p F) (γ : ℚ) :
    T.inGr γ (0 : Polynomial ℤ_[p]) = 0 := by
  rw [Tower.inGr]
  split
  · exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  · rfl

/-- The graded-expansion slot coefficient at shrunk digits: component γ reads `y`
through `r6_dEq` on the level-set restriction — display (8)'s `slotCoeff` composed
with the digit equivalence. -/
private noncomputable def r6_slotE (T : Tower p F) (b : ℕ)
    (y : T.Coord → Shrink.{0} ↥(T.stg 0).FQ) : LatticeExp T :=
  ⟨fun γ => T.inGr γ (T.slotCoeff b
      (fun c => if c ∈ T.levelSet b γ then r6_dEq T (y c) else 0)),
    by
      intro γ h0
      rcases Set.eq_empty_or_nonempty (T.levelSet b γ) with hempty | ⟨c₀, hc₀⟩
      · exfalso
        apply h0
        show T.inGr γ (T.slotCoeff b
            (fun c => if c ∈ T.levelSet b γ then r6_dEq T (y c) else 0)) = 0
        have hfun : (fun c => if c ∈ T.levelSet b γ then r6_dEq T (y c) else 0)
            = (fun _ : T.Coord => (0 : ↥(T.stg 0).FQ)) := by
          funext c; simp [hempty]
        rw [hfun, r6_slotCoeff_zero T b _ (fun _ => rfl), r6_inGr_zero]
      · obtain ⟨n, hn⟩ := (CL07_heightLattice T c₀).2
        exact ⟨n, by rw [← hc₀.2]; exact hn⟩⟩

/-- The graded expansion of a basis monomial (CL-09's `monoE`, re-emitted at
`{F : Type*}` — CL-09's file is universe-pinned to `Type` and untouched;
the lattice-support proof is CL-15a + CL-07, CL-09's own argument verbatim). -/
private noncomputable def r6_monoE (T : Tower p F) (c : T.Coord) : LatticeExp T :=
  ⟨fun γ => T.inGr γ (T.mono c), by
    intro γ hne0
    have hne : T.inGr γ (T.mono c) ≠ 0 := hne0
    have honL : T.onLattice γ := by
      by_contra hcon
      exact hne (by rw [Tower.inGr, dif_neg (fun hh => hcon hh.1)])
    have hge : T.ht c ≤ γ := by
      by_contra hcon
      exact hne ((CL15a_packE_ia T c).2 γ (not_le.mp hcon))
    have hpos : 0 ≤ γ := le_trans (CL07_heightLattice T c).1 hge
    have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast r6_strTop_pos T
    rw [Tower.onLattice] at honL
    have hfloor_nonneg : 0 ≤ ⌊(T.strTop : ℚ) * γ⌋ := by
      rw [Int.le_floor]; push_cast; exact mul_nonneg (le_of_lt hstrpos) hpos
    refine ⟨(⌊(T.strTop : ℚ) * γ⌋).toNat, ?_⟩
    have hcast : ((⌊(T.strTop : ℚ) * γ⌋).toNat : ℚ) = (⌊(T.strTop : ℚ) * γ⌋ : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
    rw [hcast, honL, eq_div_iff (ne_of_gt hstrpos)]; ring⟩

/-- **The assembly pack** (display (8) at shrunk digits): `G := gradedExpCarrier T`
(CL-08; `Gr = T.grQ` DEFINITIONALLY — the non-vacuity pin), trivial history, the
tower's real coordinates/heights/blocks/level sets, `Digit := Shrink ↥FQ`, the
display-(8) `slotCoeff`/`monoE` through the digit equivalence, `rl`-lines with the
`i > K` interior guard, trivial window. -/
private noncomputable def r6_pack (T : Tower p F) (rl : TowerRealizable T) :
    CarrierPackR p where
  G := gradedExpCarrier T
  Hist := Unit
  Coord := T.Coord
  Digit := Shrink.{0} ↥(T.stg 0).FQ
  kIdx _ := T.K
  ht _ := T.ht
  blk _ := T.blk
  lvl _ b γ := T.levelSet b γ
  slotCoeff _ b y := r6_slotE T b y
  aDim _ := T.aDim
  lines _ := rl.line
  blockEdge _ := T.blockEdge
  interiorEnd _ i := if i ≤ T.K then rl.interiorEnd i else 0
  window _ _ := True
  mono _ := r6_monoE T
  floorB _ := rl.floorB

/-- `wE` fold-back (the least-populated-level spec): a lattice expansion that
detects at an on-lattice γ and vanishes strictly below it has `wE = γ` — the
CL-14/CL-15a unfolded conclusions fold back to the pack legs through this. -/
private lemma r6_wE_eq (T : Tower p F) (B : LatticeExp T) (γ : ℚ)
    (hlat : ∃ n : ℕ, γ = (n : ℚ) / (T.strTop : ℚ))
    (hdet : B.1 γ ≠ 0) (hkill : ∀ γ' : ℚ, γ' < γ → B.1 γ' = 0) :
    wE T B = (γ : WithTop ℚ) := by
  obtain ⟨n, rfl⟩ := hlat
  have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast r6_strTop_pos T
  have hex : ∃ m : ℕ, B.1 ((m : ℚ) / (T.strTop : ℚ)) ≠ 0 := ⟨n, hdet⟩
  rw [wE, dif_pos hex]
  have hfind_le : Nat.find hex ≤ n := Nat.find_le hdet
  have hn_le : n ≤ Nat.find hex := by
    by_contra hcon
    push_neg at hcon
    have hltq : ((Nat.find hex : ℚ) / (T.strTop : ℚ)) < ((n : ℚ) / (T.strTop : ℚ)) := by
      have h1 : ((Nat.find hex : ℚ)) < (n : ℚ) := by exact_mod_cast hcon
      exact div_lt_div_of_pos_right h1 hstrpos
    exact (Nat.find_spec hex) (hkill _ hltq)
  have hfind : Nat.find hex = n := le_antisymm hfind_le hn_le
  rw [hfind]

/-- A nonzero lattice expansion has a populated component. -/
private lemma r6_exists_ne (T : Tower p F) (B : LatticeExp T) (hB : B ≠ 0) :
    ∃ γ : ℚ, B.1 γ ≠ 0 := by
  by_contra hall
  push_neg at hall
  exact hB (Subtype.ext (funext fun γ => hall γ))

/-- Unit R6 (`hc1_carrier_legs`): for every realizable tower there is a carrier
pack whose graded pieces are the tower's REAL pieces (`grQ` — the non-vacuity
pin) satisfying the LST, TYP, and DOM statement defs. PROVED 2026-07-31 (queue
item 19) at the graded-expansion pack `r6_pack` after the CL-06 (i-b) repair;
leg-by-leg fold-back from CL-14/CL-15a–d/CL-16/CL-17/CL-18 — see the module
docstring's execution record. -/
theorem R6_carrierInstance {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) :
    ∃ K : CarrierPackR p,
      (∀ γ : ℚ, K.G.Gr γ = T.grQ γ) ∧
      LSTStmt' p K ∧ TYPStmt' p K ∧ DOMStmt' p K := by
  classical
  refine ⟨r6_pack T rl, fun _ => rfl, ?_, ?_, ?_⟩
  · -- `LSTStmt'` at the pack
    intro H
    refine ⟨?_, ?_, ?_, fun b => rfl, ?_⟩
    · -- (i-a): `wE (monoE c) = ht c` — CL-15a through the `wE` spec + CL-07's LAT
      intro c
      exact r6_wE_eq T (r6_monoE T c) (T.ht c) (CL07_heightLattice T c).2
        (CL15a_packE_ia T c).1 (fun γ hγ => (CL15a_packE_ia T c).2 γ hγ)
    · -- (i-b), REPAIRED (the VARIANT-A row): CL-14 through the digit equivalence
      intro b _hwin y hfin hsupp hne
      have hne_iff : ∀ c : T.Coord, r6_dEq T (y c) ≠ 0 ↔ y c ≠ 0 :=
        fun c => r6_dEq_ne_zero T (y c)
      have hfin' : (Function.support fun c => r6_dEq T (y c)).Finite := by
        refine Set.Finite.subset hfin fun c hc => ?_
        exact Function.mem_support.mpr ((hne_iff c).mp (Function.mem_support.mp hc))
      have hsupp' : ∀ c : T.Coord, r6_dEq T (y c) ≠ 0 → T.blk c = b :=
        fun c hc => hsupp c ((hne_iff c).mp hc)
      have hneE : ∃ γ : ℚ,
          T.inGr γ (T.slotCoeff b
            (fun c => if c ∈ T.levelSet b γ then r6_dEq T (y c) else 0)) ≠ 0 :=
        r6_exists_ne T (r6_slotE T b y) hne
      obtain ⟨c₀, hc₀ne, ⟨hdet, hkill⟩, hmin⟩ :=
        CL14_packE_ib T b (fun c => r6_dEq T (y c)) hfin' hsupp' hneE
      refine ⟨c₀, (hne_iff c₀).mp hc₀ne, ?_, fun c hc => hmin c ((hne_iff c).mpr hc)⟩
      exact r6_wE_eq T (r6_slotE T b y) (T.ht c₀) (CL07_heightLattice T c₀).2 hdet hkill
    · -- (i-c): level-set functionality — CL-15b through the digit equivalence
      intro b _hwin γ x y hagree hlow
      have hagree' : ∀ c ∈ T.levelSet b γ, r6_dEq T (x c) = r6_dEq T (y c) :=
        fun c hc => congrArg (r6_dEq T) (hagree c hc)
      have hlow' : ∀ c : T.Coord, T.blk c = b → T.ht c < γ →
          r6_dEq T (x c) = 0 ∧ r6_dEq T (y c) = 0 := by
        intro c hb hht
        obtain ⟨hx0, hy0⟩ := hlow c hb hht
        exact ⟨by rw [hx0]; exact map_zero _, by rw [hy0]; exact map_zero _⟩
      exact CL15b_packE_ic T b γ (fun c => r6_dEq T (x c)) (fun c => r6_dEq T (y c))
        hagree' hlow'
    · -- (iii): floor avoidance — CL-15d verbatim
      intro b γ' hfl c hc
      exact CL15d_packE_avoid T rl b γ' hfl c hc
  · -- `TYPStmt'` at the pack
    intro H b γ'
    constructor
    · -- conjunct 1 (additivity): CL-16 through the digit equivalence
      intro x y
      show T.inGr γ' (T.slotCoeff b
            (fun c => if c ∈ T.levelSet b γ' then r6_dEq T ((x + y) c) else 0))
          = T.inGr γ' (T.slotCoeff b
              (fun c => if c ∈ T.levelSet b γ' then r6_dEq T (x c) else 0))
            + T.inGr γ' (T.slotCoeff b
                (fun c => if c ∈ T.levelSet b γ' then r6_dEq T (y c) else 0))
      have hfun : (fun c => if c ∈ T.levelSet b γ' then r6_dEq T ((x + y) c) else 0)
          = (fun c => if c ∈ T.levelSet b γ'
              then ((fun c' => r6_dEq T (x c')) + fun c' => r6_dEq T (y c')) c else 0) := by
        funext c
        by_cases hc : c ∈ T.levelSet b γ'
        · simp only [if_pos hc, Pi.add_apply]
          exact map_add (r6_dEq T) (x c) (y c)
        · simp only [if_neg hc]
      rw [hfun]
      exact packE_typ1 T b γ' (fun c => r6_dEq T (x c)) (fun c => r6_dEq T (y c))
    · -- conjunct 2 (span pricing): CL-17 after the digit-range rewrite
      show Nat.card ↥(AddSubgroup.closure
          (⋃ c ∈ T.levelSet b γ', Set.range fun y : Shrink.{0} ↥(T.stg 0).FQ =>
            T.inGr γ' (T.slotCoeff b (fun c' => if c' ∈ T.levelSet b γ'
              then r6_dEq T ((Pi.single c y : T.Coord → Shrink.{0} ↥(T.stg 0).FQ) c')
              else 0))))
        = p ^ T.aDim b γ'
      have hsingle : ∀ (c : T.Coord) (y : Shrink.{0} ↥(T.stg 0).FQ),
          (fun c' => if c' ∈ T.levelSet b γ'
              then r6_dEq T ((Pi.single c y : T.Coord → Shrink.{0} ↥(T.stg 0).FQ) c')
              else 0)
            = (fun c' => if c' ∈ T.levelSet b γ'
                then (Pi.single c (r6_dEq T y) : T.Coord → ↥(T.stg 0).FQ) c' else 0) := by
        intro c y
        funext c'
        by_cases hc' : c' ∈ T.levelSet b γ'
        · simp only [if_pos hc']
          by_cases hcc : c' = c
          · subst hcc
            rw [Pi.single_eq_same, Pi.single_eq_same]
          · simp only [Pi.single_eq_of_ne hcc, map_zero]
        · simp only [if_neg hc']
      have hset : (⋃ c ∈ T.levelSet b γ', Set.range fun y : Shrink.{0} ↥(T.stg 0).FQ =>
            T.inGr γ' (T.slotCoeff b (fun c' => if c' ∈ T.levelSet b γ'
              then r6_dEq T ((Pi.single c y : T.Coord → Shrink.{0} ↥(T.stg 0).FQ) c')
              else 0)))
          = (⋃ c ∈ T.levelSet b γ', Set.range fun y : ↥(T.stg 0).FQ =>
              T.inGr γ' (T.slotCoeff b (fun c' => if c' ∈ T.levelSet b γ'
                then (Pi.single c y : T.Coord → ↥(T.stg 0).FQ) c' else 0))) := by
        refine Set.iUnion₂_congr fun c hc => ?_
        ext z
        simp only [Set.mem_range]
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨r6_dEq T y, by rw [hsingle c y]⟩
        · rintro ⟨y, rfl⟩
          refine ⟨(r6_dEq T).symm y, ?_⟩
          rw [hsingle c ((r6_dEq T).symm y), (r6_dEq T).apply_symm_apply]
      rw [hset]
      exact packE_typ2 T b γ'
  · -- `DOMStmt'` at the pack: CL-18 (the `i > K` guard branch is vacuous)
    intro H i m b hm hb
    exact CL18_packE_dom T rl i m b hm hb

end Assembly

end LeanUrat.HC1

#print axioms LeanUrat.HC1.R6_carrierInstance
