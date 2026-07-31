/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeB8_regData
import LeanUrat.MovesS.PowSubstOK

/-!
# BridgeB15a_r2Neg — COMPILED COUNTERMODEL for IB-B15a (`bridge_r2_on_activeLocus`)

COUNTERMODEL GATE EXECUTION (2026-07-31), per the IB-B16 as-built update
(BridgeRosterPins.lean:449-462: "IB-B15a BLOCKED (suspect-false as stated;
countermodel gate queued by the orchestrator)").  The prover's countermodel
shape, realized COMPILED here: an adversarial `UCarriers 2` with `DetHyp` TRUE,
a wild first-descent pool (q₀ = 4 = 2², the ONLY non-all-active pool), and a
surviving pole of `blockSolve` at the INACTIVE block-1 coordinate there — making
the roster's `bsplit` row UNDEFINED at the all-active base pool q₀ = 2 ∈
`bridgeActiveLocus`.  Hence the (r2) clause `RegPAtR2` FAILS at a locus point:
`bridge_r2_on_activeLocus` is FALSE AS STATED.

## The instance (n = 2, p = 2)

* Block 1 (one state): a kcol outcome with kernel entry
  k(q) = (8(q−2)q² + 2(q−4)²)/q⁴ — chosen so k(m) ∈ (0,1) at every prime power
  m ≠ 4 (ESCAPE(E0) holds wherever the state is active) but k(4) = 1 EXACTLY:
  1 − k = (q−4)²(q²−2)/q⁴ =: D/q⁴ vanishes at the wild pool 4 while staying a
  NONZERO rational function (`DetHyp` holds).  Two termFin exits t₁ = (D+1)/(2q⁴)
  (verdict (1,1)) and t₂ = (D−1)/(2q⁴) (verdict (1,2)); the solve entries are
  t̂ᵢ = tᵢ/(1−k) = (D±1)/(2D), with a genuine POLE at q = 4.
* Block 2 (one state): ONE split outcome (J = 1) with a halted (1,1) member and
  a continuing size-1 member at base-change δ = 2 → the roster's bsplit row is
  Σ_{σ' ∈ Sigmas} bSplit(σ') = t̂₁(q²) = ((q²−4)²(q⁴−2)+1)/(2(q²−4)²(q⁴−2)),
  whose denominator VANISHES at the base pool q = 2.
* THE LOAD-BEARING CHEAT (recorded): the t₂ exit carries the DEGREE-2 verdict
  (1,2) on a SIZE-1 member.  NO carried law ties a halted member's verdict
  degree to its size (`DegCons` constrains sizes only), and exactly this degree
  leak protects the pole from the σ'-sum over the degree-2 `Sigmas`: the
  partner mass t̂₂(q²) sits at σ' = {(1,1),(1,2)} of degree 3 ∉ Sigmas.  In a
  degree-faithful table the σ'-graded books balance (Σ_{σ'∈Sigmas} bSplit = 1
  by part1/rep_indep conservation) and THIS route closes — see the FENCE
  CONSEQUENCE below.
* Activity: the block-1 state carries the activity cell polynomial (X−4)²
  (`act_iff`), so it is inactive EXACTLY at the pool 4; every chain law that
  binds at 4 (legs_reg's PoolHyp: empty Act; legs_read's LegAgree: block 1
  vacuous, block 2 discharged for real via the βmeas fixpoint at 16) holds.
* The chain tail (`rsh_interp`/`rs1_equates`/`x3_total`) is carried by a k = 0
  device shape with σ₀ = {(1,1),(1,1)} and W ≡ 1 (Rsh σ = [σ = σ₀]; total 1).

## COEXISTENCE RULE (soundness — the TV-H1b precedent, BINDING)

This module must NEVER import (or be imported alongside)
`LeanUrat.MovesU.BridgeRosterPins`: that file's sorried universal
`bridge_r2_on_activeLocus` plus this file's compiled negation in one
environment derive False.  Accordingly the two consumed vocabulary defs are
BYTE-IDENTICAL LOCAL COPIES (suffix `N`), recorded below at their definitions:
`RegPAtR2N` copies `RegPAtR2` (BridgeRosterPins.lean:88-90) and
`bridgeActiveLocusN` copies `bridgeActiveLocus` (BridgeRosterPins.lean:113-116).
Nothing else may re-state them; any future repair commit that lands the
re-scoped (r2) must delete the sorried IB-B15a in the SAME commit that makes
this module reachable from any importing file.

## FENCE CONSEQUENCE (recorded per the gate charge)

The (r2) transport on the active locus, AS STATED over the five static entry
families PLUS the dite families, is FALSE: the dite families (`bsplit`,
`betaLeg`) read `blockSolve` through `powSubst δ` at DESCENT pools q₀^δ, where
(i) the exponent may leave the warranted activity locus, and (ii) at a wild
descent pool `legs_read` covers ACTIVE coordinates only — nothing forbids a
surviving pole at an inactive coordinate, and this file exhibits one.  The
IB-B16 record's as-built residual index for the (r2) face (BridgeRosterPins
lines 449-462) is CONFIRMED-EXACT by countermodel: the dite-family entries at
descent pools are NOT note-warranted on the locus.  `theoremU`'s (REG-p)
premise therefore CANNOT be discharged by the bridge on the dite families
without a NEW per-pool hypothesis — the re-scoped statement drafted below.

## RE-SCOPED (r2) DRAFT — for the SIGN-OFF QUEUE (display only, NO unit here)

Split IB-B15a into (drafted as the two display defs at the end of this file,
`bridgeStaticEntryList` + `BridgeDiteOK` + `bridge_r2_static_target` +
`bridge_r2_dite_target`):
  (a) IB-B15a-static — the five static families K/bterm/Jcell/iota/Wcoef are
      (r2)-transported on the active locus UNCONDITIONALLY (chain-warranted:
      `tg_ok`/`j_ok`/`jcell_ok`/`ι_ok`/`wsh_ok` + OKat subring closure +
      `bridgeAct_ok`);
  (b) IB-B15a-dite — the `bsplit`/`betaLeg` families are (r2)-transported on
      the locus GATED by the named per-pool hypothesis `BridgeDiteOK C p`
      (every summed `blockSolve` leg lies in `OKat` at every pool value of the
      locus, after `powSubst`) — exactly the OKat obligation this countermodel
      violates, converted into an explicit premise.
Statement changes require sign-off (statement fence: MovesU/Defs.lean:209
untouchable; BridgeRosterPins.lean IB-B15a to be replaced, not weakened).

Deliverable theorems at the END of this file:
* `cm_detHyp` — DetHyp holds at the instance (the dite fires its real branch);
* `cm_two_mem_locus` — 2 ∈ the active locus (the base pool is all-active);
* `cm_bsplit_not_definedAt` — the roster's block-2 bsplit row is UNDEFINED at 2;
* `cm_regPAtR2_false` — ¬ RegPAtR2N (bridgeRegData …) 2 ⟨2,_⟩;
* `bridge_r2_on_activeLocus_false` — the ∀-statement of IB-B15a (over the
  copied vocabulary) is FALSE.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU.R2Neg
open LeanUrat.MovesS
open Polynomial

/-! ## §1 The verdict carrier and the table (n = 2) -/

/-- One state per block layer. -/
private abbrev cmState : ℕ → Type := fun _ => Unit

/-- The R20 structural verdict carrier at n = 2: the (e,f) pairs of degree ≤ 2. -/
private abbrev cmVType : Type := {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ 2}

private lemma cmVType_bound (u : cmVType) : (u.1.1 : ℕ) < 3 ∧ (u.1.2 : ℕ) < 3 := by
  obtain ⟨⟨a, b⟩, h⟩ := u
  have ha := a.pos
  have hb := b.pos
  simp only at h
  refine ⟨?_, ?_⟩ <;> nlinarith [ha, hb, h]

noncomputable instance : Fintype cmVType :=
  Fintype.ofInjective
    (fun v : cmVType => ((⟨(v.1.1 : ℕ), (cmVType_bound v).1⟩ : Fin 3),
                         (⟨(v.1.2 : ℕ), (cmVType_bound v).2⟩ : Fin 3)))
    (by
      intro v w hvw
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hvw
      exact Subtype.ext (Prod.ext (PNat.coe_injective hvw.1) (PNat.coe_injective hvw.2)))

/-- The degree-1 verdict (1,1). -/
private def w11 : cmVType := ⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩
/-- The degree-2 verdict (1,2) — carried by a SIZE-1 halted member (the recorded
degree cheat: no carried law forbids it). -/
private def w12 : cmVType := ⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩
/-- The degree-2 verdict (2,1) (Sigmas roster only). -/
private def w21 : cmVType := ⟨((2 : ℕ+), (1 : ℕ+)), by decide⟩

private lemma w_ne_11_12 : w11 ≠ w12 := by decide
private lemma w_ne_11_21 : w11 ≠ w21 := by decide
private lemma w_ne_12_21 : w12 ≠ w21 := by decide

/-- Block 1, o₀: the kcol outcome — one continuing member of size 1, δ = 1. -/
private def outK1 : Outcome cmVType cmState :=
  ⟨[⟨1, 1, Sum.inr ()⟩], List.cons_ne_nil _ _⟩
/-- Block 1, o₁: the t₁ exit — verdict (1,1) on a size-1 member. -/
private def outT1 : Outcome cmVType cmState :=
  ⟨[⟨1, 1, Sum.inl w11⟩], List.cons_ne_nil _ _⟩
/-- Block 1, o₂: the t₂ exit — verdict (1,2) on a size-1 member (THE CHEAT). -/
private def outT2 : Outcome cmVType cmState :=
  ⟨[⟨1, 1, Sum.inl w12⟩], List.cons_ne_nil _ _⟩
/-- Block 2, o₀: THE split outcome — a halted (1,1) member (size 1, δ = 1) and a
continuing member (size 1, δ = 2) targeting the block-1 state. -/
private def outSplit : Outcome cmVType cmState :=
  ⟨[⟨1, 1, Sum.inl w11⟩, ⟨1, 2, Sum.inr ()⟩], List.cons_ne_nil _ _⟩

/-- THE COUNTERMODEL TABLE. -/
noncomputable def cmT : TableShape 2 where
  State := cmState
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  VType := cmVType
  deqV := inferInstance
  finV := inferInstance
  vdeg := fun v => v.1.1 * v.1.2
  vEquiv := Equiv.refl _
  vdeg_spec := fun v => PNat.mul_coe _ _
  Out := fun _ _ => Fin 3
  finO := fun _ _ => inferInstance
  odata := fun e _ o =>
    if e = 1 then (if o = 0 then outK1 else if o = 1 then outT1 else outT2)
    else if e = 2 then (if o = 0 then outSplit else outT1)
    else outT1
  Wloc := fun _ _ _ => 0
  Wstate := fun e _ => if e = 1 then 2 else 0

/-- The block-1 state (the pole coordinate). -/
noncomputable def τ1 : cmT.State 1 := ()
/-- The block-2 state. -/
noncomputable def τ2 : cmT.State 2 := ()

/-- Roster reduction: block 1. -/
private lemma cm_odata1 (τ : cmT.State 1) (o : Fin 3) :
    cmT.odata 1 τ o = (if o = 0 then outK1 else if o = 1 then outT1 else outT2) := rfl

/-- Roster reduction: block 2. -/
private lemma cm_odata2 (τ : cmT.State 2) (o : Fin 3) :
    cmT.odata 2 τ o = (if o = 0 then outSplit else outT1) := rfl

/-- Roster reduction: padding layers. -/
private lemma cm_odata_pad {e : ℕ} (h1 : e ≠ 1) (h2 : e ≠ 2) (τ : cmT.State e)
    (o : cmT.Out e τ) : cmT.odata e τ o = outT1 := by
  show (if e = 1 then _ else if e = 2 then _ else outT1) = outT1
  rw [if_neg h1, if_neg h2]

/-- Route pins for the four outcome shapes. -/
private lemma route_outK1 : routeOf (V := cmVType) (State := cmState) outK1 = .kcol := rfl
private lemma route_outT1 : routeOf (V := cmVType) (State := cmState) outT1 = .termFin := rfl
private lemma route_outT2 : routeOf (V := cmVType) (State := cmState) outT2 = .termFin := rfl
private lemma route_outSplit : routeOf (V := cmVType) (State := cmState) outSplit = .split := rfl

/-- Verdict pins. -/
private lemma verd_outT1 : (outT1).verdicts = ({w11} : Multiset cmVType) := rfl
private lemma verd_outT2 : (outT2).verdicts = ({w12} : Multiset cmVType) := rfl

/-! ## §2 The adversarial rational functions -/

/-- D := (X−4)²(X²−2) — the det numerator; D(4) = 0 is the wild-pool zero. -/
noncomputable def polD : Polynomial ℚ := (X - 4) ^ 2 * (X ^ 2 - 2)
/-- The kernel-entry numerator 8(X−2)X² + 2(X−4)²; polK + polD = X⁴. -/
noncomputable def polK : Polynomial ℚ := 8 * (X - 2) * X ^ 2 + 2 * (X - 4) ^ 2
noncomputable def polB : Polynomial ℚ := X ^ 4
noncomputable def pol2B : Polynomial ℚ := 2 * X ^ 4
noncomputable def polT1 : Polynomial ℚ := polD + 1
noncomputable def polT2 : Polynomial ℚ := polD - 1
/-- 2D — the reduced t̂ denominator. -/
noncomputable def pol2D : Polynomial ℚ := 2 * polD

private lemma polK_add_polD : polK + polD = polB := by
  unfold polK polD polB; ring

private lemma polB_sub_polK : polB - polK = polD := by
  rw [← polK_add_polD]; ring

/-- Polynomial evaluations, expanded. -/
private lemma polD_eval (x : ℚ) : polD.eval x = (x - 4) ^ 2 * (x ^ 2 - 2) := by
  simp [polD]
private lemma polK_eval (x : ℚ) : polK.eval x = 8 * (x - 2) * x ^ 2 + 2 * (x - 4) ^ 2 := by
  simp [polK]
private lemma polB_eval (x : ℚ) : polB.eval x = x ^ 4 := by simp [polB]
private lemma pol2B_eval (x : ℚ) : pol2B.eval x = 2 * x ^ 4 := by simp [pol2B]
private lemma polT1_eval (x : ℚ) : polT1.eval x = (x - 4) ^ 2 * (x ^ 2 - 2) + 1 := by
  simp [polT1, polD]
private lemma polT2_eval (x : ℚ) : polT2.eval x = (x - 4) ^ 2 * (x ^ 2 - 2) - 1 := by
  simp [polT2, polD]

private lemma pol2D_eval (x : ℚ) : pol2D.eval x = 2 * ((x - 4) ^ 2 * (x ^ 2 - 2)) := by
  simp [pol2D, polD]

private lemma polD_ne : polD ≠ 0 := fun h => by
  have := congrArg (Polynomial.eval (0 : ℚ)) h
  rw [polD_eval] at this
  norm_num at this
private lemma polB_ne : polB ≠ 0 := fun h => by
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  rw [polB_eval] at this
  norm_num at this
private lemma pol2B_ne : pol2B ≠ 0 := fun h => by
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  rw [pol2B_eval] at this
  norm_num at this
private lemma pol2D_ne : pol2D ≠ 0 := fun h => by
  have := congrArg (Polynomial.eval (0 : ℚ)) h
  rw [pol2D_eval] at this
  norm_num at this

/-- Shorthand for the polynomial embedding into ℚ(q). -/
noncomputable abbrev aQ : Polynomial ℚ →+* Qq := algebraMap (Polynomial ℚ) Qq

private lemma aQ_ne {p : Polynomial ℚ} (hp : p ≠ 0) : aQ p ≠ 0 :=
  RatFunc.algebraMap_ne_zero hp

/-- k(q) — the symbolic kernel entry. -/
noncomputable def kQ : Qq := aQ polK / aQ polB
/-- t₁(q) — the (1,1)-exit mass. -/
noncomputable def t1Q : Qq := aQ polT1 / aQ pol2B
/-- t₂(q) — the (1,2)-exit mass. -/
noncomputable def t2Q : Qq := aQ polT2 / aQ pol2B
/-- 1 − k as a reduced-form quotient. -/
noncomputable def dQ : Qq := aQ polD / aQ polB

private lemma dQ_ne : dQ ≠ 0 := div_ne_zero (aQ_ne polD_ne) (aQ_ne polB_ne)

private lemma one_sub_kQ : (1 : Qq) - kQ = dQ := by
  unfold kQ dQ
  rw [eq_div_iff (aQ_ne polB_ne), sub_mul, one_mul,
    div_mul_cancel₀ _ (aQ_ne polB_ne), ← map_sub, polB_sub_polK]

/-- t̂₁ = (D+1)/(2D) — the block-1 solve entry at σ' = {(1,1)} (pole at 4),
DEFINED in reduced form; `bh1Q_mul_dQ` below is the solve law t̂₁·(1−k) = t₁. -/
noncomputable def bh1Q : Qq := aQ polT1 / aQ pol2D
/-- t̂₂ = (D−1)/(2D). -/
noncomputable def bh2Q : Qq := aQ polT2 / aQ pol2D

private lemma bh1Q_mul_dQ : bh1Q * dQ = t1Q := by
  unfold bh1Q dQ t1Q
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    div_eq_div_iff (aQ_ne (mul_ne_zero pol2D_ne polB_ne)) (aQ_ne pol2B_ne),
    ← map_mul, ← map_mul]
  exact congrArg aQ (by unfold pol2D pol2B polB; ring)

private lemma bh2Q_mul_dQ : bh2Q * dQ = t2Q := by
  unfold bh2Q dQ t2Q
  rw [div_mul_div_comm, ← map_mul, ← map_mul,
    div_eq_div_iff (aQ_ne (mul_ne_zero pol2D_ne polB_ne)) (aQ_ne pol2B_ne),
    ← map_mul, ← map_mul]
  exact congrArg aQ (by unfold pol2D pol2B polB; ring)

/-! ## §3 Pools and pool-shape facts -/

/-- The prime-power pool set (the N2Carriers idiom verbatim). -/
def cmPoolsSet : Set ℚ :=
  {q : ℚ | ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q = (p : ℚ) ^ (δ : ℕ)}

private lemma cm_pool_nat {q₀ : ℚ} (hq : q₀ ∈ cmPoolsSet) :
    ∃ m : ℕ, 2 ≤ m ∧ q₀ = (m : ℚ) := by
  obtain ⟨p, hp, δ, rfl⟩ := hq
  refine ⟨p ^ (δ : ℕ), ?_, by push_cast; ring⟩
  calc 2 ≤ p := hp.two_le
    _ ≤ p ^ (δ : ℕ) := Nat.le_self_pow δ.pos.ne' p

private lemma cm_pool_toNat (m : ℕ) : ((m : ℚ)).num.toNat = m := by
  rw [Rat.num_natCast]
  exact Int.toNat_natCast m

/-! ## §4 Value lemmas at the pools -/

/-- k(x) — the evaluated kernel entry. -/
noncomputable def kV (x : ℚ) : ℚ := polK.eval x / polB.eval x
/-- t₁(x). -/
noncomputable def t1V (x : ℚ) : ℚ := polT1.eval x / pol2B.eval x
/-- t₂(x). -/
noncomputable def t2V (x : ℚ) : ℚ := polT2.eval x / pol2B.eval x
/-- t̂₁(x) = (D(x)+1)/(2D(x)) — junk 0 at x = 4 (division by zero). -/
noncomputable def bh1V (x : ℚ) : ℚ := polT1.eval x / pol2D.eval x
/-- t̂₂(x). -/
noncomputable def bh2V (x : ℚ) : ℚ := polT2.eval x / pol2D.eval x

/-- Integrality bite: at a NATURAL x = m ≥ 2 with m ≠ 4 the det factor D(m) ≥ 2
(the countermodel's margins live on the integrality of the pools). -/
private lemma cm_D_ge_two {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) :
    (2 : ℚ) ≤ polD.eval (m : ℚ) := by
  rw [polD_eval]
  have h1z : (1 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 := by
    have hsplit : (m : ℤ) - 4 ≤ -1 ∨ 1 ≤ (m : ℤ) - 4 := by omega
    rcases hsplit with h | h <;> nlinarith
  have h1 : (1 : ℚ) ≤ ((m : ℚ) - 4) ^ 2 := by exact_mod_cast h1z
  have h2 : (2 : ℚ) ≤ (m : ℚ) ^ 2 - 2 := by
    have hm : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm2
    nlinarith
  nlinarith

private lemma cm_D_pos {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) :
    (0 : ℚ) < polD.eval (m : ℚ) := lt_of_lt_of_le (by norm_num) (cm_D_ge_two hm2 hm4)

private lemma cm_x_pos {m : ℕ} (hm2 : 2 ≤ m) : (0 : ℚ) < (m : ℚ) := by
  exact_mod_cast lt_of_lt_of_le (by norm_num) hm2

private lemma cm_x4_pos {m : ℕ} (hm2 : 2 ≤ m) : (0 : ℚ) < (m : ℚ) ^ 4 :=
  pow_pos (cm_x_pos hm2) 4

/-- part1's mass identity k + t₁ + t₂ = 1 (any x ≠ 0). -/
private lemma cm_masses_sum {x : ℚ} (hx : x ≠ 0) : kV x + t1V x + t2V x = 1 := by
  unfold kV t1V t2V
  rw [polK_eval, polT1_eval, polT2_eval, polB_eval, pol2B_eval]
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

/-- E0 nonneg: 0 ≤ k(m) at m ≥ 2. -/
private lemma cm_kV_nonneg {m : ℕ} (hm2 : 2 ≤ m) : 0 ≤ kV (m : ℚ) := by
  unfold kV
  rw [polK_eval, polB_eval]
  have hm : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm2
  have hnum : 0 ≤ 8 * ((m : ℚ) - 2) * (m : ℚ) ^ 2 + 2 * ((m : ℚ) - 4) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℚ) - 4), sq_nonneg (m : ℚ)]
  exact div_nonneg hnum (cm_x4_pos hm2).le

/-- E0 escape margin: k(m) < 1 at m ≥ 2, m ≠ 4 (the AM-GM-style strict gap). -/
private lemma cm_kV_lt_one {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) : kV (m : ℚ) < 1 := by
  unfold kV
  rw [polB_eval, div_lt_one (cm_x4_pos hm2)]
  have hD := cm_D_pos hm2 hm4
  have hkey : polK.eval (m : ℚ) + polD.eval (m : ℚ) = (m : ℚ) ^ 4 := by
    have := congrArg (Polynomial.eval ((m : ℚ))) polK_add_polD
    rwa [Polynomial.eval_add, polB_eval] at this
  linarith

/-- k(4) = 1 — the wild-pool kernel saturation (display; the pole mechanism). -/
private lemma cm_kV_four : kV (4 : ℚ) = 1 := by
  unfold kV
  rw [polK_eval, polB_eval]
  norm_num

/-- Abstract-d evaluation identities. -/
private lemma cm_evT1 (x : ℚ) : polT1.eval x = polD.eval x + 1 := by
  rw [polT1, Polynomial.eval_add, Polynomial.eval_one]
private lemma cm_evT2 (x : ℚ) : polT2.eval x = polD.eval x - 1 := by
  rw [polT2, Polynomial.eval_sub, Polynomial.eval_one]
private lemma cm_ev2D (x : ℚ) : pol2D.eval x = 2 * polD.eval x := by
  rw [pol2D, Polynomial.eval_mul]
  norm_num
private lemma cm_evK (x : ℚ) : polK.eval x = x ^ 4 - polD.eval x := by
  have h := congrArg (Polynomial.eval x) polB_sub_polK
  rw [Polynomial.eval_sub, polB_eval] at h
  linarith

/-- The block-1 measured fixpoint t̂ᵢ = k·t̂ᵢ + tᵢ at any x with x ≠ 0, D(x) ≠ 0. -/
private lemma cm_fix1 {x : ℚ} (hx : x ≠ 0) (hD : polD.eval x ≠ 0) :
    bh1V x = kV x * bh1V x + t1V x ∧ bh2V x = kV x * bh2V x + t2V x := by
  have hx4 : x ^ 4 ≠ 0 := pow_ne_zero _ hx
  constructor
  · unfold bh1V kV t1V
    rw [cm_evT1, cm_evK, cm_ev2D, pol2B_eval, polB_eval]
    field_simp
    ring
  · unfold bh2V kV t2V
    rw [cm_evT2, cm_evK, cm_ev2D, pol2B_eval, polB_eval]
    field_simp
    ring

/-- The junk values at the wild pool: t̂ᵢ(4) = 0 (division by zero). -/
private lemma cm_bh_four : bh1V (4 : ℚ) = 0 ∧ bh2V (4 : ℚ) = 0 := by
  have hden : pol2D.eval (4 : ℚ) = 0 := by rw [pol2D_eval]; norm_num
  unfold bh1V bh2V
  rw [hden, div_zero, div_zero]
  exact ⟨rfl, rfl⟩

/-- β_bdd bounds: t̂ᵢ(m) ∈ [0,1] at every natural m ≥ 2 (junk 0 at m = 4). -/
private lemma cm_bh_bdd {m : ℕ} (hm2 : 2 ≤ m) :
    (bh1V (m : ℚ) ∈ Set.Icc (0 : ℚ) 1) ∧ (bh2V (m : ℚ) ∈ Set.Icc (0 : ℚ) 1) := by
  by_cases hm4 : m = 4
  · subst hm4
    have h4 : ((4 : ℕ) : ℚ) = (4 : ℚ) := by norm_num
    rw [h4, cm_bh_four.1, cm_bh_four.2]
    exact ⟨⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩⟩
  · have hD := cm_D_ge_two hm2 hm4
    have hDpos : (0 : ℚ) < polD.eval (m : ℚ) := by linarith
    have h2D : pol2D.eval (m : ℚ) = 2 * polD.eval (m : ℚ) := by
      rw [pol2D_eval, polD_eval]
    have h2Dpos : (0 : ℚ) < pol2D.eval (m : ℚ) := by rw [h2D]; linarith
    have hT1 : polT1.eval (m : ℚ) = polD.eval (m : ℚ) + 1 := by
      rw [polT1_eval, polD_eval]
    have hT2 : polT2.eval (m : ℚ) = polD.eval (m : ℚ) - 1 := by
      rw [polT2_eval, polD_eval]
    constructor
    · unfold bh1V
      constructor
      · exact div_nonneg (by rw [hT1]; linarith) h2Dpos.le
      · rw [div_le_one h2Dpos, hT1, h2D]; linarith
    · unfold bh2V
      constructor
      · exact div_nonneg (by rw [hT2]; linarith) h2Dpos.le
      · rw [div_le_one h2Dpos, hT2, h2D]; linarith

/-! ## §5 The event cards (the interval partition of the 2m⁴-point box) -/

def kCardZ (m : ℕ) : ℤ := 16 * ((m : ℤ) - 2) * (m : ℤ) ^ 2 + 4 * ((m : ℤ) - 4) ^ 2
def t1CardZ (m : ℕ) : ℤ := ((m : ℤ) - 4) ^ 2 * ((m : ℤ) ^ 2 - 2) + 1
def t2CardZ (m : ℕ) : ℤ := ((m : ℤ) - 4) ^ 2 * ((m : ℤ) ^ 2 - 2) - 1
def kCard (m : ℕ) : ℕ := (kCardZ m).toNat
def t1Card (m : ℕ) : ℕ := (t1CardZ m).toNat
def t2Card (m : ℕ) : ℕ := (t2CardZ m).toNat
def aCard (m : ℕ) : ℕ := (((m : ℤ) - 4) ^ 2).toNat
def boxCard (m : ℕ) : ℕ := 2 * m ^ 4

private lemma cm_aCard_castQ (m : ℕ) : ((aCard m : ℕ) : ℚ) = ((m : ℚ) - 4) ^ 2 := by
  unfold aCard
  have hnn : (0 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 := sq_nonneg _
  have h1 : ((((m : ℤ) - 4) ^ 2).toNat : ℤ) = ((m : ℤ) - 4) ^ 2 := Int.toNat_of_nonneg hnn
  have h2 : ((((m : ℤ) - 4) ^ 2).toNat : ℚ) = ((((m : ℤ) - 4) ^ 2 : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) h1
  rw [h2]
  push_cast
  ring

private lemma cm_DZ_ge {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) :
    (2 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 * ((m : ℤ) ^ 2 - 2) := by
  have h1 : (1 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 := by
    have hsplit : (m : ℤ) - 4 ≤ -1 ∨ 1 ≤ (m : ℤ) - 4 := by omega
    rcases hsplit with h | h <;> nlinarith
  have h2 : (2 : ℤ) ≤ (m : ℤ) ^ 2 - 2 := by
    have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
    nlinarith
  nlinarith

private lemma cm_kCardZ_nonneg {m : ℕ} (hm2 : 2 ≤ m) : 0 ≤ kCardZ m := by
  unfold kCardZ
  have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
  nlinarith [sq_nonneg ((m : ℤ) - 4)]

private lemma cm_kCardZ_pos {m : ℕ} (hm2 : 2 ≤ m) : 0 < kCardZ m := by
  unfold kCardZ
  have hm : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
  by_cases h2 : m = 2
  · subst h2; norm_num
  · have : (3 : ℤ) ≤ (m : ℤ) := by
      have : 3 ≤ m := by omega
      exact_mod_cast this
    nlinarith [sq_nonneg ((m : ℤ) - 4)]

private lemma cm_t1CardZ_pos {m : ℕ} (hm2 : 2 ≤ m) : 0 < t1CardZ m := by
  unfold t1CardZ
  have hm : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
  have h2 : (0 : ℤ) ≤ (m : ℤ) ^ 2 - 2 := by nlinarith
  have h1 : (0 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg h1 h2]

private lemma cm_t2CardZ_pos {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) : 0 < t2CardZ m := by
  unfold t2CardZ
  have := cm_DZ_ge hm2 hm4
  linarith

/-- The exact tile: the three masses partition the box (ℤ-level ring identity). -/
private lemma cm_tileZ (m : ℕ) : kCardZ m + t1CardZ m + t2CardZ m = 2 * (m : ℤ) ^ 4 := by
  unfold kCardZ t1CardZ t2CardZ
  ring

private lemma cm_tile {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≠ 4) :
    kCard m + t1Card m + t2Card m = boxCard m := by
  have hk := cm_kCardZ_nonneg hm2
  have h1 := (cm_t1CardZ_pos hm2).le
  have h2 := (cm_t2CardZ_pos hm2 hm4).le
  have htile := cm_tileZ m
  have hcast : (2 : ℤ) * (m : ℤ) ^ 4 = ((2 * m ^ 4 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast] at htile
  unfold kCard t1Card t2Card boxCard
  omega

/-! ## §5' Interval-card lemmas on `Fin M` (the N2Sigmas idiom, local copies) -/

private lemma card_filter_fin_lt {M a : ℕ} (ha : a ≤ M) :
    (Finset.univ.filter (fun x : Fin M => x.1 < a)).card = a := by
  have h : Finset.univ.filter (fun x : Fin M => x.1 < a)
      = (Finset.Ico 0 a).attachFin
          (fun m hm => lt_of_lt_of_le (Finset.mem_Ico.mp hm).2 ha) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [h, Finset.card_attachFin, Nat.card_Ico, Nat.sub_zero]

private lemma card_filter_fin_ge (M b : ℕ) :
    (Finset.univ.filter (fun x : Fin M => b ≤ x.1)).card = M - b := by
  have h : Finset.univ.filter (fun x : Fin M => b ≤ x.1)
      = (Finset.Ico b M).attachFin (fun m hm => (Finset.mem_Ico.mp hm).2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
      Finset.mem_Ico]
    exact ⟨fun hb => ⟨hb, x.2⟩, fun h => h.1⟩
  rw [h, Finset.card_attachFin, Nat.card_Ico]

private lemma card_filter_fin_mid {M a b : ℕ} (hb : b ≤ M) :
    (Finset.univ.filter (fun x : Fin M => a ≤ x.1 ∧ x.1 < b)).card = b - a := by
  have h : Finset.univ.filter (fun x : Fin M => a ≤ x.1 ∧ x.1 < b)
      = (Finset.Ico a b).attachFin
          (fun m hm => lt_of_lt_of_le (Finset.mem_Ico.mp hm).2 hb) := by
    ext x
    simp [Finset.mem_attachFin, Finset.mem_Ico]
  rw [h, Finset.card_attachFin, Nat.card_Ico]

/-! ## §6 The measured side -/

/-- The block-1 cell masses (cells 0/1/2 = the k/t₁/t₂ intervals; cell 3 = the
ACTIVITY cell, mass 0 — it carries the (X−4)² activity polynomial and an EMPTY
height domain). -/
noncomputable def cmMass1 (c : ℕ) (q₀ : ℚ) : ℝ :=
  if c = 0 then ((kV q₀ : ℚ) : ℝ)
  else if c = 1 then ((t1V q₀ : ℚ) : ℝ)
  else if c = 2 then ((t2V q₀ : ℚ) : ℝ) else 0

/-- THE COUNTERMODEL MEASURED SIDE (the N2Carriers assembly idiom): boxes of
2Q⁴ points; block 1 carries four cells (three mass intervals tiling the box +
the activity cell); every other layer the single full-box mass-1 cell; the
block-1 state is active EXACTLY away from the wild pool 4. -/
noncomputable def cmM : MeasuredSide cmT where
  Pools := cmPoolsSet
  pools_prime_pow := fun _ hq₀ => hq₀
  pools_closed := by
    rintro q₀ ⟨p, hp, d, rfl⟩ δ
    exact ⟨p, hp, d * δ, by rw [PNat.mul_coe, pow_mul]⟩
  pools_infinite :=
    Set.infinite_of_injective_forall_mem
      (f := fun p : Nat.Primes => ((p : ℕ) : ℚ))
      (fun _ _ h => Subtype.ext (Nat.cast_injective h))
      (fun p => ⟨p, p.prop, 1, by rw [PNat.one_coe, pow_one]⟩)
  Box := fun q₀ _ => Fin (max 1 (2 * q₀.num.toNat ^ 4))
  finB := fun _ _ => inferInstance
  boxpos := fun _ _ => ⟨⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩⟩
  Cell := fun e _ => Fin (if e = 1 then 4 else 1)
  finC := fun _ _ => inferInstance
  cellOut := fun _ _ c => (⟨c.1 % 3, by omega⟩ : Fin 3)
  Rep := fun _ _ => Fin 1
  rep_ne := fun _ _ _ => ⟨0⟩
  cellLvl := fun _ _ _ => 0
  cellInst := fun e _ c q₀ _ =>
    if e = 1 ∧ c.1 = 3 then
      Finset.univ.filter (fun y => y.1 < aCard q₀.num.toNat)
    else {⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩}
  Hgt := ℕ
  HDom := fun e _ c => if e = 1 ∧ c.1 = 3 then (∅ : Set ℕ) else {0}
  gwt := fun e _ c h q₀ => if h = 0 then (if e = 1 then cmMass1 c.1 q₀ else 1) else 0
  cellEvt := fun e _ _ c h q₀ _ =>
    if h = 0 then
      (if e = 1 then
        (if c.1 = 0 then Finset.univ.filter (fun y => y.1 < kCard q₀.num.toNat)
         else if c.1 = 1 then Finset.univ.filter (fun y =>
           kCard q₀.num.toNat ≤ y.1 ∧ y.1 < kCard q₀.num.toNat + t1Card q₀.num.toNat)
         else if c.1 = 2 then Finset.univ.filter (fun y =>
           kCard q₀.num.toNat + t1Card q₀.num.toNat ≤ y.1)
         else ∅)
       else Finset.univ)
    else ∅
  μcell := fun e _ _ c q₀ => if e = 1 then cmMass1 c.1 q₀ else 1
  rowVal := fun e _ o q₀ => if e = 1 then cmMass1 o.1 q₀ else if o.1 = 0 then 1 else 0
  kstep := fun k e _ _ q₀ => (if e = 1 ∧ q₀ ≠ 4 then ((kV q₀ : ℚ) : ℝ) else 0) ^ k
  activeState := fun q₀ e _ => e = 1 → q₀ ≠ 4
  decA := fun q₀ e _ =>
    if he : e = 1 then
      (if h4 : q₀ = 4 then isFalse (fun hf => (hf he) h4) else isTrue (fun _ => h4))
    else isTrue (fun h => absurd h he)
  EntShape := fun _ _ => Unit
  finE := fun _ _ => inferInstance
  hent := fun _ _ _ => 0
  Went := fun _ _ _ => 0
  entEvtH := fun _ _ _ h _ _ => if h = 0 then Finset.univ else ∅
  ιDom := fun _ _ _ => {0}
  ιshH := fun _ _ _ h _ => if h = 0 then 1 else 0
  ιsh := fun _ _ _ _ => 1
  ιval := fun _ _ _ => 1
  entCount := fun _ _ _ _ => 1
  entLvl := fun _ _ _ => 0
  entInst := fun _ _ _ _ _ => {⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩}
  markedVal := fun _ _ => 1

/-- The active locus of the instance: the block-1 state is inactive EXACTLY at 4. -/
private lemma cm_active_iff (q₀ : ℚ) (e : ℕ) (τ : cmT.State e) :
    cmM.activeState q₀ e τ ↔ (e = 1 → q₀ ≠ 4) := Iff.rfl

/-- Box-typed interval-card wrappers (the n2_box_filter idiom). -/
private lemma cm_box_card (q₀ : ℚ) (N : ℕ) :
    Fintype.card (cmM.Box q₀ N) = max 1 (2 * q₀.num.toNat ^ 4) := Fintype.card_fin _

private lemma cm_box_filter_lt (q₀ : ℚ) (N : ℕ) {a : ℕ}
    (ha : a ≤ max 1 (2 * q₀.num.toNat ^ 4)) :
    (Finset.univ.filter (fun y : cmM.Box q₀ N => y.1 < a)).card = a :=
  card_filter_fin_lt ha

private lemma cm_box_filter_mid (q₀ : ℚ) (N : ℕ) {a b : ℕ}
    (hb : b ≤ max 1 (2 * q₀.num.toNat ^ 4)) :
    (Finset.univ.filter (fun y : cmM.Box q₀ N => a ≤ y.1 ∧ y.1 < b)).card = b - a :=
  card_filter_fin_mid hb

private lemma cm_box_filter_ge (q₀ : ℚ) (N : ℕ) (b : ℕ) :
    (Finset.univ.filter (fun y : cmM.Box q₀ N => b ≤ y.1)).card
      = max 1 (2 * q₀.num.toNat ^ 4) - b :=
  card_filter_fin_ge _ b

/-! ## §7 OKat/evalAt helpers (N2Sigmas §F' idiom, local copies) -/

private lemma cm_okat_alg (r : Polynomial ℚ) (q₀ : ℚ) : aQ r ∈ OKat q₀ := by
  rw [mem_OKat_iff, RatFunc.denom_algebraMap]
  simp

private lemma cm_evalAt_alg (r : Polynomial ℚ) (q₀ : ℚ)
    (hok : aQ r ∈ OKat q₀) :
    (evalAt q₀ ⟨aQ r, hok⟩ : ℚ) = r.eval q₀ := by
  show RatFunc.eval (RingHom.id ℚ) q₀ (aQ r) = r.eval q₀
  rw [RatFunc.eval_algebraMap]
  simp [Polynomial.eval₂_id]

private lemma cm_okat_div {p₁ p₂ : Polynomial ℚ} {q₀ : ℚ} (h₂ : p₂.eval q₀ ≠ 0) :
    (aQ p₁ / aQ p₂) ∈ OKat q₀ := by
  rw [mem_OKat_iff]
  intro h0
  obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd p₁ p₂
  rw [hc, Polynomial.eval_mul, h0, zero_mul] at h₂
  exact h₂ rfl

private lemma cm_evalAt_div {p₁ p₂ : Polynomial ℚ} {q₀ : ℚ} (h₂ : p₂.eval q₀ ≠ 0)
    (hok : (aQ p₁ / aQ p₂) ∈ OKat q₀) :
    (evalAt q₀ ⟨aQ p₁ / aQ p₂, hok⟩ : ℚ) = p₁.eval q₀ / p₂.eval q₀ := by
  have hp₂ : p₂ ≠ 0 := fun h0 => h₂ (by rw [h0]; simp)
  have halg : aQ p₂ ≠ 0 := RatFunc.algebraMap_ne_zero hp₂
  have hmul : (⟨aQ p₁ / aQ p₂, hok⟩ : OKat q₀) * ⟨aQ p₂, cm_okat_alg p₂ q₀⟩
      = ⟨aQ p₁, cm_okat_alg p₁ q₀⟩ :=
    Subtype.ext (div_mul_cancel₀ _ halg)
  have hev := congrArg (fun z => (evalAt q₀ z : ℚ)) hmul
  simp only [map_mul] at hev
  rw [cm_evalAt_alg, cm_evalAt_alg] at hev
  rw [eq_div_iff h₂]
  exact hev

/-! ## §8 The rationality burdens -/

/-- The (iv)-POLY presentation num/den with trivial count parts and a chosen
`degBoundS` slot (the block-1 `Wstate = 2` pin rides the BOUND, not the data). -/
private noncomputable def pgDivB (num den : Polynomial ℚ) (qp bS : ℕ)
    (hdvd : den ∣ Polynomial.X ^ qp) : PolyGeom where
  countT := 1
  degBoundT := 0
  degT_le := by simp
  countS := 1
  degBoundS := bS
  degS_le := by simp
  geom := aQ num / aQ den
  qpow := qp
  geomDenoms := ∅
  geom_denom_dvd := by simpa using (RatFunc.denom_div_dvd num den).trans hdvd

private lemma pgDivB_val (num den : Polynomial ℚ) (qp bS : ℕ)
    (hdvd : den ∣ Polynomial.X ^ qp) :
    (pgDivB num den qp bS hdvd).val = aQ num / aQ den := by
  simp [pgDivB, PolyGeom.val]

/-- The constant presentation with value c. -/
private noncomputable def pgConst (c : ℚ) (bS : ℕ) : PolyGeom :=
  pgDivB (Polynomial.C c) 1 0 bS (one_dvd _)

private lemma pgConst_val (c : ℚ) (bS : ℕ) : (pgConst c bS).val = aQ (Polynomial.C c) := by
  rw [pgConst, pgDivB_val, map_one, div_one]

private lemma pgConst_ok {c : ℚ} {bS : ℕ} {q₀ : ℚ} : (pgConst c bS).val ∈ OKat q₀ := by
  rw [pgConst_val]; exact cm_okat_alg _ _

private lemma pgConst_evalAt {c : ℚ} {bS : ℕ} {q₀ : ℚ}
    (hok : (pgConst c bS).val ∈ OKat q₀) : (evalAt q₀ ⟨(pgConst c bS).val, hok⟩ : ℚ) = c := by
  have hval : (⟨(pgConst c bS).val, hok⟩ : OKat q₀)
      = ⟨aQ (Polynomial.C c), cm_okat_alg _ _⟩ := Subtype.ext (pgConst_val c bS)
  rw [hval, cm_evalAt_alg]
  exact Polynomial.eval_C

private lemma pol2B_dvd : pol2B ∣ Polynomial.X ^ 4 := by
  refine ⟨Polynomial.C (1 / 2 : ℚ), ?_⟩
  have h2 : (2 : Polynomial ℚ) * Polynomial.C (1 / 2 : ℚ) = 1 := by
    rw [show (2 : Polynomial ℚ) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm,
      ← Polynomial.C_mul]
    norm_num
  calc Polynomial.X ^ 4 = ((2 : Polynomial ℚ) * Polynomial.C (1 / 2 : ℚ)) * Polynomial.X ^ 4 := by
        rw [h2, one_mul]
    _ = pol2B * Polynomial.C (1 / 2 : ℚ) := by unfold pol2B; ring

private noncomputable def pgK : PolyGeom := pgDivB polK polB 4 2 (by unfold polB; exact dvd_rfl)
private noncomputable def pgT1 : PolyGeom := pgDivB polT1 pol2B 4 2 pol2B_dvd
private noncomputable def pgT2 : PolyGeom := pgDivB polT2 pol2B 4 2 pol2B_dvd

private lemma pgK_val : pgK.val = aQ polK / aQ polB := by
  unfold pgK; exact pgDivB_val _ _ _ _ _
private lemma pgT1_val : pgT1.val = aQ polT1 / aQ pol2B := by
  unfold pgT1; exact pgDivB_val _ _ _ _ _
private lemma pgT2_val : pgT2.val = aQ polT2 / aQ pol2B := by
  unfold pgT2; exact pgDivB_val _ _ _ _ _

/-- The tg presentation roster: block 1 = (k, t₁, t₂); every other layer the
(1, 0, 0) padding (the split outcome's tg slot is never interpolated). -/
private noncomputable def cmTg (e : ℕ) (o : Fin 3) : PolyGeom :=
  if e = 1 then (if o = 0 then pgK else if o = 1 then pgT1 else pgT2)
  else if o = 0 then pgConst 1 0 else pgConst 0 0

/-- The activity polynomial roster: the block-1 activity cell carries (X−4)². -/
private noncomputable def cmCellP (e : ℕ) (c : ℕ) : Polynomial ℚ :=
  if e = 1 ∧ c = 3 then (Polynomial.X - 4) ^ 2 else 1

private lemma cm_actPoly_eval (x : ℚ) :
    ((Polynomial.X - 4 : Polynomial ℚ) ^ 2).eval x = (x - 4) ^ 2 := by simp

private lemma cm_actPoly_deg : ((Polynomial.X - 4 : Polynomial ℚ) ^ 2).natDegree = 2 := by
  rw [show (4 : Polynomial ℚ) = Polynomial.C 4 from (map_ofNat Polynomial.C 4).symm,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]

private lemma cm_actPoly_ne : ((Polynomial.X - 4 : Polynomial ℚ) ^ 2) ≠ 0 := by
  rw [show (4 : Polynomial ℚ) = Polynomial.C 4 from (map_ofNat Polynomial.C 4).symm]
  exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 4)

/-- Pool denominators never vanish. -/
private lemma cm_polB_eval_ne {q₀ : ℚ} (hq : q₀ ∈ cmPoolsSet) : polB.eval q₀ ≠ 0 := by
  obtain ⟨m, hm2, rfl⟩ := cm_pool_nat hq
  rw [polB_eval]
  exact (cm_x4_pos hm2).ne'

private lemma cm_pol2B_eval_ne {q₀ : ℚ} (hq : q₀ ∈ cmPoolsSet) : pol2B.eval q₀ ≠ 0 := by
  obtain ⟨m, hm2, rfl⟩ := cm_pool_nat hq
  rw [pol2B_eval]
  have := cm_x4_pos hm2
  positivity

/-! ## §8' Route facts -/

private lemma cm_route1_cases (τ : cmT.State 1) (o : Fin 3) :
    (o = 0 ∧ routeOf (cmT.odata 1 τ o) = .kcol) ∨
    (o = 1 ∧ routeOf (cmT.odata 1 τ o) = .termFin ∧ (cmT.odata 1 τ o).verdicts = {w11}) ∨
    (o = 2 ∧ routeOf (cmT.odata 1 τ o) = .termFin ∧ (cmT.odata 1 τ o).verdicts = {w12}) := by
  rcases o with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

private lemma cm_route1_ne_split (τ : cmT.State 1) (o : Fin 3) :
    routeOf (cmT.odata 1 τ o) ≠ .split := by
  rcases cm_route1_cases τ o with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    (rw [h]; exact fun hc => Route.noConfusion hc)

private lemma cm_route2_cases (τ : cmT.State 2) (o : Fin 3) :
    (o = 0 ∧ routeOf (cmT.odata 2 τ o) = .split) ∨
    (o ≠ 0 ∧ routeOf (cmT.odata 2 τ o) = .termFin ∧ (cmT.odata 2 τ o).verdicts = {w11}) := by
  rcases o with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨fun h => absurd (congrArg Fin.val h) (by norm_num), rfl, rfl⟩
  · exact Or.inr ⟨fun h => absurd (congrArg Fin.val h) (by norm_num), rfl, rfl⟩

private lemma cm_route_pad {e : ℕ} (h1 : e ≠ 1) (h2 : e ≠ 2) (τ : cmT.State e)
    (o : Fin 3) :
    routeOf (cmT.odata e τ o) = .termFin ∧ (cmT.odata e τ o).verdicts = {w11} := by
  rw [cm_odata_pad h1 h2]
  exact ⟨rfl, rfl⟩

private lemma cm_route_ne_split_of_ne {e : ℕ} (h1 : e ≠ 1) (h2 : e ≠ 2)
    (τ : cmT.State e) (o : Fin 3) : routeOf (cmT.odata e τ o) ≠ .split := by
  rw [(cm_route_pad h1 h2 τ o).1]
  exact fun hc => Route.noConfusion hc

/-! ## §8'' The RatBurdens laws -/

private lemma cm_tg_ok (e : ℕ) (o : Fin 3) {q₀ : ℚ} (hq : q₀ ∈ cmPoolsSet) :
    (cmTg e o).val ∈ OKat q₀ := by
  unfold cmTg
  split_ifs with h1 h2 h3 h4
  · rw [pgK_val]; exact cm_okat_div (cm_polB_eval_ne hq)
  · rw [pgT1_val]; exact cm_okat_div (cm_pol2B_eval_ne hq)
  · rw [pgT2_val]; exact cm_okat_div (cm_pol2B_eval_ne hq)
  · exact pgConst_ok
  · exact pgConst_ok

/-- evalAt of the tg presentations = the measured rows (any OKat witness). -/
private lemma cm_tg_evalAt (e : ℕ) (τ : cmT.State e) (o : Fin 3) {q₀ : ℚ}
    (hq : q₀ ∈ cmPoolsSet) (hok : (cmTg e o).val ∈ OKat q₀) :
    ((evalAt q₀ ⟨(cmTg e o).val, hok⟩ : ℚ) : ℝ) = cmM.rowVal e τ o q₀ := by
  by_cases he : e = 1
  · subst he
    have hrow : cmM.rowVal 1 τ o q₀ = cmMass1 o.1 q₀ := rfl
    rw [hrow]
    rcases o with ⟨v, hv⟩
    interval_cases v
    · have hval : (⟨(cmTg 1 ⟨0, hv⟩).val, hok⟩ : OKat q₀)
          = ⟨aQ polK / aQ polB, cm_okat_div (cm_polB_eval_ne hq)⟩ :=
        Subtype.ext pgK_val
      rw [hval, cm_evalAt_div (cm_polB_eval_ne hq)]
      rfl
    · have hval : (⟨(cmTg 1 ⟨1, hv⟩).val, hok⟩ : OKat q₀)
          = ⟨aQ polT1 / aQ pol2B, cm_okat_div (cm_pol2B_eval_ne hq)⟩ :=
        Subtype.ext pgT1_val
      rw [hval, cm_evalAt_div (cm_pol2B_eval_ne hq)]
      rfl
    · have hval : (⟨(cmTg 1 ⟨2, hv⟩).val, hok⟩ : OKat q₀)
          = ⟨aQ polT2 / aQ pol2B, cm_okat_div (cm_pol2B_eval_ne hq)⟩ :=
        Subtype.ext pgT2_val
      rw [hval, cm_evalAt_div (cm_pol2B_eval_ne hq)]
      rfl
  · have hrow : cmM.rowVal e τ o q₀ = if o.1 = 0 then 1 else 0 := if_neg he
    rw [hrow]
    by_cases ho : o = 0
    · subst ho
      have htg : cmTg e 0 = pgConst 1 0 := by unfold cmTg; rw [if_neg he, if_pos rfl]
      have hval : (⟨(cmTg e 0).val, hok⟩ : OKat q₀)
          = ⟨(pgConst 1 0).val, pgConst_ok⟩ := Subtype.ext (congrArg PolyGeom.val htg)
      rw [hval, pgConst_evalAt]
      norm_num
    · have htg : cmTg e o = pgConst 0 0 := by unfold cmTg; rw [if_neg he, if_neg ho]
      have hval : (⟨(cmTg e o).val, hok⟩ : OKat q₀)
          = ⟨(pgConst 0 0).val, pgConst_ok⟩ := Subtype.ext (congrArg PolyGeom.val htg)
      have ho1 : o.1 ≠ 0 := fun h => ho (Fin.ext h)
      rw [hval, pgConst_evalAt, if_neg ho1]
      norm_num

/-! ## §9 THE RatBurdens record -/

noncomputable def cmRB : RatBurdens cmT cmM where
  tgP := fun e _ o => cmTg e o
  jP := fun e _ _ => pgConst 1 (if e = 1 then 2 else 0)
  ιP := fun _ _ _ => pgConst 1 0
  tg_ok := fun e τ o q₀ hq => cm_tg_ok e o hq
  j_ok := fun _ _ _ _ _ => pgConst_ok
  ι_ok := fun _ _ _ _ _ => pgConst_ok
  tg_interp := fun e τ o q₀ h _ => cm_tg_evalAt e τ o h _
  j_interp := fun e τ o q₀ h hroute => by
    rw [pgConst_evalAt]
    -- a split route forces e = 2, o = 0, where the row mass is 1
    by_cases he : e = 1
    · subst he; exact absurd hroute (cm_route1_ne_split τ o)
    · by_cases he2 : e = 2
      · subst he2
        rcases cm_route2_cases τ o with ⟨ho, -⟩ | ⟨-, hr, -⟩
        · have ho1 : o.1 = 0 := congrArg Fin.val ho
          have hrow : cmM.rowVal 2 τ o q₀ = 1 := by
            show (if (2 : ℕ) = 1 then cmMass1 o.1 q₀ else if o.1 = 0 then 1 else 0) = 1
            rw [if_neg (by norm_num : ¬(2 : ℕ) = 1), if_pos ho1]
          rw [hrow]
          norm_num
        · rw [hr] at hroute; exact absurd hroute (fun hc => Route.noConfusion hc)
      · exact absurd hroute (cm_route_ne_split_of_ne he he2 τ o)
  ι_interp := fun e τ ε q₀ h => by
    rw [pgConst_evalAt]
    show ((1 : ℚ) : ℝ) = 1
    norm_num
  ι_countS_one := fun _ _ _ => rfl
  ι_count := fun e τ ε q₀ _ => by
    show ((1 : Polynomial ℚ).eval q₀ : ℚ) = ((1 : ℕ) : ℚ)
    simp
  tg_degT := fun e τ o => by unfold cmTg; split_ifs <;> rfl
  tg_degS := fun e τ o => by
    show (cmTg e o).degBoundS = (if e = 1 then 2 else 0)
    unfold cmTg
    split_ifs <;> rfl
  j_degT := fun _ _ _ => rfl
  j_degS := fun _ _ _ => rfl
  ι_degT := fun _ _ _ => rfl
  ι_degS := fun _ _ _ => rfl
  cellP := fun e _ c => cmCellP e c.1
  cellP_deg := fun e τ c => by
    show (cmCellP e c.1).natDegree ≤ (if e = 1 then 2 else 0)
    unfold cmCellP
    by_cases h : e = 1 ∧ c.1 = 3
    · rw [if_pos h, cm_actPoly_deg, if_pos h.1]
    · rw [if_neg h]
      simp
  cellP_nonzero := fun e _ τ c => by
    show cmCellP e c.1 ≠ 0
    unfold cmCellP
    by_cases h : e = 1 ∧ c.1 = 3
    · rw [if_pos h]; exact cm_actPoly_ne
    · rw [if_neg h]; exact one_ne_zero
  cellP_count := fun e τ c q₀ hq hact => by
    obtain ⟨m, hm2, rfl⟩ := cm_pool_nat hq
    have hQ : (((m : ℚ)).num.toNat) = m := cm_pool_toNat m
    show ((cmCellP e c.1).eval (m : ℚ) : ℚ) = _
    unfold cmCellP
    by_cases h : e = 1 ∧ c.1 = 3
    · rw [if_pos h, cm_actPoly_eval]
      have hinst : cmM.cellInst e τ c (m : ℚ) (cmM.cellLvl e τ c)
          = Finset.univ.filter (fun y => y.1 < aCard (((m : ℚ)).num.toNat)) := if_pos h
      rw [hinst]
      have hle : aCard (((m : ℚ)).num.toNat) ≤ max 1 (2 * (((m : ℚ)).num.toNat) ^ 4) := by
        rw [hQ]
        refine le_trans ?_ (le_max_right _ _)
        have hbound : ((m : ℤ) - 4) ^ 2 ≤ 2 * (m : ℤ) ^ 4 := by
          have hm : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
          nlinarith [sq_nonneg ((m : ℤ) - 4), sq_nonneg (m : ℤ), sq_nonneg ((m : ℤ) + 1),
            sq_nonneg ((m : ℤ) ^ 2 - 2)]
        have hcast : ((2 * m ^ 4 : ℕ) : ℤ) = 2 * (m : ℤ) ^ 4 := by push_cast; ring
        unfold aCard
        omega
      rw [cm_box_filter_lt _ _ hle, hQ]
      unfold aCard
      have hnn : (0 : ℤ) ≤ ((m : ℤ) - 4) ^ 2 := sq_nonneg _
      push_cast [Int.toNat_of_nonneg hnn]
      ring
    · rw [if_neg h]
      have hinst : cmM.cellInst e τ c (m : ℚ) (cmM.cellLvl e τ c)
          = {⟨0, Nat.lt_of_lt_of_le Nat.one_pos (le_max_left _ _)⟩} := if_neg h
      rw [hinst]
      simp
  act_iff := fun q₀ hq e he τ => by
    constructor
    · intro hact c
      show (cmCellP e c.1).eval q₀ ≠ 0
      unfold cmCellP
      by_cases h : e = 1 ∧ c.1 = 3
      · rw [if_pos h, cm_actPoly_eval]
        exact pow_ne_zero _ (sub_ne_zero.mpr (hact h.1))
      · rw [if_neg h]
        simp
    · intro hall he1
      subst he1
      have hc := hall ⟨3, by norm_num⟩
      intro h4
      apply hc
      show (cmCellP 1 (3 : ℕ)).eval q₀ = 0
      unfold cmCellP
      rw [if_pos ⟨rfl, rfl⟩, cm_actPoly_eval, h4]
      norm_num
  jPCell := fun _ _ _ => pgConst 1 0
  jcell_ok := fun _ _ _ _ _ => pgConst_ok
  jcell_interp := fun e τ c x q₀ h hroute hact => by
    rw [pgConst_evalAt]
    have he : e ≠ 1 := by
      intro he1
      subst he1
      exact cm_route1_ne_split τ (cmM.cellOut 1 τ c) hroute
    have hμ : cmM.μcell e τ x c q₀ = 1 := if_neg he
    rw [hμ]
    norm_num
  jcell_sum := fun e τ o hroute => by
    have he : e ≠ 1 := by
      intro he1; subst he1; exact cm_route1_ne_split τ o hroute
    have he2 : e = 2 := by
      by_contra he2
      exact cm_route_ne_split_of_ne he he2 τ o hroute
    subst he2
    have ho : o = 0 := by
      rcases cm_route2_cases τ o with ⟨ho, -⟩ | ⟨-, hr, -⟩
      · exact ho
      · rw [hr] at hroute; exact absurd hroute (fun hc => Route.noConfusion hc)
    subst ho
    have hcells : cmM.cells 2 τ 0 = Finset.univ := by
      ext c
      simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
        Finset.mem_univ, iff_true]
      have hc1 : c.1 < 1 := by
        have := c.2
        simpa using this
      apply Fin.ext
      show c.1 % 3 = 0
      omega
    rw [hcells]
    have huniv : (Finset.univ : Finset (cmM.Cell 2 τ)) = {⟨0, by norm_num⟩} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      apply Fin.ext
      have := c.2
      simpa using this
    rw [huniv, Finset.sum_singleton]

end LeanUrat.MovesU.R2Neg
