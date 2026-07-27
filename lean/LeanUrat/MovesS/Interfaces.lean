/-
MovesS/Interfaces — §2.D's hypothesis interfaces: RS1Meas, RS1Bundle, RS4Chain,
ReadOffBundle (R25/R29: THE one canonical location; elaborated AFTER the S2/S4
definition units so `evalRe`/`Rsh`/`markedPairing`/`bhatMeas` are in scope).
The §W4-SYNC seam entries (W-pins, TreeIface/FiberIface/ReadLedger, the packages)
are NOT built at E-phase — this file contains NOTHING from that section.
Blueprint: lean/notes/MOVESS_LEAN_BLUEPRINT_2026-07-28.md (REV 13) §2.D.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef
import LeanUrat.MovesS.EvalReDef
import LeanUrat.MovesS.ConsumedDeltas
import LeanUrat.MovesS.BlockSolve
import LeanUrat.MovesS.BlockSolveTot
import LeanUrat.MovesS.RshDef
import LeanUrat.MovesS.MarkedDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

-- The abstract box carrier has no computable equality; `shevt_grouping`'s biUnion
-- takes the classical one (proof-irrelevant, last-resort priority).
attribute [local instance 0] Classical.decEq

variable {n : ℕ}

/-- The RAW measured family (R32): NO hypothesis fields — the carrier the W-2/W-3
pins are stated OVER, so the pins are obligations, not projections.  βmeas is the
h_ent-indexed measured conditional subtree value (owner [3t]). -/
structure RS1Meas (T : TableShape n) (M : MeasuredSide T) where
  βmeas : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ
  β_bdd : ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h_ent τ σ' q₀ ∈ Set.Icc (0 : ℝ) 1
  βfull : ∀ e, e ∈ Finset.Icc 1 n → ℕ → ∀ τ : T.State e, Multiset T.VType → ℚ → ℝ

/-- RS.1's interface — NO symbolic β input (R8/R2-9): measured objects only.
Instantiating this at wave 4 requires PROVING the pinned W-2/W-3 for the raw
family from their displayed packages (R32) — the fields cannot be self-supplied.
`xrb` is (XRB) CL-9 OPEN, POINTWISE AT POOLS (R40); `recursion_meas` is
ACTIVITY-GUARDED (R16(i)) — junk-block rows at wild pools make NO demand
(det(I − D_{q₀}) = 0 stays a tolerated FINDING); discharge = the pinned W-3. -/
structure RS1Bundle (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    extends RS1Meas T M where
  xrb : ∀ e (he : e ∈ Finset.Icc 1 n) (h h' : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βmeas e he h τ σ' q₀ = βmeas e he h' τ σ' q₀
  recursion_meas : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools → M.activeState q₀ e τ →
    ∀ h_ent : ℕ, βmeas e he h_ent τ σ' q₀
      = evalRe T M RB hdc e he τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
  nsNull : Prop
  rexact : nsNull → ∀ e (he : e ∈ Finset.Icc 1 n) (h_ent : ℕ) (τ : T.State e)
    (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀

/-- RS.4's chain — the FULL displayed inherited set as explicit components (R2-19),
σ-index = verdict multisets (R2-11).  `pools_e0` is RE-SCOPED to all-active BASE
pools (R51); `legs_reg` carries CL-1's full per-pool quantifier at EVERY base prime
(R21); `wsh_ok` is denominator regularity ONLY (R53) — CL-17(ii)'s production burden
is the seam pin W17ii (S-8), its inheritance the NAMED TYPED field `wsh17_pin`
(R57): wave 4 instantiates it with W17ii's statement; U-28 takes `h17 : C.wsh17_pin`
as an explicit premise; NO unconditional marking while it is open. -/
structure RS4Chain (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e)
    (F : ShapeFam T) where
  L : LedgerIV T M
  B : RS1Bundle T M RB hdc hK
  hns : B.nsNull
  PrimePools : Set ℚ
  prime_sub : PrimePools ⊆ M.Pools
  prime_base : ∀ q₀, q₀ ∈ PrimePools ↔ ∃ p : ℕ, p.Prime ∧ q₀ = (p : ℚ)
  pools_e0 : ∀ e (he : e ∈ Finset.Icc 1 n), ∀ q₀ ∈ PrimePools ∩ allActivePools M,
    Nonempty (PoolHyp T M RB e (hK e he) q₀)
  legs_reg : ∀ p : ℕ, (p : ℚ) ∈ PrimePools → RegP T M RB p hK F
  Sigmas : Finset (Multiset T.VType)
  sig_exact : ∀ σ, σ ∈ Sigmas ↔ (σ.map fun v => ((T.vdeg v : ℕ))).sum = n
  WshP : Shape T → PolyGeom
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, (WshP Ŝ).val ∈ OKat q₀
  wsh17_pin : Prop
  WshVal : Shape T → ℚ → ℝ
  wsh_interp : ∀ Ŝ (hŜ : Ŝ ∈ F.Sh), ∀ q₀ (h : q₀ ∈ M.Pools),
    ((evalAt q₀ ⟨(WshP Ŝ).val, wsh_ok Ŝ hŜ q₀ h⟩ : ℚ) : ℝ) = WshVal Ŝ q₀
  wshval_bdd : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, WshVal Ŝ q₀ ∈ Set.Icc (0 : ℝ) 1
  -- TYPED SHALLOW CARRIERS (R34 — fields, not prose):
  shDom  : Shape T → Set M.Hgt
  shEvtH : Shape T → M.Hgt → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  visH   : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset M.Hgt
  shEvt  : Shape T → ∀ (q₀ : ℚ) (N : ℕ), Finset (M.Box q₀ N)
  shWeightH : Shape T → M.Hgt → ℚ → ℝ
  shevt_grouping : ∀ Ŝ (q₀ : ℚ) (N : ℕ),
    shEvt Ŝ q₀ N = (visH Ŝ q₀ N).biUnion (fun h => shEvtH Ŝ h q₀ N)
  shDom_ne : ∀ Ŝ ∈ F.Sh, (shDom Ŝ).Nonempty
  sh_realized : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ allActivePools M,
    ∃ N₀, ∀ N ≥ N₀, (shEvt Ŝ q₀ N).Nonempty
  shweight_card : ∀ Ŝ ∈ F.Sh, ∀ h : M.Hgt, h ∈ shDom Ŝ → ∀ q₀ ∈ M.Pools,
    ∃ N₀, ∀ N ≥ N₀, shWeightH Ŝ h q₀ * (Fintype.card (M.Box q₀ N) : ℝ)
      = ((shEvtH Ŝ h q₀ N).card : ℝ)
  wshval_card : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, ∃ N₀, ∀ N ≥ N₀,
    WshVal Ŝ q₀ * (Fintype.card (M.Box q₀ N) : ℝ) = ((shEvt Ŝ q₀ N).card : ℝ)
  Rval : Multiset T.VType → ℚ → ℝ
  r_bdd : ∀ σ (q₀ : ℚ), q₀ ∈ M.Pools → Rval σ q₀ ∈ Set.Icc (0 : ℝ) 1
  decidedTotal : ℚ → ℝ
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1
  rs1_equates : ∀ p ∈ PrimePools, (∑ σ ∈ Sigmas, Rval σ p) = decidedTotal p
  rsh_interp : ∀ σ ∈ Sigmas, ∀ p ∈ PrimePools, ∀ hdet : DetHyp T RB hK,
    ∃ hok : Rsh T M RB hdc hK hdet F WshP σ ∈ OKat p,
      ((evalAt p ⟨Rsh T M RB hdc hK hdet F WshP σ, hok⟩ : ℚ) : ℝ) = Rval σ p

/-- R23: the read-off bundle U-24b consumes — coordinate coverage as TYPED DATA.
EVERY e ∈ Icc 1 n, EVERY τA : Act (= every τ — the pools are all-active), EVERY σ',
every h_ent: total coordinate coverage, auditable from the type. -/
structure ReadOffBundle {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (S : Set ℚ) (hS : S ⊆ allActivePools M) (B : RS1Bundle T M RB hdc hK)
    (hdet : DetHyp T RB hK) where
  pkg : ∀ q₀, q₀ ∈ S → ∀ e (he : e ∈ Finset.Icc 1 n), PoolHyp T M RB e (hK e he) q₀
  read : ∀ q₀ (hq : q₀ ∈ S), ∀ e (he : e ∈ Finset.Icc 1 n),
    ∀ τA : (pkg q₀ hq e he).Act, ∀ σ' : Multiset T.VType, ∀ h_ent : ℕ,
    AVAgree (pkg q₀ hq e he) (blockSolve T RB hdc hK hdet e he (↑τA) σ')
      (bhatMeas (pkg q₀ hq e he) (fun e' he' => B.βmeas e' he' h_ent) σ') τA

end LeanUrat.MovesS
