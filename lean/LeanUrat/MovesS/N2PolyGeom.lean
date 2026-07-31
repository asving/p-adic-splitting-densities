/-
Unit `n2_polygeom_data` (medium; S5 construction batch) — the RatBurdens instance
with the three PolyGeom presentations in the CORRECTED form (R30):
q⁻³ (qpow 3, geomDenoms ∅) · 1 − q⁻¹ = (X−1)/X (qpow 1) · q⁻¹ − q⁻³ = (X²−1)/X³
(qpow 3) — all inhabit PolyGeom under the restored X^b · ∏(1 − X^a) law.

`n2RB` is assembled by obligation group (the `n2M` pattern of N2Carriers.lean):
this unit fills the tg/j/ι presentation DATA, the OK laws (`n2_ok`'s fields), the
vacuous split-interpolation law, the degree pins (`n2_degpins_*`'s fields), the
ι countS pin, and the cellP ≡ 1 data with its degree/nonzero laws.  The five
remaining proof fields (`tg_interp`, `ι_interp`, `ι_count`, `cellP_count`,
`act_iff`) are owned by `n2_interp_tg`/`n2_interp_iota`/`n2_activity` and are
UNPROVABLE until their `n2M` inputs (rowVal/ιsh/entCount/cellInst/activeState)
are filled by `n2_events`/`n2_ent_flow`/`n2_carriers` in N2Carriers.lean.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

/-! ### The presentation constructors -/

/-- The generic (iv)-POLY presentation with trivial count parts (the n = 2 table
has `Wloc ≡ 0`, `Wstate ≡ 0`, so both count polynomials are the constant 1 with
degree bound 0) and geometric part `num / den` with `den ∣ X^qp`
(`geomDenoms = ∅`). -/
private noncomputable def pgDiv (num den : Polynomial ℚ) (qp : ℕ)
    (hdvd : den ∣ Polynomial.X ^ qp) : PolyGeom where
  countT := 1
  degBoundT := 0
  degT_le := by simp
  countS := 1
  degBoundS := 0
  degS_le := by simp
  geom := algebraMap (Polynomial ℚ) Qq num / algebraMap (Polynomial ℚ) Qq den
  qpow := qp
  geomDenoms := ∅
  geom_denom_dvd := by simpa using (RatFunc.denom_div_dvd num den).trans hdvd

/-- o_K: q⁻³ — qpow 3, geomDenoms ∅ (R30's corrected first presentation). -/
private noncomputable def pgK : PolyGeom :=
  pgDiv 1 (Polynomial.X ^ 3) 3 dvd_rfl
/-- o_spl: 1 − q⁻¹ = (X − 1)/X — qpow 1. -/
private noncomputable def pgSpl : PolyGeom :=
  pgDiv (Polynomial.X - 1) Polynomial.X 1 ⟨1, by ring⟩
/-- o_in: q⁻¹ − q⁻³ = (X² − 1)/X³ — qpow 3. -/
private noncomputable def pgIn : PolyGeom :=
  pgDiv (Polynomial.X ^ 2 - 1) (Polynomial.X ^ 3) 3 dvd_rfl
/-- Padding at the levels e ≠ 2: the constant 1 (the terminal head outcome). -/
private noncomputable def pgOne : PolyGeom := pgDiv 1 1 0 (one_dvd _)
/-- Padding at the levels e ≠ 2: the constant 0 (the roster's duplicate
outcomes carry no mass).
QUEUE ITEM 10 REPAIR (Asvin sign-off 2026-07-31; probe `MovesU/SynK2_cl6N2.lean`):
`countS := 0` — the honest cell census for the padding rows, whose cell fibers
are EMPTY.  The old `pgDiv`-pinned `countS = 1` refuted `PolyGeomLaws n2T n2M
n2RB` at (e, o, q₀) = (1, 1, 2) (compiled `n2_polyGeomLaws_isEmpty`, git history
of the probe file — superseded by this repair in the same commit).  The change
is VAL-PRESERVING (`pgZero_val : pgZero.val = 0`, as before) and keeps the
degree pins (`natDegree 0 = 0 ≤ 0`); no external consumer pins `tgP`'s `countS`
(probe-grep-verified). -/
private noncomputable def pgZero : PolyGeom where
  countT := 1
  degBoundT := 0
  degT_le := by simp
  countS := 0
  degBoundS := 0
  degS_le := by simp
  geom := 0
  qpow := 0
  geomDenoms := ∅
  geom_denom_dvd := by simp

/-- The block-2 roster: o_K ↦ q⁻³, o_spl ↦ (X−1)/X, o_in ↦ (X²−1)/X³. -/
private noncomputable def tgTop : Fin 3 → PolyGeom := fun o =>
  if o = 0 then pgK else if o = 1 then pgSpl else pgIn
/-- The e ≠ 2 roster padding: (1, 0, 0) — outcome 0 carries the terminal mass 1;
`rowVal`'s eventual e ≠ 2 fill (unit n2_events' file) must match. -/
private noncomputable def tgLow : Fin 3 → PolyGeom := fun o =>
  if o = 0 then pgOne else pgZero

/-- The tg/j presentation data (`n2T.Out e τ` is `Fin 3` at every level). -/
private noncomputable def n2tgP : ∀ e (τ : n2T.State e), n2T.Out e τ → PolyGeom :=
  fun e _ o => if e = 2 then tgTop o else tgLow o

/-- The INIT-RAT presentation: the constant-1 presentation with the `Went`
degree bounds (the blueprint's ι pins are then definitional). -/
private noncomputable def n2ιP : ∀ e (τ : n2T.State e), n2M.EntShape e τ → PolyGeom :=
  fun e τ ε =>
  { countT := 1
    degBoundT := n2M.Went e τ ε
    degT_le := by simp
    countS := 1
    degBoundS := n2M.Went e τ ε
    degS_le := by simp
    geom := 1
    qpow := 0
    geomDenoms := ∅
    geom_denom_dvd := by simp [RatFunc.denom_one] }

/-! ### Evaluation-regularity (the OK laws) -/

private lemma pools_ne_zero {q₀ : ℚ} (hq : q₀ ∈ n2M.Pools) : q₀ ≠ 0 := by
  obtain ⟨p, hp, δ, rfl⟩ := n2M.pools_prime_pow q₀ hq
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)

private lemma pgDiv_val (num den : Polynomial ℚ) (qp : ℕ)
    (h : den ∣ Polynomial.X ^ qp) :
    (pgDiv num den qp h).val
      = algebraMap (Polynomial ℚ) Qq num / algebraMap (Polynomial ℚ) Qq den := by
  simp [pgDiv, PolyGeom.val]

private lemma pgDiv_val_mem {q₀ : ℚ} {num den : Polynomial ℚ} {qp : ℕ}
    {h : den ∣ Polynomial.X ^ qp} (hden : den.eval q₀ ≠ 0) :
    (pgDiv num den qp h).val ∈ OKat q₀ := by
  rw [pgDiv_val, mem_OKat_iff]
  intro h0
  obtain ⟨c, hc⟩ := RatFunc.denom_div_dvd num den
  rw [hc, Polynomial.eval_mul, h0, zero_mul] at hden
  exact hden rfl

/-- The repaired padding presentation still has value 0 (queue item 10:
val-preservation). -/
private lemma pgZero_val : pgZero.val = 0 := by
  simp [pgZero, PolyGeom.val]

private lemma pgZero_val_mem (q₀ : ℚ) : pgZero.val ∈ OKat q₀ := by
  rw [pgZero_val]; exact zero_mem _

private lemma n2tgP_ok (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ)
    (hq : q₀ ∈ n2M.Pools) : (n2tgP e τ o).val ∈ OKat q₀ := by
  have hne : q₀ ≠ 0 := pools_ne_zero hq
  simp only [n2tgP, tgTop, tgLow, pgK, pgSpl, pgIn, pgOne]
  split_ifs <;>
    first
      | exact pgDiv_val_mem (by simp [hne])
      | exact pgZero_val_mem q₀

private lemma n2ιP_val (e : ℕ) (τ : n2T.State e) (ε : n2M.EntShape e τ) :
    (n2ιP e τ ε).val = 1 := by
  simp [n2ιP, PolyGeom.val]

private lemma pgOne_val : pgOne.val = 1 := by
  unfold pgOne
  rw [pgDiv_val, map_one, div_one]

/-! ### The route fact (no split outcomes anywhere in the n = 2 table) -/

private lemma n2_route_ne_split (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) :
    routeOf (n2T.odata e τ o) ≠ Route.split := by
  by_cases he : e = 2
  · subst he
    obtain ⟨hrK, hrSpl, hrIn, _, _, _, _, hexh, _, hstate2, _, _⟩ := n2_shape
    have hτ := hstate2 τ
    subst hτ
    rcases hexh o with rfl | rfl | rfl
    · rw [hrK]; exact fun h => Route.noConfusion h
    · rw [hrSpl]; exact fun h => Route.noConfusion h
    · rw [hrIn]; exact fun h => Route.noConfusion h
  · simp only [n2T]
    rw [if_neg he]
    exact fun h => Route.noConfusion h

/-! ### The degree pins (Wloc ≡ 0, Wstate ≡ 0 at n = 2) -/

private lemma n2tgP_degBoundT (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) :
    (n2tgP e τ o).degBoundT = 0 := by
  simp only [n2tgP, tgTop, tgLow, pgK, pgSpl, pgIn, pgOne, pgZero]
  split_ifs <;> rfl

private lemma n2tgP_degBoundS (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) :
    (n2tgP e τ o).degBoundS = 0 := by
  simp only [n2tgP, tgTop, tgLow, pgK, pgSpl, pgIn, pgOne, pgZero]
  split_ifs <;> rfl

/-! ### The interpolation laws (seam discharge 2026-07-29, SEAM-4): the owning
n2M inputs — rowVal (n2_events fill) · ιsh (n2_ent_flow fill) · entCount — are
FILLED in N2Carriers.lean, so the three owned proof fields (`tg_interp`,
`ι_interp`, `ι_count`) are now provable in place; the owner units n2_interp_tg /
n2_interp_iota project them from the instance. -/

/-- Evaluation of a polynomial fraction `p/q` at `x` is `p.eval x / q.eval x`
whenever `q.eval x ≠ 0` (local copy of PowSubstOK's private lemma, as in
N2Rsh.lean). -/
private lemma eval_algebraMap_div (x : ℚ) (p q : Polynomial ℚ) (hq : q.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℚ) x
        (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      = p.eval x / q.eval x := by
  have hq0 : q ≠ 0 := fun h0 => hq (by rw [h0]; simp)
  have hqne : algebraMap (Polynomial ℚ) Qq q ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  have hdvd : (algebraMap (Polynomial ℚ) Qq p
      / algebraMap (Polynomial ℚ) Qq q).denom ∣ q :=
    (RatFunc.denom_dvd hq0).mpr ⟨p, rfl⟩
  have hgden : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [Polynomial.eval₂_id]
    obtain ⟨c, hc⟩ := hdvd
    intro hz
    exact hq (by rw [hc, Polynomial.eval_mul, hz, zero_mul])
  have hden_q : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [RatFunc.denom_algebraMap]; simp
  have epq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq p) = p.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have eqq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq q) = q.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have hmul : (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      * algebraMap (Polynomial ℚ) Qq q = algebraMap (Polynomial ℚ) Qq p :=
    div_mul_cancel₀ _ hqne
  have key := congrArg (RatFunc.eval (RingHom.id ℚ) x) hmul
  rw [RatFunc.eval_mul (RingHom.id ℚ) x hgden hden_q, epq, eqq] at key
  rw [eq_div_iff hq]
  exact key

/-- `evalAt` of a `pgDiv` presentation with regular denominator. -/
private lemma evalAt_pgDiv {q₀ : ℚ} {num den : Polynomial ℚ} {qp : ℕ}
    {hdvd : den ∣ Polynomial.X ^ qp} (hden : den.eval q₀ ≠ 0)
    (hok : (pgDiv num den qp hdvd).val ∈ OKat q₀) :
    (evalAt q₀ ⟨(pgDiv num den qp hdvd).val, hok⟩ : ℚ)
      = num.eval q₀ / den.eval q₀ := by
  show RatFunc.eval (RingHom.id ℚ) q₀ (pgDiv num den qp hdvd).val
      = num.eval q₀ / den.eval q₀
  rw [pgDiv_val]
  exact eval_algebraMap_div q₀ num den hden

/-- `evalAt` of an OK element with value 1 (the ι presentations). -/
private lemma evalAt_of_val_one {q₀ : ℚ} {g : Qq} (hg : g ∈ OKat q₀) (h1 : g = 1) :
    (evalAt q₀ ⟨g, hg⟩ : ℚ) = 1 := by
  have hsub : (⟨g, hg⟩ : OKat q₀) = 1 := Subtype.ext h1
  rw [hsub, map_one]

/-- `evalAt` of the repaired zero-padding presentation (queue item 10): value 0. -/
private lemma evalAt_pgZero {q₀ : ℚ} (hok : pgZero.val ∈ OKat q₀) :
    (evalAt q₀ ⟨pgZero.val, hok⟩ : ℚ) = 0 := by
  have hsub : (⟨pgZero.val, hok⟩ : OKat q₀) = 0 := Subtype.ext pgZero_val
  rw [hsub, map_zero]

/-- tg/j interpolation at every pool (owner unit `n2_interp_tg`): the evaluated
presentation is the measured row of N2Carriers' `rowVal` fill. -/
private lemma n2tgP_interp (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ)
    (h : q₀ ∈ n2M.Pools) (hok : (n2tgP e τ o).val ∈ OKat q₀) :
    ((evalAt q₀ ⟨(n2tgP e τ o).val, hok⟩ : ℚ) : ℝ) = n2M.rowVal e τ o q₀ := by
  have hne : q₀ ≠ 0 := pools_ne_zero h
  have hneR : (q₀ : ℝ) ≠ 0 := by exact_mod_cast hne
  by_cases he : e = 2
  · subst he
    rcases o with ⟨v, hv⟩
    interval_cases v
    · -- o_K: q₀⁻³
      have hval := evalAt_pgDiv (num := 1) (den := Polynomial.X ^ 3) (qp := 3)
        (hdvd := dvd_rfl) (q₀ := q₀) (by simp [hne]) hok
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      show (((1 : Polynomial ℚ).eval q₀ / (Polynomial.X ^ 3 : Polynomial ℚ).eval q₀ : ℚ) : ℝ)
          = ((q₀ : ℝ))⁻¹ ^ 3
      rw [Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast
      rw [one_div, inv_pow]
    · -- o_spl: 1 − q₀⁻¹
      have hval := evalAt_pgDiv (num := Polynomial.X - 1) (den := Polynomial.X) (qp := 1)
        (hdvd := ⟨1, by ring⟩) (q₀ := q₀) (by simpa using hne) hok
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      show (((Polynomial.X - 1 : Polynomial ℚ).eval q₀
            / (Polynomial.X : Polynomial ℚ).eval q₀ : ℚ) : ℝ)
          = 1 - ((q₀ : ℝ))⁻¹
      rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
      push_cast
      rw [sub_div, div_self hneR, one_div]
    · -- o_in: q₀⁻¹ − q₀⁻³
      have hval := evalAt_pgDiv (num := Polynomial.X ^ 2 - 1) (den := Polynomial.X ^ 3)
        (qp := 3) (hdvd := dvd_rfl) (q₀ := q₀) (by simp [hne]) hok
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      show (((Polynomial.X ^ 2 - 1 : Polynomial ℚ).eval q₀
            / (Polynomial.X ^ 3 : Polynomial ℚ).eval q₀ : ℚ) : ℝ)
          = ((q₀ : ℝ))⁻¹ - ((q₀ : ℝ))⁻¹ ^ 3
      rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
        Polynomial.eval_pow, Polynomial.eval_X]
      push_cast
      field_simp
  · -- e ≠ 2: the (1, 0, 0) padding row against rowVal's terminal-head fill
    rcases o with ⟨v, hv⟩
    have htg : n2tgP e τ ⟨v, hv⟩ = tgLow ⟨v, hv⟩ := if_neg he
    have hok' : (tgLow ⟨v, hv⟩).val ∈ OKat q₀ := htg ▸ hok
    have hsub : (⟨(n2tgP e τ ⟨v, hv⟩).val, hok⟩ : OKat q₀)
        = ⟨(tgLow ⟨v, hv⟩).val, hok'⟩ := Subtype.ext (congrArg PolyGeom.val htg)
    have hrow : n2M.rowVal e τ ⟨v, hv⟩ q₀ = if v = 0 then (1 : ℝ) else 0 := if_neg he
    rw [hsub, hrow]
    interval_cases v
    · rw [if_pos rfl]
      have hval := evalAt_pgDiv (num := 1) (den := 1) (qp := 0)
        (hdvd := one_dvd _) (q₀ := q₀) (by simp) hok'
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      simp
    · rw [if_neg one_ne_zero]
      have hval := evalAt_pgZero (q₀ := q₀) hok'
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      simp
    · rw [if_neg (by omega : ¬(2 = 0))]
      have hval := evalAt_pgZero (q₀ := q₀) hok'
      refine (congrArg (fun t : ℚ => (t : ℝ)) hval).trans ?_
      simp

/-! ### The instance -/

/- SEAM DISCHARGE 2026-07-29 (SEAM-4): the last three owned fields (`tg_interp`
by n2_interp_tg; `ι_interp`/`ι_count` by n2_interp_iota) are FILLED — their n2M
inputs (rowVal · ιsh · entCount) landed with N2Carriers.lean, and the owner unit
theorems project these fields.  `cellP_count`/`act_iff` (owner n2_activity) were
filled at the same seam discharge — see the comment at those fields.  n2RB is
now sorry-free. -/
noncomputable def n2RB : RatBurdens n2T n2M where
  tgP := n2tgP
  jP := n2tgP
  ιP := n2ιP
  tg_ok := fun e τ o q₀ hq => n2tgP_ok e τ o q₀ hq
  j_ok := fun e τ o q₀ hq => n2tgP_ok e τ o q₀ hq
  ι_ok := fun e τ ε q₀ _ => by rw [n2ιP_val]; exact one_mem _
  -- tg_interp: OWNED by n2_interp_tg — FILLED (seam discharge 2026-07-29): rowVal
  -- landed with n2_events' fill in N2Carriers.lean; the evaluation is n2tgP_interp.
  tg_interp := fun e τ o q₀ h _ => n2tgP_interp e τ o q₀ h (n2tgP_ok e τ o q₀ h)
  j_interp := fun e τ o q₀ h hsplit => absurd hsplit (n2_route_ne_split e τ o)
  -- ι_interp/ι_count: OWNED by n2_interp_iota — FILLED (seam discharge 2026-07-29):
  -- ιsh ≡ 1 and entCount ≡ 1 landed with n2_ent_flow's fill in N2Carriers.lean; the
  -- ι presentation has val 1 (n2ιP_val) and countT = 1, so both laws evaluate.
  ι_interp := fun e τ ε q₀ h => by
    have h1 : ∀ hok : (n2ιP e τ ε).val ∈ OKat q₀,
        ((evalAt q₀ ⟨(n2ιP e τ ε).val, hok⟩ : ℚ) : ℝ) = 1 := fun hok => by
      rw [evalAt_of_val_one hok (n2ιP_val e τ ε)]; exact Rat.cast_one
    exact h1 _
  ι_countS_one := fun _ _ _ => rfl
  ι_count := fun e τ ε q₀ h => by
    show ((1 : Polynomial ℚ).eval q₀ : ℚ) = ((1 : ℕ) : ℚ)
    rw [Polynomial.eval_one, Nat.cast_one]
  tg_degT := fun e τ o => n2tgP_degBoundT e τ o
  tg_degS := fun e τ o => n2tgP_degBoundS e τ o
  j_degT := fun e τ o => n2tgP_degBoundT e τ o
  j_degS := fun e τ o => n2tgP_degBoundS e τ o
  ι_degT := fun _ _ _ => rfl
  ι_degS := fun _ _ _ => rfl
  cellP := fun _ _ _ => 1
  cellP_deg := fun e τ c => by simp
  cellP_nonzero := fun _ _ _ _ => one_ne_zero
  -- cellP_count/act_iff: OWNED by n2_activity — FILLED (seam discharge, 2026-07-29):
  -- the n2M inputs (cellInst = singleton, cellLvl = 0, activeState ≡ True) landed
  -- with n2_carriers/n2_ent_flow, so both laws evaluate: eval 1 = 1 = card {·},
  -- and activity ↔ (1 ≠ 0) is trivially two-sided.
  cellP_count := fun e τ c q₀ _ _ => by
    show ((1 : Polynomial ℚ).eval q₀ : ℚ)
      = ((n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card : ℚ)
    rw [Polynomial.eval_one,
      show (n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card = 1 from rfl,
      Nat.cast_one]
  act_iff := fun q₀ _ e _ τ =>
    iff_of_true trivial fun c => by
      show (1 : Polynomial ℚ).eval q₀ ≠ 0
      rw [Polynomial.eval_one]; exact one_ne_zero
  -- (J-RAT) per-cell tables (ratification 2026-07-28 finding 3): the n = 2 table
  -- has NO split outcome at any layer (n2_route_ne_split), so both laws are
  -- guard-vacuous; the per-cell presentation data is the constant 1-presentation.
  jPCell := fun _ _ _ => pgOne
  jcell_ok := fun _ _ _ q₀ _ => by
    show pgOne.val ∈ OKat q₀
    rw [pgOne_val]; exact one_mem _
  jcell_interp := fun e τ c _ _ _ hsplit _ =>
    absurd hsplit (n2_route_ne_split e τ (n2M.cellOut e τ c))
  jcell_sum := fun e τ o hsplit => absurd hsplit (n2_route_ne_split e τ o)

/-- The symbolic variable q (the RatFunc X). -/
noncomputable def qX : Qq := algebraMap (Polynomial ℚ) Qq Polynomial.X

private lemma qX_ne_zero : qX ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

private lemma pgK_val : pgK.val = qX⁻¹ ^ 3 := by
  unfold pgK
  rw [pgDiv_val, map_one, map_pow]
  show 1 / qX ^ 3 = qX⁻¹ ^ 3
  rw [one_div, inv_pow]

private lemma pgSpl_val : pgSpl.val = 1 - qX⁻¹ := by
  unfold pgSpl
  rw [pgDiv_val, map_sub, map_one]
  show (qX - 1) / qX = 1 - qX⁻¹
  rw [sub_div, div_self qX_ne_zero, one_div]

private lemma pgIn_val : pgIn.val = qX⁻¹ - qX⁻¹ ^ 3 := by
  unfold pgIn
  rw [pgDiv_val, map_sub, map_one, map_pow, map_pow]
  show (qX ^ 2 - 1) / qX ^ 3 = qX⁻¹ - qX⁻¹ ^ 3
  field_simp

theorem n2_polygeom_data :
    (n2RB.tgP 2 n2τ n2oK).val = qX⁻¹ ^ 3 ∧
    (n2RB.tgP 2 n2τ n2oSpl).val = 1 - qX⁻¹ ∧
    (n2RB.tgP 2 n2τ n2oIn).val = qX⁻¹ - qX⁻¹ ^ 3 ∧
    (n2RB.tgP 2 n2τ n2oK).qpow = 3 ∧
    (n2RB.tgP 2 n2τ n2oSpl).qpow = 1 ∧
    (n2RB.tgP 2 n2τ n2oIn).qpow = 3 ∧
    (n2RB.tgP 2 n2τ n2oK).geomDenoms = ∅ := by
  exact ⟨pgK_val, pgSpl_val, pgIn_val, rfl, rfl, rfl, rfl⟩

/-! ### [QUEUE ITEM 10 COMPANIONS, 2026-07-31] The CL-6 count laws at the
repaired pack — the two `PolyGeomLaws` VALUE obligations, proved HERE because
the presentation constants are private to this file; the SYN2-K2 probe module
(`MovesU/SynK2_cl6N2.lean`) assembles the `Nonempty (PolyGeomLaws n2T n2M n2RB)`
witness from them (the `BridgeKernels.cl6` "moves out" evidence). -/

/-- CL-6 T-count law at the n = 2 pack: every roster presentation carries the
constant-1 `countT`, so it evaluates to the ℕ-count 1 at every q₀. -/
theorem n2_tcount_val (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ) :
    (n2RB.tgP e τ o).countT.eval q₀ = ((1 : ℕ) : ℚ) := by
  have h1 : (n2RB.tgP e τ o).countT = 1 := by
    show (n2tgP e τ o).countT = 1
    simp only [n2tgP, tgTop, tgLow, pgK, pgSpl, pgIn, pgOne, pgZero, pgDiv]
    split_ifs <;> rfl
  rw [h1]
  simp

/-- CL-6 cell-count law at the n = 2 pack (the repaired census): every roster
presentation's `countS` evaluates to the outcome's cell-fiber census — 1 at the
real rows (singleton fibers: the three block-2 rosters and the e ≠ 2 terminal
head), 0 at the e ≠ 2 padding rows (EMPTY fibers, matched by the repaired
`pgZero.countS = 0`).  Before the queue-item-10 repair this law was REFUTABLE
at (e, o) = (1, 1) — the compiled probe record. -/
theorem n2_scount_val (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ) :
    (n2RB.tgP e τ o).countS.eval q₀
      = ∑ c ∈ n2M.cells e τ o,
          ((n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card : ℚ) := by
  -- every cell instance is a singleton: the census is the fiber cardinality
  have hinst : ∀ c : n2M.Cell e τ,
      (n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card = 1 := fun _ => rfl
  have hsum : ∑ c ∈ n2M.cells e τ o,
      ((n2M.cellInst e τ c q₀ (n2M.cellLvl e τ c)).card : ℚ)
      = ((n2M.cells e τ o).card : ℚ) := by
    rw [Finset.sum_congr rfl (fun c _ => by rw [hinst c, Nat.cast_one]),
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_def]
  rw [hsum]
  by_cases he : e = 2
  · -- the block-2 layer: three real rosters, singleton fibers, countS ≡ 1
    subst he
    obtain ⟨_, _, _, _, _, _, _, _, _, hstate2, _, _⟩ := n2_shape
    have hτ := hstate2 τ
    subst hτ
    rcases o with ⟨v, hv⟩
    have hfib : n2M.cells 2 n2τ (⟨v, hv⟩ : Fin 3)
        = {(show n2M.Cell 2 n2τ from ⟨v, by simpa using hv⟩)} := by
      ext c
      simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
        Finset.mem_singleton]
      constructor
      · intro h
        have h1 : c.1 % 3 = v := congrArg Fin.val h
        have h2 : c.1 < 3 := c.2
        exact Fin.ext (by change c.1 = v; omega)
      · rintro rfl
        exact Fin.ext (by change v % 3 = v; omega)
    rw [hfib, Finset.card_singleton]
    interval_cases v <;>
      · change (1 : Polynomial ℚ).eval q₀ = ((1 : ℕ) : ℚ)
        simp
  · -- e ≠ 2: the one-cell layer — the terminal head o = 0 has the full fiber,
    -- the padding rows o = 1, 2 have EMPTY fibers and countS = 0
    have hc1 : ∀ c : n2M.Cell e τ, c.1 = 0 := by
      intro c
      have h2 := c.2
      have h3 : (if e = 2 then 3 else 1) = 1 := if_neg he
      omega
    rcases o with ⟨v, hv⟩
    have hcs : (n2RB.tgP e τ ⟨v, hv⟩).countS = if v = 0 then 1 else 0 := by
      change (n2tgP e τ ⟨v, hv⟩).countS = _
      simp only [n2tgP, if_neg he, tgLow]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (congrArg Fin.val h1) (by simpa using h2)
      · exact absurd (Fin.ext (by simpa using h2)) h1
      · rfl
    by_cases hv0 : v = 0
    · subst hv0
      have hfib : n2M.cells e τ (⟨0, hv⟩ : Fin 3) = Finset.univ := by
        ext c
        simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq,
          Finset.mem_univ, iff_true]
        exact Fin.ext (by change c.1 % 3 = 0; rw [hc1 c])
      rw [hfib, Finset.card_univ]
      have hcard : Fintype.card (n2M.Cell e τ) = 1 := by
        change Fintype.card (Fin (if e = 2 then 3 else 1)) = 1
        rw [Fintype.card_fin, if_neg he]
      rw [hcard, hcs, if_pos rfl]
      simp
    · have hfib : n2M.cells e τ (⟨v, hv⟩ : Fin 3) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        simp only [MeasuredSide.cells, Set.mem_toFinset, Set.mem_setOf_eq] at hc
        have h1 : c.1 % 3 = v := congrArg Fin.val hc
        rw [hc1 c] at h1
        exact hv0 h1.symm
      rw [hfib, Finset.card_empty]
      rw [hcs, if_neg hv0]
      simp

end LeanUrat.MovesS
