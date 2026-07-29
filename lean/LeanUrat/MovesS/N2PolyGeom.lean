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
outcomes carry no mass). -/
private noncomputable def pgZero : PolyGeom := pgDiv 0 1 0 (one_dvd _)

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

private lemma n2tgP_ok (e : ℕ) (τ : n2T.State e) (o : n2T.Out e τ) (q₀ : ℚ)
    (hq : q₀ ∈ n2M.Pools) : (n2tgP e τ o).val ∈ OKat q₀ := by
  have hne : q₀ ≠ 0 := pools_ne_zero hq
  simp only [n2tgP, tgTop, tgLow, pgK, pgSpl, pgIn, pgOne, pgZero]
  split_ifs <;> exact pgDiv_val_mem (by simp [hne])

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

/-! ### The instance -/

/- The five `sorry` fields below are OWNED BY OTHER UNITS (the `n2M` assembly
pattern): `tg_interp` by n2_interp_tg, `ι_interp`/`ι_count` by n2_interp_iota,
`cellP_count`/`act_iff` by n2_activity.  Each is a constraint on an `n2M` field
that is still `sorry` in N2Carriers.lean (rowVal · ιsh · entCount ·
cellInst/cellLvl · activeState respectively), so no proof can exist here until
n2_events/n2_ent_flow/n2_carriers land their fills. -/
noncomputable def n2RB : RatBurdens n2T n2M where
  tgP := n2tgP
  jP := n2tgP
  ιP := n2ιP
  tg_ok := fun e τ o q₀ hq => n2tgP_ok e τ o q₀ hq
  j_ok := fun e τ o q₀ hq => n2tgP_ok e τ o q₀ hq
  ι_ok := fun e τ ε q₀ _ => by rw [n2ιP_val]; exact one_mem _
  tg_interp := sorry -- OWNED: n2_interp_tg (blocked on n2M.rowVal)
  j_interp := fun e τ o q₀ h hsplit => absurd hsplit (n2_route_ne_split e τ o)
  ι_interp := sorry -- OWNED: n2_interp_iota (blocked on n2M.ιsh)
  ι_countS_one := fun _ _ _ => rfl
  ι_count := sorry -- OWNED: n2_interp_iota (blocked on n2M.entCount)
  tg_degT := fun e τ o => n2tgP_degBoundT e τ o
  tg_degS := fun e τ o => n2tgP_degBoundS e τ o
  j_degT := fun e τ o => n2tgP_degBoundT e τ o
  j_degS := fun e τ o => n2tgP_degBoundS e τ o
  ι_degT := fun _ _ _ => rfl
  ι_degS := fun _ _ _ => rfl
  cellP := fun _ _ _ => 1
  cellP_deg := fun e τ c => by simp
  cellP_nonzero := fun _ _ _ _ => one_ne_zero
  cellP_count := sorry -- OWNED: n2_activity (blocked on n2M.cellInst/cellLvl)
  act_iff := sorry -- OWNED: n2_activity (blocked on n2M.activeState)
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
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · show pgK.val = qX⁻¹ ^ 3
    exact pgK_val
  · show pgSpl.val = 1 - qX⁻¹
    exact pgSpl_val
  · show pgIn.val = qX⁻¹ - qX⁻¹ ^ 3
    exact pgIn_val

end LeanUrat.MovesS
