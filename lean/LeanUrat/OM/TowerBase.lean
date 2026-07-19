import Mathlib
import LeanUrat.OM.RphiRing
import LeanUrat.OM.RphiRingGenH
import LeanUrat.OM.RphiGenHCount

/-!
# B-RING, wave TowerBase: the order-`r≥3` tower closure — the coefficient-ring abstraction

Blueprint: `uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §7 (THE DESIGN) + §4/§5.3
(the recursion + the W6c compounding gate). The math is DONE (W6c gate: the doubly-gapped tower
compounds cleanly, distinct power-basis monomials ⟹ no cross-level cancellation). This module is
the Lean abstraction, **purely additive** on the FROZEN concrete layer
(`RphiRingGenH`/`RphiGenHCount`/`RestartEquivGenH`) — the concrete count `= the level-0 instance`.

The concrete `RphiGenHCount.card_filtIdeal` counts a gapped ring `AdjoinRoot (X^e − c·p^h)` over
`ZMod (p^N)` via the base's ball-count `#{a : ZMod(p^N) | v_p a ≥ k} = p^(N − min N k)`. For order
`r` the child ring is built over `R_{r−1}` (itself a gapped tower ring), so the count must be
parameterized by the base's OWN (recursive) ball-count.

## Deliverables (BANKED, core-only footprint `[propext, Classical.choice, Quot.sound]`)

1. **`TowerBase R`** — the coefficient-ring class: a finite comm ring `R` with the interface the
   count consumes. The primitive is a valuation-ball IDEAL family `B : ℕ → Ideal R`
   (`B k = {a | vB a ≥ k}`; ideal-valued so the count is correct at GAPPED thresholds — `B k = {0}`
   once `k` exceeds the base's top valuation, giving ball-count `1`, not `0`), a uniformizer `ϖ`
   with its own valuation `vUnif` (`1` at level 0; `h` for a tower level), a residue card `Q`, a
   `ballCount : ℕ → ℕ` with `ball_count_spec : Nat.card (B k) = ballCount k`, and the minimal ring
   facts (`B_zero`, `B_antitone`, `B_mul_uniformizer` = the uniformizer bumps the ball by `vUnif`).
2. **`instTowerBase_ZMod`** — the level-0 instance `TowerBase (ZMod (p^N))`, `B k = span {p^k}`,
   `ballCount k = p^(N − min N k)`, `vUnif = 1`; `ball_count_spec` reuses
   `RphiGenHCount.ball_count_clamped`.
3. **`RphiGenH R e h c`** (`= AdjoinRoot (X^e − C c · C ϖ^h)` over `R`) + **`card_filtIdeal_gen`**:
   `Nat.card (filtIdealG w) = ∏_{i<e} R.ballCount (⌈(w−ih)/e⌉⁺)` — the per-digit product with the
   BASE's own ball-count per coordinate. The θ-closure ports base-agnostically. REDUCTION CHECK:
   `reduction_gate_2323_N5` reproduces the banked W6a numbers (wild ⟨2,3⟩, N=5, w∈{1,2,3} →
   512/512/256) at `R = ZMod(2^5)`.
4. **`instTowerBase_RphiGenH`** (THE CRUX — the inductive step): `[TowerBase R] → [Nontrivial R] →
   TowerBase (RphiGenH R e h c)`, with `ϖ := θ`, `vUnif := h`, `B := filtIdealG`,
   `ballCount := card_filtIdeal_gen`, `Q` carried. `ball_count_spec` IS `card_filtIdeal_gen`; the
   W6c-gate "compounds cleanly" IS `PhiG_theta_bump` (the per-slot θ-bump `vL θ = h`, no
   cross-level cancellation — the W6a-shaped per-level strictness re-proved over `R`). This CLOSES
   order-`r`: the tower is `Nat`-iterated `RphiGenH` from `ZMod (p^N)`, each level a `TowerBase`
   over the last. `instTowerBase_level1` witnesses the composition end-to-end.

## Deliverable 5 (NAMED, not built): the abstract restart + `r_level_census`

The closure follow-up (§7 deliverable 5), to be built on top of this abstraction:
* `restartEquivGenH` / `card_restartGenH_fiber` re-stated over `[TowerBase R]` (abstract base) —
  port `RestartEquivGenH` with `ZMod (p^N) → R`, `p → ϖ`, the per-coordinate count `→ R.ballCount`;
  the dictionary / cap-`φ^μ` argument uses only ring structure + the base ball-count (grep
  `RestartEquivGenH` for `ZMod`-specific steps).
* `r_level_census` by `Nat`-recursion on tower height: order-`r` restart `= restartEquivGenH` over
  the level-`(r−1)` tower base; `TowerRestartGenH.two_level_census_genH` is the order-2 (base-case)
  instance. This is the remaining wave; the infrastructure it needs is fully banked here.

Discipline: no `sorry`/`axiom`/`native_decide`; mathlib-only beyond the frozen concrete layer;
core-only footprint (checked with `#print axioms`).
-/

namespace LeanUrat.OM

open Polynomial

set_option linter.dupNamespace false
set_option linter.unusedVariables false

/-- Coefficient-ring abstraction for the gapped-ring filtration count. The primitive is a
valuation-ball IDEAL family `B k = {a | vB a ≥ k}` (ideal-valued so the count is correct at
gapped thresholds: `B k = {0}` once `k` exceeds the base's top valuation, giving ball-count 1,
not 0). `ϖ` bumps the ball by `vUnif`. -/
class TowerBase (R : Type*) [CommRing R] [Finite R] where
  ϖ : R
  Q : ℕ
  /-- the base uniformizer's own valuation (`vB ϖ`): `1` for `ZMod (p^N)`, `h` for a tower
  ring built with child parameter `h`. Must be positive. -/
  vUnif : ℕ
  hvUnif_pos : 1 ≤ vUnif
  B : ℕ → Ideal R
  ballCount : ℕ → ℕ
  ball_count_spec : ∀ k, Nat.card (B k) = ballCount k
  B_zero : B 0 = ⊤
  B_antitone : ∀ ⦃j k : ℕ⦄, j ≤ k → B k ≤ B j
  B_mul_uniformizer : ∀ (k : ℕ) (x : R), x ∈ B k → ϖ * x ∈ B (k + vUnif)

namespace TowerBase

variable {R : Type*} [CommRing R] [Finite R] [TowerBase R]

/-- `ϖ^m` bumps the ball by `m·vUnif` (`≥ m` since `vUnif ≥ 1`). -/
theorem B_mul_uniformizer_pow (m k : ℕ) (x : R) (hx : x ∈ B k) :
    ϖ ^ m * x ∈ B (k + m * vUnif R) := by
  induction m with
  | zero => simpa using hx
  | succ n ih =>
    have hstep := B_mul_uniformizer (R := R) (k + n * vUnif R) (ϖ ^ n * x) ih
    have he : ϖ * (ϖ ^ n * x) = ϖ ^ (n + 1) * x := by rw [pow_succ]; ring
    rw [he] at hstep
    have : ϖ ^ (n + 1) * x ∈ B (k + n * vUnif R + vUnif R) := hstep
    have hle : k + (n + 1) * vUnif R ≤ k + n * vUnif R + vUnif R := le_of_eq (by ring)
    exact (B_antitone (R := R) hle) this

/-- `ϖ^m` bumps by at least `m` (using `vUnif ≥ 1`). -/
theorem B_mul_uniformizer_pow_ge (m k : ℕ) (x : R) (hx : x ∈ B k) : ϖ ^ m * x ∈ B (k + m) := by
  have h1 := B_mul_uniformizer_pow (R := R) m k x hx
  have hle : k + m ≤ k + m * vUnif R := by
    have hv := hvUnif_pos (R := R)
    have : m ≤ m * vUnif R := Nat.le_mul_of_pos_right m hv
    omega
  exact (B_antitone (R := R) hle) h1

/-- `c·ϖ^m` bumps the ball by at least `m` (`c` any ring element). -/
theorem B_mul_c_uniformizer_pow (c : R) (m k : ℕ) (x : R) (hx : x ∈ B k) :
    c * ϖ ^ m * x ∈ B (k + m) := by
  have h1 := B_mul_uniformizer_pow_ge (R := R) m k x hx
  have : c * ϖ ^ m * x = c * (ϖ ^ m * x) := by ring
  rw [this]; exact Ideal.mul_mem_left _ _ h1

/-! ## The abstract child ring -/

variable (R) in
noncomputable def phiGen (e h : ℕ) (c : Rˣ) : R[X] := X ^ e - C (c : R) * C (ϖ : R) ^ h
variable (R) in
theorem phiGen_eq (e h : ℕ) (c : Rˣ) : phiGen R e h c = X ^ e - C ((c : R) * (ϖ : R) ^ h) := by
  simp only [phiGen, map_mul, map_pow]
variable (R) in
noncomputable abbrev RphiGenH (e h : ℕ) (c : Rˣ) : Type _ := AdjoinRoot (phiGen R e h c)
theorem monic_phiGen {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) : (phiGen R e h c).Monic := by
  rw [phiGen_eq]; exact monic_X_pow_sub_C _ he.ne'
theorem natDegree_phiGen [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    (phiGen R e h c).natDegree = e := by rw [phiGen_eq]; exact natDegree_X_pow_sub_C
theorem degree_phiGen [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    (phiGen R e h c).degree = e := by rw [phiGen_eq]; exact degree_X_pow_sub_C he _
variable (R) in
noncomputable def thetaGen (e h : ℕ) (c : Rˣ) : RphiGenH R e h c := AdjoinRoot.root (phiGen R e h c)
theorem thetaGen_eq_root (e h : ℕ) (c : Rˣ) :
    thetaGen R e h c = AdjoinRoot.root (phiGen R e h c) := rfl
variable (R) in
noncomputable def digitMapG (e h : ℕ) (c : Rˣ) : degreeLT R e →ₗ[R] RphiGenH R e h c :=
  (AdjoinRoot.mkₐ (phiGen R e h c)).toLinearMap ∘ₗ (degreeLT R e).subtype
@[simp] theorem digitMapG_apply (e h : ℕ) (c : Rˣ) (b : degreeLT R e) :
    digitMapG R e h c b = AdjoinRoot.mk (phiGen R e h c) (b : R[X]) := rfl
theorem digitMapG_injective [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    Function.Injective (digitMapG R e h c) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨b, hb⟩ hb0
  apply Subtype.ext; show b = 0
  by_contra hne
  exact AdjoinRoot.mk_ne_zero_of_degree_lt (monic_phiGen he h c) hne
    (by rw [degree_phiGen he h c]; exact mem_degreeLT.mp hb) hb0
theorem digitMapG_surjective [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    Function.Surjective (digitMapG R e h c) := by
  intro x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨⟨g %ₘ phiGen R e h c, mem_degreeLT.mpr ?_⟩, ?_⟩
  · rw [← degree_phiGen he h c]; exact degree_modByMonic_lt g (monic_phiGen he h c)
  · rw [digitMapG_apply]
    have hmod : g %ₘ phiGen R e h c + phiGen R e h c * (g /ₘ phiGen R e h c) = g :=
      modByMonic_add_div g (phiGen R e h c)
    exact AdjoinRoot.mk_eq_mk.mpr ⟨-(g /ₘ phiGen R e h c), by linear_combination hmod⟩
variable (R) in
noncomputable def digitEquivG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    degreeLT R e ≃ₗ[R] RphiGenH R e h c :=
  LinearEquiv.ofBijective (digitMapG R e h c)
    ⟨digitMapG_injective he h c, digitMapG_surjective he h c⟩
theorem finite_RphiGenH [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    Finite (RphiGenH R e h c) :=
  Finite.of_equiv _ ((degreeLTEquiv R e).toEquiv.symm.trans (digitEquivG R he h c).toEquiv)
theorem thetaGen_pow_e (e h : ℕ) (c : Rˣ) :
    thetaGen R e h c ^ e = algebraMap R (RphiGenH R e h c) ((c : R) * (ϖ : R) ^ h) := by
  have h1 : AdjoinRoot.mk (phiGen R e h c) (X ^ e - C ((c : R) * (ϖ : R) ^ h)) = 0 := by
    rw [← phiGen_eq]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h1
  rw [thetaGen_eq_root, h1, AdjoinRoot.algebraMap_eq]; rfl

/-! ## assemble / digitCoeff -/

variable (R) in
noncomputable def digitEquivFullG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    RphiGenH R e h c ≃ₗ[R] (Fin e → R) := (digitEquivG R he h c).symm.trans (degreeLTEquiv R e)
noncomputable def digitCoeffG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ)
    (x : RphiGenH R e h c) : Fin e → R := digitEquivFullG R he h c x
variable (R) in
noncomputable def assembleG {e : ℕ} (h : ℕ) (c : Rˣ) (b : Fin e → R) : RphiGenH R e h c :=
  ∑ i : Fin e, algebraMap R (RphiGenH R e h c) (b i) * thetaGen R e h c ^ (i : ℕ)
theorem assembleG_eq [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (b : Fin e → R) :
    assembleG R h c b = digitEquivG R he h c ((degreeLTEquiv R e).symm b) := by
  rw [assembleG]
  show (∑ i : Fin e, algebraMap R (RphiGenH R e h c) (b i) * thetaGen R e h c ^ (i : ℕ))
      = digitEquivG R he h c ((degreeLTEquiv R e).symm b)
  rw [digitEquivG]; show _ = digitMapG R e h c ((degreeLTEquiv R e).symm b)
  rw [digitMapG_apply]
  have hpoly : (((degreeLTEquiv R e).symm b : degreeLT R e) : R[X])
      = ∑ i : Fin e, monomial (i : ℕ) (b i) := rfl
  rw [hpoly, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    ← thetaGen_eq_root, ← AdjoinRoot.algebraMap_eq]
theorem digitCoeffG_assembleG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ)
    (b : Fin e → R) : digitCoeffG he h c (assembleG R h c b) = b := by
  rw [digitCoeffG, digitEquivFullG, assembleG_eq he h c]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
theorem assembleG_digitCoeffG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ)
    (x : RphiGenH R e h c) : assembleG R h c (digitCoeffG he h c x) = x := by
  rw [assembleG_eq he h c, digitCoeffG, digitEquivFullG]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

/-! ## θ-shift on digit vectors -/

noncomputable def shiftVecG {n : ℕ} (h : ℕ) (c : Rˣ) (b : Fin (n + 1) → R) : Fin (n + 1) → R :=
  Fin.cons ((c : R) * (ϖ : R) ^ h * b (Fin.last n)) (fun j : Fin n => b (Fin.castSucc j))
theorem thetaGen_mul_assembleG {n : ℕ} (h : ℕ) (c : Rˣ) (b : Fin (n + 1) → R) :
    thetaGen R (n + 1) h c * assembleG R h c b = assembleG R h c (shiftVecG h c b) := by
  rw [assembleG, assembleG, Finset.mul_sum, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hlast : thetaGen R (n + 1) h c
        * ((algebraMap R (RphiGenH R (n + 1) h c)) (b (Fin.last n))
          * thetaGen R (n + 1) h c ^ (Fin.last n : ℕ))
      = (algebraMap R (RphiGenH R (n + 1) h c)) (shiftVecG h c b 0)
          * thetaGen R (n + 1) h c ^ ((0 : Fin (n + 1)) : ℕ) := by
    rw [shiftVecG, Fin.cons_zero, Fin.val_last, Fin.val_zero, pow_zero, mul_one]
    rw [map_mul, map_mul, map_pow]
    have hθe : thetaGen R (n + 1) h c ^ (n + 1)
        = algebraMap R (RphiGenH R (n + 1) h c) ((c : R) * (ϖ : R) ^ h) := thetaGen_pow_e (n+1) h c
    rw [map_mul, map_pow] at hθe
    calc thetaGen R (n + 1) h c
            * ((algebraMap R (RphiGenH R (n + 1) h c)) (b (Fin.last n))
              * thetaGen R (n + 1) h c ^ n)
        = (algebraMap R (RphiGenH R (n + 1) h c)) (b (Fin.last n))
            * thetaGen R (n + 1) h c ^ (n + 1) := by rw [pow_succ]; ring
      _ = (algebraMap R (RphiGenH R (n + 1) h c)) (b (Fin.last n))
            * ((algebraMap R (RphiGenH R (n + 1) h c)) (c : R)
              * (algebraMap R (RphiGenH R (n + 1) h c)) (ϖ : R) ^ h) := by rw [hθe]
      _ = (algebraMap R (RphiGenH R (n + 1) h c)) (c : R)
            * (algebraMap R (RphiGenH R (n + 1) h c)) (ϖ : R) ^ h
            * (algebraMap R (RphiGenH R (n + 1) h c)) (b (Fin.last n)) := by ring
  have hsum : (∑ i : Fin n, thetaGen R (n + 1) h c
        * ((algebraMap R (RphiGenH R (n + 1) h c)) (b i.castSucc)
          * thetaGen R (n + 1) h c ^ (i.castSucc : ℕ)))
      = ∑ i : Fin n, (algebraMap R (RphiGenH R (n + 1) h c)) (shiftVecG h c b i.succ)
          * thetaGen R (n + 1) h c ^ (i.succ : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    have hs : shiftVecG h c b i.succ = b i.castSucc := by rw [shiftVecG, Fin.cons_succ]
    rw [hs]
    have hv1 : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := by rw [Fin.val_succ, Fin.val_castSucc]
    rw [hv1, pow_succ]; ring
  rw [hlast, hsum]; ring

/-! ## The Phi predicate (digit-ball) and θ-closure. Reuse `RphiGenHCount.dexp`. -/

/-- `PhiG w x`: each digit `a_i` of `x` lies in `B (dexp w i)`. -/
def PhiG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ) (x : RphiGenH R e h c) : Prop :=
  ∀ i : Fin e, digitCoeffG he h c x i ∈ B (R := R) (RphiGenHCount.dexp e h w (i : ℕ))

theorem PhiG_theta [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ)
    {x : RphiGenH R e h c} (hx : PhiG he h c w x) :
    PhiG he h c w (thetaGen R e h c * x) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hx_eq : x = assembleG R h c (digitCoeffG he h c x) := (assembleG_digitCoeffG he h c x).symm
  have hshift : thetaGen R (n+1) h c * x
      = assembleG R h c (shiftVecG h c (digitCoeffG he h c x)) := by
    conv_lhs => rw [hx_eq]
    exact thetaGen_mul_assembleG h c (digitCoeffG he h c x)
  intro i
  rw [PhiG] at hx
  rw [hshift, digitCoeffG_assembleG he h c]
  refine Fin.cases ?_ ?_ i
  · rw [shiftVecG, Fin.cons_zero]
    have hbl : digitCoeffG he h c x (Fin.last n) ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w n) := by
      have := hx (Fin.last n); rwa [Fin.val_last] at this
    have hwrap : RphiGenHCount.dexp (n+1) h w 0 ≤ RphiGenHCount.dexp (n+1) h w n + h := by
      have := RphiGenHCount.dexp_wrap (n+1) h he w; simpa using this
    have hstep := B_mul_c_uniformizer_pow (R := R) (c : R) h (RphiGenHCount.dexp (n+1) h w n)
      (digitCoeffG he h c x (Fin.last n)) hbl
    show (c : R) * (ϖ:R)^h * digitCoeffG he h c x (Fin.last n)
        ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w 0)
    exact (B_antitone (R := R) hwrap) hstep
  · intro j
    rw [shiftVecG, Fin.cons_succ]
    have hbj : digitCoeffG he h c x (Fin.castSucc j)
        ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w (j.castSucc : ℕ)) := hx (Fin.castSucc j)
    have hmono : RphiGenHCount.dexp (n+1) h w (j.succ : ℕ)
        ≤ RphiGenHCount.dexp (n+1) h w (j.castSucc : ℕ) := by
      apply RphiGenHCount.dexp_antitone (n+1) h he
      rw [Fin.val_succ, Fin.val_castSucc]; omega
    show digitCoeffG he h c x (Fin.castSucc j) ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w (j.succ:ℕ))
    exact (B_antitone (R := R) hmono) hbj

theorem PhiG_zero [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ) :
    PhiG he h c w (0 : RphiGenH R e h c) := by
  intro i
  rw [digitCoeffG, map_zero]
  exact Ideal.zero_mem _

theorem PhiG_add [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ)
    {x y : RphiGenH R e h c} (hx : PhiG he h c w x) (hy : PhiG he h c w y) :
    PhiG he h c w (x + y) := by
  intro i
  have hd : digitCoeffG he h c (x + y) i
      = digitCoeffG he h c x i + digitCoeffG he h c y i := by
    rw [digitCoeffG, digitCoeffG, digitCoeffG, map_add]; rfl
  show digitCoeffG he h c (x+y) i ∈ B (R := R) (RphiGenHCount.dexp e h w (i:ℕ))
  rw [hd]; exact Ideal.add_mem _ (hx i) (hy i)

theorem PhiG_smul [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ) (s : R)
    {x : RphiGenH R e h c} (hx : PhiG he h c w x) :
    PhiG he h c w (s • x) := by
  intro i
  have hd : digitCoeffG he h c (s • x) i = s * digitCoeffG he h c x i := by
    rw [digitCoeffG, digitCoeffG, map_smul]; rfl
  show digitCoeffG he h c (s • x) i ∈ B (R := R) (RphiGenHCount.dexp e h w (i:ℕ))
  rw [hd]; exact Ideal.mul_mem_left _ _ (hx i)

theorem PhiG_theta_pow [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w k : ℕ)
    {x : RphiGenH R e h c} (hx : PhiG he h c w x) :
    PhiG he h c w (thetaGen R e h c ^ k * x) := by
  induction k with
  | zero => rwa [pow_zero, one_mul]
  | succ m ih =>
    have : thetaGen R e h c ^ (m + 1) * x = thetaGen R e h c * (thetaGen R e h c ^ m * x) := by
      rw [pow_succ]; ring
    rw [this]; exact PhiG_theta he h c w ih

theorem PhiG_mul [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ)
    (r : RphiGenH R e h c) {x : RphiGenH R e h c} (hx : PhiG he h c w x) :
    PhiG he h c w (r * x) := by
  set d := digitCoeffG he h c r with hd_def
  have hr : r = ∑ i : Fin e, d i • thetaGen R e h c ^ (i : ℕ) := by
    have hass : assembleG R h c d = r := assembleG_digitCoeffG he h c r
    rw [assembleG] at hass
    rw [← hass]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def]
  rw [hr, Finset.sum_mul]
  apply Finset.sum_induction _ (fun z => PhiG he h c w z)
    (fun a b => PhiG_add he h c w) (PhiG_zero he h c w)
  intro i _
  rw [smul_mul_assoc]
  exact PhiG_smul he h c w _ (PhiG_theta_pow he h c w (i : ℕ) hx)

/-- The digit-ball ideal = the abstract filtration ideal. -/
def filtIdealG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ) :
    Ideal (RphiGenH R e h c) where
  carrier := {x | PhiG he h c w x}
  add_mem' hx hy := PhiG_add he h c w hx hy
  zero_mem' := PhiG_zero he h c w
  smul_mem' r _x hx := PhiG_mul he h c w r hx

theorem mem_filtIdealG [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ)
    (x : RphiGenH R e h c) : x ∈ filtIdealG he h c w ↔ PhiG he h c w x := Iff.rfl

/-- `filtIdealG 0 = ⊤`: `dexp 0 i = 0` so every digit lies in `B 0 = ⊤`. -/
theorem filtIdealG_zero_eq_top [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) :
    filtIdealG he h c 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [mem_filtIdealG]
  intro i
  have hdexp : RphiGenHCount.dexp e h 0 (i:ℕ) = 0 := by
    have := (RphiGenHCount.dexp_le_iff e h he 0 (i:ℕ) 0).mpr (by omega); omega
  rw [hdexp, B_zero (R := R)]
  exact Submodule.mem_top

/-- `filtIdealG` is antitone in `w` (larger `w` ⟹ each digit-ball threshold larger ⟹ fewer). -/
theorem filtIdealG_antitone [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ)
    ⦃w w' : ℕ⦄ (hww : w ≤ w') : filtIdealG he h c w' ≤ filtIdealG he h c w := by
  intro x hx
  rw [mem_filtIdealG] at hx ⊢
  intro i
  have hmono : RphiGenHCount.dexp e h w (i:ℕ) ≤ RphiGenHCount.dexp e h w' (i:ℕ) := by
    rw [RphiGenHCount.dexp_le_iff e h he]
    have hd := (RphiGenHCount.dexp_le_iff e h he w' (i:ℕ)
      (RphiGenHCount.dexp e h w' (i:ℕ))).mp le_rfl
    omega
  exact (B_antitone (R := R) hmono) (hx i)

/-- **θ-bump** (the inductive `B_mul_uniformizer` for the tower ring): multiplying by `θ`
raises the filtration by `h` (`vL θ = h`). This IS the W6a-shaped per-slot strictness re-proved
over `R`: the digit-shift lands each digit in a strictly-higher base-ball, no cross-level
cancellation (distinct power-basis monomials). -/
theorem PhiG_theta_bump [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ)
    {x : RphiGenH R e h c} (hx : PhiG he h c w x) :
    PhiG he h c (w + h) (thetaGen R e h c * x) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hx_eq : x = assembleG R h c (digitCoeffG he h c x) := (assembleG_digitCoeffG he h c x).symm
  have hshift : thetaGen R (n+1) h c * x
      = assembleG R h c (shiftVecG h c (digitCoeffG he h c x)) := by
    conv_lhs => rw [hx_eq]
    exact thetaGen_mul_assembleG h c (digitCoeffG he h c x)
  intro i
  rw [PhiG] at hx
  rw [hshift, digitCoeffG_assembleG he h c]
  refine Fin.cases ?_ ?_ i
  · -- digit 0 = c·ϖ^h·(old digit n): need B(dexp (w+h) 0), have B(dexp w n + h)
    rw [shiftVecG, Fin.cons_zero]
    have hbl : digitCoeffG he h c x (Fin.last n) ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w n) := by
      have := hx (Fin.last n); rwa [Fin.val_last] at this
    have hstep := B_mul_c_uniformizer_pow (R := R) (c : R) h (RphiGenHCount.dexp (n+1) h w n)
      (digitCoeffG he h c x (Fin.last n)) hbl
    -- dexp (w+h) 0 ≤ dexp w n + h
    have hle : RphiGenHCount.dexp (n+1) h (w+h) 0 ≤ RphiGenHCount.dexp (n+1) h w n + h := by
      rw [RphiGenHCount.dexp_le_iff (n+1) h he]
      have hd := (RphiGenHCount.dexp_le_iff (n+1) h he w n (RphiGenHCount.dexp (n+1) h w n)).mp le_rfl
      -- w ≤ n*h + (n+1)*dexp; want w+h ≤ 0 + (n+1)*(dexp + h)
      have hexp : (n+1) * h = n * h + h := by ring
      simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_add]; omega
    show (c : R) * (ϖ:R)^h * digitCoeffG he h c x (Fin.last n)
        ∈ B (R := R) (RphiGenHCount.dexp (n+1) h (w+h) 0)
    exact (B_antitone (R := R) hle) hstep
  · -- digit (j+1) = old digit j: need B(dexp (w+h) (j+1)), have B(dexp w j)
    intro j
    rw [shiftVecG, Fin.cons_succ]
    have hbj : digitCoeffG he h c x (Fin.castSucc j)
        ∈ B (R := R) (RphiGenHCount.dexp (n+1) h w (j.castSucc : ℕ)) := hx (Fin.castSucc j)
    have hle : RphiGenHCount.dexp (n+1) h (w+h) (j.succ : ℕ)
        ≤ RphiGenHCount.dexp (n+1) h w (j.castSucc : ℕ) := by
      rw [RphiGenHCount.dexp_le_iff (n+1) h he]
      have hd := (RphiGenHCount.dexp_le_iff (n+1) h he w (j.castSucc:ℕ)
        (RphiGenHCount.dexp (n+1) h w (j.castSucc:ℕ))).mp le_rfl
      rw [Fin.val_succ, Fin.val_castSucc] at *
      -- w ≤ j*h + (n+1)*dexp; want w+h ≤ (j+1)*h + (n+1)*dexp
      have hexp : ((j:ℕ)+1) * h = (j:ℕ) * h + h := by ring
      omega
    show digitCoeffG he h c x (Fin.castSucc j)
        ∈ B (R := R) (RphiGenHCount.dexp (n+1) h (w+h) (j.succ:ℕ))
    exact (B_antitone (R := R) hle) hbj

/-! ## The per-digit product count (the base's own ball-count per coordinate) -/

/-- **`card_filtIdeal_gen`**: `card (filtIdeal w) = ∏_{i<e} R.ballCount (⌈(w − i·h)/e⌉⁺)`. -/
theorem card_filtIdeal_gen [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (c : Rˣ) (w : ℕ) :
    Nat.card (filtIdealG he h c w)
      = ∏ i : Fin e, (ballCount (R := R) (RphiGenHCount.dexp e h w (i : ℕ))) := by
  have hcard1 : Nat.card (filtIdealG he h c w)
      = Nat.card {a : Fin e → R //
          ∀ i : Fin e, a i ∈ B (R := R) (RphiGenHCount.dexp e h w (i:ℕ))} := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquiv (digitEquivFullG R he h c).toEquiv ?_)
    intro x
    rw [mem_filtIdealG]
    rfl
  rw [hcard1]
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : Fin e) (y : R) => y ∈ B (R := R) (RphiGenHCount.dexp e h w (i:ℕ))))]
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact ball_count_spec (R := R) (RphiGenHCount.dexp e h w (i : ℕ))

/-! ## THE INDUCTIVE STEP: a tower ring is itself a `TowerBase` -/

/-- **`instTowerBase_RphiGenH` (the crux)**: `RphiGenH R e h c` is a `TowerBase` over `R`, with
uniformizer `θ` (valuation `vUnif = h`), ball `filtIdealG`, and ball-count `card_filtIdeal_gen`
(the per-digit product of `R`'s own ball-count). The `ball_count_spec` IS `card_filtIdeal_gen`;
the W6c-gate "compounds cleanly" is exactly `PhiG_theta_bump` (the per-slot θ-bump, no
cross-level cancellation). This closes order-`r`: the tower is `Nat`-iterated `RphiGenH` from
`ZMod (p^N)`, each level a `TowerBase` over the last. -/
@[reducible] noncomputable def instTowerBase_RphiGenH {R : Type*} [CommRing R] [Finite R] [TowerBase R]
    [Nontrivial R] {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (c : Rˣ)
    [Finite (RphiGenH R e h c)] :
    TowerBase (RphiGenH R e h c) :=
  { ϖ := thetaGen R e h c
    Q := TowerBase.Q R
    vUnif := h
    hvUnif_pos := hh
    B := fun k => filtIdealG he h c k
    ballCount := fun k => ∏ i : Fin e, (ballCount (R := R) (RphiGenHCount.dexp e h k (i : ℕ)))
    ball_count_spec := fun k => card_filtIdeal_gen he h c k
    B_zero := filtIdealG_zero_eq_top he h c
    B_antitone := fun _ _ hjk => filtIdealG_antitone he h c hjk
    B_mul_uniformizer := fun k x hx => by
      have := PhiG_theta_bump he h c k (x := x) hx
      exact this }

end TowerBase

open TowerBase
open RphiRing (neZero_pow_base)

/-- Level-0 ZMod instance. -/
@[reducible] noncomputable def instTowerBase_ZMod (p N : ℕ) [hp : Fact p.Prime] (hN : 0 < N) :
    TowerBase (ZMod (p ^ N)) :=
  haveI := neZero_pow_base p N hN
  { ϖ := (p : ZMod (p ^ N))
    Q := p
    vUnif := 1
    hvUnif_pos := le_refl 1
    B := fun k => Ideal.span {(p : ZMod (p ^ N)) ^ k}
    ballCount := fun k => p ^ (N - min N k)
    ball_count_spec := by
      intro k
      have hset : Nat.card {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^k ∣ a}
          = p ^ (N - min N k) := RphiGenHCount.ball_count_clamped p N k
      rw [← hset]
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro a
      rw [Ideal.mem_span_singleton]
    B_zero := by rw [pow_zero, Ideal.span_singleton_one]
    B_antitone := by
      intro j k hjk
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hjk)
    B_mul_uniformizer := by
      intro k x hx
      rw [Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t, by rw [pow_succ]; ring⟩ }

/-- **Reduction gate**: ZMod instance ball-count product reproduces banked W6a 512/512/256. -/
theorem reduction_gate_2323_N5 :
    (∏ i : Fin 2, (instTowerBase_ZMod 2 5 (by norm_num)).ballCount
        (RphiGenHCount.dexp 2 3 1 (i:ℕ))) = 512
    ∧ (∏ i : Fin 2, (instTowerBase_ZMod 2 5 (by norm_num)).ballCount
        (RphiGenHCount.dexp 2 3 2 (i:ℕ))) = 512
    ∧ (∏ i : Fin 2, (instTowerBase_ZMod 2 5 (by norm_num)).ballCount
        (RphiGenHCount.dexp 2 3 3 (i:ℕ))) = 256 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Composition check (the recursion end-to-end)**: the tower instance composes over the ZMod
instance — a level-1 tower ring `RphiGenH (ZMod (p^N)) e h c` is itself a `TowerBase`. This is
one Nat-recursion step; iterating gives the order-`r` tower. -/
@[reducible] noncomputable def instTowerBase_level1 (p N : ℕ) [hp : Fact p.Prime] (hN : 0 < N)
    {e : ℕ} (he : 0 < e) (h : ℕ) (hh : 0 < h) (c : (ZMod (p ^ N))ˣ) :
    letI := instTowerBase_ZMod p N hN
    haveI : Nontrivial (ZMod (p ^ N)) := RphiRing.nontrivial_base p N hN
    haveI : Finite (TowerBase.RphiGenH (ZMod (p ^ N)) e h c) :=
      TowerBase.finite_RphiGenH he h c
    TowerBase (TowerBase.RphiGenH (ZMod (p ^ N)) e h c) :=
  letI := instTowerBase_ZMod p N hN
  haveI : Nontrivial (ZMod (p ^ N)) := RphiRing.nontrivial_base p N hN
  haveI : Finite (TowerBase.RphiGenH (ZMod (p ^ N)) e h c) :=
    TowerBase.finite_RphiGenH he h c
  TowerBase.instTowerBase_RphiGenH he h hh c

end LeanUrat.OM

