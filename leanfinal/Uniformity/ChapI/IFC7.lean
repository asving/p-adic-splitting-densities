/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC6
import Uniformity.ChapH.H97r4
import Uniformity.ChapG.G61b
import Uniformity.ChapG.G61c
import Uniformity.ChapG.G55
import Uniformity.ChapG.G60
import Uniformity.ChapG.G47
import Uniformity.ChapG.G46
import Uniformity.ChapG.G14

/-!
# Uniformity.ChapI.IFC7 — THE FIVE EXACT CUBIC DENSITIES (A0-CUBIC closes)

**[A0C 2026-08-28]** — unit A0C (verdict `runs/wave-c/verdict_A0C.md`).  The five exact
degree-3 splitting-density values (COROLLARY HM3.D, `spec/EFF-HMENU3.md` `.17`), proved
uniformly over every complete DVR with finite residue field, both characteristics, wild
primes included; the five `IFC6.CubicValueLaw` instances; and the fired socket
`decidedSliceAt_three : DecidedSliceAt 3` — the capstone field `a0` at `n = 3`.

With `q = residueCard O` and `Φ = q⁴+q³+q²+q+1` (so `(q−1)Φ = q⁵−1`):

| type | value |
|---|---|
| `c3split`    | `q³(q²−q+1) / (6(q+1)Φ)` |
| `c3linInert` | `q³(q²+q+1) / (2(q+1)Φ)` |
| `c3inert`    | `q³(q+1) / (3Φ)`         |
| `c3linRam`   | `q(q³+q+1) / ((q+1)Φ)`   |
| `c3ram`      | `(q²+1) / Φ`             |

**Numeric certification** (2026-08-28, `verification/a0c_cubic_cert.py`): the five closed
forms are certified by (A) exact symbolic identities incl. the fixed-point recursion below,
(B) exact `F_q` strata counts, (C) exhaustive finite-level classification by the repo's
exact integer oracle, (D) a decorrelated PARI leg (`nfinit`/`idealprimedec`), calibrated on
the Lean-proved `n = 2` values.

## The proof architecture (the SQUEEZE + the FIXED-POINT LOOP)

1. **Sharp lower bounds suffice**: `totalMass_three` (H97b, landed) says the five genuine
   densities sum to `1`; the five target values also sum to `1` (a rational identity); and
   `genuineDensity_three_eq_decidedDensity` (H97b) rekeys everything to `decidedDensity`.
   So five sharp LOWER bounds force all five equalities — no upper-bound machinery.
2. **Each sharp lower bound is a fixed-point inequality**, collapsing the infinite
   self-similar stratification into ONE step: for each type `σ`,

       decidedSeq O 3 σ (M+3) ≥ b_σ + q⁻⁵ · decidedSeq O 3 σ M
                                    [+ (q−1)q⁻³ · decidedSeq O 2 σ' M  for the DBL types]

   realized by an explicit injection of disjoint decided families into
   `decidedSet O 3 σ (M+3)`:
   * **level-1 bases** (reduction separable): the `coeffFactor`-preimages of the landed
     level-1 certificates `inert3_decided` / `linInert_decided_res` / (new)
     `split3_decided_res`, counted by G.60's censuses;
   * **recentred Newton-polygon bases** (reduction a cube): the E/L/R certificates of
     H97r2 placed at every residue centre `γ` (G.61d/e placed them at `γ = 0` only —
     that is exactly why their bounds were not sharp);
   * **the DBL bases** (reduction `(X−r̄)²(X−s̄)`): a Hensel-peeled linear factor times a
     quadratic part that is either directly Eisenstein or a `π`-rescale of an `n = 2`
     decided class — consuming the LANDED exact `n = 2` values (G.46/G.47);
   * **the loop stratum** (reduction a cube, recentred coefficients in
     `π³O × π²O × πO`): the `π`-rescale of an arbitrary level-`M` decided class,
     through H97r3's mixed-precision box `MBox` — the mirror image of the landed sharp
     UNDECIDED count `card_undecidedTriple_sharp`.
3. Passing `M → ∞` (`decidedSeq_tendsto`) and solving `D ≥ b + q⁻⁵D` gives each sharp
   bound; the squeeze closes.

**⚠ TRUST BOUNDARY.**  Every `theorem` here is NEW and flagged for the standing review;
zero `sorry`, zero new axiom; AxCheck footer expects Lean core only.  No landed file is
touched; every landed name is consumed as-is.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFC7

open IsLocalRing Polynomial

/-! ## §0 Prelude: representative sections and small kit -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- A choice of representative for each level-`N` class (mirror of H97r3's `resSect`). -/
noncomputable def resOut {N : ℕ} (x : Res O N) : O :=
  Function.surjInv Ideal.Quotient.mk_surjective x

theorem mk_resOut {N : ℕ} (x : Res O N) :
    Ideal.Quotient.mk ((maximalIdeal O) ^ N) (resOut x) = x :=
  Function.surjInv_eq _ x

variable {π : O}

/-- Membership of a class in `dvdSet` gives divisibility of the canonical representative. -/
theorem dvd_resOut_of_mem_dvdSet (hπ : Irreducible π) {k N : ℕ} (hk : k ≤ N)
    {x : Res O N} (hx : x ∈ Menu.dvdSet π k N) : π ^ k ∣ resOut x := by
  refine Menu.dvd_of_mem_dvdSet hπ hk ?_
  rw [mk_resOut]
  exact hx

/-- Membership in `exactSet` gives exact valuation of the canonical representative. -/
theorem exact_resOut_of_mem_exactSet (hπ : Irreducible π) {k N : ℕ} (hk : k + 1 ≤ N)
    {x : Res O N} (hx : x ∈ Menu.exactSet π k N) :
    π ^ k ∣ resOut x ∧ ¬ π ^ (k + 1) ∣ resOut x := by
  refine ⟨dvd_resOut_of_mem_dvdSet hπ (by omega) hx.1, fun hdvd => hx.2 ?_⟩
  rw [← mk_resOut x]
  exact Menu.mem_dvdSet_of_dvd hdvd

/-- Two coefficient vectors in the same level-`N` class (`N ≥ 1`) have the same residues. -/
theorem resVec_congr (hπ : Irreducible π) {N : ℕ} (hN : 1 ≤ N) {a a' : Fin 3 → O}
    (h : proj O 3 N a = proj O 3 N a') : resVec a = resVec a' := by
  have hd := (proj_eq_iff_dvd hπ a a').1 h
  funext i
  have h1 : π ∣ (a' i - a i) := (dvd_pow_self π (by omega : N ≠ 0)).trans (hd i)
  have h2 : a' i - a i ∈ maximalIdeal O := (mem_maximalIdeal_iff_dvd hπ _).2 h1
  show residue O (a i) = residue O (a' i)
  have := (residue_eq_zero_iff (a' i - a i)).2 h2
  rw [map_sub] at this
  exact (sub_eq_zero.mp this).symm

end Kit

/-! ## §1 The recentred (cube-frame) families: the generic member, decidedness, injectivity

A cube-frame family member is `F_b(X − δ)` where `δ = resSect γ` is the lift of the residue
centre and `b` (the recentred coefficient vector) has all coordinates in `𝔪`. -/

section CubeFrame

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- The cubic whose recentring at `resSect γ` has coefficient vector `b`. -/
noncomputable def cubeMember (γ : ResidueField O) (b : Fin 3 → O) : Fin 3 → O :=
  shiftVec b (-(resSect O γ))

theorem shiftVec_cubeMember (γ : ResidueField O) (b : Fin 3 → O) :
    shiftVec (cubeMember γ b) (resSect O γ) = b := by
  have h := shiftVec_shiftVec_neg b (-(resSect O γ))
  rwa [neg_neg] at h

/-- Every lift of the class of a cube member recentres, mod `π^(M+3)`, to `b`. -/
theorem shiftVec_dvd_of_lift (hπ : Irreducible π) {M : ℕ} {γ : ResidueField O}
    {b a' : Fin 3 → O}
    (h : proj O 3 (M + 3) a' = proj O 3 (M + 3) (cubeMember γ b)) :
    ∀ i, π ^ (M + 3) ∣ (shiftVec a' (resSect O γ) i - b i) := by
  intro i
  have hd := (proj_eq_iff_dvd hπ (cubeMember γ b) a').1 h.symm
  have := dvd_shiftVec_sub (π := π) (resSect O γ) hd i
  rwa [shiftVec_cubeMember] at this

/-- **Generic cube-frame decidedness**: a type verdict stable on the recentred vector's
`π^(M+3)`-class decides the cube member's level-`(M+3)` class. -/
theorem cube_decided (hπ : Irreducible π) {M : ℕ} {σ : FactorizationType}
    (γ : ResidueField O) {b : Fin 3 → O}
    (hcert : ∀ b' : Fin 3 → O, (∀ i, π ^ (M + 3) ∣ (b' i - b i)) →
      typeOf (monicPoly b') = σ) :
    DecidedAt O 3 σ (M + 3) (proj O 3 (M + 3) (cubeMember γ b)) := by
  refine decidedAt_of_congr hπ (fun a' ha' => ?_)
  rw [← typeOf_shiftVec a' (resSect O γ)]
  refine hcert _ (fun i => ?_)
  have hd := dvd_shiftVec_sub (π := π) (resSect O γ) ha' i
  rwa [shiftVec_cubeMember] at hd

/-- The residue vector of a cube member is the cube's coefficient vector — the class-level
reduction-shape tag of every cube-frame family. -/
theorem resVec_cubeMember {γ : ResidueField O} {b : Fin 3 → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) :
    resVec (cubeMember γ b) = cubeCoeff γ := by
  have h := (shiftVec_mem_iff (cubeMember γ b) (resSect O γ)).1 (fun i => by
    rw [shiftVec_cubeMember]; exact hb i)
  rwa [residue_resSect] at h

/-- **Generic cube-frame injectivity**: the class of a cube member (with recentred
coordinates in `𝔪`) determines the centre `γ` and the recentred vector's class. -/
theorem cubeMember_inj (hπ : Irreducible π) {M : ℕ} {γ γ' : ResidueField O}
    {b b' : Fin 3 → O} (hb : ∀ i, b i ∈ maximalIdeal O) (hb' : ∀ i, b' i ∈ maximalIdeal O)
    (h : proj O 3 (M + 3) (cubeMember γ b) = proj O 3 (M + 3) (cubeMember γ' b')) :
    γ = γ' ∧ ∀ i, π ^ (M + 3) ∣ (b' i - b i) := by
  have hres : resVec (cubeMember γ b) = resVec (cubeMember γ' b') :=
    resVec_congr hπ (by omega) h
  have h1 : resVec (cubeMember γ b) = cubeCoeff γ := resVec_cubeMember hb
  have h2 : resVec (cubeMember γ' b') = cubeCoeff γ' := resVec_cubeMember hb'
  have hγ : γ = γ' := cubeCoeff_injective (by rw [← h1, hres, h2])
  subst hγ
  refine ⟨rfl, fun i => ?_⟩
  have hd := (proj_eq_iff_dvd hπ _ _).1 h
  have hs := dvd_shiftVec_sub (π := π) (resSect O γ) hd i
  rwa [shiftVec_cubeMember, shiftVec_cubeMember] at hs

end CubeFrame

/-! ## §2 The four cube-frame parameter families (E, R, L, loop)

Parameter data lives in the landed digit sets (`dvdSet`/`exactSet`, G.14) at level `M+3`
and, for the loop, in H97r3's mixed-precision box over a decided level-`M` class. -/

section CubeFamilies

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}

/-- E-family parameters: centre × (`v = 1` digits, `v ≥ 1` digits, `v ≥ 1` digits). -/
def EParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) : Type _ :=
  ResidueField O × Menu.exactSet π 1 (M + 3) × Menu.dvdSet π 1 (M + 3) ×
    Menu.dvdSet π 1 (M + 3)

/-- R-family parameters: centre × (`v = 2`, `v ≥ 2`, `v ≥ 1`). -/
def RParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) : Type _ :=
  ResidueField O × Menu.exactSet π 2 (M + 3) × Menu.dvdSet π 2 (M + 3) ×
    Menu.dvdSet π 1 (M + 3)

/-- L-family parameters: centre × (`v ≥ 2`, `v = 1`, `v ≥ 1`). -/
def LParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) : Type _ :=
  ResidueField O × Menu.dvdSet π 2 (M + 3) × Menu.exactSet π 1 (M + 3) ×
    Menu.dvdSet π 1 (M + 3)

/-- Loop parameters: centre × (mixed-precision box over a `σ`-decided level-`M` class). -/
def LoopParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (σ : FactorizationType) (M : ℕ) : Type _ :=
  ResidueField O × ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M))

instance {M : ℕ} : Finite (EParams O π M) :=
  inferInstanceAs (Finite (ResidueField O × Menu.exactSet π 1 (M + 3) ×
    Menu.dvdSet π 1 (M + 3) × Menu.dvdSet π 1 (M + 3)))

instance {M : ℕ} : Finite (RParams O π M) :=
  inferInstanceAs (Finite (ResidueField O × Menu.exactSet π 2 (M + 3) ×
    Menu.dvdSet π 2 (M + 3) × Menu.dvdSet π 1 (M + 3)))

instance {M : ℕ} : Finite (LParams O π M) :=
  inferInstanceAs (Finite (ResidueField O × Menu.dvdSet π 2 (M + 3) ×
    Menu.exactSet π 1 (M + 3) × Menu.dvdSet π 1 (M + 3)))

instance {σ : FactorizationType} {M : ℕ} : Finite (LoopParams O σ M) :=
  inferInstanceAs (Finite (ResidueField O × ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M))))

noncomputable def eMap (M : ℕ) (p : EParams O π M) : Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (cubeMember p.1 ![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1])

noncomputable def rMap (M : ℕ) (p : RParams O π M) : Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (cubeMember p.1 ![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1])

noncomputable def lMap (M : ℕ) (p : LParams O π M) : Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (cubeMember p.1 ![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1])

/-- The loop member: recentred vector `(π³d₀, π²d₁, πd₂)` over the box's representatives. -/
noncomputable def loopMap {σ : FactorizationType} (M : ℕ) (p : LoopParams O σ M) :
    Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (cubeMember p.1
    ![π ^ 3 * resOut (p.2 : MBox O M).1, π ^ 2 * resOut (p.2 : MBox O M).2.1,
      π * resOut (p.2 : MBox O M).2.2])

/-- Local copy of H97r3's private divisibility-transfer helper. -/
private theorem a0c_dvd_sub {p c x y : O} (hpc : p ∣ c) (hs : c ∣ (x - y)) (hy : p ∣ y) :
    p ∣ x := by
  have h1 : p ∣ x - y := hpc.trans hs
  have h2 : p ∣ (x - y) + y := dvd_add h1 hy
  rwa [sub_add_cancel] at h2

/-- Local copy of H97r3's private non-divisibility-transfer helper. -/
private theorem a0c_not_dvd_sub {p c x y : O} (hpc : p ∣ c) (hs : c ∣ (x - y))
    (hy : ¬ p ∣ y) : ¬ p ∣ x := fun hx => hy (a0c_dvd_sub hpc (dvd_sub_comm.1 hs) hx)

theorem eMap_decided (hπ : Irreducible π) (M : ℕ) (p : EParams O π M) :
    eMap M p ∈ decidedSet O 3 c3ram (M + 3) := by
  obtain ⟨h0d, h0n⟩ := exact_resOut_of_mem_exactSet hπ (by omega) p.2.1.2
  have h1d : π ∣ resOut p.2.2.1.1 := by
    simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.1.2
  have h2d : π ∣ resOut p.2.2.2.1 := by
    simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2
  refine cube_decided hπ p.1 (fun b' hb' => ?_)
  have hb0 := hb' 0
  have hb1 := hb' 1
  have hb2 := hb' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hb0 hb1 hb2
  refine typeOf_ram3_of_val_one hπ ?_ ?_ ?_ ?_
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb0 (by simpa using h0d)
  · exact a0c_not_dvd_sub (pow_dvd_pow π (by omega)) hb0 (by simpa using h0n)
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb1 h1d
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb2 h2d

theorem rMap_decided (hπ : Irreducible π) (M : ℕ) (p : RParams O π M) :
    rMap M p ∈ decidedSet O 3 c3ram (M + 3) := by
  obtain ⟨h0d, h0n⟩ := exact_resOut_of_mem_exactSet hπ (by omega) p.2.1.2
  have h1d : π ^ 2 ∣ resOut p.2.2.1.1 := dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.1.2
  have h2d : π ∣ resOut p.2.2.2.1 := by
    simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2
  refine cube_decided hπ p.1 (fun b' hb' => ?_)
  have hb0 := hb' 0
  have hb1 := hb' 1
  have hb2 := hb' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hb0 hb1 hb2
  refine typeOf_ram3_of_val_two hπ ?_ ?_ ?_ ?_
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb2 h2d
  · exact a0c_dvd_sub (pow_dvd_pow π (by omega)) hb1 h1d
  · exact a0c_dvd_sub (pow_dvd_pow π (by omega)) hb0 h0d
  · exact a0c_not_dvd_sub (pow_dvd_pow π (by omega)) hb0 (by simpa using h0n)

theorem lMap_decided (hπ : Irreducible π) (M : ℕ) (p : LParams O π M) :
    lMap M p ∈ decidedSet O 3 c3linRam (M + 3) := by
  have h0d : π ^ 2 ∣ resOut p.2.1.1 := dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.1.2
  obtain ⟨h1d, h1n⟩ := exact_resOut_of_mem_exactSet hπ (by omega) p.2.2.1.2
  have h2d : π ∣ resOut p.2.2.2.1 := by
    simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2
  refine cube_decided hπ p.1 (fun b' hb' => ?_)
  have hb0 := hb' 0
  have hb1 := hb' 1
  have hb2 := hb' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hb0 hb1 hb2
  refine typeOf_linRam_of_val_one hπ ?_ ?_ ?_ ?_
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb2 h2d
  · exact a0c_dvd_sub (dvd_pow_self π (by omega)) hb1 (by simpa using h1d)
  · exact a0c_not_dvd_sub (pow_dvd_pow π (by omega)) hb1 (by simpa using h1n)
  · exact a0c_dvd_sub (pow_dvd_pow π (by omega)) hb0 h0d

theorem loopMap_decided (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ)
    (p : LoopParams O σ M) : loopMap (π := π) M p ∈ decidedSet O 3 σ (M + 3) := by
  refine cube_decided hπ p.1 (fun b' hb' => ?_)
  have hb0 := hb' 0
  have hb1 := hb' 1
  have hb2 := hb' 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hb0 hb1 hb2
  obtain ⟨c0, hc0⟩ := hb0
  obtain ⟨c1, hc1⟩ := hb1
  obtain ⟨c2, hc2⟩ := hb2
  have hext := typeOf_extract hπ
    (b := b')
    (d := ![resOut (p.2 : MBox O M).1 + π ^ M * c0,
      resOut (p.2 : MBox O M).2.1 + π ^ (M + 1) * c1,
      resOut (p.2 : MBox O M).2.2 + π ^ (M + 2) * c2])
    (by
      show b' 0 = π ^ 3 * (resOut (p.2 : MBox O M).1 + π ^ M * c0)
      linear_combination hc0)
    (by
      show b' 1 = π ^ 2 * (resOut (p.2 : MBox O M).2.1 + π ^ (M + 1) * c1)
      linear_combination hc1)
    (by
      show b' 2 = π * (resOut (p.2 : MBox O M).2.2 + π ^ (M + 2) * c2)
      linear_combination hc2)
  rw [hext]
  have hbox : mkBox (O := O) M
      ![resOut (p.2 : MBox O M).1, resOut (p.2 : MBox O M).2.1, resOut (p.2 : MBox O M).2.2]
      = (p.2 : MBox O M) := by
    refine Prod.ext (mk_resOut _) (Prod.ext ?_ ?_)
    · exact mk_resOut _
    · exact mk_resOut _
  have hmem : mtrunc (O := O) M (p.2 : MBox O M) ∈ decidedSet O 3 σ M := p.2.2
  have hproj : proj O 3 M
      (![resOut (p.2 : MBox O M).1, resOut (p.2 : MBox O M).2.1,
        resOut (p.2 : MBox O M).2.2]) ∈ decidedSet O 3 σ M := by
    rw [← mtrunc_mkBox (O := O) M, hbox]
    exact hmem
  refine hproj _ ?_
  rw [proj_eq_iff_dvd hπ]
  intro i
  fin_cases i
  · exact ⟨-c0, by show resOut (p.2 : MBox O M).1
      - (resOut (p.2 : MBox O M).1 + π ^ M * c0) = π ^ M * (-c0); ring⟩
  · exact ⟨-(π * c1), by show resOut (p.2 : MBox O M).2.1
      - (resOut (p.2 : MBox O M).2.1 + π ^ (M + 1) * c1) = π ^ M * (-(π * c1)); ring⟩
  · exact ⟨-(π ^ 2 * c2), by show resOut (p.2 : MBox O M).2.2
      - (resOut (p.2 : MBox O M).2.2 + π ^ (M + 2) * c2) = π ^ M * (-(π ^ 2 * c2)); ring⟩

/-- All three coordinates of an E/R/L representative vector are in `𝔪`. -/
private theorem a0c_vec_mem (hπ : Irreducible π) {u v w : O} (hu : π ∣ u) (hv : π ∣ v)
    (hw : π ∣ w) : ∀ i, (![u, v, w] : Fin 3 → O) i ∈ maximalIdeal O := by
  intro i
  fin_cases i
  · exact (mem_maximalIdeal_iff_dvd hπ _).2 hu
  · exact (mem_maximalIdeal_iff_dvd hπ _).2 hv
  · exact (mem_maximalIdeal_iff_dvd hπ _).2 hw

/-- Recover a level-`N` class equality from a `π^N`-congruence of representatives. -/
private theorem a0c_class_eq (hπ : Irreducible π) {N : ℕ} {x x' : Res O N}
    (h : π ^ N ∣ (resOut x' - resOut x)) : x = x' := by
  rw [← mk_resOut x, ← mk_resOut x']
  exact (Ideal.Quotient.eq).2 ((mem_maximalIdeal_pow_iff_dvd hπ N _).2 (dvd_sub_comm.1 h))

private theorem a0c_e_mem (hπ : Irreducible π) {M : ℕ} (p : EParams O π M) :
    ∀ i, (![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1] : Fin 3 → O) i
      ∈ maximalIdeal O :=
  a0c_vec_mem hπ
    (by simpa using (exact_resOut_of_mem_exactSet hπ (by omega) p.2.1.2).1)
    (by simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.1.2)
    (by simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2)

private theorem a0c_r_mem (hπ : Irreducible π) {M : ℕ} (p : RParams O π M) :
    ∀ i, (![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1] : Fin 3 → O) i
      ∈ maximalIdeal O :=
  a0c_vec_mem hπ
    ((dvd_pow_self π two_ne_zero).trans
      (exact_resOut_of_mem_exactSet hπ (by omega) p.2.1.2).1)
    ((dvd_pow_self π two_ne_zero).trans
      (dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.1.2))
    (by simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2)

private theorem a0c_l_mem (hπ : Irreducible π) {M : ℕ} (p : LParams O π M) :
    ∀ i, (![resOut p.2.1.1, resOut p.2.2.1.1, resOut p.2.2.2.1] : Fin 3 → O) i
      ∈ maximalIdeal O :=
  a0c_vec_mem hπ
    ((dvd_pow_self π two_ne_zero).trans
      (dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.1.2))
    (by simpa using (exact_resOut_of_mem_exactSet hπ (by omega) p.2.2.1.2).1)
    (by simpa using dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2.2.2)

private theorem a0c_loop_mem (hπ : Irreducible π) {σ : FactorizationType} {M : ℕ}
    (p : LoopParams O σ M) :
    ∀ i, (![π ^ 3 * resOut (p.2 : MBox O M).1, π ^ 2 * resOut (p.2 : MBox O M).2.1,
      π * resOut (p.2 : MBox O M).2.2] : Fin 3 → O) i ∈ maximalIdeal O :=
  a0c_vec_mem hπ ⟨π ^ 2 * resOut (p.2 : MBox O M).1, by ring⟩
    ⟨π * resOut (p.2 : MBox O M).2.1, by ring⟩
    ⟨resOut (p.2 : MBox O M).2.2, by ring⟩

theorem eMap_inj (hπ : Irreducible π) (M : ℕ) :
    Function.Injective (eMap (O := O) (π := π) M) := by
  intro p p' h
  obtain ⟨hγ, hd⟩ := cubeMember_inj hπ (a0c_e_mem hπ p) (a0c_e_mem hπ p') h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext hγ (Prod.ext (Subtype.ext (a0c_class_eq hπ h0))
    (Prod.ext (Subtype.ext (a0c_class_eq hπ h1)) (Subtype.ext (a0c_class_eq hπ h2))))

theorem rMap_inj (hπ : Irreducible π) (M : ℕ) :
    Function.Injective (rMap (O := O) (π := π) M) := by
  intro p p' h
  obtain ⟨hγ, hd⟩ := cubeMember_inj hπ (a0c_r_mem hπ p) (a0c_r_mem hπ p') h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext hγ (Prod.ext (Subtype.ext (a0c_class_eq hπ h0))
    (Prod.ext (Subtype.ext (a0c_class_eq hπ h1)) (Subtype.ext (a0c_class_eq hπ h2))))

theorem lMap_inj (hπ : Irreducible π) (M : ℕ) :
    Function.Injective (lMap (O := O) (π := π) M) := by
  intro p p' h
  obtain ⟨hγ, hd⟩ := cubeMember_inj hπ (a0c_l_mem hπ p) (a0c_l_mem hπ p') h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext hγ (Prod.ext (Subtype.ext (a0c_class_eq hπ h0))
    (Prod.ext (Subtype.ext (a0c_class_eq hπ h1)) (Subtype.ext (a0c_class_eq hπ h2))))

theorem loopMap_inj (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ) :
    Function.Injective (loopMap (O := O) (π := π) (σ := σ) M) := by
  intro p p' h
  obtain ⟨hγ, hd⟩ := cubeMember_inj hπ (a0c_loop_mem hπ p) (a0c_loop_mem hπ p') h
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  -- cancel the extracted powers of `π` (mirror of H97r3's `undecided_of_extract`)
  have c0 : π ^ M ∣ (resOut (p'.2 : MBox O M).1 - resOut (p.2 : MBox O M).1) := by
    obtain ⟨c, hc⟩ := h0
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 3 hπ.ne_zero) ?_⟩
    calc π ^ 3 * (resOut (p'.2 : MBox O M).1 - resOut (p.2 : MBox O M).1)
        = π ^ 3 * resOut (p'.2 : MBox O M).1 - π ^ 3 * resOut (p.2 : MBox O M).1 := by ring
      _ = π ^ (M + 3) * c := hc
      _ = π ^ 3 * (π ^ M * c) := by ring
  have c1 : π ^ (M + 1) ∣ (resOut (p'.2 : MBox O M).2.1 - resOut (p.2 : MBox O M).2.1) := by
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) ?_⟩
    calc π ^ 2 * (resOut (p'.2 : MBox O M).2.1 - resOut (p.2 : MBox O M).2.1)
        = π ^ 2 * resOut (p'.2 : MBox O M).2.1 - π ^ 2 * resOut (p.2 : MBox O M).2.1 := by
          ring
      _ = π ^ (M + 3) * c := hc
      _ = π ^ 2 * (π ^ (M + 1) * c) := by ring
  have c2 : π ^ (M + 2) ∣ (resOut (p'.2 : MBox O M).2.2 - resOut (p.2 : MBox O M).2.2) := by
    obtain ⟨c, hc⟩ := h2
    refine ⟨c, mul_left_cancel₀ hπ.ne_zero ?_⟩
    calc π * (resOut (p'.2 : MBox O M).2.2 - resOut (p.2 : MBox O M).2.2)
        = π * resOut (p'.2 : MBox O M).2.2 - π * resOut (p.2 : MBox O M).2.2 := by ring
      _ = π ^ (M + 3) * c := hc
      _ = π * (π ^ (M + 2) * c) := by ring
  have hbox : (p.2 : MBox O M) = (p'.2 : MBox O M) :=
    Prod.ext (a0c_class_eq hπ c0) (Prod.ext (a0c_class_eq hπ c1) (a0c_class_eq hπ c2))
  exact Prod.ext hγ (Subtype.ext hbox)

/-- E- and R-images are disjoint (`v(b₀) = 1` against `v(b₀) = 2`). -/
theorem eMap_ne_rMap (hπ : Irreducible π) (M : ℕ) (p : EParams O π M) (p' : RParams O π M) :
    eMap M p ≠ rMap M p' := by
  intro h
  obtain ⟨-, hd⟩ := cubeMember_inj hπ (a0c_e_mem hπ p) (a0c_r_mem hπ p') h
  have h0 := hd 0
  simp only [Matrix.cons_val_zero] at h0
  refine (exact_resOut_of_mem_exactSet hπ (by omega : 1 + 1 ≤ M + 3) p.2.1.2).2 ?_
  have hr : π ^ (1 + 1) ∣ resOut p'.2.1.1 := by
    simpa using (exact_resOut_of_mem_exactSet hπ (by omega : 2 + 1 ≤ M + 3) p'.2.1.2).1
  exact a0c_dvd_sub (pow_dvd_pow π (by omega)) (dvd_sub_comm.1 h0) hr

/-- E- and loop-images are disjoint (`v(b₀) = 1` against `v(b₀) ≥ 3`). -/
theorem eMap_ne_loopMap (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ)
    (p : EParams O π M) (p' : LoopParams O σ M) :
    eMap M p ≠ loopMap (π := π) M p' := by
  intro h
  obtain ⟨-, hd⟩ := cubeMember_inj hπ (a0c_e_mem hπ p) (a0c_loop_mem hπ p') h
  have h0 := hd 0
  simp only [Matrix.cons_val_zero] at h0
  refine (exact_resOut_of_mem_exactSet hπ (by omega : 1 + 1 ≤ M + 3) p.2.1.2).2 ?_
  have hr : π ^ (1 + 1) ∣ π ^ 3 * resOut (p'.2 : MBox O M).1 :=
    ⟨π * resOut (p'.2 : MBox O M).1, by ring⟩
  exact a0c_dvd_sub (pow_dvd_pow π (by omega)) (dvd_sub_comm.1 h0) hr

/-- R- and loop-images are disjoint (`v(b₀) = 2` against `v(b₀) ≥ 3`). -/
theorem rMap_ne_loopMap (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ)
    (p : RParams O π M) (p' : LoopParams O σ M) :
    rMap M p ≠ loopMap (π := π) M p' := by
  intro h
  obtain ⟨-, hd⟩ := cubeMember_inj hπ (a0c_r_mem hπ p) (a0c_loop_mem hπ p') h
  have h0 := hd 0
  simp only [Matrix.cons_val_zero] at h0
  refine (exact_resOut_of_mem_exactSet hπ (by omega : 2 + 1 ≤ M + 3) p.2.1.2).2 ?_
  have hr : π ^ (2 + 1) ∣ π ^ 3 * resOut (p'.2 : MBox O M).1 :=
    ⟨resOut (p'.2 : MBox O M).1, by ring⟩
  exact a0c_dvd_sub (pow_dvd_pow π (by omega)) (dvd_sub_comm.1 h0) hr

/-- L- and loop-images are disjoint (`v(b₁) = 1` against `v(b₁) ≥ 2`). -/
theorem lMap_ne_loopMap (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ)
    (p : LParams O π M) (p' : LoopParams O σ M) :
    lMap M p ≠ loopMap (π := π) M p' := by
  intro h
  obtain ⟨-, hd⟩ := cubeMember_inj hπ (a0c_l_mem hπ p) (a0c_loop_mem hπ p') h
  have h1 := hd 1
  simp only [Matrix.cons_val_one] at h1
  refine (exact_resOut_of_mem_exactSet hπ (by omega : 1 + 1 ≤ M + 3) p.2.2.1.2).2 ?_
  have hr : π ^ (1 + 1) ∣ π ^ 2 * resOut (p'.2 : MBox O M).2.1 :=
    ⟨resOut (p'.2 : MBox O M).2.1, by ring⟩
  exact a0c_dvd_sub (pow_dvd_pow π (by omega)) (dvd_sub_comm.1 h1) hr

end CubeFamilies

/-! ## §3 The residue-level shape tags and their pairwise disjointness

Each family pins the residue vector of every lift: `cubeCoeff γ` (cube frames),
`dblCoeff r s` (DBL frames), or a separable predicate class (level-1 bases). -/

section Shapes

variable {K : Type*} [Field K]

/-- Coefficient vector of `(X − r)²(X − s)`. -/
def dblCoeff (r s : K) : Fin 3 → K :=
  ![-(r ^ 2 * s), r ^ 2 + 2 * r * s, -(2 * r + s)]

theorem cVal_dblCoeff (r s y : K) :
    y ^ 3 + dblCoeff r s 2 * y ^ 2 + dblCoeff r s 1 * y + dblCoeff r s 0
      = (y - r) ^ 2 * (y - s) := by
  show y ^ 3 + (-(2 * r + s)) * y ^ 2 + (r ^ 2 + 2 * r * s) * y + (-(r ^ 2 * s))
      = (y - r) ^ 2 * (y - s)
  ring

theorem cVal_cubeCoeff (γ y : K) :
    y ^ 3 + cubeCoeff γ 2 * y ^ 2 + cubeCoeff γ 1 * y + cubeCoeff γ 0 = (y - γ) ^ 3 := by
  show y ^ 3 + (-(3 * γ)) * y ^ 2 + (3 * γ ^ 2) * y + (-(γ ^ 3)) = (y - γ) ^ 3
  ring

theorem noRootCubic_ne_cubeCoeff {v : Fin 3 → K} (hv : Menu.NoRootCubic v)
    (γ : K) : v ≠ cubeCoeff γ := by
  intro h
  refine hv γ ?_
  rw [h, cVal_cubeCoeff]
  ring

theorem noRootCubic_ne_dblCoeff {v : Fin 3 → K} (hv : Menu.NoRootCubic v)
    (r s : K) : v ≠ dblCoeff r s := by
  intro h
  refine hv s ?_
  rw [h, cVal_dblCoeff]
  ring

theorem linAni_ne_cubeCoeff {v : Fin 3 → K} (hv : Menu.LinAni v) (γ : K) :
    v ≠ cubeCoeff γ := by
  intro heq
  obtain ⟨ρ, p, hAni, hc⟩ := hv
  have hcc := hc.symm.trans heq
  have h0 : -(ρ * p.1) = -(γ ^ 3) := congrFun hcc 0
  have h1 : p.1 + ρ * p.2 = 3 * γ ^ 2 := congrFun hcc 1
  have h2 : -(p.2 + ρ) = -(3 * γ) := congrFun hcc 2
  have hcube : (γ - ρ) ^ 3 = 0 := by
    linear_combination h0 + ρ * h1 + ρ ^ 2 * h2
  have hγρ : γ = ρ := sub_eq_zero.1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hcube)
  refine hAni γ ?_
  have hp2 : p.2 = 2 * γ := by linear_combination -h2 + hγρ
  have hp1 : p.1 = γ ^ 2 := by linear_combination h1 - ρ * hp2 + 2 * γ * hγρ
  linear_combination -γ * hp2 + hp1

theorem linAni_ne_dblCoeff {v : Fin 3 → K} (hv : Menu.LinAni v) {r s : K} (hrs : r ≠ s) :
    v ≠ dblCoeff r s := by
  intro heq
  obtain ⟨ρ, p, hAni, hc⟩ := hv
  have hcc := hc.symm.trans heq
  have h0 : -(ρ * p.1) = -(r ^ 2 * s) := congrFun hcc 0
  have h1 : p.1 + ρ * p.2 = r ^ 2 + 2 * r * s := congrFun hcc 1
  have h2 : -(p.2 + ρ) = -(2 * r + s) := congrFun hcc 2
  have hr : (r - ρ) * (r ^ 2 - p.2 * r + p.1) = 0 := by
    linear_combination h0 + r * h1 + r ^ 2 * h2
  have hs : (s - ρ) * (s ^ 2 - p.2 * s + p.1) = 0 := by
    linear_combination h0 + s * h1 + s ^ 2 * h2
  rcases mul_eq_zero.mp hr with h | h
  · rcases mul_eq_zero.mp hs with h' | h'
    · exact hrs (by linear_combination h - h')
    · exact hAni s h'
  · exact hAni r h

theorem split3_ne_cubeCoeff {v : Fin 3 → K} (hv : Menu.Split3 v) (γ : K) :
    v ≠ cubeCoeff γ := by
  intro heq
  obtain ⟨r, s, t, hrs, hrt, hst, hc⟩ := hv
  have hcc := hc.symm.trans heq
  have h0 : -(r * s * t) = -(γ ^ 3) := congrFun hcc 0
  have h1 : r * s + r * t + s * t = 3 * γ ^ 2 := congrFun hcc 1
  have h2 : -(r + s + t) = -(3 * γ) := congrFun hcc 2
  have hr : (r - γ) ^ 3 = 0 := by linear_combination -h0 - r * h1 - r ^ 2 * h2
  have hs : (s - γ) ^ 3 = 0 := by linear_combination -h0 - s * h1 - s ^ 2 * h2
  refine hrs ?_
  have h1' : r = γ := sub_eq_zero.1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hr)
  have h2' : s = γ := sub_eq_zero.1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hs)
  exact h1'.trans h2'.symm

theorem split3_ne_dblCoeff {v : Fin 3 → K} (hv : Menu.Split3 v) {r s : K} (hrs : r ≠ s) :
    v ≠ dblCoeff r s := by
  intro heq
  obtain ⟨a, b, c, hab, hac, hbc, hc⟩ := hv
  have hcc := hc.symm.trans heq
  have h0 : -(a * b * c) = -(r ^ 2 * s) := congrFun hcc 0
  have h1 : a * b + a * c + b * c = r ^ 2 + 2 * r * s := congrFun hcc 1
  have h2 : -(a + b + c) = -(2 * r + s) := congrFun hcc 2
  have ha : (a - r) ^ 2 * (a - s) = 0 := by linear_combination -h0 - a * h1 - a ^ 2 * h2
  have hb : (b - r) ^ 2 * (b - s) = 0 := by linear_combination -h0 - b * h1 - b ^ 2 * h2
  have hcr : (c - r) ^ 2 * (c - s) = 0 := by linear_combination -h0 - c * h1 - c ^ 2 * h2
  have hA : a = r ∨ a = s := by
    rcases mul_eq_zero.mp ha with h | h
    · exact Or.inl (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h))
    · exact Or.inr (sub_eq_zero.1 h)
  have hB : b = r ∨ b = s := by
    rcases mul_eq_zero.mp hb with h | h
    · exact Or.inl (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h))
    · exact Or.inr (sub_eq_zero.1 h)
  have hC : c = r ∨ c = s := by
    rcases mul_eq_zero.mp hcr with h | h
    · exact Or.inl (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h))
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hA with rfl | rfl <;> rcases hB with h | h <;> rcases hC with h' | h' <;>
    simp_all

theorem cubeCoeff_ne_dblCoeff {γ r s : K} (hrs : r ≠ s) : cubeCoeff γ ≠ dblCoeff r s := by
  intro heq
  have h0 : -(γ ^ 3) = -(r ^ 2 * s) := congrFun heq 0
  have h1 : 3 * γ ^ 2 = r ^ 2 + 2 * r * s := congrFun heq 1
  have h2 : -(3 * γ) = -(2 * r + s) := congrFun heq 2
  have hr : (r - γ) ^ 3 = 0 := by linear_combination h0 + r * h1 + r ^ 2 * h2
  have hs : (s - γ) ^ 3 = 0 := by linear_combination h0 + s * h1 + s ^ 2 * h2
  refine hrs ?_
  have h1' : r = γ := sub_eq_zero.1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hr)
  have h2' : s = γ := sub_eq_zero.1 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hs)
  exact h1'.trans h2'.symm

/-- `(X−r)²(X−s)` determines the ordered pair `(r, s)` when `r ≠ s`. -/
theorem dblCoeff_inj {r s r' s' : K} (hrs : r ≠ s) (hrs' : r' ≠ s')
    (h : dblCoeff r s = dblCoeff r' s') : r = r' ∧ s = s' := by
  have h0 : -(r ^ 2 * s) = -(r' ^ 2 * s') := congrFun h 0
  have h1 : r ^ 2 + 2 * r * s = r' ^ 2 + 2 * r' * s' := congrFun h 1
  have h2 : -(2 * r + s) = -(2 * r' + s') := congrFun h 2
  have hr' : (r' - r) ^ 2 * (r' - s) = 0 := by
    linear_combination h0 + r' * h1 + r' ^ 2 * h2
  have hs' : (s' - r) ^ 2 * (s' - s) = 0 := by
    linear_combination h0 + s' * h1 + s' ^ 2 * h2
  have hR : r' = r ∨ r' = s := by
    rcases mul_eq_zero.mp hr' with h' | h'
    · exact Or.inl (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'))
    · exact Or.inr (sub_eq_zero.1 h')
  rcases hR with hRr | hRs
  · exact ⟨hRr.symm, by linear_combination -h2 + 2 * hRr⟩
  · have hS : s' = r ∨ s' = s := by
      rcases mul_eq_zero.mp hs' with h' | h'
      · exact Or.inl (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'))
      · exact Or.inr (sub_eq_zero.1 h')
    rcases hS with hSr | hSs
    · exact absurd (by linear_combination -h2 + 2 * hRs + hSr : r = s) hrs
    · exact absurd (hRs.trans hSs.symm) hrs'

end Shapes

/-! ## §4 The DBL (double-root × simple-root) frame: Hensel peel of a linear factor

The member is `(X − u)·g` with `u ≡ s̄`, `ḡ = (X − r̄)²`, `r̄ ≠ s̄`; decidedness is the
landed `decidedAt_of_peel_decided`; the quadratic part is either directly Eisenstein
(→ `ramType`) or a `π`-rescale of an `n = 2` decided class (→ any `σ'`). -/

section DblFrame

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}

/-- The n = 2 recentring: coefficient vector of `G_b(X + γ)` for a monic quadratic. -/
def shiftVec2 (b : Fin 2 → O) (γ : O) : Fin 2 → O :=
  ![γ ^ 2 + b 1 * γ + b 0, b 1 + 2 * γ]

theorem monicPoly_shiftVec2 (b : Fin 2 → O) (γ : O) :
    monicPoly (shiftVec2 b γ) = (monicPoly b).comp (X + C γ) := by
  rw [monicPoly_two_expand (shiftVec2 b γ), monicPoly_two_expand b]
  simp only [shiftVec2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    add_comp, mul_comp, pow_comp, X_comp, C_comp, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem typeOf_shiftVec2 (b : Fin 2 → O) (γ : O) :
    typeOf (monicPoly (shiftVec2 b γ)) = typeOf (monicPoly b) := by
  rw [monicPoly_shiftVec2]
  exact typeOf_shift (monicPoly_monic b) γ

theorem shiftVec2_shiftVec2_neg (b : Fin 2 → O) (γ : O) :
    shiftVec2 (shiftVec2 b γ) (-γ) = b := by
  funext i
  fin_cases i
  · show (-γ) ^ 2 + (b 1 + 2 * γ) * (-γ) + (γ ^ 2 + b 1 * γ + b 0) = b 0
    ring
  · show (b 1 + 2 * γ) + 2 * (-γ) = b 1
    ring

theorem dvd_shiftVec2_sub {N : ℕ} {b b' : Fin 2 → O} (γ : O)
    (h : ∀ i, π ^ N ∣ (b' i - b i)) : ∀ i, π ^ N ∣ (shiftVec2 b' γ i - shiftVec2 b γ i) := by
  intro i
  obtain ⟨c0, hc0⟩ := h 0
  obtain ⟨c1, hc1⟩ := h 1
  fin_cases i
  · show π ^ N ∣ ((γ ^ 2 + b' 1 * γ + b' 0) - (γ ^ 2 + b 1 * γ + b 0))
    exact ⟨γ * c1 + c0, by linear_combination γ * hc1 + hc0⟩
  · show π ^ N ∣ ((b' 1 + 2 * γ) - (b 1 + 2 * γ))
    exact ⟨c1, by linear_combination hc1⟩

/-- The n = 2 `π`-extraction preserves the type (quadratic mirror of `typeOf_extract`). -/
theorem typeOf_extract2 (hπ : Irreducible π) {b d : Fin 2 → O}
    (e0 : b 0 = π ^ 2 * d 0) (e1 : b 1 = π * d 1) :
    typeOf (monicPoly b) = typeOf (monicPoly d) := by
  refine typeOf_scale hπ (monicPoly_monic d) ?_ 1 ?_
  · rw [monicPoly_natDegree, monicPoly_natDegree]
  · rw [monicPoly_natDegree, monicPoly_two_expand b, monicPoly_two_expand d, e0, e1]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_add, map_mul, map_pow,
      pow_one]
    ring

/-- The assembled DBL member: `(X − u)·(X² + g₁X + g₀)` with `u = resSect s + π·resOut ω`. -/
noncomputable def dblAssemble {M : ℕ} (s : ResidueField O) (ω : Res O (M + 2))
    (g : Fin 2 → O) : Fin 3 → O :=
  ![-((resSect O s + π * resOut ω) * g 0), g 0 - (resSect O s + π * resOut ω) * g 1,
    g 1 - (resSect O s + π * resOut ω)]

theorem monicPoly_dblAssemble {M : ℕ} (s : ResidueField O) (ω : Res O (M + 2))
    (g : Fin 2 → O) :
    monicPoly (dblAssemble (π := π) s ω g)
      = (X - C (resSect O s + π * resOut ω)) * monicPoly g := by
  rw [cubic_expand, monicPoly_two_expand]
  simp only [dblAssemble, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_sub, map_neg, map_mul, map_add]
  ring

theorem peel_dblAssemble {M : ℕ} (s : ResidueField O) (ω : Res O (M + 2)) (g : Fin 2 → O) :
    peel (dblAssemble (π := π) s ω g) (resSect O s + π * resOut ω) = g := by
  funext i
  fin_cases i
  · simp [peel, dblAssemble]
    ring
  · simp [peel, dblAssemble]

/-- The residue vector of a DBL member is `dblCoeff r s` — its reduction-shape tag. -/
theorem resVec_dblAssemble (hπ : Irreducible π) {M : ℕ} {r s : ResidueField O}
    {ω : Res O (M + 2)} {g : Fin 2 → O}
    (hgres : (fun i => residue O (g i)) = ![r ^ 2, -(2 * r)]) :
    resVec (dblAssemble (π := π) s ω g) = dblCoeff r s := by
  have hπ0 : residue O π = 0 :=
    (residue_eq_zero_iff π).2 ((mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl)
  have hu : residue O (resSect O s + π * resOut ω) = s := by
    rw [map_add, map_mul, residue_resSect, hπ0, zero_mul, add_zero]
  have h0 : residue O (g 0) = r ^ 2 := by simpa using congrFun hgres 0
  have h1 : residue O (g 1) = -(2 * r) := by simpa using congrFun hgres 1
  funext i
  fin_cases i
  · simp only [resVec, dblAssemble, dblCoeff]
    simp [map_neg, map_sub, map_mul, hu, h0]
    ring
  · simp only [resVec, dblAssemble, dblCoeff]
    simp [map_neg, map_sub, map_mul, hu, h0, h1]
    ring
  · simp only [resVec, dblAssemble, dblCoeff]
    simp [map_neg, map_sub, map_mul, hu, h1]
    ring

/-- **DBL decidedness**: if the quadratic part's level-`(M+3)` class is `σ'`-decided and its
reduction is `(X − r̄)²` with `r̄ ≠ s̄`, the assembled cubic's class is
`⟨(1,1) ::ₘ σ'⟩`-decided. -/
theorem dblAssemble_decided (hπ : Irreducible π) {M : ℕ} {σ' : FactorizationType}
    {r s : ResidueField O} (hrs : r ≠ s) {ω : Res O (M + 2)} {g : Fin 2 → O}
    (hgres : (fun i => residue O (g i)) = ![r ^ 2, -(2 * r)])
    (hdec : DecidedAt O 2 σ' (M + 3) (proj O 2 (M + 3) g)) :
    DecidedAt O 3 ⟨(1, 1) ::ₘ σ'.data⟩ (M + 3)
      (proj O 3 (M + 3) (dblAssemble (π := π) s ω g)) := by
  have hπ0 : residue O π = 0 :=
    (residue_eq_zero_iff π).2 ((mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl)
  have hu : residue O (resSect O s + π * resOut ω) = s := by
    rw [map_add, map_mul, residue_resSect, hπ0, zero_mul, add_zero]
  have h0 : residue O (g 0) = r ^ 2 := by simpa using congrFun hgres 0
  have h1 : residue O (g 1) = -(2 * r) := by simpa using congrFun hgres 1
  have hroot : (monicPoly (dblAssemble (π := π) s ω g)).eval
      (resSect O s + π * resOut ω) = 0 := by
    rw [monicPoly_dblAssemble]
    simp
  have hgu : residue O ((monicPoly g).eval (resSect O s + π * resOut ω)) = (s - r) ^ 2 := by
    rw [monicPoly_two_expand]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow, map_mul]
    rw [residue_resSect, hπ0, h0, h1]
    ring
  have hunit : IsUnit ((monicPoly (dblAssemble (π := π) s ω g)).derivative.eval
      (resSect O s + π * resOut ω)) := by
    have hd : (monicPoly (dblAssemble (π := π) s ω g)).derivative.eval
        (resSect O s + π * resOut ω)
        = (monicPoly g).eval (resSect O s + π * resOut ω) := by
      rw [monicPoly_dblAssemble]
      simp [derivative_mul]
    rw [hd]
    by_contra hcon
    have hmem : (monicPoly g).eval (resSect O s + π * resOut ω) ∈ maximalIdeal O :=
      (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcon)
    have hz := (residue_eq_zero_iff _).2 hmem
    rw [hgu] at hz
    exact (sub_ne_zero.2 (Ne.symm hrs)) ((pow_eq_zero_iff (by norm_num)).1 hz)
  refine decidedAt_of_peel_decided hπ (by omega) hroot hunit ?_
  rw [peel_dblAssemble]
  exact hdec

/-- **DBL injectivity**: the class of the assembled cubic determines `r`, `s`, `ω`, and the
quadratic part's level-`(M+3)` class. -/
theorem dblAssemble_inj (hπ : Irreducible π) {M : ℕ} {r r' s s' : ResidueField O}
    (hrs : r ≠ s) (hrs' : r' ≠ s') {ω ω' : Res O (M + 2)} {g g' : Fin 2 → O}
    (hgres : (fun i => residue O (g i)) = ![r ^ 2, -(2 * r)])
    (hgres' : (fun i => residue O (g' i)) = ![r' ^ 2, -(2 * r')])
    (h : proj O 3 (M + 3) (dblAssemble (π := π) s ω g)
      = proj O 3 (M + 3) (dblAssemble (π := π) s' ω' g')) :
    r = r' ∧ s = s' ∧ ω = ω' ∧ proj O 2 (M + 3) g = proj O 2 (M + 3) g' := by
  have hπ0 : residue O π = 0 :=
    (residue_eq_zero_iff π).2 ((mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl)
  -- (r, s) recovery through the reduction shape
  have hshape : dblCoeff r s = dblCoeff r' s' := by
    have h1 := resVec_dblAssemble (π := π) hπ (s := s) (ω := ω) hgres
    have h2 := resVec_dblAssemble (π := π) hπ (s := s') (ω := ω') hgres'
    rw [← h1, ← h2]
    exact resVec_congr hπ (by omega) h
  obtain ⟨hrr', hss'⟩ := dblCoeff_inj hrs hrs' hshape
  set u := resSect O s + π * resOut ω with hu_def
  set u' := resSect O s' + π * resOut ω' with hu'_def
  set a := dblAssemble (π := π) s ω g with ha_def
  set a' := dblAssemble (π := π) s' ω' g' with ha'_def
  have hd : ∀ i, π ^ (M + 3) ∣ (a' i - a i) := (proj_eq_iff_dvd hπ a a').1 h
  have hru : residue O u = s := by
    rw [hu_def, map_add, map_mul, residue_resSect, hπ0, zero_mul, add_zero]
  have hru' : residue O u' = s' := by
    rw [hu'_def, map_add, map_mul, residue_resSect, hπ0, zero_mul, add_zero]
  have hroot : (monicPoly a).eval u = 0 := by
    rw [ha_def, monicPoly_dblAssemble]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    rw [hu_def]
    ring
  have hroot' : (monicPoly a').eval u' = 0 := by
    rw [ha'_def, monicPoly_dblAssemble]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    rw [hu'_def]
    ring
  -- the class congruence pushes the old cubic's value at the new root deep
  have hEa : π ^ (M + 3) ∣ (monicPoly a).eval u' := by
    have hval : (monicPoly a).eval u'
        = (a 2 - a' 2) * u' ^ 2 + (a 1 - a' 1) * u' + (a 0 - a' 0) := by
      have hexp : (monicPoly a).eval u' - (monicPoly a').eval u'
          = (a 2 - a' 2) * u' ^ 2 + (a 1 - a' 1) * u' + (a 0 - a' 0) := by
        rw [cubic_eval, cubic_eval]
        ring
      rw [← hexp, hroot', sub_zero]
    rw [hval]
    exact dvd_add (dvd_add ((dvd_sub_comm.1 (hd 2)).mul_right _)
      ((dvd_sub_comm.1 (hd 1)).mul_right _)) (dvd_sub_comm.1 (hd 0))
  -- factor out (u' − u); the cofactor is a unit (its residue is (s − r)²)
  have hEa' : π ^ (M + 3) ∣ (u' - u) * (u' ^ 2 + u' * u + u ^ 2 + a 2 * (u' + u) + a 1) := by
    have hfactor : (monicPoly a).eval u' - (monicPoly a).eval u
        = (u' - u) * (u' ^ 2 + u' * u + u ^ 2 + a 2 * (u' + u) + a 1) := by
      rw [cubic_eval, cubic_eval]
      ring
    rw [← hfactor, hroot, sub_zero]
    exact hEa
  have ha2res : residue O (a 2) = -(2 * r) - s := by
    have hcomp : a 2 = g 1 - u := by
      rw [ha_def]
      simp [dblAssemble]
      exact hu_def.symm
    rw [hcomp, map_sub, hru]
    have h1 : residue O (g 1) = -(2 * r) := by simpa using congrFun hgres 1
    rw [h1]
  have ha1res : residue O (a 1) = r ^ 2 + 2 * r * s := by
    have hcomp : a 1 = g 0 - u * g 1 := by
      rw [ha_def]
      simp [dblAssemble]
      exact Or.inl hu_def.symm
    have h0 : residue O (g 0) = r ^ 2 := by simpa using congrFun hgres 0
    have h1 : residue O (g 1) = -(2 * r) := by simpa using congrFun hgres 1
    rw [hcomp, map_sub, map_mul, hru, h0, h1]
    ring
  have hDres : residue O (u' ^ 2 + u' * u + u ^ 2 + a 2 * (u' + u) + a 1) = (s - r) ^ 2 := by
    simp only [map_add, map_mul, map_pow, hru, hru', ha2res, ha1res, ← hss']
    ring
  have hDunit : IsUnit (u' ^ 2 + u' * u + u ^ 2 + a 2 * (u' + u) + a 1) := by
    by_contra hcon
    have hmem := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcon)
    have hz := (residue_eq_zero_iff _).2 hmem
    rw [hDres] at hz
    exact (sub_ne_zero.2 (Ne.symm hrs)) ((pow_eq_zero_iff (by norm_num)).1 hz)
  have huu : π ^ (M + 3) ∣ (u' - u) :=
    dvd_of_isUnit_mul hDunit (by rwa [mul_comm] at hEa')
  -- ω recovery: cancel one π
  have hww : ω = ω' := by
    have hsub : u' - u = π * (resOut ω' - resOut ω) := by
      rw [hu_def, hu'_def, hss']
      ring
    rw [hsub] at huu
    obtain ⟨c, hc⟩ := huu
    have hcancel : π ^ (M + 2) ∣ (resOut ω' - resOut ω) := by
      refine ⟨c, mul_left_cancel₀ hπ.ne_zero ?_⟩
      calc π * (resOut ω' - resOut ω) = π ^ (M + 3) * c := hc
        _ = π * (π ^ (M + 2) * c) := by ring
    have hmk : Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (resOut ω')
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + 2)) (resOut ω) := by
      rw [Ideal.Quotient.eq]
      exact (mem_maximalIdeal_pow_iff_dvd hπ (M + 2) _).2
        (by rw [show resOut ω' - resOut ω = -(resOut ω - resOut ω') from by ring] at hcancel ⊢
            exact hcancel)
    rw [mk_resOut, mk_resOut] at hmk
    exact hmk.symm
  -- the quadratic part's class, through the peel
  refine ⟨hrr', hss', hww, (proj_eq_iff_dvd hπ g g').2 (fun i => ?_)⟩
  have hp := peel_congr (π := π) (N := M + 3) hd huu i
  rwa [show peel a' u' = g' from peel_dblAssemble (π := π) s' ω' g',
    show peel a u = g from peel_dblAssemble (π := π) s ω g] at hp

end DblFrame

/-! ## §5 The two quadratic-part families (direct Eisenstein / n = 2 rescale) -/

section QuadParts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}

/-- Direct-Eisenstein quadratic-part parameters (`v(recentred g₀) = 1`, `v(g₁) ≥ 1`). -/
def QDirParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) : Type _ :=
  Menu.exactSet π 1 (M + 3) × Menu.dvdSet π 1 (M + 3)

/-- The n = 2 mixed-precision truncation (quadratic mirror of H97r3's `mtrunc`). -/
def qtrunc (M : ℕ) (w : Res O (M + 1) × Res O (M + 2)) : Coeff O 2 M :=
  ![resFactor (O := O) (by omega : M ≤ M + 1) w.1,
    resFactor (O := O) (by omega : M ≤ M + 2) w.2]

/-- The n = 2 mixed-precision box over a decided class: `(d₀ mod π^(M+1), d₁ mod π^(M+2))`
with truncation in `decidedSet O 2 σ' M`. -/
def QInsParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (σ' : FactorizationType) (M : ℕ) : Type _ :=
  {w : Res O (M + 1) × Res O (M + 2) // qtrunc M w ∈ decidedSet O 2 σ' M}

/-- The direct quadratic part: recentre `(v = 1, v ≥ 1)` digits at `resSect r`. -/
noncomputable def qDir (r : ResidueField O) (M : ℕ) (p : QDirParams O π M) : Fin 2 → O :=
  shiftVec2 ![resOut p.1.1, resOut p.2.1] (-(resSect O r))

/-- The inserted quadratic part: recentre the `π`-rescale of an n = 2 decided class. -/
noncomputable def qIns (r : ResidueField O) {σ' : FactorizationType} (M : ℕ)
    (p : QInsParams O σ' M) : Fin 2 → O :=
  shiftVec2 ![π ^ 2 * resOut p.1.1, π * resOut p.1.2] (-(resSect O r))

/-- (private) H97r3's congruence-transfer helpers, re-derived (they are `private` there). -/
private theorem a0c_dvd_of_dvd_sub {p c x y : O} (hpc : p ∣ c) (hs : c ∣ (x - y))
    (hy : p ∣ y) : p ∣ x := by
  have h2 : p ∣ (x - y) + y := dvd_add (hpc.trans hs) hy
  simpa using h2

private theorem a0c_not_dvd_of_dvd_sub {p c x y : O} (hpc : p ∣ c) (hs : c ∣ (x - y))
    (hy : ¬ p ∣ y) : ¬ p ∣ x := fun hx =>
  hy (a0c_dvd_of_dvd_sub hpc (dvd_sub_comm.1 hs) hx)

/-- (private) unshifting a recentred quadratic recovers the recentred vector. -/
private theorem shiftVec2_unshift (e : Fin 2 → O) (ρ : O) :
    shiftVec2 (shiftVec2 e (-ρ)) ρ = e := by
  have h := shiftVec2_shiftVec2_neg e (-ρ)
  rwa [neg_neg] at h

theorem qDir_res (hπ : Irreducible π) (r : ResidueField O) (M : ℕ) (p : QDirParams O π M) :
    (fun i => residue O (qDir (π := π) r M p i)) = ![r ^ 2, -(2 * r)] := by
  have h0 : π ∣ resOut p.1.1 := by
    have h := (exact_resOut_of_mem_exactSet hπ (by omega) p.1.2).1
    rwa [pow_one] at h
  have h1 : π ∣ resOut p.2.1 := by
    have h := dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2
    rwa [pow_one] at h
  have hz0 : residue O (resOut p.1.1) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h0)
  have hz1 : residue O (resOut p.2.1) = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h1)
  have hρ : residue O (resSect O r) = r := residue_resSect O r
  funext i
  fin_cases i
  · show residue O ((-(resSect O r)) ^ 2 + resOut p.2.1 * (-(resSect O r)) + resOut p.1.1)
        = r ^ 2
    simp only [map_add, map_mul, map_pow, map_neg, hρ, hz0, hz1]
    ring
  · show residue O (resOut p.2.1 + 2 * (-(resSect O r))) = -(2 * r)
    simp only [map_add, map_mul, map_neg, map_ofNat, hρ, hz1]
    ring

theorem qIns_res (hπ : Irreducible π) (r : ResidueField O) {σ' : FactorizationType} (M : ℕ)
    (p : QInsParams O σ' M) :
    (fun i => residue O (qIns (π := π) r M p i)) = ![r ^ 2, -(2 * r)] := by
  have hπ0 : residue O π = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 dvd_rfl)
  have hρ : residue O (resSect O r) = r := residue_resSect O r
  funext i
  fin_cases i
  · show residue O ((-(resSect O r)) ^ 2 + (π * resOut p.1.2) * (-(resSect O r))
        + π ^ 2 * resOut p.1.1) = r ^ 2
    simp only [map_add, map_mul, map_pow, map_neg, hρ, hπ0]
    ring
  · show residue O ((π * resOut p.1.2) + 2 * (-(resSect O r))) = -(2 * r)
    simp only [map_add, map_mul, map_neg, map_ofNat, hπ0, hρ]
    ring

/-- The direct quadratic part is `ramType`-decided at level `M + 3` (shifted Eisenstein). -/
theorem qDir_decided (hπ : Irreducible π) (r : ResidueField O) (M : ℕ)
    (p : QDirParams O π M) :
    DecidedAt O 2 ramType (M + 3) (proj O 2 (M + 3) (qDir (π := π) r M p)) := by
  have hinv : shiftVec2 (qDir (π := π) r M p) (resSect O r)
      = ![resOut p.1.1, resOut p.2.1] :=
    shiftVec2_unshift ![resOut p.1.1, resOut p.2.1] (resSect O r)
  have he0 := exact_resOut_of_mem_exactSet hπ (by omega : 1 + 1 ≤ M + 3) p.1.2
  have he0d : π ∣ resOut p.1.1 := by have h := he0.1; rwa [pow_one] at h
  have he1 : π ∣ resOut p.2.1 := by
    have h := dvd_resOut_of_mem_dvdSet hπ (by omega) p.2.2
    rwa [pow_one] at h
  refine decidedAt_of_congr hπ (fun b' hb' => ?_)
  rw [← typeOf_shiftVec2 b' (resSect O r)]
  have hkey : ∀ i, π ^ (M + 3)
      ∣ (shiftVec2 b' (resSect O r) i - (![resOut p.1.1, resOut p.2.1] : Fin 2 → O) i) := by
    intro i
    have h := dvd_shiftVec2_sub (π := π) (resSect O r) hb' i
    rwa [hinv] at h
  have hdvd1 : π ∣ π ^ (M + 3) := dvd_pow_self π (by omega)
  have hdvd2 : π ^ 2 ∣ π ^ (M + 3) := pow_dvd_pow π (by omega)
  have h0 : π ∣ shiftVec2 b' (resSect O r) 0 :=
    a0c_dvd_of_dvd_sub hdvd1 (hkey 0) he0d
  have h0' : ¬ π ^ 2 ∣ shiftVec2 b' (resSect O r) 0 :=
    a0c_not_dvd_of_dvd_sub hdvd2 (hkey 0) he0.2
  have h1 : π ∣ shiftVec2 b' (resSect O r) 1 :=
    a0c_dvd_of_dvd_sub hdvd1 (hkey 1) he1
  exact typeOf_ram_of_eisenstein ((mem_maximalIdeal_iff_dvd hπ _).2 h0)
    (fun hc => h0' ((mem_maximalIdeal_pow_iff_dvd hπ 2 _).1 hc))
    ((mem_maximalIdeal_iff_dvd hπ _).2 h1)

/-- The inserted quadratic part is `σ'`-decided at level `M + 3` (`π`-rescale of a decided
level-`M` class). -/
theorem qIns_decided (hπ : Irreducible π) (r : ResidueField O) {σ' : FactorizationType}
    (M : ℕ) (p : QInsParams O σ' M) :
    DecidedAt O 2 σ' (M + 3) (proj O 2 (M + 3) (qIns (π := π) r M p)) := by
  have hinv : shiftVec2 (qIns (π := π) r M p) (resSect O r)
      = ![π ^ 2 * resOut p.1.1, π * resOut p.1.2] :=
    shiftVec2_unshift ![π ^ 2 * resOut p.1.1, π * resOut p.1.2] (resSect O r)
  refine decidedAt_of_congr hπ (fun b' hb' => ?_)
  rw [← typeOf_shiftVec2 b' (resSect O r)]
  have hkey : ∀ i, π ^ (M + 3) ∣ (shiftVec2 b' (resSect O r) i
      - (![π ^ 2 * resOut p.1.1, π * resOut p.1.2] : Fin 2 → O) i) := by
    intro i
    have h := dvd_shiftVec2_sub (π := π) (resSect O r) hb' i
    rwa [hinv] at h
  obtain ⟨c0, hc0⟩ := hkey 0
  obtain ⟨c1, hc1⟩ := hkey 1
  have e0 : shiftVec2 b' (resSect O r) 0
      = π ^ 2 * (resOut p.1.1 + π ^ (M + 1) * c0) := by
    have h0 : shiftVec2 b' (resSect O r) 0 - π ^ 2 * resOut p.1.1 = π ^ (M + 3) * c0 := hc0
    linear_combination h0
  have e1 : shiftVec2 b' (resSect O r) 1
      = π * (resOut p.1.2 + π ^ (M + 2) * c1) := by
    have h1 : shiftVec2 b' (resSect O r) 1 - π * resOut p.1.2 = π ^ (M + 3) * c1 := hc1
    linear_combination h1
  rw [typeOf_extract2 hπ (d := ![resOut p.1.1 + π ^ (M + 1) * c0,
    resOut p.1.2 + π ^ (M + 2) * c1]) e0 e1]
  refine p.2 _ ?_
  funext i
  fin_cases i
  · have hR : qtrunc (O := O) M p.1 0
        = Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resOut p.1.1) := by
      have h1 := resFactor_mk (O := O) (by omega : M ≤ M + 1) (resOut p.1.1)
      rw [mk_resOut] at h1
      exact h1
    show Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resOut p.1.1 + π ^ (M + 1) * c0)
        = qtrunc M p.1 0
    rw [hR, Ideal.Quotient.eq]
    rw [show (resOut p.1.1 + π ^ (M + 1) * c0) - resOut p.1.1 = π ^ M * (π * c0) by ring]
    exact (mem_maximalIdeal_pow_iff_dvd hπ M _).2 ⟨π * c0, rfl⟩
  · have hR : qtrunc (O := O) M p.1 1
        = Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resOut p.1.2) := by
      have h1 := resFactor_mk (O := O) (by omega : M ≤ M + 2) (resOut p.1.2)
      rw [mk_resOut] at h1
      exact h1
    show Ideal.Quotient.mk ((maximalIdeal O) ^ M) (resOut p.1.2 + π ^ (M + 2) * c1)
        = qtrunc M p.1 1
    rw [hR, Ideal.Quotient.eq]
    rw [show (resOut p.1.2 + π ^ (M + 2) * c1) - resOut p.1.2 = π ^ M * (π ^ 2 * c1) by ring]
    exact (mem_maximalIdeal_pow_iff_dvd hπ M _).2 ⟨π ^ 2 * c1, rfl⟩

theorem qDir_inj (hπ : Irreducible π) (r : ResidueField O) (M : ℕ) {p p' : QDirParams O π M}
    (h : proj O 2 (M + 3) (qDir (π := π) r M p) = proj O 2 (M + 3) (qDir (π := π) r M p')) :
    p = p' := by
  have hd := (proj_eq_iff_dvd hπ (qDir (π := π) r M p) (qDir (π := π) r M p')).1 h
  have hinv : shiftVec2 (qDir (π := π) r M p) (resSect O r)
      = ![resOut p.1.1, resOut p.2.1] := shiftVec2_unshift _ _
  have hinv' : shiftVec2 (qDir (π := π) r M p') (resSect O r)
      = ![resOut p'.1.1, resOut p'.2.1] := shiftVec2_unshift _ _
  have hkey : ∀ i, π ^ (M + 3) ∣ ((![resOut p'.1.1, resOut p'.2.1] : Fin 2 → O) i
      - (![resOut p.1.1, resOut p.2.1] : Fin 2 → O) i) := by
    intro i
    have hs := dvd_shiftVec2_sub (π := π) (resSect O r) hd i
    rwa [hinv, hinv'] at hs
  have h0 : p.1.1 = p'.1.1 := by
    rw [← mk_resOut p.1.1, ← mk_resOut p'.1.1, Ideal.Quotient.eq]
    exact (mem_maximalIdeal_pow_iff_dvd hπ (M + 3) _).2 (dvd_sub_comm.1 (hkey 0))
  have h1 : p.2.1 = p'.2.1 := by
    rw [← mk_resOut p.2.1, ← mk_resOut p'.2.1, Ideal.Quotient.eq]
    exact (mem_maximalIdeal_pow_iff_dvd hπ (M + 3) _).2 (dvd_sub_comm.1 (hkey 1))
  exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)

theorem qIns_inj (hπ : Irreducible π) (r : ResidueField O) {σ' : FactorizationType} (M : ℕ)
    {p p' : QInsParams O σ' M}
    (h : proj O 2 (M + 3) (qIns (π := π) r M p) = proj O 2 (M + 3) (qIns (π := π) r M p')) :
    p = p' := by
  have hd := (proj_eq_iff_dvd hπ (qIns (π := π) r M p) (qIns (π := π) r M p')).1 h
  have hinv : shiftVec2 (qIns (π := π) r M p) (resSect O r)
      = ![π ^ 2 * resOut p.1.1, π * resOut p.1.2] := shiftVec2_unshift _ _
  have hinv' : shiftVec2 (qIns (π := π) r M p') (resSect O r)
      = ![π ^ 2 * resOut p'.1.1, π * resOut p'.1.2] := shiftVec2_unshift _ _
  have hkey : ∀ i, π ^ (M + 3)
      ∣ ((![π ^ 2 * resOut p'.1.1, π * resOut p'.1.2] : Fin 2 → O) i
        - (![π ^ 2 * resOut p.1.1, π * resOut p.1.2] : Fin 2 → O) i) := by
    intro i
    have hs := dvd_shiftVec2_sub (π := π) (resSect O r) hd i
    rwa [hinv, hinv'] at hs
  have h0 : p.1.1 = p'.1.1 := by
    obtain ⟨c, hc⟩ := hkey 0
    have hc' : π ^ 2 * resOut p'.1.1 - π ^ 2 * resOut p.1.1 = π ^ (M + 3) * c := hc
    have hcc : resOut p.1.1 - resOut p'.1.1 = π ^ (M + 1) * (-c) :=
      mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero)
        (by linear_combination -hc')
    rw [← mk_resOut p.1.1, ← mk_resOut p'.1.1, Ideal.Quotient.eq, hcc]
    exact (mem_maximalIdeal_pow_iff_dvd hπ (M + 1) _).2 ⟨-c, rfl⟩
  have h1 : p.1.2 = p'.1.2 := by
    obtain ⟨c, hc⟩ := hkey 1
    have hc' : π * resOut p'.1.2 - π * resOut p.1.2 = π ^ (M + 3) * c := hc
    have hcc : resOut p.1.2 - resOut p'.1.2 = π ^ (M + 2) * (-c) :=
      mul_left_cancel₀ hπ.ne_zero (by linear_combination -hc')
    rw [← mk_resOut p.1.2, ← mk_resOut p'.1.2, Ideal.Quotient.eq, hcc]
    exact (mem_maximalIdeal_pow_iff_dvd hπ (M + 2) _).2 ⟨-c, rfl⟩
  exact Subtype.ext (Prod.ext h0 h1)

/-- The two quadratic-part families are disjoint at the class level (`v(recentred g₀) = 1`
against `v ≥ 2`). -/
theorem qDir_ne_qIns (hπ : Irreducible π) (r : ResidueField O) {σ' : FactorizationType}
    (M : ℕ) (p : QDirParams O π M) (p' : QInsParams O σ' M) :
    proj O 2 (M + 3) (qDir (π := π) r M p) ≠ proj O 2 (M + 3) (qIns (π := π) r M p') := by
  intro h
  have hd := (proj_eq_iff_dvd hπ (qDir (π := π) r M p) (qIns (π := π) r M p')).1 h
  have hinvD : shiftVec2 (qDir (π := π) r M p) (resSect O r)
      = ![resOut p.1.1, resOut p.2.1] := shiftVec2_unshift _ _
  have hinvI : shiftVec2 (qIns (π := π) r M p') (resSect O r)
      = ![π ^ 2 * resOut p'.1.1, π * resOut p'.1.2] := shiftVec2_unshift _ _
  have hkey0 : π ^ (M + 3) ∣ (π ^ 2 * resOut p'.1.1 - resOut p.1.1) := by
    have hs := dvd_shiftVec2_sub (π := π) (resSect O r) hd 0
    rwa [hinvD, hinvI] at hs
  have h2 : π ^ 2 ∣ resOut p.1.1 := by
    have ha : π ^ 2 ∣ π ^ 2 * resOut p'.1.1 := Dvd.intro _ rfl
    have hb : π ^ 2 ∣ (π ^ 2 * resOut p'.1.1 - resOut p.1.1) :=
      (pow_dvd_pow π (le_refl 2)).trans ((pow_dvd_pow π (by omega)).trans hkey0)
    have hc := dvd_sub ha hb
    rwa [sub_sub_cancel] at hc
  exact (exact_resOut_of_mem_exactSet hπ (by omega) p.1.2).2 h2

/-- (private) the `AddMonoidHom` form of `qtrunc`, for the fibre-count engine. -/
private def qtruncHom (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (M : ℕ) : (Res O (M + 1) × Res O (M + 2)) →+ Coeff O 2 M :=
  Pi.addMonoidHom fun i =>
    ![((resFactor (O := O) (by omega : M ≤ M + 1)).toAddMonoidHom.comp
        (AddMonoidHom.fst (Res O (M + 1)) (Res O (M + 2)))),
      ((resFactor (O := O) (by omega : M ≤ M + 2)).toAddMonoidHom.comp
        (AddMonoidHom.snd (Res O (M + 1)) (Res O (M + 2))))] i

private theorem qtruncHom_apply (M : ℕ) (w : Res O (M + 1) × Res O (M + 2)) :
    qtruncHom O M w = qtrunc M w := by
  funext i
  fin_cases i <;> rfl

private theorem qtruncHom_surjective (M : ℕ) :
    Function.Surjective (qtruncHom O M) := by
  intro c
  obtain ⟨y, hy⟩ := resFactor_surjective (O := O) (by omega : M ≤ M + 1) (c 0)
  obtain ⟨z, hz⟩ := resFactor_surjective (O := O) (by omega : M ≤ M + 2) (c 1)
  refine ⟨(y, z), ?_⟩
  funext i
  fin_cases i
  · exact hy
  · exact hz

/-- Cardinality of the inserted box: `q³` fibre digits over each decided level-`M` class. -/
theorem card_qInsParams (σ' : FactorizationType) (M : ℕ) :
    Nat.card (QInsParams O σ' M) * residueCard O ^ (2 * M)
      = decidedCount O 2 σ' M * residueCard O ^ (2 * M + 3) := by
  classical
  have hpre : (qtruncHom O M) ⁻¹' (decidedSet O 2 σ' M)
      = {w : Res O (M + 1) × Res O (M + 2) | qtrunc M w ∈ decidedSet O 2 σ' M} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_setOf_eq, qtruncHom_apply]
  have h1 := card_preimage_of_surjective (qtruncHom O M) (qtruncHom_surjective M)
    (decidedSet O 2 σ' M)
  have h2 := card_preimage_of_surjective (qtruncHom O M) (qtruncHom_surjective M) Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h2
  have hQ : Nat.card (QInsParams O σ' M)
      = Nat.card ((qtruncHom O M) ⁻¹' (decidedSet O 2 σ' M)) := by
    rw [hpre]
    rfl
  have hprod : Nat.card (Res O (M + 1) × Res O (M + 2)) = residueCard O ^ (2 * M + 3) := by
    rw [Nat.card_prod, card_res, card_res, ← pow_add]
    congr 1
    omega
  have hcf : Nat.card (Coeff O 2 M) = residueCard O ^ (2 * M) := card_coeff 2 M
  rw [hprod, hcf] at h2
  have hdc : decidedCount O 2 σ' M = Nat.card (decidedSet O 2 σ' M) := rfl
  rw [hQ, h1, hdc, h2]
  ring

end QuadParts

/-! ## §6 The level-1 (separable-reduction) base families -/

section LevelOne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- Reducing a monic polynomial along a ring hom reduces its coefficient vector
(G61c's private `g61c_map_monicPoly`, repeated). -/
private theorem ifc7_map_monicPoly {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (φ : R →+* S) {n : ℕ} (a : Fin n → R) :
    (monicPoly a).map φ = monicPoly (fun i => φ (a i)) := by
  simp only [monicPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]

/-- The monic cubic, expanded (G61c's private `g61c_cubic_eval` inline `hexp`, repeated). -/
private theorem ifc7_cubic_expand {K : Type*} [CommRing K] [IsDomain K] (a : Fin 3 → K) :
    monicPoly a = X ^ 3 + C (a 2) * X ^ 2 + C (a 1) * X + C (a 0) := by
  simp only [monicPoly, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero,
    pow_one, mul_one]
  ring

/-- **Split, level 1** (new; the `Split3` mirror of `inert3_decided`, via G.55's
`typeOf_split3_of_residue`): a class whose residue cubic has three distinct roots is
`c3split`-decided. -/
theorem split3_decided_res {v : Fin 3 → ResidueField O} (hv : Menu.Split3 v) :
    DecidedAt O 3 c3split 1 (Menu.liftRes1 v) := by
  obtain ⟨r, s, t, hrs, hrt, hst, hveq⟩ := hv
  have e0 : v 0 = -(r * s * t) := by rw [hveq]; rfl
  have e1 : v 1 = r * s + r * t + s * t := by rw [hveq]; rfl
  have e2 : v 2 = -(r + s + t) := by rw [hveq]; rfl
  intro b hb
  have hres : (fun i => residue O (b i)) = v := Menu.residue_comp_of_proj_liftRes1 hb
  refine typeOf_split3_of_residue (resSect O r) (resSect O s) (resSect O t)
    (isUnit_sub_of_residue_ne (by rw [residue_resSect, residue_resSect]; exact hrs))
    (isUnit_sub_of_residue_ne (by rw [residue_resSect, residue_resSect]; exact hrt))
    (isUnit_sub_of_residue_ne (by rw [residue_resSect, residue_resSect]; exact hst)) ?_
  rw [residue_resSect, residue_resSect, residue_resSect,
    ifc7_map_monicPoly (residue O) b, hres, ifc7_cubic_expand, e0, e1, e2]
  simp only [map_neg, map_add, map_mul]
  ring

/-- The level-1 base family for a level-1 certificate: all level-`(M+3)` refinements. -/
def levelOneFam (P : Set (Fin 3 → ResidueField O)) (M : ℕ) : Set (Coeff O 3 (M + 3)) :=
  (coeffFactor (O := O) 3 (by omega : 1 ≤ M + 3)) ⁻¹' (Menu.liftRes1 '' P)

theorem levelOneFam_subset_decided {σ : FactorizationType}
    {P : Set (Fin 3 → ResidueField O)}
    (hdec : ∀ v ∈ P, DecidedAt O 3 σ 1 (Menu.liftRes1 v)) (M : ℕ) :
    levelOneFam (O := O) P M ⊆ decidedSet O 3 σ (M + 3) := by
  intro c hc
  have hc' : coeffFactor (O := O) 3 (by omega : 1 ≤ M + 3) c ∈ Menu.liftRes1 '' P := hc
  obtain ⟨v, hvP, hveq⟩ := hc'
  refine preimage_decidedSet_subset (O := O) (by omega : 1 ≤ M + 3) ?_
  exact Set.mem_preimage.2 (hveq ▸ hdec v hvP)

theorem card_levelOneFam (P : Set (Fin 3 → ResidueField O)) (M : ℕ) :
    Nat.card (levelOneFam (O := O) P M) * residueCard O ^ 3
      = Nat.card P * residueCard O ^ (3 * (M + 3)) := by
  have h1 := card_preimage_coeffFactor (O := O) 3 (by omega : 1 ≤ M + 3)
    (Menu.liftRes1 '' P)
  rw [card_coeff, card_coeff, Nat.card_image_of_injective Menu.liftRes1_injective,
    show (3 * 1 : ℕ) = 3 from rfl] at h1
  exact h1

/-- Members of a level-1 family have their residue vector in `P` — the shape tag. -/
theorem resVec_of_mem_levelOneFam {P : Set (Fin 3 → ResidueField O)} {M : ℕ}
    {a : Fin 3 → O} (h : proj O 3 (M + 3) a ∈ levelOneFam (O := O) P M) :
    resVec a ∈ P := by
  have h2 : coeffFactor (O := O) 3 (by omega : 1 ≤ M + 3) (proj O 3 (M + 3) a)
      ∈ Menu.liftRes1 '' P := h
  rw [coeffFactor_proj, proj_one_eq_liftRes1] at h2
  obtain ⟨v, hvP, hveq⟩ := h2
  have hv : v = resVec a := Menu.liftRes1_injective hveq
  exact hv ▸ hvP

end LevelOne

/-! ## §7 The five master step inequalities

Each is the count of the disjoint decided families at level `M + 3`, divided by
`q^(3(M+3))`.  Notation: `q = (residueCard O : ℝ)`. -/

section Steps

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-! ### §7a The counting and arithmetic kit -/

/-- A decided subset plus an injective decided family with disjoint range, counted. -/
private theorem a0c_card_add_le {α : Type*} [Finite α] {S A : Set α} (hA : A ⊆ S)
    {P : Type*} [Finite P] (f : P → α) (hf : Function.Injective f) (hfS : ∀ p, f p ∈ S)
    (hdisj : ∀ p, f p ∉ A) : Nat.card A + Nat.card P ≤ Nat.card S := by
  classical
  set F : A ⊕ P → S := Sum.elim (fun a => ⟨a.1, hA a.2⟩) (fun p => ⟨f p, hfS p⟩) with hF
  have hinj : Function.Injective F := by
    rintro (a | p) (a' | p') h
    · simp only [hF, Sum.elim_inl, Subtype.mk.injEq] at h
      exact congrArg Sum.inl (Subtype.ext h)
    · simp only [hF, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd (h ▸ a.2) (hdisj p')
    · simp only [hF, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd (h.symm ▸ a'.2) (hdisj p)
    · simp only [hF, Sum.elim_inr, Subtype.mk.injEq] at h
      exact congrArg Sum.inr (hf h)
  have hcard := Nat.card_le_card_of_injective F hinj
  rwa [Nat.card_sum] at hcard

/-- Injective decided family alone, counted. -/
private theorem a0c_card_le {α : Type*} [Finite α] {S : Set α}
    {P : Type*} [Finite P] (f : P → α) (hf : Function.Injective f) (hfS : ∀ p, f p ∈ S) :
    Nat.card P ≤ Nat.card S := by
  have hinj : Function.Injective (fun p => (⟨f p, hfS p⟩ : S)) := by
    intro p p' h
    exact hf (congrArg Subtype.val h)
  exact Nat.card_le_card_of_injective _ hinj

/-- The generic step arithmetic: from a count inequality and the loop's mixed-precision
identity, the fixed-point seq inequality (all in `ℝ`, powers of `x = q`). -/
private theorem a0c_step_arith (x : ℝ) (hx0 : 0 < x) (M : ℕ) (T cPre cM cN3 : ℝ)
    (hpre : cPre * x ^ (3 * M) = cM * x ^ (3 * M + 3))
    (hcount : T + x * cPre ≤ cN3) :
    T / x ^ (3 * (M + 3)) + (x ^ 5)⁻¹ * (cM / x ^ (3 * M)) ≤ cN3 / x ^ (3 * (M + 3)) := by
  have hxne : x ≠ 0 := hx0.ne'
  have hpre' : cPre = cM * x ^ 3 := by
    have h4 : cPre * x ^ (3 * M) = (cM * x ^ 3) * x ^ (3 * M) := by
      rw [hpre, show 3 * M + 3 = 3 + 3 * M from by omega, pow_add]
      ring
    exact mul_right_cancel₀ (pow_ne_zero _ hxne) h4
  rw [le_div_iff₀ (pow_pos hx0 _), add_mul]
  have e1 : T / x ^ (3 * (M + 3)) * x ^ (3 * (M + 3)) = T :=
    div_mul_cancel₀ _ (pow_ne_zero _ hxne)
  have e2 : ((x ^ 5)⁻¹ * (cM / x ^ (3 * M))) * x ^ (3 * (M + 3)) = cM * x ^ 4 := by
    rw [show 3 * (M + 3) = 3 * M + 9 from by omega, pow_add]
    field_simp
  rw [e1, e2]
  calc T + cM * x ^ 4 = T + x * cPre := by rw [hpre']; ring
    _ ≤ cN3 := hcount

/-- Off-diagonal pair census, subtraction-free. -/
private theorem a0c_card_ne_pairs (K : Type*) [Finite K] :
    Nat.card {p : K × K // p.1 ≠ p.2} + Nat.card K = Nat.card K ^ 2 := by
  classical
  have h1 : Nat.card {p : K × K // p.1 = p.2} = Nat.card K := by
    refine Nat.card_congr ⟨fun p => p.1.1, fun k => ⟨(k, k), rfl⟩, fun p => ?_, fun k => rfl⟩
    ext
    · rfl
    · exact p.2
  have h2 : Nat.card ({p : K × K // p.1 = p.2} ⊕ {p : K × K // p.1 ≠ p.2})
      = Nat.card (K × K) :=
    Nat.card_congr (Equiv.sumCompl (fun p : K × K => p.1 = p.2))
  rw [Nat.card_sum, h1, Nat.card_prod] at h2
  rw [pow_two, ← h2]
  omega

/-- The loop-box count, cast to `ℝ` and normalized. -/
private theorem a0c_loop_pre (σ : FactorizationType) (M : ℕ) :
    (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M)) : ℝ)
        * (residueCard O : ℝ) ^ (3 * M)
      = (decidedCount O 3 σ M : ℝ) * (residueCard O : ℝ) ^ (3 * M + 3) := by
  have h := card_preimage_mtrunc (O := O) M (decidedSet O 3 σ M)
  rw [card_coeff, card_mbox] at h
  exact_mod_cast h

/-- Coordinates of a loop member's recentred vector are in `𝔪`. -/
private theorem a0c_loop_mem_m {π : O} (hπ : Irreducible π) {σ : FactorizationType} {M : ℕ}
    (p : LoopParams O σ M) : ∀ i,
    (![π ^ 3 * resOut (p.2 : MBox O M).1, π ^ 2 * resOut (p.2 : MBox O M).2.1,
      π * resOut (p.2 : MBox O M).2.2] : Fin 3 → O) i ∈ maximalIdeal O := by
  intro i
  fin_cases i
  · show π ^ 3 * resOut (p.2 : MBox O M).1 ∈ maximalIdeal O
    exact (mem_maximalIdeal_iff_dvd hπ _).2 ⟨π ^ 2 * resOut (p.2 : MBox O M).1, by ring⟩
  · show π ^ 2 * resOut (p.2 : MBox O M).2.1 ∈ maximalIdeal O
    exact (mem_maximalIdeal_iff_dvd hπ _).2 ⟨π * resOut (p.2 : MBox O M).2.1, by ring⟩
  · show π * resOut (p.2 : MBox O M).2.2 ∈ maximalIdeal O
    exact (mem_maximalIdeal_iff_dvd hπ _).2 ⟨resOut (p.2 : MBox O M).2.2, by ring⟩

/-- A loop member's residue vector is the cube tag. -/
private theorem a0c_loop_resVec {π : O} (hπ : Irreducible π) {σ : FactorizationType} {M : ℕ}
    (p : LoopParams O σ M) :
    resVec (cubeMember p.1 ![π ^ 3 * resOut (p.2 : MBox O M).1,
      π ^ 2 * resOut (p.2 : MBox O M).2.1, π * resOut (p.2 : MBox O M).2.2])
      = cubeCoeff p.1 :=
  resVec_cubeMember (a0c_loop_mem_m hπ p)

/-! ### §7b The five steps -/

/-- **STEP (inert)**: level-1 base (`NoRootCubic` census) + loop. -/
theorem step_inert (M : ℕ) :
    (Nat.card {v : Fin 3 → ResidueField O // Menu.NoRootCubic v} : ℝ)
        / (residueCard O : ℝ) ^ 3
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 c3inert M
      ≤ decidedSeq O 3 c3inert (M + 3) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  -- the two disjoint decided families
  have hA : levelOneFam (O := O) {v | Menu.NoRootCubic v} M ⊆ decidedSet O 3 c3inert (M + 3) :=
    levelOneFam_subset_decided (fun v hv => inert3_decided hv) M
  have hdisj : ∀ p : LoopParams O c3inert M,
      loopMap (π := π) M p ∉ levelOneFam (O := O) {v | Menu.NoRootCubic v} M := by
    intro p hmem
    have hres := resVec_of_mem_levelOneFam (O := O)
      (P := {v | Menu.NoRootCubic v}) (M := M) hmem
    rw [a0c_loop_resVec hπ p] at hres
    exact noRootCubic_ne_cubeCoeff hres p.1 rfl
  have hcount := a0c_card_add_le hA (loopMap (π := π) M) (loopMap_inj hπ M)
    (loopMap_decided hπ M) hdisj
  -- cards
  have hLP : Nat.card (LoopParams O c3inert M)
      = residueCard O * Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3inert M)) := by
    unfold LoopParams
    rw [Nat.card_prod]
    rfl
  rw [hLP] at hcount
  -- pass to ℝ
  have hcount' : (Nat.card (levelOneFam (O := O) {v | Menu.NoRootCubic v} M) : ℝ)
      + (residueCard O : ℝ)
        * (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3inert M)) : ℝ)
      ≤ (decidedCount O 3 c3inert (M + 3) : ℝ) := by
    exact_mod_cast hcount
  have harith := a0c_step_arith (residueCard O : ℝ) hq0 M
    (Nat.card (levelOneFam (O := O) {v | Menu.NoRootCubic v} M))
    (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3inert M)))
    (decidedCount O 3 c3inert M) (decidedCount O 3 c3inert (M + 3))
    (a0c_loop_pre c3inert M) hcount'
  -- identify the base term
  have hfam : (Nat.card (levelOneFam (O := O) {v | Menu.NoRootCubic v} M) : ℝ)
      / (residueCard O : ℝ) ^ (3 * (M + 3))
      = (Nat.card {v : Fin 3 → ResidueField O // Menu.NoRootCubic v} : ℝ)
        / (residueCard O : ℝ) ^ 3 := by
    rw [div_eq_div_iff (pow_pos hq0 _).ne' (pow_pos hq0 _).ne']
    have h := card_levelOneFam (O := O) {v | Menu.NoRootCubic v} M
    exact_mod_cast h
  rw [show decidedSeq O 3 c3inert (M + 3)
      = (decidedCount O 3 c3inert (M + 3) : ℝ) / (residueCard O : ℝ) ^ (3 * (M + 3)) from rfl,
    show decidedSeq O 3 c3inert M
      = (decidedCount O 3 c3inert M : ℝ) / (residueCard O : ℝ) ^ (3 * M) from rfl,
    ← hfam]
  exact harith

/-- The four digit-set cardinalities at level `M + 3`, packaged. -/
private theorem a0c_digit_cards {π : O} (hπ : Irreducible π) (M : ℕ) :
    Nat.card (Menu.dvdSet π 1 (M + 3)) = residueCard O ^ (M + 2)
    ∧ Nat.card (Menu.dvdSet π 2 (M + 3)) = residueCard O ^ (M + 1)
    ∧ Nat.card (Menu.exactSet π 1 (M + 3)) + residueCard O ^ (M + 1)
        = residueCard O ^ (M + 2)
    ∧ Nat.card (Menu.exactSet π 2 (M + 3)) + residueCard O ^ M
        = residueCard O ^ (M + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := Menu.card_dvdSet (O := O) hπ (k := 1) (r := M + 2)
    rwa [show 1 + (M + 2) = M + 3 from by omega] at h
  · have h := Menu.card_dvdSet (O := O) hπ (k := 2) (r := M + 1)
    rwa [show 2 + (M + 1) = M + 3 from by omega] at h
  · have h := Menu.card_exactSet_add (O := O) hπ (k := 1) (r := M + 1)
    rwa [show 1 + (M + 1) + 1 = M + 3 from by omega] at h
  · have h := Menu.card_exactSet_add (O := O) hπ (k := 2) (r := M)
    rwa [show 2 + M + 1 = M + 3 from by omega] at h

/-- The exponent splittings used by every base-term computation. -/
private theorem a0c_pow_split (x : ℝ) (M : ℕ) :
    x ^ (M + 1) = x ^ M * x ^ 1 ∧ x ^ (M + 2) = x ^ M * x ^ 2
    ∧ x ^ (3 * (M + 3)) = (x ^ M) ^ 3 * x ^ 9 := by
  refine ⟨pow_add x M 1, pow_add x M 2, ?_⟩
  rw [show 3 * (M + 3) = M * 3 + 9 from by omega, pow_add, pow_mul]

/-- **STEP (ram)**: E + R bases + loop. -/
theorem step_ram (M : ℕ) :
    (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3
        + ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 5)
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 c3ram M
      ≤ decidedSeq O 3 c3ram (M + 3) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  set F : (EParams O π M ⊕ RParams O π M ⊕ LoopParams O c3ram M) → Coeff O 3 (M + 3) :=
    Sum.elim (eMap M) (Sum.elim (rMap M) (loopMap (π := π) M)) with hF
  have hFS : ∀ z, F z ∈ decidedSet O 3 c3ram (M + 3) := by
    rintro (p | p | p)
    · exact eMap_decided hπ M p
    · exact rMap_decided hπ M p
    · exact loopMap_decided hπ M p
  have hFinj : Function.Injective F := by
    rintro (p | p | p) (p' | p' | p') h <;>
      simp only [hF, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (eMap_inj hπ M h)
    · exact absurd h (eMap_ne_rMap hπ M p p')
    · exact absurd h (eMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (eMap_ne_rMap hπ M p' p)
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) (rMap_inj hπ M h)
    · exact absurd h (rMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (eMap_ne_loopMap hπ M p' p)
    · exact absurd h.symm (rMap_ne_loopMap hπ M p' p)
    · exact congrArg (fun z => Sum.inr (Sum.inr z)) (loopMap_inj hπ M h)
  have hcount := a0c_card_le F hFinj hFS
  rw [Nat.card_sum, Nat.card_sum] at hcount
  have hE : Nat.card (EParams O π M)
      = residueCard O * (Nat.card (Menu.exactSet π 1 (M + 3))
        * (Nat.card (Menu.dvdSet π 1 (M + 3)) * Nat.card (Menu.dvdSet π 1 (M + 3)))) := by
    unfold EParams
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    rfl
  have hR : Nat.card (RParams O π M)
      = residueCard O * (Nat.card (Menu.exactSet π 2 (M + 3))
        * (Nat.card (Menu.dvdSet π 2 (M + 3)) * Nat.card (Menu.dvdSet π 1 (M + 3)))) := by
    unfold RParams
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    rfl
  have hLP : Nat.card (LoopParams O c3ram M)
      = residueCard O * Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3ram M)) := by
    unfold LoopParams
    rw [Nat.card_prod]
    rfl
  obtain ⟨hD1, hD2, hE1, hE2⟩ := a0c_digit_cards (O := O) hπ M
  rw [hE, hR, hLP, hD1, hD2, ← add_assoc] at hcount
  -- pass to ℝ, naming the base total T
  have hcount' : ((residueCard O : ℝ) * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (residueCard O : ℝ) ^ (M + 2)))
      + (residueCard O : ℝ) * ((Nat.card (Menu.exactSet π 2 (M + 3)) : ℝ)
        * ((residueCard O : ℝ) ^ (M + 1) * (residueCard O : ℝ) ^ (M + 2))))
      + (residueCard O : ℝ)
        * (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3ram M)) : ℝ)
      ≤ (decidedCount O 3 c3ram (M + 3) : ℝ) := by
    exact_mod_cast hcount
  have harith := a0c_step_arith (residueCard O : ℝ) hq0 M _
    (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3ram M)))
    (decidedCount O 3 c3ram M) (decidedCount O 3 c3ram (M + 3))
    (a0c_loop_pre c3ram M) hcount'
  -- identify the base term
  have hcE1 : (Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ)
      = (residueCard O : ℝ) ^ (M + 2) - (residueCard O : ℝ) ^ (M + 1) := by
    have h := congrArg (Nat.cast (R := ℝ)) hE1
    push_cast at h
    linarith
  have hcE2 : (Nat.card (Menu.exactSet π 2 (M + 3)) : ℝ)
      = (residueCard O : ℝ) ^ (M + 1) - (residueCard O : ℝ) ^ M := by
    have h := congrArg (Nat.cast (R := ℝ)) hE2
    push_cast at h
    linarith
  obtain ⟨hp1, hp2, hp3⟩ := a0c_pow_split (residueCard O : ℝ) M
  have hbase : ((residueCard O : ℝ) * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (residueCard O : ℝ) ^ (M + 2)))
      + (residueCard O : ℝ) * ((Nat.card (Menu.exactSet π 2 (M + 3)) : ℝ)
        * ((residueCard O : ℝ) ^ (M + 1) * (residueCard O : ℝ) ^ (M + 2))))
      / (residueCard O : ℝ) ^ (3 * (M + 3))
      = ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3
        + ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 5 := by
    rw [hcE1, hcE2, hp1, hp2, hp3]
    have hyne : (residueCard O : ℝ) ^ M ≠ 0 := (pow_pos hq0 M).ne'
    field_simp
  rw [show decidedSeq O 3 c3ram (M + 3)
      = (decidedCount O 3 c3ram (M + 3) : ℝ) / (residueCard O : ℝ) ^ (3 * (M + 3)) from rfl,
    show decidedSeq O 3 c3ram M
      = (decidedCount O 3 c3ram M : ℝ) / (residueCard O : ℝ) ^ (3 * M) from rfl,
    ← hbase]
  exact harith

/-! ### §7c The DBL family maps -/

variable {π : O}

/-- DBL-direct parameters: an ordered distinct residue pair, the root digits, and a
direct-Eisenstein quadratic part. -/
def DblDirParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (M : ℕ) : Type _ :=
  {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} × Res O (M + 2) × QDirParams O π M

/-- DBL-inserted parameters: pair, root digits, and an `n = 2` rescaled decided class. -/
def DblInsParams (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (σ' : FactorizationType) (M : ℕ) : Type _ :=
  {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} × Res O (M + 2) × QInsParams O σ' M

instance {M : ℕ} : Finite (QDirParams O π M) :=
  inferInstanceAs (Finite (Menu.exactSet π 1 (M + 3) × Menu.dvdSet π 1 (M + 3)))

instance {σ' : FactorizationType} {M : ℕ} : Finite (QInsParams O σ' M) :=
  inferInstanceAs
    (Finite {w : Res O (M + 1) × Res O (M + 2) // qtrunc M w ∈ decidedSet O 2 σ' M})

instance {M : ℕ} : Finite (DblDirParams O π M) :=
  inferInstanceAs (Finite ({pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2}
    × Res O (M + 2) × QDirParams O π M))

instance {σ' : FactorizationType} {M : ℕ} : Finite (DblInsParams O σ' M) :=
  inferInstanceAs (Finite ({pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2}
    × Res O (M + 2) × QInsParams O σ' M))

noncomputable def dblDirMap (M : ℕ) (p : DblDirParams O π M) : Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (dblAssemble (π := π) p.1.1.2 p.2.1 (qDir (π := π) p.1.1.1 M p.2.2))

noncomputable def dblInsMap {σ' : FactorizationType} (M : ℕ) (p : DblInsParams O σ' M) :
    Coeff O 3 (M + 3) :=
  proj O 3 (M + 3) (dblAssemble (π := π) p.1.1.2 p.2.1 (qIns (π := π) p.1.1.1 M p.2.2))

theorem dblDirMap_decided (hπ : Irreducible π) (M : ℕ) (p : DblDirParams O π M) :
    dblDirMap (π := π) M p ∈ decidedSet O 3 c3linRam (M + 3) := by
  exact dblAssemble_decided hπ p.1.2 (qDir_res hπ p.1.1.1 M p.2.2)
    (qDir_decided hπ p.1.1.1 M p.2.2)

theorem dblInsMap_decided (hπ : Irreducible π) {σ' : FactorizationType} (M : ℕ)
    (p : DblInsParams O σ' M) :
    dblInsMap (π := π) M p ∈ decidedSet O 3 ⟨(1, 1) ::ₘ σ'.data⟩ (M + 3) :=
  dblAssemble_decided hπ p.1.2 (qIns_res hπ p.1.1.1 M p.2.2)
    (qIns_decided hπ p.1.1.1 M p.2.2)

theorem dblDirMap_inj (hπ : Irreducible π) (M : ℕ) :
    Function.Injective (dblDirMap (O := O) (π := π) M) := by
  rintro ⟨⟨⟨r, s⟩, hrs⟩, ω, pq⟩ ⟨⟨⟨r', s'⟩, hrs'⟩, ω', pq'⟩ h
  obtain ⟨hr, hs, hw, hg⟩ := dblAssemble_inj hπ hrs hrs'
    (qDir_res hπ r M pq) (qDir_res hπ r' M pq') h
  subst hr; subst hs; subst hw
  cases qDir_inj hπ r M hg
  rfl

theorem dblInsMap_inj (hπ : Irreducible π) {σ' : FactorizationType} (M : ℕ) :
    Function.Injective (dblInsMap (O := O) (π := π) (σ' := σ') M) := by
  rintro ⟨⟨⟨r, s⟩, hrs⟩, ω, pq⟩ ⟨⟨⟨r', s'⟩, hrs'⟩, ω', pq'⟩ h
  obtain ⟨hr, hs, hw, hg⟩ := dblAssemble_inj hπ hrs hrs'
    (qIns_res hπ r M pq) (qIns_res hπ r' M pq') h
  subst hr; subst hs; subst hw
  cases qIns_inj hπ r M hg
  rfl

/-- Any cube-frame class differs from any DBL class (cube tag against double-root tag). -/
private theorem a0c_cube_ne_dbl (hπ : Irreducible π) {M : ℕ} {γ : ResidueField O}
    {b : Fin 3 → O} (hb : ∀ i, b i ∈ maximalIdeal O) {r s : ResidueField O} (hrs : r ≠ s)
    {ω : Res O (M + 2)} {g : Fin 2 → O}
    (hgres : (fun i => residue O (g i)) = ![r ^ 2, -(2 * r)]) :
    proj O 3 (M + 3) (cubeMember γ b) ≠ proj O 3 (M + 3) (dblAssemble (π := π) s ω g) := by
  intro h
  have h1 : resVec (cubeMember γ b) = cubeCoeff γ := resVec_cubeMember hb
  have h2 := resVec_dblAssemble (π := π) hπ (s := s) (ω := ω) hgres
  have h3 : cubeCoeff γ = dblCoeff r s := by
    rw [← h1, ← h2]
    exact resVec_congr hπ (by omega) h
  exact cubeCoeff_ne_dblCoeff hrs h3

theorem lMap_ne_dblDirMap (hπ : Irreducible π) (M : ℕ) (p : LParams O π M)
    (p' : DblDirParams O π M) : lMap M p ≠ dblDirMap (π := π) M p' :=
  a0c_cube_ne_dbl hπ (a0c_l_mem hπ p) p'.1.2 (qDir_res hπ p'.1.1.1 M p'.2.2)

theorem lMap_ne_dblInsMap (hπ : Irreducible π) {σ' : FactorizationType} (M : ℕ)
    (p : LParams O π M) (p' : DblInsParams O σ' M) :
    lMap M p ≠ dblInsMap (π := π) M p' :=
  a0c_cube_ne_dbl hπ (a0c_l_mem hπ p) p'.1.2 (qIns_res hπ p'.1.1.1 M p'.2.2)

theorem dblDirMap_ne_loopMap (hπ : Irreducible π) {σ : FactorizationType} (M : ℕ)
    (p : DblDirParams O π M) (p' : LoopParams O σ M) :
    dblDirMap (π := π) M p ≠ loopMap (π := π) M p' := by
  intro h
  exact a0c_cube_ne_dbl hπ (a0c_loop_mem hπ p') p.1.2
    (qDir_res hπ p.1.1.1 M p.2.2) h.symm

theorem dblInsMap_ne_loopMap (hπ : Irreducible π) {σ σ' : FactorizationType} (M : ℕ)
    (p : DblInsParams O σ' M) (p' : LoopParams O σ M) :
    dblInsMap (π := π) M p ≠ loopMap (π := π) M p' := by
  intro h
  exact a0c_cube_ne_dbl hπ (a0c_loop_mem hπ p') p.1.2
    (qIns_res hπ p.1.1.1 M p.2.2) h.symm

theorem dblDirMap_ne_dblInsMap (hπ : Irreducible π) {σ' : FactorizationType} (M : ℕ)
    (p : DblDirParams O π M) (p' : DblInsParams O σ' M) :
    dblDirMap (π := π) M p ≠ dblInsMap (π := π) M p' := by
  intro h
  obtain ⟨hr, hs, hw, hg⟩ := dblAssemble_inj hπ p.1.2 p'.1.2
    (qDir_res hπ p.1.1.1 M p.2.2) (qIns_res hπ p'.1.1.1 M p'.2.2) h
  rw [← hr] at hg
  exact qDir_ne_qIns hπ p.1.1.1 M p.2.2 p'.2.2 hg

/-- A DBL member never sits in a level-1 (separable-shape) family: `P` avoiding `dblCoeff`. -/
private theorem a0c_dbl_notin_levelOne (hπ : Irreducible π) {M : ℕ}
    {P : Set (Fin 3 → ResidueField O)}
    (hP : ∀ v ∈ P, ∀ (r s : ResidueField O), r ≠ s → v ≠ dblCoeff r s)
    {r s : ResidueField O} (hrs : r ≠ s) {ω : Res O (M + 2)} {g : Fin 2 → O}
    (hgres : (fun i => residue O (g i)) = ![r ^ 2, -(2 * r)]) :
    proj O 3 (M + 3) (dblAssemble (π := π) s ω g) ∉ levelOneFam (O := O) P M := by
  intro hmem
  have hres := resVec_of_mem_levelOneFam (O := O) (P := P) (M := M) hmem
  rw [resVec_dblAssemble (π := π) hπ hgres] at hres
  exact hP _ hres r s hrs rfl

/-- The DBL-inserted box count, cast to `ℝ` and normalized (mirror of `a0c_loop_pre`). -/
private theorem a0c_qins_pre (σ' : FactorizationType) (M : ℕ) :
    (Nat.card (QInsParams O σ' M) : ℝ) * (residueCard O : ℝ) ^ (2 * M)
      = (decidedCount O 2 σ' M : ℝ) * (residueCard O : ℝ) ^ (2 * M + 3) := by
  exact_mod_cast card_qInsParams (O := O) σ' M

/-- The pair census, cast to `ℝ`. -/
private theorem a0c_pairs_cast :
    (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
      = (residueCard O : ℝ) ^ 2 - (residueCard O : ℝ) := by
  have h := congrArg (Nat.cast (R := ℝ)) (a0c_card_ne_pairs (ResidueField O))
  push_cast at h
  have : (residueCard O : ℝ) = (Nat.card (ResidueField O) : ℝ) := rfl
  rw [this]
  linarith

/-- The `n = 2` box count solved: `cQ = c2M · q³`. -/
private theorem a0c_qins_solved (σ' : FactorizationType) (M : ℕ) :
    (Nat.card (QInsParams O σ' M) : ℝ)
      = (decidedCount O 2 σ' M : ℝ) * (residueCard O : ℝ) ^ 3 := by
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  have h := a0c_qins_pre (O := O) σ' M
  have h4 : (Nat.card (QInsParams O σ' M) : ℝ) * (residueCard O : ℝ) ^ (2 * M)
      = ((decidedCount O 2 σ' M : ℝ) * (residueCard O : ℝ) ^ 3)
        * (residueCard O : ℝ) ^ (2 * M) := by
    rw [h, show 2 * M + 3 = 3 + 2 * M from by omega, pow_add]
    ring
  exact mul_right_cancel₀ (pow_ne_zero _ hq0.ne') h4

/-- `x^(2M) = (x^M)²`. -/
private theorem a0c_pow_split2 (x : ℝ) (M : ℕ) : x ^ (2 * M) = (x ^ M) ^ 2 := by
  rw [show 2 * M = M * 2 from by omega, pow_mul]

/-- **STEP (linRam)**: L base + DBL-direct (Eisenstein) + DBL-inserted (n = 2 ram) + loop. -/
theorem step_linRam (M : ℕ) :
    (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4
        + ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
            * decidedSeq O 2 ramType M)
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 c3linRam M
      ≤ decidedSeq O 3 c3linRam (M + 3) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  set F : (LParams O π M ⊕ DblDirParams O π M ⊕ DblInsParams O ramType M
      ⊕ LoopParams O c3linRam M) → Coeff O 3 (M + 3) :=
    Sum.elim (lMap M) (Sum.elim (dblDirMap (π := π) M)
      (Sum.elim (dblInsMap (π := π) M) (loopMap (π := π) M))) with hF
  have hFS : ∀ z, F z ∈ decidedSet O 3 c3linRam (M + 3) := by
    rintro (p | p | p | p)
    · exact lMap_decided hπ M p
    · exact dblDirMap_decided hπ M p
    · exact dblInsMap_decided hπ M p
    · exact loopMap_decided hπ M p
  have hFinj : Function.Injective F := by
    rintro (p | p | p | p) (p' | p' | p' | p') h <;>
      simp only [hF, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (lMap_inj hπ M h)
    · exact absurd h (lMap_ne_dblDirMap hπ M p p')
    · exact absurd h (lMap_ne_dblInsMap hπ M p p')
    · exact absurd h (lMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (lMap_ne_dblDirMap hπ M p' p)
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) (dblDirMap_inj hπ M h)
    · exact absurd h (dblDirMap_ne_dblInsMap hπ M p p')
    · exact absurd h (dblDirMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (lMap_ne_dblInsMap hπ M p' p)
    · exact absurd h.symm (dblDirMap_ne_dblInsMap hπ M p' p)
    · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z))) (dblInsMap_inj hπ M h)
    · exact absurd h (dblInsMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (lMap_ne_loopMap hπ M p' p)
    · exact absurd h.symm (dblDirMap_ne_loopMap hπ M p' p)
    · exact absurd h.symm (dblInsMap_ne_loopMap hπ M p' p)
    · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr z))) (loopMap_inj hπ M h)
  have hcount := a0c_card_le F hFinj hFS
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum] at hcount
  have hL : Nat.card (LParams O π M)
      = residueCard O * (Nat.card (Menu.dvdSet π 2 (M + 3))
        * (Nat.card (Menu.exactSet π 1 (M + 3)) * Nat.card (Menu.dvdSet π 1 (M + 3)))) := by
    unfold LParams
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    rfl
  have hDir : Nat.card (DblDirParams O π M)
      = Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2}
        * (residueCard O ^ (M + 2)
          * (Nat.card (Menu.exactSet π 1 (M + 3)) * Nat.card (Menu.dvdSet π 1 (M + 3)))) := by
    unfold DblDirParams QDirParams
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_res]
  have hIns : Nat.card (DblInsParams O ramType M)
      = Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2}
        * (residueCard O ^ (M + 2) * Nat.card (QInsParams O ramType M)) := by
    unfold DblInsParams
    rw [Nat.card_prod, Nat.card_prod, card_res]
  have hLP : Nat.card (LoopParams O c3linRam M)
      = residueCard O
        * Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3linRam M)) := by
    unfold LoopParams
    rw [Nat.card_prod]
    rfl
  obtain ⟨hD1, hD2, hE1, hE2⟩ := a0c_digit_cards (O := O) hπ M
  rw [hL, hDir, hIns, hLP, hD1, hD2, ← add_assoc, ← add_assoc] at hcount
  have hcount' : ((residueCard O : ℝ) * ((residueCard O : ℝ) ^ (M + 1)
        * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ) * (residueCard O : ℝ) ^ (M + 2)))
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2)
          * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ) * (residueCard O : ℝ) ^ (M + 2)))
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (Nat.card (QInsParams O ramType M) : ℝ)))
      + (residueCard O : ℝ)
        * (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3linRam M)) : ℝ)
      ≤ (decidedCount O 3 c3linRam (M + 3) : ℝ) := by
    exact_mod_cast hcount
  have harith := a0c_step_arith (residueCard O : ℝ) hq0 M _
    (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 c3linRam M)))
    (decidedCount O 3 c3linRam M) (decidedCount O 3 c3linRam (M + 3))
    (a0c_loop_pre c3linRam M) hcount'
  have hcE1 : (Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ)
      = (residueCard O : ℝ) ^ (M + 2) - (residueCard O : ℝ) ^ (M + 1) := by
    have h := congrArg (Nat.cast (R := ℝ)) hE1
    push_cast at h
    linarith
  obtain ⟨hp1, hp2, hp3⟩ := a0c_pow_split (residueCard O : ℝ) M
  have hbase : ((residueCard O : ℝ) * ((residueCard O : ℝ) ^ (M + 1)
        * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ) * (residueCard O : ℝ) ^ (M + 2)))
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2)
          * ((Nat.card (Menu.exactSet π 1 (M + 3)) : ℝ) * (residueCard O : ℝ) ^ (M + 2)))
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (Nat.card (QInsParams O ramType M) : ℝ)))
      / (residueCard O : ℝ) ^ (3 * (M + 3))
      = ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4
        + ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
          * ((decidedCount O 2 ramType M : ℝ) / (residueCard O : ℝ) ^ (2 * M)) := by
    rw [hcE1, a0c_pairs_cast, a0c_qins_solved, hp1, hp2, hp3,
      a0c_pow_split2 (residueCard O : ℝ) M]
    have hyne : (residueCard O : ℝ) ^ M ≠ 0 := (pow_pos hq0 M).ne'
    field_simp
  rw [show decidedSeq O 3 c3linRam (M + 3)
      = (decidedCount O 3 c3linRam (M + 3) : ℝ) / (residueCard O : ℝ) ^ (3 * (M + 3))
      from rfl,
    show decidedSeq O 3 c3linRam M
      = (decidedCount O 3 c3linRam M : ℝ) / (residueCard O : ℝ) ^ (3 * M) from rfl,
    show decidedSeq O 2 ramType M
      = (decidedCount O 2 ramType M : ℝ) / (residueCard O : ℝ) ^ (2 * M) from rfl,
    ← hbase]
  exact harith

/-- **The generic level-1-base + DBL-inserted + loop step** (shared by linInert and split):
`P` is the level-1 shape family, `σ` the cubic type, `σ'` the `n = 2` insertion type. -/
private theorem a0c_step_dblins {σ σ' : FactorizationType}
    {P : Set (Fin 3 → ResidueField O)}
    (hdec1 : ∀ v ∈ P, DecidedAt O 3 σ 1 (Menu.liftRes1 v))
    (hcons : (⟨(1, 1) ::ₘ σ'.data⟩ : FactorizationType) = σ)
    (hPd : ∀ v ∈ P, ∀ (r s : ResidueField O), r ≠ s → v ≠ dblCoeff r s)
    (hPc : ∀ v ∈ P, ∀ γ : ResidueField O, v ≠ cubeCoeff γ) (M : ℕ) :
    ((Nat.card P : ℝ) / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
            * decidedSeq O 2 σ' M)
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 σ M
      ≤ decidedSeq O 3 σ (M + 3) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast residueCard_pos O
  have hA : levelOneFam (O := O) P M ⊆ decidedSet O 3 σ (M + 3) :=
    levelOneFam_subset_decided hdec1 M
  set F : (DblInsParams O σ' M ⊕ LoopParams O σ M) → Coeff O 3 (M + 3) :=
    Sum.elim (dblInsMap (π := π) M) (loopMap (π := π) M) with hF
  have hFS : ∀ z, F z ∈ decidedSet O 3 σ (M + 3) := by
    rintro (p | p)
    · exact hcons ▸ dblInsMap_decided hπ M p
    · exact loopMap_decided hπ M p
  have hFinj : Function.Injective F := by
    rintro (p | p) (p' | p') h <;> simp only [hF, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (dblInsMap_inj hπ M h)
    · exact absurd h (dblInsMap_ne_loopMap hπ M p p')
    · exact absurd h.symm (dblInsMap_ne_loopMap hπ M p' p)
    · exact congrArg Sum.inr (loopMap_inj hπ M h)
  have hdisj : ∀ z, F z ∉ levelOneFam (O := O) P M := by
    rintro (p | p) hmem <;> simp only [hF, Sum.elim_inl, Sum.elim_inr] at hmem
    · exact a0c_dbl_notin_levelOne hπ hPd p.1.2 (qIns_res hπ p.1.1.1 M p.2.2) hmem
    · have hres := resVec_of_mem_levelOneFam (O := O) (P := P) (M := M) hmem
      rw [a0c_loop_resVec hπ p] at hres
      exact hPc _ hres p.1 rfl
  have hcount := a0c_card_add_le hA F hFinj hFS hdisj
  rw [Nat.card_sum] at hcount
  have hIns : Nat.card (DblInsParams O σ' M)
      = Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2}
        * (residueCard O ^ (M + 2) * Nat.card (QInsParams O σ' M)) := by
    unfold DblInsParams
    rw [Nat.card_prod, Nat.card_prod, card_res]
  have hLP : Nat.card (LoopParams O σ M)
      = residueCard O * Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M)) := by
    unfold LoopParams
    rw [Nat.card_prod]
    rfl
  rw [hIns, hLP, ← add_assoc] at hcount
  have hcount' : ((Nat.card (levelOneFam (O := O) P M) : ℝ)
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (Nat.card (QInsParams O σ' M) : ℝ)))
      + (residueCard O : ℝ)
        * (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M)) : ℝ)
      ≤ (decidedCount O 3 σ (M + 3) : ℝ) := by
    exact_mod_cast hcount
  have harith := a0c_step_arith (residueCard O : ℝ) hq0 M _
    (Nat.card ((mtrunc (O := O) M) ⁻¹' (decidedSet O 3 σ M)))
    (decidedCount O 3 σ M) (decidedCount O 3 σ (M + 3))
    (a0c_loop_pre σ M) hcount'
  obtain ⟨hp1, hp2, hp3⟩ := a0c_pow_split (residueCard O : ℝ) M
  have hcA : (Nat.card (levelOneFam (O := O) P M) : ℝ)
      = (Nat.card P : ℝ) * ((residueCard O : ℝ) ^ M) ^ 3 * (residueCard O : ℝ) ^ 6 := by
    have h := congrArg (Nat.cast (R := ℝ)) (card_levelOneFam (O := O) P M)
    push_cast at h
    rw [hp3] at h
    have h4 : (Nat.card (levelOneFam (O := O) P M) : ℝ) * (residueCard O : ℝ) ^ 3
        = ((Nat.card P : ℝ) * ((residueCard O : ℝ) ^ M) ^ 3 * (residueCard O : ℝ) ^ 6)
          * (residueCard O : ℝ) ^ 3 := by
      linear_combination h
    exact mul_right_cancel₀ (pow_ne_zero _ hq0.ne') h4
  have hbase : ((Nat.card (levelOneFam (O := O) P M) : ℝ)
      + (Nat.card {pr : ResidueField O × ResidueField O // pr.1 ≠ pr.2} : ℝ)
        * ((residueCard O : ℝ) ^ (M + 2) * (Nat.card (QInsParams O σ' M) : ℝ)))
      / (residueCard O : ℝ) ^ (3 * (M + 3))
      = (Nat.card P : ℝ) / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
          * ((decidedCount O 2 σ' M : ℝ) / (residueCard O : ℝ) ^ (2 * M)) := by
    rw [hcA, a0c_pairs_cast, a0c_qins_solved, hp2, hp3,
      a0c_pow_split2 (residueCard O : ℝ) M]
    have hyne : (residueCard O : ℝ) ^ M ≠ 0 := (pow_pos hq0 M).ne'
    field_simp
  rw [show decidedSeq O 3 σ (M + 3)
      = (decidedCount O 3 σ (M + 3) : ℝ) / (residueCard O : ℝ) ^ (3 * (M + 3)) from rfl,
    show decidedSeq O 3 σ M
      = (decidedCount O 3 σ M : ℝ) / (residueCard O : ℝ) ^ (3 * M) from rfl,
    show decidedSeq O 2 σ' M
      = (decidedCount O 2 σ' M : ℝ) / (residueCard O : ℝ) ^ (2 * M) from rfl,
    ← hbase]
  exact harith

/-- **STEP (linInert)**: level-1 base (`LinAni` census) + DBL-inserted (n = 2 inert) + loop. -/
theorem step_linInert (M : ℕ) :
    ((Nat.card {v : Fin 3 → ResidueField O // Menu.LinAni v} : ℝ)
          / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
            * decidedSeq O 2 inertType M)
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 c3linInert M
      ≤ decidedSeq O 3 c3linInert (M + 3) :=
  a0c_step_dblins (P := {v | Menu.LinAni v}) (fun _ hv => linInert_decided_res hv) rfl
    (fun _ hv _ _ hrs => linAni_ne_dblCoeff hv hrs)
    (fun _ hv γ => linAni_ne_cubeCoeff hv γ) M

/-- **STEP (split)**: level-1 base (`Split3` census) + DBL-inserted (n = 2 split) + loop. -/
theorem step_split (M : ℕ) :
    ((Nat.card {v : Fin 3 → ResidueField O // Menu.Split3 v} : ℝ)
          / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
            * decidedSeq O 2 splitType M)
      + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 c3split M
      ≤ decidedSeq O 3 c3split (M + 3) :=
  a0c_step_dblins (P := {v | Menu.Split3 v}) (fun _ hv => split3_decided_res hv) rfl
    (fun _ hv _ _ hrs => split3_ne_dblCoeff hv hrs)
    (fun _ hv γ => split3_ne_cubeCoeff hv γ) M

end Steps

/-! ## §8 The five sharp lower bounds (fixed points solved) -/

section Lowers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- `Φ = q⁴+q³+q²+q+1` as a real. -/
noncomputable def PhiR (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] : ℝ :=
  (residueCard O : ℝ) ^ 4 + (residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) ^ 2
    + (residueCard O : ℝ) + 1

theorem phiR_pos : 0 < PhiR O := by
  have hq0 : (0 : ℝ) ≤ (residueCard O : ℝ) := Nat.cast_nonneg _
  unfold PhiR
  positivity

/-- Solve `D ≥ b + q⁻⁵ D` in the limit: the generic fixed-point extractor, with an
`M`-dependent base term converging to `b` (the DBL steps carry `decidedSeq O 2 σ' M`). -/
theorem density_ge_of_step {σ : FactorizationType} {bs : ℕ → ℝ} {b : ℝ}
    (hb : Filter.Tendsto bs Filter.atTop (nhds b))
    (hstep : ∀ M, bs M + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 σ M
      ≤ decidedSeq O 3 σ (M + 3)) :
    b * (residueCard O : ℝ) ^ 5 / ((residueCard O : ℝ) ^ 5 - 1)
      ≤ decidedDensity O 3 σ := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hL : Filter.Tendsto (fun M => decidedSeq O 3 σ (M + 3)) Filter.atTop
      (nhds (decidedDensity O 3 σ)) :=
    (decidedSeq_tendsto (O := O) 3 σ).comp (Filter.tendsto_add_atTop_nat 3)
  have hR : Filter.Tendsto
      (fun M => bs M + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedSeq O 3 σ M) Filter.atTop
      (nhds (b + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ)) :=
    hb.add ((decidedSeq_tendsto (O := O) 3 σ).const_mul _)
  have hfix : b + ((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ
      ≤ decidedDensity O 3 σ :=
    le_of_tendsto_of_tendsto' hR hL hstep
  have hpos : (0 : ℝ) < (residueCard O : ℝ) ^ 5 := by linarith
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (residueCard O : ℝ) ^ 5 - 1)]
  have h2 : (((residueCard O : ℝ) ^ 5)⁻¹ * decidedDensity O 3 σ) * (residueCard O : ℝ) ^ 5
      = decidedDensity O 3 σ := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right hfix hpos.le
  rw [add_mul, h2] at h3
  linarith

theorem sharp_inert :
    (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1) / (3 * PhiR O)
      ≤ decidedDensity O 3 c3inert := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hcen : 3 * (Nat.card {v : Fin 3 → ResidueField O // Menu.NoRootCubic v} : ℝ)
      + (residueCard O : ℝ) = (residueCard O : ℝ) ^ 3 := by
    have h := congrArg (Nat.cast (R := ℝ))
      (Menu.three_mul_card_noRootCubic (ResidueField O))
    push_cast at h
    exact_mod_cast h
  have hD := density_ge_of_step (bs := fun _ =>
      (Nat.card {v : Fin 3 → ResidueField O // Menu.NoRootCubic v} : ℝ)
        / (residueCard O : ℝ) ^ 3)
    tendsto_const_nhds (step_inert (O := O))
  refine le_trans (le_of_eq ?_) hD
  have hnrc : (Nat.card {v : Fin 3 → ResidueField O // Menu.NoRootCubic v} : ℝ)
      = ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / 3 := by linarith
  rw [hnrc]
  unfold PhiR
  have h1 : ((residueCard O : ℝ) ^ 5 - 1) ≠ 0 := by linarith
  field_simp
  ring

theorem sharp_ram :
    ((residueCard O : ℝ) ^ 2 + 1) / PhiR O ≤ decidedDensity O 3 c3ram := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hD := density_ge_of_step (bs := fun _ =>
      ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3
        + ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 5)
    tendsto_const_nhds (step_ram (O := O))
  refine le_trans (le_of_eq ?_) hD
  unfold PhiR
  have h1 : ((residueCard O : ℝ) ^ 5 - 1) ≠ 0 := by linarith
  field_simp
  ring

theorem sharp_linRam :
    (residueCard O : ℝ) * ((residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) + 1)
      / (((residueCard O : ℝ) + 1) * PhiR O) ≤ decidedDensity O 3 c3linRam := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hb : Filter.Tendsto (fun M => ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4
      + ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 3
      + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
        * decidedSeq O 2 ramType M) Filter.atTop
      (nhds (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4
        + ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 3
        + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
          * decidedDensity O 2 ramType)) :=
    tendsto_const_nhds.add ((decidedSeq_tendsto (O := O) 2 ramType).const_mul _)
  have hD := density_ge_of_step hb (step_linRam (O := O))
  rw [decidedDensity_two_ram_eq] at hD
  refine le_trans (le_of_eq ?_) hD
  unfold PhiR
  have h1 : ((residueCard O : ℝ) ^ 5 - 1) ≠ 0 := by linarith
  have h2 : ((residueCard O : ℝ) + 1) ≠ 0 := by linarith
  field_simp
  ring

theorem sharp_linInert :
    (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 + (residueCard O : ℝ) + 1)
      / (2 * ((residueCard O : ℝ) + 1) * PhiR O) ≤ decidedDensity O 3 c3linInert := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hcen : 2 * (Nat.card {v : Fin 3 → ResidueField O // Menu.LinAni v} : ℝ)
      + (residueCard O : ℝ) ^ 2 = (residueCard O : ℝ) ^ 3 := by
    have h := congrArg (Nat.cast (R := ℝ)) (Menu.two_mul_card_linAni (ResidueField O))
    push_cast at h
    exact_mod_cast h
  have hb : Filter.Tendsto (fun M =>
      (Nat.card {v : Fin 3 → ResidueField O // Menu.LinAni v} : ℝ)
        / (residueCard O : ℝ) ^ 3
      + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
        * decidedSeq O 2 inertType M) Filter.atTop
      (nhds ((Nat.card {v : Fin 3 → ResidueField O // Menu.LinAni v} : ℝ)
        / (residueCard O : ℝ) ^ 3
      + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
        * decidedDensity O 2 inertType)) :=
    tendsto_const_nhds.add ((decidedSeq_tendsto (O := O) 2 inertType).const_mul _)
  have hD := density_ge_of_step hb (step_linInert (O := O))
  rw [decidedDensity_two_inert_eq] at hD
  refine le_trans (le_of_eq ?_) hD
  have hla : (Nat.card {v : Fin 3 → ResidueField O // Menu.LinAni v} : ℝ)
      = ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / 2 := by linarith
  rw [hla]
  unfold PhiR
  have h1 : ((residueCard O : ℝ) ^ 5 - 1) ≠ 0 := by linarith
  have h2 : ((residueCard O : ℝ) + 1) ≠ 0 := by linarith
  field_simp
  ring

theorem sharp_split :
    (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ) + 1)
      / (6 * ((residueCard O : ℝ) + 1) * PhiR O) ≤ decidedDensity O 3 c3split := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have hq5 : (1 : ℝ) < (residueCard O : ℝ) ^ 5 :=
    one_lt_pow₀ (by linarith) (by norm_num)
  have hcen : 6 * (Nat.card {v : Fin 3 → ResidueField O // Menu.Split3 v} : ℝ)
      + 3 * (residueCard O : ℝ) ^ 2
      = (residueCard O : ℝ) ^ 3 + 2 * (residueCard O : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) (Menu.six_mul_card_split3 (ResidueField O))
    push_cast at h
    exact_mod_cast h
  have hb : Filter.Tendsto (fun M =>
      (Nat.card {v : Fin 3 → ResidueField O // Menu.Split3 v} : ℝ)
        / (residueCard O : ℝ) ^ 3
      + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
        * decidedSeq O 2 splitType M) Filter.atTop
      (nhds ((Nat.card {v : Fin 3 → ResidueField O // Menu.Split3 v} : ℝ)
        / (residueCard O : ℝ) ^ 3
      + (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 3)
        * decidedDensity O 2 splitType)) :=
    tendsto_const_nhds.add ((decidedSeq_tendsto (O := O) 2 splitType).const_mul _)
  have hD := density_ge_of_step hb (step_split (O := O))
  rw [decidedDensity_two_split_eq] at hD
  refine le_trans (le_of_eq ?_) hD
  have hs3 : (Nat.card {v : Fin 3 → ResidueField O // Menu.Split3 v} : ℝ)
      = ((residueCard O : ℝ) ^ 3 + 2 * (residueCard O : ℝ)
        - 3 * (residueCard O : ℝ) ^ 2) / 6 := by linarith
  rw [hs3]
  unfold PhiR
  have h1 : ((residueCard O : ℝ) ^ 5 - 1) ≠ 0 := by linarith
  have h2 : ((residueCard O : ℝ) + 1) ≠ 0 := by linarith
  field_simp
  ring

end Lowers

/-! ## §9 THE SQUEEZE: the five exact values -/

section Exact

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **THE FIVE EXACT CUBIC DENSITIES** (COROLLARY HM3.D), for the GENUINE density, over
every complete DVR with finite residue field — both characteristics, wild primes included. -/
theorem genuineDensity_three_exact :
    genuineDensity O 3 c3split
        = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ) + 1)
          / (6 * ((residueCard O : ℝ) + 1) * PhiR O)
    ∧ genuineDensity O 3 c3linInert
        = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 + (residueCard O : ℝ) + 1)
          / (2 * ((residueCard O : ℝ) + 1) * PhiR O)
    ∧ genuineDensity O 3 c3inert
        = (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1) / (3 * PhiR O)
    ∧ genuineDensity O 3 c3linRam
        = (residueCard O : ℝ) * ((residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) + 1)
          / (((residueCard O : ℝ) + 1) * PhiR O)
    ∧ genuineDensity O 3 c3ram = ((residueCard O : ℝ) ^ 2 + 1) / PhiR O := by
  have hq2 : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hΦ : (0 : ℝ) < PhiR O := phiR_pos
  have h1 := sharp_split (O := O)
  have h2 := sharp_linInert (O := O)
  have h3 := sharp_inert (O := O)
  have h4 := sharp_linRam (O := O)
  have h5 := sharp_ram (O := O)
  have htot := totalMass_three (O := O)
  have he1 := genuineDensity_three_eq_decidedDensity (O := O) c3split
  have he2 := genuineDensity_three_eq_decidedDensity (O := O) c3linInert
  have he3 := genuineDensity_three_eq_decidedDensity (O := O) c3inert
  have he4 := genuineDensity_three_eq_decidedDensity (O := O) c3linRam
  have he5 := genuineDensity_three_eq_decidedDensity (O := O) c3ram
  rw [he1, he2, he3, he4, he5] at htot
  have hsum : (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ) + 1)
        / (6 * ((residueCard O : ℝ) + 1) * PhiR O)
      + (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) ^ 2 + (residueCard O : ℝ) + 1)
        / (2 * ((residueCard O : ℝ) + 1) * PhiR O)
      + (residueCard O : ℝ) ^ 3 * ((residueCard O : ℝ) + 1) / (3 * PhiR O)
      + (residueCard O : ℝ) * ((residueCard O : ℝ) ^ 3 + (residueCard O : ℝ) + 1)
        / (((residueCard O : ℝ) + 1) * PhiR O)
      + ((residueCard O : ℝ) ^ 2 + 1) / PhiR O = 1 := by
    unfold PhiR
    have hne : ((residueCard O : ℝ) + 1) ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨by rw [he1]; linarith, by rw [he2]; linarith, by rw [he3]; linarith,
    by rw [he4]; linarith, by rw [he5]; linarith⟩

end Exact

/-! ## §10 The five value laws and THE SOCKET FIRES -/

section Laws

open Uniformity.Density.IFC6

/-- The common conversion: an exact `genuineDensity` value in `PhiR`-form becomes a
`CubicValueLaw` witness pair.  `num`/`den` are the polynomials, `hval` extracts the value. -/
private theorem a0c_law_of_value {σ : FactorizationType} (num den : Polynomial ℚ)
    (hden0 : den.eval (0 : ℚ) ≠ 0)
    (hval : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        genuineDensity O 3 σ
          = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) :
    CubicValueLaw σ := by
  refine ⟨num, den, ?_, ?_⟩
  · intro h
    exact hden0 (by rw [h]; simp)
  · intro O _ _ _ _ _
    exact hval O

theorem cubicValueLaw_split : CubicValueLaw c3split := by
  refine a0c_law_of_value
    (Polynomial.X ^ 5 - Polynomial.X ^ 4 + Polynomial.X ^ 3)
    (6 * (Polynomial.X + 1)
      * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1))
    (by norm_num) ?_
  intro O _ _ _ _ _
  have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
  have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
  have hval := (genuineDensity_three_exact (O := O)).1
  have hden : (6 * (Polynomial.X + 1) * (Polynomial.X ^ 4 + Polynomial.X ^ 3
      + Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = 6 * (((residueCard O : ℕ) : ℚ) + 1) * (((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 + ((residueCard O : ℕ) : ℚ) ^ 2
        + ((residueCard O : ℕ) : ℚ) + 1) := by simp
  have hnum : (Polynomial.X ^ 5 - Polynomial.X ^ 4 + Polynomial.X ^ 3 : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = ((residueCard O : ℕ) : ℚ) ^ 5
        - ((residueCard O : ℕ) : ℚ) ^ 4 + ((residueCard O : ℕ) : ℚ) ^ 3 := by simp
  refine ⟨by rw [hden]; positivity, ?_⟩
  rw [hval, hden, hnum]
  unfold PhiR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem cubicValueLaw_linInert : CubicValueLaw c3linInert := by
  refine a0c_law_of_value
    (Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 3)
    (2 * (Polynomial.X + 1)
      * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1))
    (by norm_num) ?_
  intro O _ _ _ _ _
  have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
  have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
  have hval := (genuineDensity_three_exact (O := O)).2.1
  have hden : (2 * (Polynomial.X + 1) * (Polynomial.X ^ 4 + Polynomial.X ^ 3
      + Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = 2 * (((residueCard O : ℕ) : ℚ) + 1) * (((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 + ((residueCard O : ℕ) : ℚ) ^ 2
        + ((residueCard O : ℕ) : ℚ) + 1) := by simp
  have hnum : (Polynomial.X ^ 5 + Polynomial.X ^ 4 + Polynomial.X ^ 3 : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = ((residueCard O : ℕ) : ℚ) ^ 5
        + ((residueCard O : ℕ) : ℚ) ^ 4 + ((residueCard O : ℕ) : ℚ) ^ 3 := by simp
  refine ⟨by rw [hden]; positivity, ?_⟩
  rw [hval, hden, hnum]
  unfold PhiR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem cubicValueLaw_inert : CubicValueLaw c3inert := by
  refine a0c_law_of_value
    (Polynomial.X ^ 4 + Polynomial.X ^ 3)
    (3 * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1))
    (by norm_num) ?_
  intro O _ _ _ _ _
  have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
  have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
  have hval := (genuineDensity_three_exact (O := O)).2.2.1
  have hden : (3 * (Polynomial.X ^ 4 + Polynomial.X ^ 3
      + Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = 3 * (((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 + ((residueCard O : ℕ) : ℚ) ^ 2
        + ((residueCard O : ℕ) : ℚ) + 1) := by simp
  have hnum : (Polynomial.X ^ 4 + Polynomial.X ^ 3 : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = ((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 := by simp
  refine ⟨by rw [hden]; positivity, ?_⟩
  rw [hval, hden, hnum]
  unfold PhiR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem cubicValueLaw_linRam : CubicValueLaw c3linRam := by
  refine a0c_law_of_value
    (Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X)
    ((Polynomial.X + 1)
      * (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1))
    (by norm_num) ?_
  intro O _ _ _ _ _
  have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
  have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
  have hval := (genuineDensity_three_exact (O := O)).2.2.2.1
  have hden : ((Polynomial.X + 1) * (Polynomial.X ^ 4 + Polynomial.X ^ 3
      + Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = (((residueCard O : ℕ) : ℚ) + 1) * (((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 + ((residueCard O : ℕ) : ℚ) ^ 2
        + ((residueCard O : ℕ) : ℚ) + 1) := by simp
  have hnum : (Polynomial.X ^ 4 + Polynomial.X ^ 2 + Polynomial.X : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = ((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 2 + ((residueCard O : ℕ) : ℚ) := by simp
  refine ⟨by rw [hden]; positivity, ?_⟩
  rw [hval, hden, hnum]
  unfold PhiR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem cubicValueLaw_ram : CubicValueLaw c3ram := by
  refine a0c_law_of_value
    (Polynomial.X ^ 2 + 1)
    (Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1)
    (by norm_num) ?_
  intro O _ _ _ _ _
  have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
  have hqR : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast two_le_residueCard O
  have hval := (genuineDensity_three_exact (O := O)).2.2.2.2
  have hden : ((Polynomial.X ^ 4 + Polynomial.X ^ 3
      + Polynomial.X ^ 2 + Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = (((residueCard O : ℕ) : ℚ) ^ 4
        + ((residueCard O : ℕ) : ℚ) ^ 3 + ((residueCard O : ℕ) : ℚ) ^ 2
        + ((residueCard O : ℕ) : ℚ) + 1) := by simp
  have hnum : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = ((residueCard O : ℕ) : ℚ) ^ 2 + 1 := by simp
  refine ⟨by rw [hden]; positivity, ?_⟩
  rw [hval, hden, hnum]
  unfold PhiR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]

/-- ★ **THE CAPSTONE FIELD `a0` AT `n = 3`**: the degree-3 decided-value law, outright. -/
theorem decidedSliceAt_three : DecidedSliceAt 3 :=
  decidedSliceAt_three_of_values cubicValueLaw_split cubicValueLaw_linInert
    cubicValueLaw_inert cubicValueLaw_linRam cubicValueLaw_ram

end Laws

end Uniformity.Density.IFC7

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFC7.sharp_split
#print axioms Uniformity.Density.IFC7.sharp_linInert
#print axioms Uniformity.Density.IFC7.sharp_inert
#print axioms Uniformity.Density.IFC7.sharp_linRam
#print axioms Uniformity.Density.IFC7.sharp_ram
#print axioms Uniformity.Density.IFC7.genuineDensity_three_exact
#print axioms Uniformity.Density.IFC7.cubicValueLaw_split
#print axioms Uniformity.Density.IFC7.cubicValueLaw_linInert
#print axioms Uniformity.Density.IFC7.cubicValueLaw_inert
#print axioms Uniformity.Density.IFC7.cubicValueLaw_linRam
#print axioms Uniformity.Density.IFC7.cubicValueLaw_ram
#print axioms Uniformity.Density.IFC7.decidedSliceAt_three
