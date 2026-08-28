/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130nv2
import Uniformity.ChapC.C132nv0
import Uniformity.ChapC.C132nv1
import Uniformity.ChapC.C132nv5
import Uniformity.ChapC.C136t

/-!
# Uniformity.ChapC.C136d0 — the μ₄ operator stack's base: D3-00/D3-01/D3-02 [D3A 2026-08-28]

**Unit D3A** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.2, rows D3-00, D3-01, D3-02).
One file for the three chained rows (recorded deviation: §5 names declarations, not files;
the three rows are consumed as one dependency chain, so they land as one unit — exactly as
C132nv0/nv1/nv2 landed the same three shapes one level down for the μ₃ campaign).

The μ₄ stack mirrors the landed μ₃ NV series ONE LEVEL UP, with `g8` in place of `Φ₂` and
outer side `(u, e) = (85, 2)` in place of `(21, 2)`:

* **D3-00 (support shell).**  The `g8`-development support layer `dv3Hgt`/`dv3Pin`/`dv3Supp`
  (mirror of C.11's `dv2Hgt`/`dv2Pin`/`dv2Supp`, one level up: the inner read is now the
  LEVEL-2 cleared support `dv2Supp L Ψ₂ · u₂ ℓ₂` — this equality of shapes IS the tower
  recursion, exactly as `dv2Hgt L A := dvSupp F A L.u L.ℓ` was one level down), and the
  zero/ne-top/add/negation bank (mirror of `C132nv0.dv2Supp_zero_eq_top` through
  `C132nv0.dv2Supp_add_eq`).  Parameter-free: no S2 numeral occurs in Part 1 or Part 3;
  the bank is generic over any level datum `L`, any inner key/side `(Ψ₂, u₂, ℓ₂)`, and any
  outer key/side `(Ψ₃, u₃, ℓ₃)`.  Because `dv2Supp`'s own laws carry the monicity/degree/
  positivity hypotheses that `LevelDatum` bundled one level down, the generic lemmas here
  thread `hΨ₂ : Ψ₂.Monic`, `hΨ₂d : 0 < Ψ₂.natDegree`, `hℓ₂ : 0 < ℓ₂` explicitly wherever
  the corresponding C132nv0 inner law needs them (the file docstring of C132nv0 documents
  the same discipline for its own `Ψ`).
* **D3-01 (μ₄ value).**  The S2 numeral instantiation `s2Hgt₄ g := toZ (dv3Supp L Φ₂ 21 2
  g₈ g 85 2)` at the SAME level datum `s2Hgt₂`/`s2Hgt₃` read, with the zero/finiteness/add
  laws (mirror of `C132nv1.s2Hgt₃`'s bank) and the tower-height tooth
  `s2Hgt₄ g₈ = 85 = u₄` (mirror of `C132nv1.s2Hgt₃_Φ₂`'s `s2Hgt₃ Φ₂ = 21 = u₃`).  The
  development key is M3-RP10b's landed `g₈`, tied by an anti-drift pin to the T2 depth-three
  `KeyChain` slot `keyAt 3` (`C136t.s2DepthThreeKeyAt_three`).
* **D3-02 (endpoint/minimizer).**  The outer endpoint/minimizer bank (mirror of
  `C132nv2.Dv2OnSide` through `C132nv2.dv2Supp_mul_eq_add_of_endpoint_le`), with the ONE
  explicit hypothesis `Dv3ResSurv` — the μ₃-residual survival for `Ψ₃`-digit products —
  playing exactly the role `Dv2ResSurv` played one level down.

## What this unit does NOT claim (honesty scope)

`Dv3ResSurv` is NOT discharged here: that is the μ₃ survival core (row D3-03, superseded by
the [DWR] §11.7 L2E shared engine) — reading the landed μ₃ normalized operator on `g8`-digit
products is genuine new mathematics, not a port.  Consequently no unconditional μ₄ product
law is stated; every product-law theorem in Part 3 carries `Dv3ResSurv` as an explicit
premise (mirroring C132nv2's honesty scope verbatim).  No `FGMNSourceData`/calculus record
is packaged here (rows D3-18/19).

**DEPENDS.** C.11 (`dv2Hgt`, `dv2Pin`, `dv2Supp`) · C132nv0 (the level-2 `dv2Supp` bank —
the inner laws of the new layer) · C132nv1 (`s2Φ₂_monic`, `s2Φ₂_natDegree`,
`s2Hgt₃_eq_dv2Supp`) · C132nv5 (`s2Hgt₃_one_eq_zero`) · C136t (`s2DepthThreeKeyAt_three`,
`s2DepthThreeKeyChain`) · C132rp10/rp10b (`g8`, `s2Mu3_gEight_monic`,
`s2Mu3_gEight_natDegree`) · C130nv2 (`weight_read`, `succ_le_of_weight_succ_le`) · C130s6
(`toZ` and its laws) · C118a (`inf_range_ext`, `smul_top_pos`, `dev_zero_any`) · B.02–B.05,
B32a, B35a, B39b (the `dev` bank, generic over any monic divisor).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the rows' sketches (the one explicit hypothesis is documented above and named, never
smuggled in as a silent premise).  Verdict: `runs/wave-c/verdict_D3A.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136d0

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C132nv0
open Uniformity.Density.Tower.C130nv2 (weight_read succ_le_of_weight_succ_le)

/-! ## Part 1 — D3-00: the `Ψ₃`-development support layer and its law bank

The three definitions mirror C.11's `dv2Hgt`/`dv2Pin`/`dv2Supp` one level up: the inner
read is the level-2 cleared support at the inner key/side `(Ψ₂, u₂, ℓ₂)`.  The bank then
mirrors C132nv0 lemma-for-lemma, with C132nv0's own `dv2Supp` laws consumed as the inner
facts exactly where C132nv0 consumed C130s6's `dvSupp` laws. -/

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The level-3 slot height of a coefficient: the LEVEL-2 cleared support at the inner
key/side.  This equality of shapes IS the tower recursion (mirror of C.11's
`dv2Hgt L A := dvSupp F A L.u L.ℓ`, one level up). -/
noncomputable def dv3Hgt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (A : Polynomial O) : ℕ∞ :=
  dv2Supp L Ψ₂ A u₂ ℓ₂

/-- Anti-drift pin: the layer's inner read IS `dv2Supp` at the inner key/side. -/
theorem dv3Hgt_eq_dv2Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (A : Polynomial O) :
    dv3Hgt L Ψ₂ u₂ ℓ₂ A = dv2Supp L Ψ₂ A u₂ ℓ₂ := rfl

/-- The level-3 pins of `f` at the outer key `Ψ₃`: the level-3 slot heights of the
`Ψ₃`-development coefficients (B.02's `dev`, two levels up). -/
noncomputable def dv3Pin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ f : Polynomial O) (j : ℕ) : ℕ∞ :=
  dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ f j)

/-- The level-3 cleared support `inf_j (ℓ₃·dv3Pin_j + u₃·j)` — B.14's shape at the level-3
polygon.  The range bound mirrors C.11's, as C.06's does two levels down. -/
noncomputable def dv3Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ f : Polynomial O) (u₃ ℓ₃ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf
    (fun j => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞))

/-! ### The inner-height shims (mirror of C132nv2's Part 0, one level up)

Free from C132nv0's `dv2Supp` bank, exactly as C132nv2's `dv2Hgt` shims were free from
C130s6's `dvSupp` bank. -/

/-- `dv3Hgt` of `0` is `⊤` (mirror of C132nv2's `dv2Hgt_zero`; free from C132nv0's
`dv2Supp_zero_eq_top`). -/
theorem dv3Hgt_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) :
    dv3Hgt L Ψ₂ u₂ ℓ₂ (0 : Polynomial O) = ⊤ :=
  dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂

/-- a nonzero polynomial has finite `dv3Hgt` (free from C132nv0's
`dv2Supp_ne_top_of_ne_zero`). -/
theorem dv3Hgt_ne_top_of_ne_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) (u₂ ℓ₂ : ℕ)
    {A : Polynomial O} (hA : A ≠ 0) : dv3Hgt L Ψ₂ u₂ ℓ₂ A ≠ ⊤ :=
  dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hA

/-- The ultrametric inequality for `dv3Hgt` (free from C132nv0's
`min_dv2Supp_le_dv2Supp_add`). -/
theorem min_dv3Hgt_le_dv3Hgt_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (A B : Polynomial O) :
    min (dv3Hgt L Ψ₂ u₂ ℓ₂ A) (dv3Hgt L Ψ₂ u₂ ℓ₂ B) ≤ dv3Hgt L Ψ₂ u₂ ℓ₂ (A + B) :=
  min_dv2Supp_le_dv2Supp_add L hΨ₂ hΨ₂d hℓ₂ A B

/-- The ultrametric EQUALITY off ties for `dv3Hgt` (free from C132nv0's
`dv2Supp_add_eq`). -/
theorem dv3Hgt_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {A B : Polynomial O}
    (hne : dv3Hgt L Ψ₂ u₂ ℓ₂ A ≠ dv3Hgt L Ψ₂ u₂ ℓ₂ B) :
    dv3Hgt L Ψ₂ u₂ ℓ₂ (A + B) = min (dv3Hgt L Ψ₂ u₂ ℓ₂ A) (dv3Hgt L Ψ₂ u₂ ℓ₂ B) :=
  dv2Supp_add_eq L hΨ₂ hΨ₂d hℓ₂ hne

/-! ### The `dv3Supp` zero/ne-top/add/negation bank (mirror of C132nv0, one level up) -/

/-- `dv3Pin` vanishes to `⊤` past the degree (mirror of C132nv0's `dv2Pin_top_of_gt`, one
level up: the development term itself vanishes by B04's `dev_eq_zero_of_lt`, and `dv3Hgt`
of `0` is `⊤` by C132nv0's `dv2Supp_zero_eq_top`). -/
theorem dv3Pin_top_of_gt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O}
    (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) (f : Polynomial O) {j : ℕ}
    (hj : f.natDegree < j) : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = ⊤ := by
  have hjd : j ≤ j * Ψ₃.natDegree := Nat.le_mul_of_pos_right _ hΨ₃d
  rw [dv3Pin, dev_eq_zero_of_lt hΨ₃ hΨ₃d f j (by omega), dv3Hgt]
  exact dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂

/-- `dv3Supp` of `0` is `⊤` (mirror of C132nv0's `dv2Supp_zero_eq_top`; no outer monicity
needed, since `dev` of the zero polynomial vanishes for ANY divisor). -/
theorem dv3Supp_zero_eq_top {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (Ψ₃ : Polynomial O) (u₃ : ℕ)
    {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (0 : Polynomial O) u₃ ℓ₃ = ⊤ := by
  rw [dv3Supp]
  simp only [Polynomial.natDegree_zero, Nat.zero_add, Finset.range_one, Finset.inf_singleton]
  rw [dv3Pin, C118a.dev_zero_any, dv3Hgt, dv2Supp_zero_eq_top L Ψ₂ u₂ hℓ₂,
    C118a.smul_top_pos hℓ₃, top_add]

/-- `dv3Supp` read over any range past the degree (mirror of C132nv0's
`dv2Supp_eq_inf_range`; the added abscissae have `dv3Pin = ⊤` by `dv3Pin_top_of_gt`). -/
theorem dv3Supp_eq_inf_range {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ : ℕ) {ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O}
    (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (f : Polynomial O) {M : ℕ} (hM : f.natDegree < M) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃
      = (Finset.range M).inf (fun j => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞)) := by
  rw [dv3Supp]
  have h := C118a.inf_range_ext (m := f.natDegree) (M := M - 1) (by omega)
      (fun j => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞)) (fun i hi1 _ => by
        rw [dv3Pin_top_of_gt L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d f hi1, C118a.smul_top_pos hℓ₃, top_add])
  rw [h, show M - 1 + 1 = M by omega]

/-- a nonzero polynomial has finite `dv3Supp` (mirror of C132nv0's
`dv2Supp_ne_top_of_ne_zero`; the per-slot step is C132nv0's `dv2Supp_ne_top_of_ne_zero`
applied at `dv3Hgt`'s underlying `dv2Supp`, rather than a fresh degree argument). -/
theorem dv3Supp_ne_top_of_ne_zero {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) (u₂ ℓ₂ : ℕ)
    {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) (u₃ ℓ₃ : ℕ)
    {f : Polynomial O} (hf : f ≠ 0) : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ ≠ ⊤ := by
  intro htop
  rw [dv3Supp] at htop
  have hall : ∀ j ∈ Finset.range (f.natDegree + 1), dev Ψ₃ f j = 0 := by
    intro j hj
    have hle := Finset.inf_le
      (f := fun j => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞)) hj
    rw [htop] at hle
    have hterm : ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + ((u₃ : ℕ∞) * (j : ℕ∞)) = ⊤ :=
      top_le_iff.mp hle
    have hleft : ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = ⊤ := by
      rcases WithTop.add_eq_top.mp hterm with h | h
      · exact h
      · rw [← Nat.cast_mul] at h
        exact absurd h (ENat.coe_ne_top _)
    have hdvtop : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = ⊤ := by
      by_contra hx
      rw [nsmul_eq_mul] at hleft
      exact WithTop.mul_ne_top (ENat.coe_ne_top ℓ₃) hx hleft
    rw [dv3Pin, dv3Hgt] at hdvtop
    by_contra hne
    exact absurd hdvtop (dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hne)
  have hrec : ∑ j ∈ Finset.range (f.natDegree + 1), dev Ψ₃ f j * Ψ₃ ^ j = f :=
    sum_dev_eq hΨ₃ hΨ₃d f
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hΨ₃d))
  refine hf ?_
  rw [← hrec]
  exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]

/-- ★ **the `dv3Supp` ultrametric inequality** (mirror of C132nv0's
`min_dv2Supp_le_dv2Supp_add`): per-slot, `dev` is additive (B32a) and `dv3Hgt` is
ultrametric (C132nv0's `min_dv2Supp_le_dv2Supp_add`, one level down). -/
theorem min_dv3Supp_le_dv3Supp_add {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (f g : Polynomial O) :
    min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃)
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃ := by
  set M := max (max f.natDegree g.natDegree) (f + g).natDegree + 1 with hMdef
  rw [dv3Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d hℓ₃ f (M := M) (by omega),
    dv3Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d hℓ₃ g (M := M) (by omega),
    dv3Supp_eq_inf_range L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d hℓ₃ (f + g) (M := M) (by omega)]
  refine Finset.le_inf fun j hj => ?_
  have hmono : Monotone fun x : ℕ∞ => ℓ₃ • x + ((u₃ : ℕ∞) * (j : ℕ∞)) := by
    intro x y hxy
    exact add_le_add (nsmul_le_nsmul_right hxy ℓ₃) le_rfl
  have hs : min (dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j) (dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g j)
      ≤ dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) j := by
    rw [dv3Pin, dv3Pin, dv3Pin, dev_add_of_monic hΨ₃ f g j, dv3Hgt, dv3Hgt, dv3Hgt]
    exact min_dv2Supp_le_dv2Supp_add L hΨ₂ hΨ₂d hℓ₂ (dev Ψ₃ f j) (dev Ψ₃ g j)
  calc min ((Finset.range M).inf fun i => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f i + (u₃ * i : ℕ∞))
        ((Finset.range M).inf fun i => ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g i + (u₃ * i : ℕ∞))
      ≤ min (ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞))
        (ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g j + (u₃ * j : ℕ∞)) :=
        min_le_min (Finset.inf_le hj) (Finset.inf_le hj)
    _ = ℓ₃ • min (dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j) (dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g j) + (u₃ * j : ℕ∞) :=
        (hmono.map_min).symm
    _ ≤ ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) j + (u₃ * j : ℕ∞) := hmono hs

/-- `dv3Supp` is negation-invariant (per-slot mirror of C132nv0's `dv2Supp_neg`, through
B39b's `dev_neg` and C132nv0's `dv2Supp_neg` at `dv3Hgt`'s underlying `dv2Supp`). -/
theorem dv3Supp_neg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (u₂ ℓ₂ : ℕ) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic)
    (f : Polynomial O) (u₃ ℓ₃ : ℕ) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (-f) u₃ ℓ₃ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ := by
  rw [dv3Supp, dv3Supp, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun j _ => ?_
  rw [dv3Pin, dv3Pin, dev_neg hΨ₃, dv3Hgt, dv3Hgt, dv2Supp_neg L hΨ₂]

/-- the strict half of equality off ties: the lower side wins outright (mirror of
C132nv0's `dv2Supp_add_eq_of_lt`). -/
theorem dv3Supp_add_eq_of_lt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {f g : Polynomial O}
    (hlt : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ < dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ := by
  have hge : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃ := by
    have h := min_dv3Supp_le_dv3Supp_add (u₂ := u₂) (u₃ := u₃) L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ f g
    rwa [min_eq_left hlt.le] at h
  refine le_antisymm ?_ hge
  have h2 : min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃)
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ := by
    have h3 := min_dv3Supp_le_dv3Supp_add (u₂ := u₂) (u₃ := u₃) L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ (f + g) (-g)
    rw [dv3Supp_neg L hΨ₂ u₂ ℓ₂ hΨ₃] at h3
    calc min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃)
        ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ ((f + g) + -g) u₃ ℓ₃ := h3
      _ = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ := by rw [add_neg_cancel_right]
  by_contra hcon
  exact absurd h2 (not_le.mpr (lt_min (not_le.mp hcon) hlt))

/-- ★ **the `dv3Supp` ultrametric EQUALITY OFF TIES** (mirror of C132nv0's
`dv2Supp_add_eq`, the E.10 `hgt_add_eq` law two levels up). -/
theorem dv3Supp_add_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {Ψ₂ : Polynomial O} (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {Ψ₃ : Polynomial O} (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {f g : Polynomial O}
    (hne : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ ≠ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (f + g) u₃ ℓ₃
      = min (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃) (dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact dv3Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ h
  · rw [min_eq_right h.le, add_comm]
    exact dv3Supp_add_eq_of_lt L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ h

end Generic

/-! ## Part 2 — D3-01: the μ₄ value table `s2Hgt₄` and the tooth `s2Hgt₄ g₈ = 85 = u₄`

The first NUMERAL instantiation of the Part-1 bank, at the S2 depth-three occurrence:
`s2Hgt₄ g := toZ (dv3Supp L Φ₂ 21 2 g₈ g 85 2)`, where `L := (s2Tower h2 hq).levelDatum h2`
is the SAME level datum `s2Hgt₂`/`s2Hgt₃` read, `Φ₂ := s2DepthTwoKeyAt h2 hq 2` is the
promoted level-2 key at its landed inner side `(21, 2)`, and the development key is
M3-RP10b's `g₈` — the T2 chain's `keyAt 3` (`C136t.s2DepthThreeKeyAt_three`) — at the
campaign's outer side `(u, e) = (85, 2)`.  Mirror of C132nv1, one level up. -/

section S2

open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv5
open Uniformity.Density.Tower.C132rp10 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136t

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ### Plumbing: `g₈`'s monicity and degree, in the campaign's `g8` spelling -/

/-- `g₈` is monic — M3-RP10's landed monicity (`s2Mu3_gEight_monic`), restated at
M3-RP10b's `g8` (definitionally the same polynomial; C136t's
`s2DepthThreeKeyAt_monic_three` reads the same fact through the T1 chain). -/
theorem s2g8_monic : (g8 h2 hq : Polynomial O).Monic := s2Mu3_gEight_monic h2 hq

/-- `deg g₈ = 8` — M3-RP10's landed degree (`s2Mu3_gEight_natDegree`), restated at `g8`. -/
theorem s2g8_natDegree : (g8 h2 hq : Polynomial O).natDegree = 8 :=
  s2Mu3_gEight_natDegree h2 hq

/-- Anti-drift pin: the development key IS the T2 depth-three chain's `keyAt 3`
(C136t's `s2DepthThreeKeyAt_three`, read through the `KeyChain` field). -/
theorem s2g8_eq_keyChain_three :
    (g8 h2 hq : Polynomial O) = (s2DepthThreeKeyChain h2 hq).keyAt 3 :=
  (s2DepthThreeKeyAt_three h2 hq).symm

/-! ### The VALUE table `s2Hgt₄` and its shape/zero/finiteness/add laws -/

/-- **the S2 μ₄ VALUE table**: the corpus's `e₄`-cleared μ₄ support at the S2 side
`(u₄, ℓ₄) = (85, 2)`, developed in the depth-three key `g₈`, whose coefficients are read
by the μ₃ support at its landed side `(21, 2)` — the level datum `s2Hgt₂`/`s2Hgt₃`
themselves read. -/
noncomputable def s2Hgt₄ (g : Polynomial O) : WithTop ℤ :=
  toZ (dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
    (g8 h2 hq) g 85 2)

/-- Anti-drift pin (the "field shape" tooth): the table IS `dv3Supp` at the S2 numerals —
nothing fresh, mirroring `C132nv1.s2Hgt₃_eq_dv2Supp` one level up. -/
theorem s2Hgt₄_eq_dv3Supp (g : Polynomial O) :
    s2Hgt₄ h2 hq g = toZ (dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2) := rfl

/-- The table read at the T2 chain slot: `s2Hgt₄` develops in `keyAt 3` of the landed
depth-three `KeyChain` (the C136t carrier this file consumes). -/
theorem s2Hgt₄_eq_keyChain_dev (g : Polynomial O) :
    s2Hgt₄ h2 hq g = toZ (dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 ((s2DepthThreeKeyChain h2 hq).keyAt 3) g 85 2) := by
  rw [s2Hgt₄, ← s2g8_eq_keyChain_three h2 hq]

/-- the `hgt_zero` field at μ₄ (mirror of `s2Hgt₃_zero`). -/
theorem s2Hgt₄_zero : s2Hgt₄ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2Hgt₄, dv3Supp_zero_eq_top _ _ _ (by norm_num) _ _ (by norm_num), toZ_top]

/-- every nonzero polynomial has finite μ₄ height (mirror of `s2Hgt₃_ne_top`). -/
theorem s2Hgt₄_ne_top {g : Polynomial O} (hg : g ≠ 0) : s2Hgt₄ h2 hq g ≠ ⊤ := by
  rw [s2Hgt₄, ne_eq, toZ_eq_top_iff]
  exact dv3Supp_ne_top_of_ne_zero _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) 21 2 (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) 85 2 hg

/-- the μ₄ ultrametric inequality (mirror of `s2Hgt₃_add_ge`). -/
theorem s2Hgt₄_add_ge (g g' : Polynomial O) :
    min (s2Hgt₄ h2 hq g) (s2Hgt₄ h2 hq g') ≤ s2Hgt₄ h2 hq (g + g') := by
  rw [s2Hgt₄, s2Hgt₄, s2Hgt₄, ← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_dv3Supp_le_dv3Supp_add _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) g g')

/-- the μ₄ ultrametric equality off ties (mirror of `s2Hgt₃_add_eq`). -/
theorem s2Hgt₄_add_eq (g g' : Polynomial O) (hne : s2Hgt₄ h2 hq g ≠ s2Hgt₄ h2 hq g') :
    s2Hgt₄ h2 hq (g + g') = min (s2Hgt₄ h2 hq g) (s2Hgt₄ h2 hq g') := by
  have hne' : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g 85 2
      ≠ dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
        (g8 h2 hq) g' 85 2 :=
    fun heq => hne (congrArg toZ heq)
  rw [s2Hgt₄, s2Hgt₄, s2Hgt₄, ← toZ_min]
  exact congrArg toZ (dv3Supp_add_eq _ (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) (by norm_num) hne')

/-! ### The tower-height tooth `s2Hgt₄ g₈ = 85 = u₄`

Mirror of `C132nv1.s2Hgt₃_Φ₂`: `g₈`'s own development in itself has `dev = 0` at `j = 0`,
`dev = 1` at `j = 1`, and `dev = 0` past `j = 1` (since `g₈` is monic of positive degree,
the `j = 1` remainder is `1 %ₘ g₈ = 1` and B04 kills every slot `≥ 2`); the inner μ₃ reads
of the two digit values `0`/`1` are `⊤` (Part 1's `dv3Hgt_zero`) and `0` (M3-NV5's landed
`s2Hgt₃_one_eq_zero`, transported across `s2Hgt₃_eq_dv2Supp`). -/

/-- the inner μ₃ read of the digit `0` is `⊤` (Part 1's `dv3Hgt_zero` at the S2
numerals). -/
private theorem s2_dv3Hgt_zero :
    dv3Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (0 : Polynomial O) = (⊤ : ℕ∞) :=
  dv3Hgt_zero _ _ _ (by norm_num)

/-- the inner μ₃ read of the digit `1` is `0` — literally M3-NV5's `s2Hgt₃ 1 = 0` tooth,
transported across the `s2Hgt₃_eq_dv2Supp` anti-drift pin (no fresh computation). -/
private theorem s2_dv3Hgt_one :
    dv3Hgt ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (1 : Polynomial O) = (0 : ℕ∞) := by
  apply C130s6.toZ_inj
  rw [dv3Hgt, ← s2Hgt₃_eq_dv2Supp h2 hq, s2Hgt₃_one_eq_zero h2 hq]
  rfl

private theorem g8_one_mod : (1 : Polynomial O) %ₘ g8 h2 hq = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2g8_monic h2 hq)).mpr
    (Polynomial.degree_lt_degree
      (by rw [Polynomial.natDegree_one, s2g8_natDegree h2 hq]; norm_num))

private theorem g8_dev0 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 0 = 0 := by
  have h := dev_mul_pow_of_lt (s2g8_monic h2 hq) 1 1 0 Nat.one_pos
  rwa [one_mul, pow_one] at h

private theorem g8_dev1 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 1 = 1 := by
  have h := dev_mul_pow (s2g8_monic h2 hq) 1 (1 : Polynomial O) 0
  rw [Nat.add_zero, one_mul, pow_one] at h
  rw [h]
  exact g8_one_mod h2 hq

private theorem g8_dev_of_two_le {j : ℕ} (hj : 2 ≤ j) :
    dev (g8 h2 hq) (g8 h2 hq : Polynomial O) j = 0 := by
  refine dev_eq_zero_of_lt (s2g8_monic h2 hq)
    (by rw [s2g8_natDegree h2 hq]; norm_num) _ j ?_
  rw [s2g8_natDegree h2 hq]
  omega

/-- ★ **the tower-height tooth**: `s2Hgt₄ g₈ = 85 = u₄`, the μ₄ analogue of
`C132nv1.s2Hgt₃_Φ₂`'s `s2Hgt₃ Φ₂ = 21 = u₃` (row D3-01's signed value pin). -/
theorem s2Hgt₄_g8 : s2Hgt₄ h2 hq (g8 h2 hq) = ((85 : ℤ) : WithTop ℤ) := by
  have hd2 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 2 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd3 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 3 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd4 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 4 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd5 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 5 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd6 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 6 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd7 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 7 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hd8 : dev (g8 h2 hq) (g8 h2 hq : Polynomial O) 8 = 0 :=
    g8_dev_of_two_le h2 hq (by norm_num)
  have hval : dv3Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
      (g8 h2 hq) (g8 h2 hq) 85 2 = ((85 : ℕ) : ℕ∞) := by
    rw [dv3Supp, s2g8_natDegree h2 hq,
      show Finset.range (8 + 1) = {0, 1, 2, 3, 4, 5, 6, 7, 8} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_insert,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_insert, Finset.inf_insert,
      Finset.inf_singleton, dv3Pin, dv3Pin, dv3Pin, dv3Pin, dv3Pin, dv3Pin, dv3Pin,
      dv3Pin, dv3Pin, g8_dev0 h2 hq, g8_dev1 h2 hq, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
      s2_dv3Hgt_one h2 hq, s2_dv3Hgt_zero h2 hq]
    simp
  rw [s2Hgt₄, hval, toZ_coe]
  norm_num

/-- the tooth at the T2 chain slot: `s2Hgt₄ (keyAt 3) = 85` (the form the D3 stack's
chain-level consumers read). -/
theorem s2Hgt₄_keyChain_three :
    s2Hgt₄ h2 hq ((s2DepthThreeKeyChain h2 hq).keyAt 3) = ((85 : ℤ) : WithTop ℤ) := by
  rw [← s2g8_eq_keyChain_three h2 hq]
  exact s2Hgt₄_g8 h2 hq

end S2

/-! ## Part 3 — D3-02: the `dv3Supp` outer endpoint/minimizer bank

Mirror of C132nv2's Parts 1–3 (the endpoint/minimizer bank and the convolution-pricing
bank), one level up, leaving ONE explicit hypothesis, `Dv3ResSurv` — the μ₃-residual
survival for `Ψ₃`-digit products, playing exactly the role `Dv2ResSurv` played one level
down.  It is NOT discharged here (see the file docstring's honesty scope): reading the
landed μ₃ normalized operator on `g8`-digit products is row D3-03's genuine new core
(superseded by the [DWR] §11.7 L2E engine), not a port.  Every other declaration is
UNCONDITIONAL, parameter-free (no S2 numeral), and mirrors its `dv2Supp` counterpart by
the substitution `dv2Hgt L ↦ dv3Hgt L Ψ₂ u₂ ℓ₂`, `Ψ ↦ Ψ₃`, `dv2Pin L Ψ ↦
dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃`, `dv2Supp L Ψ · u₂ ℓ₂ ↦ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ · u₃ ℓ₃`,
`Dv2OnSide ↦ Dv3OnSide`, `dv2SideSet/dv2SideMin ↦ dv3SideSet/dv3SideMin`. -/

section GenericEndpoint

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The on-side predicate at the `dv3`-level.**  The abscissa `j` attains the cleared
level-3 support at slope `−u₃/ℓ₃`, AND its level-3 pin is finite (mirror of C132nv2's
`Dv2OnSide`, one level up). -/
def Dv3OnSide {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ f : Polynomial O) (u₃ ℓ₃ j : ℕ) : Prop :=
  dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ = ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞) ∧
    dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j ≠ ⊤

/-- **The on-side abscissae, as a `Finset`** (mirror of C132nv2's `dv2SideSet`). -/
noncomputable def dv3SideSet {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ f : Polynomial O) (u₃ ℓ₃ : ℕ) : Finset ℕ :=
  open Classical in
  (Finset.range (f.natDegree + 1)).filter (fun j => Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j)

/-- **The side's left endpoint** (mirror of C132nv2's `dv2SideMin`). -/
noncomputable def dv3SideMin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ f : Polynomial O) (u₃ ℓ₃ : ℕ)
    (h : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty) : ℕ :=
  (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).min' h

variable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) {Ψ₂ Ψ₃ : Polynomial O}

/-- Membership in `dv3SideSet` projects to the on-side predicate. -/
theorem dv3OnSide_of_mem_dv3SideSet {u₂ ℓ₂ : ℕ} {f : Polynomial O} {u₃ ℓ₃ j : ℕ}
    (hj : j ∈ dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃) : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃) from hj)).2

/-- An on-side slot lies in `dv3SideSet`. -/
theorem mem_dv3SideSet_of_dv3OnSide {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic)
    (hΨ₃d : 0 < Ψ₃.natDegree) {f : Polynomial O} {u₃ ℓ₃ j : ℕ}
    (hj : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j) : j ∈ dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ := by
  classical
  simp only [dv3SideSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hj⟩
  by_contra hdeg
  exact hj.2 (dv3Pin_top_of_gt L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d f (by omega))

/-- **The chosen minimizer is on-side.** -/
theorem dv3OnSide_dv3SideMin {u₂ ℓ₂ : ℕ} (f : Polynomial O) (u₃ ℓ₃ : ℕ)
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty) :
    Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne) :=
  dv3OnSide_of_mem_dv3SideSet L (Finset.min'_mem _ hne)

/-- **The chosen minimizer is the LEFTMOST on-side slot.** -/
theorem dv3SideMin_le_of_dv3OnSide {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic)
    (hΨ₃d : 0 < Ψ₃.natDegree) {f : Polynomial O} {u₃ ℓ₃ j : ℕ}
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty)
    (hj : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j) :
    dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne ≤ j :=
  Finset.min'_le _ _ (mem_dv3SideSet_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d hj)

/-- Every slot strictly left of the chosen minimizer is strictly off the side. -/
theorem not_dv3OnSide_of_lt_dv3SideMin {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic)
    (hΨ₃d : 0 < Ψ₃.natDegree) {f : Polynomial O} {u₃ ℓ₃ j : ℕ}
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty)
    (hlt : j < dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne) :
    ¬ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j :=
  fun hj => absurd (dv3SideMin_le_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d hne hj) (by omega)

/-- **The unique lowest convolution pair.** -/
theorem dv3OnSide_endpoint_unique {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic)
    (hΨ₃d : 0 < Ψ₃.natDegree) {g z : Polynomial O} {u₃ ℓ₃ j i : ℕ}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty)
    (hsum : j + i = dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng
      + dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz)
    (hj : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ j) (hi : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ i) :
    j = dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng
      ∧ i = dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz := by
  have h1 := dv3SideMin_le_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d hng hj
  have h2 := dv3SideMin_le_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d hnz hi
  omega

/-- The height at the chosen minimizer is a natural number. -/
theorem exists_dv3SideMin_height {u₂ ℓ₂ : ℕ} (f : Polynomial O) (u₃ ℓ₃ : ℕ)
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty) :
    ∃ H : ℕ, dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne) = (H : ℕ∞) :=
  ENat.ne_top_iff_exists.1 (dv3OnSide_dv3SideMin L f u₃ ℓ₃ hne).2 |>.imp fun _ h => h.symm

/-- **The support value, read off any on-side slot.** -/
theorem dv3Supp_eq_of_dv3OnSide {u₂ ℓ₂ : ℕ} {f : Polynomial O} {u₃ ℓ₃ j H : ℕ}
    (hH : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = (H : ℕ∞)) (hj : Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ = ((ℓ₃ * H + u₃ * j : ℕ) : ℕ∞) := by
  rw [hj.1, hH, weight_read]

/-- **The support infimum lies below the weighted pin at every abscissa** (mirror of
C132nv2's `dv2Supp_le_term`, including past-degree abscissae via `dv3Pin_top_of_gt`). -/
theorem dv3Supp_le_term (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) (u₂ : ℕ) {ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (f : Polynomial O) (u₃ : ℕ) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (j : ℕ) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ ≤ ℓ₃ • dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j + (u₃ * j : ℕ∞) := by
  by_cases hj : j ≤ f.natDegree
  · unfold dv3Supp
    exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [dv3Pin_top_of_gt L Ψ₂ u₂ hℓ₂ hΨ₃ hΨ₃d f (by omega), C118a.smul_top_pos hℓ₃, top_add]
    exact le_top

/-- **The support line lies below the level-3 polygon**, ℕ-cleared. -/
theorem le_dv3Weight (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {f : Polynomial O} {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {S H j : ℕ}
    (hS : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ = (S : ℕ∞))
    (hH : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = (H : ℕ∞)) :
    S ≤ ℓ₃ * H + u₃ * j := by
  have h := dv3Supp_le_term (Ψ₂ := Ψ₂) L hΨ₃ hΨ₃d u₂ hℓ₂ f u₃ hℓ₃ j
  rw [hS, hH, weight_read] at h
  exact_mod_cast h

/-- **Off the side the support line is strictly below the polygon.** -/
theorem lt_dv3Weight (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) {f : Polynomial O} {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) {S H j : ℕ}
    (hS : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ = (S : ℕ∞))
    (hH : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ f j = (H : ℕ∞))
    (hns : ¬ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j) : S < ℓ₃ * H + u₃ * j := by
  rcases eq_or_lt_of_le (le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hS hH) with heq | hlt
  · refine absurd ⟨?_, hH ▸ ENat.coe_ne_top H⟩ hns
    rw [hS, hH, weight_read, ← heq]
  · exact hlt

/-! ### The ONE explicit hypothesis: `Dv3ResSurv` (mirror of C132nv2's `Dv2ResSurv`)

Every `dev Ψ₃` output has degree `< Ψ₃.natDegree` UNCONDITIONALLY (B03's `degree_dev_lt`),
so a digit PRODUCT `A * B` has degree `< 2 * Ψ₃.natDegree` — at most two `Ψ₃`-development
slots, `0` (the reduced remainder) and `1` (the bare quotient).  `Dv3ResSurv` packages
exactly the two facts the pricing bank needs about those two slots, in the digit heights
alone: the EXACT value at the reduced slot (the μ₃ analogue of NV3's "reduction modulo the
key preserves the product value" — row D3-03's content) and the STRICT slot-`1` carry
bound.  Discharged for `(Ψ₃, u₃, ℓ₃) = (g8, 85, 2)` by the D3-03/L2E campaign rows from
the landed μ₃ normalized residual product — NOT here. -/

/-- **THE ONE explicit hypothesis ("μ₃-residual survival")**: for any two
`Ψ₃`-digit-bounded `A, B` of known `dv3Hgt` heights, their product's `Ψ₃`-reduced value is
EXACTLY the sum of the heights, and its carry (slot `1`) value is bounded STRICTLY above
the line. -/
def Dv3ResSurv {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ₂ : Polynomial O) (u₂ ℓ₂ : ℕ) (Ψ₃ : Polynomial O) (u₃ ℓ₃ : ℕ) : Prop :=
  ∀ ⦃A B : Polynomial O⦄ ⦃Ha Hb : ℕ⦄,
    A.natDegree < Ψ₃.natDegree → B.natDegree < Ψ₃.natDegree →
    dv3Hgt L Ψ₂ u₂ ℓ₂ A = (Ha : ℕ∞) → dv3Hgt L Ψ₂ u₂ ℓ₂ B = (Hb : ℕ∞) →
    dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (A * B) 0) = ((Ha + Hb : ℕ) : ℕ∞) ∧
    ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞) + 1 ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (A * B) 1) + (u₃ : ℕ∞)

/-- A product of two outer digits is SHORT (degree `< 2 · deg Ψ₃`; mirror of C132nv2's
`natDegree_dev2_mul_lt`). -/
theorem natDegree_dev3_mul_lt (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree)
    {g z : Polynomial O} {j i : ℕ} (hgj : dev Ψ₃ g j ≠ 0) (hzi : dev Ψ₃ z i ≠ 0) :
    (dev Ψ₃ g j * dev Ψ₃ z i).natDegree < 2 * Ψ₃.natDegree := by
  rw [natDegree_mul hgj hzi]
  have h1 : (dev Ψ₃ g j).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₃ hΨ₃d g j)
  have h2 : (dev Ψ₃ z i).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₃ hΨ₃d z i)
  omega

/-- ★ **The convolution term estimate, `≥`-direction, level three** (mirror of C132nv2's
`le_line_dev2_term`): every term of the outer convolution of `g · z` weighs at least
`Sg + Sz` at every slot `J`.  UNCONDITIONAL beyond `Dv3ResSurv`. -/
theorem le_line_dev3_term (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ = (Sg : ℕ∞))
    (hSz : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ = (Sz : ℕ∞)) (J j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (dev Ψ₃ g j * dev Ψ₃ z i * Ψ₃ ^ (j + i)) J)
        + (u₃ * J : ℕ∞) := by
  by_cases hgj : dev Ψ₃ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  by_cases hzi : dev Ψ₃ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  have hHa' : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g j ≠ ⊤ := by
    rw [dv3Pin, dv3Hgt]; exact dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hgj
  have hHb' : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z i ≠ ⊤ := by
    rw [dv3Pin, dv3Hgt]; exact dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have h1 : Sg ≤ ℓ₃ * Ha + u₃ * j := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSg hHa.symm
  have h2 : Sz ≤ ℓ₃ * Hb + u₃ * i := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSz hHb.symm
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ₃ (j + i) _ J hJlt, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ₃ (j + i) _ s]
  have hAdeg : (dev Ψ₃ g j).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₃ hΨ₃d g j)
  have hBdeg : (dev Ψ₃ z i).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₃ hΨ₃d z i)
  have hnat : Sg + Sz ≤ ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by
    calc Sg + Sz ≤ (ℓ₃ * Ha + u₃ * j) + (ℓ₃ * Hb + u₃ * i) := Nat.add_le_add h1 h2
      _ = ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by ring
  match s with
  | 0 =>
    have hval := (hSurv3 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have : ((Sg + Sz : ℕ) : ℕ∞) ≤ ((ℓ₃ * (Ha + Hb) + u₃ * (j + i) : ℕ) : ℕ∞) := by
      exact_mod_cast hnat
    refine le_trans this (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have hval := (hSurv3 hAdeg hBdeg hHa.symm hHb.symm).2
    have hweak : ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞)
        ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (dev Ψ₃ g j * dev Ψ₃ z i) 1) + (u₃ : ℕ∞) :=
      le_trans le_self_add hval
    have hstep : ((Sg + Sz : ℕ) : ℕ∞) ≤ ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞) + (u₃ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hweak le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ₃ hΨ₃d _ (s + 2) (by
      have := natDegree_dev3_mul_lt hΨ₃ hΨ₃d hgj hzi
      nlinarith), dv3Hgt_zero L Ψ₂ u₂ hℓ₂, C118a.smul_top_pos hℓ₃, top_add]
    exact le_top

/-- ★ **The strict convolution term estimate, level three** (mirror of C132nv2's
`lt_line_dev2_term`, the survival direction): every term of the outer convolution OTHER
than an exact-slot on-side pair weighs at least `Sg + Sz + 1`. -/
theorem lt_line_dev3_term (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree) {u₂ ℓ₂ : ℕ}
    (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ = (Sg : ℕ∞))
    (hSz : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ = (Sz : ℕ∞)) {J j i : ℕ}
    (hbad : ¬ (j + i = J ∧ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ j
      ∧ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞)
      ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (dev Ψ₃ g j * dev Ψ₃ z i * Ψ₃ ^ (j + i)) J)
        + (u₃ * J : ℕ∞) := by
  by_cases hgj : dev Ψ₃ g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  by_cases hzi : dev Ψ₃ z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  have hHa' : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g j ≠ ⊤ := by
    rw [dv3Pin, dv3Hgt]; exact dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hgj
  have hHb' : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z i ≠ ⊤ := by
    rw [dv3Pin, dv3Hgt]; exact dv2Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hzi
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 hHa'
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1 hHb'
  have hAdeg : (dev Ψ₃ g j).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt hΨ₃ hΨ₃d g j)
  have hBdeg : (dev Ψ₃ z i).natDegree < Ψ₃.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt hΨ₃ hΨ₃d z i)
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt hΨ₃ (j + i) _ J hJlt, dv3Hgt_zero L Ψ₂ u₂ hℓ₂,
      C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow hΨ₃ (j + i) _ s]
  match s with
  | 0 =>
    have hoff : ¬ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ j
        ∨ ¬ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ i := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨by omega, hcon.1, hcon.2⟩
    have hstrict : Sg + Sz + 1 ≤ ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by
      rcases hoff with hng | hnz
      · have h1 : Sg < ℓ₃ * Ha + u₃ * j := lt_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSg hHa.symm hng
        have h2 : Sz ≤ ℓ₃ * Hb + u₃ * i := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSz hHb.symm
        calc Sg + Sz + 1 ≤ (ℓ₃ * Ha + u₃ * j) + (ℓ₃ * Hb + u₃ * i) := by omega
          _ = ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by ring
      · have h1 : Sg ≤ ℓ₃ * Ha + u₃ * j := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSg hHa.symm
        have h2 : Sz < ℓ₃ * Hb + u₃ * i := lt_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSz hHb.symm hnz
        calc Sg + Sz + 1 ≤ (ℓ₃ * Ha + u₃ * j) + (ℓ₃ * Hb + u₃ * i) := by omega
          _ = ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by ring
    have hval := (hSurv3 hAdeg hBdeg hHa.symm hHb.symm).1
    rw [Nat.add_zero, hval]
    have hcast : ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ((ℓ₃ * (Ha + Hb) + u₃ * (j + i) : ℕ) : ℕ∞) := by
      exact_mod_cast hstrict
    refine le_trans hcast (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  | 1 =>
    have h1 : Sg ≤ ℓ₃ * Ha + u₃ * j := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSg hHa.symm
    have h2 : Sz ≤ ℓ₃ * Hb + u₃ * i := le_dv3Weight L hΨ₃ hΨ₃d hℓ₂ hℓ₃ hSz hHb.symm
    have hval := (hSurv3 hAdeg hBdeg hHa.symm hHb.symm).2
    have hstep : ((Sg + Sz + 1 : ℕ) : ℕ∞)
        ≤ (ℓ₃ • ((Ha + Hb : ℕ) : ℕ∞) + 1) + (u₃ * (j + i) : ℕ∞) := by
      rw [nsmul_eq_mul]
      have hnat : Sg + Sz + 1 ≤ (ℓ₃ * (Ha + Hb) + 1) + u₃ * (j + i) := by
        have h3 : Sg + Sz ≤ (ℓ₃ * Ha + u₃ * j) + (ℓ₃ * Hb + u₃ * i) := Nat.add_le_add h1 h2
        have h4 : (ℓ₃ * Ha + u₃ * j) + (ℓ₃ * Hb + u₃ * i)
            = ℓ₃ * (Ha + Hb) + u₃ * (j + i) := by ring
        omega
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hval le_rfl) (le_of_eq ?_))
    push_cast; ring
  | (s + 2) =>
    rw [dev_eq_zero_of_lt hΨ₃ hΨ₃d _ (s + 2) (by
      have h := natDegree_dev3_mul_lt hΨ₃ hΨ₃d hgj hzi
      nlinarith), dv3Hgt_zero L Ψ₂ u₂ hℓ₂, C118a.smul_top_pos hℓ₃, top_add]
    exact le_top

/-- The finite-sum ultrametric for `dv3Hgt`, in the weighted form the outer convolution
consumes (mirror of C132nv2's `le_weight_dv2Hgt_sum`; free from Part 1's `dv3Hgt` zero/
ultrametric-add shims). -/
private theorem le_weight_dv3Hgt_sum (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) {ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {c d : ℕ∞}
    (hall : ∀ p ∈ s, c ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (G p) + d) :
    c ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (∑ p ∈ s, G p) + d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, dv3Hgt_zero L Ψ₂ u₂ hℓ₂, C118a.smul_top_pos hℓ₃, top_add]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    have hmono : Monotone (fun x : ℕ∞ => ℓ₃ • x + d) :=
      fun x y hxy => add_le_add (nsmul_le_nsmul_right hxy ℓ₃) le_rfl
    calc c ≤ min (ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (G a) + d)
          (ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (∑ p ∈ t, G p) + d) :=
          le_min (hall a (Finset.mem_cons_self a t))
            (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
      _ = ℓ₃ • min (dv3Hgt L Ψ₂ u₂ ℓ₂ (G a)) (dv3Hgt L Ψ₂ u₂ ℓ₂ (∑ p ∈ t, G p)) + d :=
          (hmono.map_min).symm
      _ ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂ (G a + ∑ p ∈ t, G p) + d :=
          hmono (min_dv3Hgt_le_dv3Hgt_add L hΨ₂ hΨ₂d hℓ₂ _ _)

/-- ★ **The `dv3Supp` product law, `≥`-direction, UNIVERSAL** (mirror of C132nv2's
`dv2Supp_add_le_dv2Supp_mul`; the level-three B.33, two levels up): every zero case
included.  This is the "≥" half of the eventual μ₄ product law; the "≤" half needs
`Dv3ResSurv` at the chosen minimizers, assembled below. -/
theorem dv3Supp_add_le_dv3Supp_mul (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) (g z : Polynomial O) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃
      ≤ dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃ := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃]
    exact le_top
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dv3Supp_zero_eq_top L Ψ₂ u₂ hℓ₂ Ψ₃ u₃ hℓ₃]
    exact le_top
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1
    (dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hg)
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1
    (dv3Supp_ne_top_of_ne_zero L hΨ₂ hΨ₂d u₂ ℓ₂ hΨ₃ hΨ₃d u₃ ℓ₃ hz)
  rw [← hSg, ← hSz, ← Nat.cast_add]
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ₃.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₃d)
  have hzN : z.natDegree < N * Ψ₃.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₃d)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ₃ g j * Ψ₃ ^ j = g := sum_dev_eq hΨ₃ hΨ₃d g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ₃ z i * Ψ₃ ^ i = z := sum_dev_eq hΨ₃ hΨ₃d z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ₃ g j * Ψ₃ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ₃ z i * Ψ₃ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  rw [dv3Supp]
  refine Finset.le_inf fun J _ => ?_
  have hdev : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) J
      = dv3Hgt L Ψ₂ u₂ ℓ₂ (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) J) := by
    rw [dv3Pin]
    congr 1
    conv_lhs => rw [hrep]
    exact dev_finsetSum hΨ₃ _ _ J
  rw [hdev]
  exact le_weight_dv3Hgt_sum L hΨ₂ hΨ₂d hℓ₂ hℓ₃ _ _
    (fun p _ => le_line_dev3_term L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3
      hSg.symm hSz.symm J p.1 p.2)

/-! ### The endpoint/minimizer assembly (mirror of C132nv2's Part 3)

`Dv3ResSurv` supplies the endpoint's own survival directly (its first clause, applied at
the CHOSEN minimizers) — so every theorem below closes with `Dv3ResSurv` alone, no
separate endpoint hypothesis, exactly as one level down. -/

/-- Every on-side abscissa lies within the development range (mirror of C132nv2's
`dv2SideMin_le_natDegree`). -/
theorem dv3SideMin_le_natDegree {u₂ ℓ₂ : ℕ} (f : Polynomial O) (u₃ ℓ₃ : ℕ)
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃).Nonempty) :
    dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne ≤ f.natDegree := by
  classical
  have hmem := Finset.min'_mem (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃) hne
  have h := (Finset.mem_filter.mp (show dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ hne ∈
    (Finset.range (f.natDegree + 1)).filter
      (fun j => Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ f u₃ ℓ₃ j) from hmem)).1
  rw [Finset.mem_range] at h
  omega

/-- ★ **The endpoint survives, DERIVED from `Dv3ResSurv`** (mirror of C132nv2's
`dv2_endpoint_dev_le`): the product's development coefficient at the SUM of the chosen
minimizers has inner value at most `Hg + Hz`. -/
private theorem dv3_endpoint_dev_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty) {Hg Hz : ℕ}
    (hHg : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng) = (Hg : ℕ∞))
    (hHz : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) = (Hz : ℕ∞)) :
    dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (g * z)
        (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng + dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz))
      ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  set jg := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng with hjg
  set jz := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz with hjz
  have hSg : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ = ((ℓ₃ * Hg + u₃ * jg : ℕ) : ℕ∞) :=
    dv3Supp_eq_of_dv3OnSide L hHg (dv3OnSide_dv3SideMin L g u₃ ℓ₃ hng)
  have hSz : dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ = ((ℓ₃ * Hz + u₃ * jz : ℕ) : ℕ∞) :=
    dv3Supp_eq_of_dv3OnSide L hHz (dv3OnSide_dv3SideMin L z u₃ ℓ₃ hnz)
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * Ψ₃.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₃d)
  have hzN : z.natDegree < N * Ψ₃.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hΨ₃d)
  have hgrep : ∑ j ∈ Finset.range N, dev Ψ₃ g j * Ψ₃ ^ j = g := sum_dev_eq hΨ₃ hΨ₃d g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev Ψ₃ z i * Ψ₃ ^ i = z := sum_dev_eq hΨ₃ hΨ₃d z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev Ψ₃ g j * Ψ₃ ^ j)
        * (∑ i ∈ Finset.range N, dev Ψ₃ z i * Ψ₃ ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hp0 : ((jg, jz) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N := by
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have := dv3SideMin_le_natDegree L g u₃ ℓ₃ hng
      omega
    · have := dv3SideMin_le_natDegree L z u₃ ℓ₃ hnz
      omega
  have hT0 : dev Ψ₃ (dev Ψ₃ g jg * dev Ψ₃ z jz * Ψ₃ ^ (jg + jz)) (jg + jz)
      = dev Ψ₃ (dev Ψ₃ g jg * dev Ψ₃ z jz) 0 := by
    have h := dev_mul_pow hΨ₃ (jg + jz) (dev Ψ₃ g jg * dev Ψ₃ z jz) 0
    rwa [Nat.add_zero] at h
  have hsplit : dev Ψ₃ (g * z) (jg + jz)
      = dev Ψ₃ (dev Ψ₃ g jg * dev Ψ₃ z jz) 0
        + ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
            dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) (jg + jz) := by
    have hdev : dev Ψ₃ (g * z) (jg + jz)
        = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) (jg + jz) := by
      conv_lhs => rw [hrep]
      exact dev_finsetSum hΨ₃ _ _ (jg + jz)
    rw [hdev, ← hT0]
    exact (Finset.add_sum_erase _ _ hp0).symm
  have hallR : ∀ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      ((ℓ₃ * (Hg + Hz) + u₃ * (jg + jz) + 1 : ℕ) : ℕ∞)
        ≤ ℓ₃ • dv3Hgt L Ψ₂ u₂ ℓ₂
            (dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) (jg + jz))
          + (u₃ * (jg + jz) : ℕ∞) := by
    intro p hp
    have hbad : ¬ (p.1 + p.2 = jg + jz ∧ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ p.1
        ∧ Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ p.2) := by
      rintro ⟨hsum, h1, h2⟩
      obtain ⟨e1, e2⟩ := dv3OnSide_endpoint_unique L hℓ₂ hΨ₃ hΨ₃d hng hnz hsum h1 h2
      exact (Finset.mem_erase.1 hp).1 (Prod.ext_iff.2 ⟨e1, e2⟩)
    refine le_trans (le_of_eq ?_)
      (lt_line_dev3_term L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hSg hSz hbad)
    push_cast; ring
  have hRw := le_weight_dv3Hgt_sum L hΨ₂ hΨ₂d hℓ₂ hℓ₃ _ _ hallR
  have hR : ((Hg + Hz : ℕ) : ℕ∞) + 1
      ≤ dv3Hgt L Ψ₂ u₂ ℓ₂ (∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
          dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) (jg + jz)) :=
    succ_le_of_weight_succ_le hRw
  have hAdeg : (dev Ψ₃ g jg).natDegree < Ψ₃.natDegree := by
    rcases eq_or_ne (dev Ψ₃ g jg) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨ₃d
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ₃ hΨ₃d g jg)
  have hBdeg : (dev Ψ₃ z jz).natDegree < Ψ₃.natDegree := by
    rcases eq_or_ne (dev Ψ₃ z jz) 0 with h0 | hne
    · rw [h0, natDegree_zero]; exact hΨ₃d
    · exact natDegree_lt_natDegree hne (degree_dev_lt hΨ₃ hΨ₃d z jz)
  have hval : dv3Hgt L Ψ₂ u₂ ℓ₂ (dev Ψ₃ (dev Ψ₃ g jg * dev Ψ₃ z jz) 0)
      = ((Hg + Hz : ℕ) : ℕ∞) :=
    (hSurv3 hAdeg hBdeg hHg hHz).1
  rw [hsplit]
  set T := dev Ψ₃ (dev Ψ₃ g jg * dev Ψ₃ z jz) 0 with hT
  set R := ∑ p ∈ (Finset.range N ×ˢ Finset.range N).erase (jg, jz),
      dev Ψ₃ (dev Ψ₃ g p.1 * dev Ψ₃ z p.2 * Ψ₃ ^ (p.1 + p.2)) (jg + jz) with hRdef
  rcases eq_or_ne (dv3Hgt L Ψ₂ u₂ ℓ₂ T) (dv3Hgt L Ψ₂ u₂ ℓ₂ R) with heq | hne
  · exfalso
    have h1 : ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ ((Hg + Hz : ℕ) : ℕ∞) := by
      calc ((Hg + Hz : ℕ) : ℕ∞) + 1 ≤ dv3Hgt L Ψ₂ u₂ ℓ₂ R := hR
        _ = dv3Hgt L Ψ₂ u₂ ℓ₂ T := heq.symm
        _ = ((Hg + Hz : ℕ) : ℕ∞) := hval
    rw [show ((Hg + Hz : ℕ) : ℕ∞) + 1 = ((Hg + Hz + 1 : ℕ) : ℕ∞) by push_cast; ring] at h1
    exact absurd (by exact_mod_cast h1 : Hg + Hz + 1 ≤ Hg + Hz) (by omega)
  · rw [dv3Hgt_add_eq L hΨ₂ hΨ₂d hℓ₂ hne, hval]
    exact min_le_left _ _

/-- ★ **The endpoint lemma, level three, value form** (mirror of C132nv2's
`dv2Supp_mul_of_endpoint_le`): given `Dv3ResSurv`, the product's cleared support is
EXACTLY the sum of the factors' supports, read at the sum of the chosen minimizers. -/
theorem dv3Supp_mul_of_endpoint_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty) {Hg Hz : ℕ}
    (hHg : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng) = (Hg : ℕ∞))
    (hHz : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) = (Hz : ℕ∞)) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
      = ((ℓ₃ * (Hg + Hz)
          + u₃ * (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng
            + dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) : ℕ) : ℕ∞) := by
  set jg := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng with hjg
  set jz := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz with hjz
  have hSg := dv3Supp_eq_of_dv3OnSide L hHg (dv3OnSide_dv3SideMin L g u₃ ℓ₃ hng)
  have hSz := dv3Supp_eq_of_dv3OnSide L hHz (dv3OnSide_dv3SideMin L z u₃ ℓ₃ hnz)
  have hup := dv3_endpoint_dev_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hng hnz hHg hHz
  refine le_antisymm ?_ ?_
  · refine le_trans (dv3Supp_le_term L hΨ₃ hΨ₃d u₂ hℓ₂ (g * z) u₃ hℓ₃ (jg + jz)) ?_
    refine le_trans (add_le_add (nsmul_le_nsmul_right hup ℓ₃) le_rfl) (le_of_eq ?_)
    rw [nsmul_eq_mul]; push_cast; ring
  · refine le_trans (le_of_eq ?_)
      (dv3Supp_add_le_dv3Supp_mul L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 g z)
    rw [hSg, hSz]; push_cast; ring

/-- ★ **The endpoint lemma, level three, minimizer form** (mirror of C132nv2's
`dv2OnSide_mul_endpoint` — row D3-02's signed endpoint-uniqueness exit): the sum of the
chosen minimizers IS a product minimizer. -/
theorem dv3OnSide_mul_endpoint (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty) {Hg Hz : ℕ}
    (hHg : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng) = (Hg : ℕ∞))
    (hHz : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) = (Hz : ℕ∞)) :
    Dv3OnSide L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
      (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng + dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) := by
  set jg := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng with hjg
  set jz := dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz with hjz
  have hval := dv3Supp_mul_of_endpoint_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hng hnz hHg hHz
  have hup' : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) (jg + jz) ≤ ((Hg + Hz : ℕ) : ℕ∞) :=
    dv3_endpoint_dev_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hng hnz hHg hHz
  have hlow := dv3Supp_le_term (Ψ₂ := Ψ₂) L hΨ₃ hΨ₃d u₂ hℓ₂ (g * z) u₃ hℓ₃ (jg + jz)
  rw [hval] at hlow
  have hhgt_ne : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) (jg + jz) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hup'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hhgt_ne
  have hcle : c ≤ Hg + Hz := by rw [← hc] at hup'; exact_mod_cast hup'
  have hcge : Hg + Hz ≤ c := by
    rw [← hc, nsmul_eq_mul] at hlow
    have hnat : ℓ₃ * (Hg + Hz) + u₃ * (jg + jz) ≤ ℓ₃ * c + u₃ * (jg + jz) := by
      exact_mod_cast hlow
    have hmul : ℓ₃ * (Hg + Hz) ≤ ℓ₃ * c := by omega
    exact Nat.le_of_mul_le_mul_left hmul hℓ₃
  have hcexact : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [← hc]; exact_mod_cast (show c = Hg + Hz by omega)
  refine ⟨?_, by rw [hcexact]; exact ENat.coe_ne_top _⟩
  rw [hval, hcexact, nsmul_eq_mul]
  push_cast; ring

/-- The chosen product minimizer is BOUNDED BY the sum of the factors' minimizers (mirror
of C132nv2's `dv2SideMin_mul_le`). -/
theorem dv3SideMin_mul_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty) {Hg Hz : ℕ}
    (hHg : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng) = (Hg : ℕ∞))
    (hHz : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) = (Hz : ℕ∞))
    (hne : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃).Nonempty) :
    dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃ hne
      ≤ dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng + dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz :=
  dv3SideMin_le_of_dv3OnSide L hℓ₂ hΨ₃ hΨ₃d hne
    (dv3OnSide_mul_endpoint L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hng hnz hHg hHz)

/-- ★ **The consumption shape, level three** (mirror of C132nv2's
`dv2Supp_mul_eq_add_of_endpoint_le`): given `Dv3ResSurv`, the level-three product law
fires — `dv3Supp (g · z) = dv3Supp g + dv3Supp z`. -/
theorem dv3Supp_mul_eq_add_of_endpoint_le (hΨ₂ : Ψ₂.Monic) (hΨ₂d : 0 < Ψ₂.natDegree)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hΨ₃ : Ψ₃.Monic) (hΨ₃d : 0 < Ψ₃.natDegree) {u₃ ℓ₃ : ℕ}
    (hℓ₃ : 0 < ℓ₃) (hSurv3 : Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃) {g z : Polynomial O}
    (hng : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃).Nonempty)
    (hnz : (dv3SideSet L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃).Nonempty) {Hg Hz : ℕ}
    (hHg : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ g (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ hng) = (Hg : ℕ∞))
    (hHz : dv3Pin L Ψ₂ u₂ ℓ₂ Ψ₃ z (dv3SideMin L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ hnz) = (Hz : ℕ∞)) :
    dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ (g * z) u₃ ℓ₃
      = dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ g u₃ ℓ₃ + dv3Supp L Ψ₂ u₂ ℓ₂ Ψ₃ z u₃ ℓ₃ := by
  rw [dv3Supp_mul_of_endpoint_le L hΨ₂ hΨ₂d hℓ₂ hΨ₃ hΨ₃d hℓ₃ hSurv3 hng hnz hHg hHz,
    dv3Supp_eq_of_dv3OnSide L hHg (dv3OnSide_dv3SideMin L g u₃ ℓ₃ hng),
    dv3Supp_eq_of_dv3OnSide L hHz (dv3OnSide_dv3SideMin L z u₃ ℓ₃ hnz)]
  push_cast
  ring

end GenericEndpoint

end Uniformity.Density.Tower.C136d0

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136d0.dv3Hgt
#print axioms Uniformity.Density.Tower.C136d0.dv3Hgt_eq_dv2Supp
#print axioms Uniformity.Density.Tower.C136d0.dv3Pin
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp
#print axioms Uniformity.Density.Tower.C136d0.dv3Hgt_zero
#print axioms Uniformity.Density.Tower.C136d0.dv3Hgt_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C136d0.min_dv3Hgt_le_dv3Hgt_add
#print axioms Uniformity.Density.Tower.C136d0.dv3Hgt_add_eq
#print axioms Uniformity.Density.Tower.C136d0.dv3Pin_top_of_gt
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_zero_eq_top
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_eq_inf_range
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C136d0.min_dv3Supp_le_dv3Supp_add
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_neg
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_add_eq_of_lt
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_add_eq
#print axioms Uniformity.Density.Tower.C136d0.s2g8_monic
#print axioms Uniformity.Density.Tower.C136d0.s2g8_natDegree
#print axioms Uniformity.Density.Tower.C136d0.s2g8_eq_keyChain_three
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_eq_dv3Supp
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_eq_keyChain_dev
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_zero
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_ne_top
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_add_ge
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_add_eq
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_g8
#print axioms Uniformity.Density.Tower.C136d0.s2Hgt₄_keyChain_three
#print axioms Uniformity.Density.Tower.C136d0.Dv3OnSide
#print axioms Uniformity.Density.Tower.C136d0.dv3SideSet
#print axioms Uniformity.Density.Tower.C136d0.dv3SideMin
#print axioms Uniformity.Density.Tower.C136d0.dv3OnSide_of_mem_dv3SideSet
#print axioms Uniformity.Density.Tower.C136d0.mem_dv3SideSet_of_dv3OnSide
#print axioms Uniformity.Density.Tower.C136d0.dv3OnSide_dv3SideMin
#print axioms Uniformity.Density.Tower.C136d0.dv3SideMin_le_of_dv3OnSide
#print axioms Uniformity.Density.Tower.C136d0.not_dv3OnSide_of_lt_dv3SideMin
#print axioms Uniformity.Density.Tower.C136d0.dv3OnSide_endpoint_unique
#print axioms Uniformity.Density.Tower.C136d0.exists_dv3SideMin_height
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_eq_of_dv3OnSide
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_le_term
#print axioms Uniformity.Density.Tower.C136d0.le_dv3Weight
#print axioms Uniformity.Density.Tower.C136d0.lt_dv3Weight
#print axioms Uniformity.Density.Tower.C136d0.Dv3ResSurv
#print axioms Uniformity.Density.Tower.C136d0.natDegree_dev3_mul_lt
#print axioms Uniformity.Density.Tower.C136d0.le_line_dev3_term
#print axioms Uniformity.Density.Tower.C136d0.lt_line_dev3_term
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_add_le_dv3Supp_mul
#print axioms Uniformity.Density.Tower.C136d0.dv3SideMin_le_natDegree
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_mul_of_endpoint_le
#print axioms Uniformity.Density.Tower.C136d0.dv3OnSide_mul_endpoint
#print axioms Uniformity.Density.Tower.C136d0.dv3SideMin_mul_le
#print axioms Uniformity.Density.Tower.C136d0.dv3Supp_mul_eq_add_of_endpoint_le

end AxCheck
