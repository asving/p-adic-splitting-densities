/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.HenselCount
import LeanUrat.OM.SparseResultant
import LeanUrat.OM.RestartEquiv

/-!
# BlockProduct — Phase-B wave W4d2-1: the multi-block product law at level `N`

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md`, "(d2) multi-block cells —
GATE-CORRECTED FORM" (pinned 2026-07-04) + the d2-0 numeric gate
`/workspace-vast/asving/tmp/phaseb_w4d2_0/SUMMARY.md`.  The verified law:
`|fiber| · p^X = Π_i |P_i|` with `X = Σ_{i<j} m_i m_j w_ij` — the multiplication map
`Π_i P_i → fiber` is exactly `p^X`-to-1 (census-level independence ONLY; decided `μ = 1`
blocks obey the same pattern formula at floor `e + 1`).

**Deliverable 1 (`pair_fiber_card`, `pair_card`).**  `HenselCount.fiber_card`/`image_card`
restricted to *sub-cells* of the `p^(c+1)`-divisibility cells: any subsets
`S_A ⊆ cell A₀ a (c+1)`, `S_B ⊆ cell B₀ b (c+1)` that are **kernel-saturated**
(`Saturated · · (N-c)`: stable under coefficientwise `p^(N-c)`-perturbation among monics of
the right degree).  The torsor argument restricts verbatim: `fiber_sub_dvd` puts any second
factorization within `p^(N-c)` of the base point, and saturation pulls it back into the
sub-cells, so the sub-cell fiber IS the full-cell fiber (`p^c` points), and the counting
identity `card(image) · p^c = card S_A · card S_B` follows by the same fiber-summing.
Floor-defined sub-cells (`patternCell`, per-coefficient floors `flo`) are saturated iff
`flo i ≤ N - c` for all `i` and contained in the Hensel cell iff `c + 1 ≤ flo i`
(`pair_card_pattern` states both hypotheses explicitly).

**Deliverable 2 (`GoodChain`, `blocks_card`).**  The k-block iteration, by folding
deliverable 1 along a list of blocks: `card (imageSet l) * p^X = Π_i card (coset i)` where
`X` accumulates the per-step resultant valuations `c` (supplied against the partial product
center; `resultant_mul_p_pow` reduces those to pairwise data via mathlib's
`resultant_mul_right`).  The fold's induction invariant is that each partial image is again
a sub-cell-with-saturation; containment is generic (`mul_image_subset_cell`), and saturation
of an image is a genuine **one-step Hensel lifting** statement (`mul_image_saturated`),
provable under the stronger margin `N ≤ 2·(m - c)` with component saturation levels
`m_A, m_B ≤ m - c` — the adjugate solves the linearized equation exactly and the quadratic
correction dies outright.  `GoodChain` carries the per-step facts as constructor fields, so
partial/case-specific margin bookkeeping stays with the consumer.

**THE MARGIN QUESTION (deliverable 3) — answered: `2c < N` FAILS at ALL THREE d2-0 gates.**
* case A (p=2, N=5): `c = X = 4`, `2c = 8 ≥ 5`;
* case B (p=3, N=3): `c = X = 2`, `2c = 4 ≥ 3`;
* case C (p=3, N=4): `c = X = 4`, `2c = 8 ≥ 4`.
Worse, the sub-cell premises THEMSELVES fail at the gates: at case B the pattern coset's
x-adic floors are `(2, 1)` (constant/linear slot), so the coset is *not* inside the Hensel
cell `cell(A₀, 2, c+1 = 3)` (floors < 3) *and* not kernel-saturated (slot-0 floor
`2 > N - c = 1`).  Same at A (`floors (3,2)/(5,3)` vs `N - c = 1`, `c+1 = 5`) and C
(`floors (5,3)/(3)` vs `N - c = 0`, `c+1 = 5`).  The gate's verified law therefore lives
strictly beyond the uniform-margin regime banked here: the W4d2′ sharpening obligation is a
Newton-polygon-graded (per-slot) margin — per-slot floors interlocking with the graded
valuation of the resultant, not the flat `2c < N` / `flo ≤ N - c` pair.  Deliverables 1–2
are banked under the stated (sufficient, gate-empty) margins; the gate instances are proved
below by direct enumeration/closed forms (`gateB_*`, `gateA_coset_product`,
`gateC_coset_product`), and the `hres` supplier at case B's standard product representative
is discharged exactly (`caseB_hres`: `Res(φ_{c̃=1}, φ_{c̃=2}, 2, 2) = p² · unit` via
`SparseResultant.resultant_sparseTwist_isUnit`, so `c = 2` is pinned in Lean, not just
numerically).

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints (checked with
`#print axioms`, prints removed after checking); no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.BlockProduct

open Polynomial Matrix
open LeanUrat.OM
open LeanUrat.OM.HenselCount

variable {p : ℕ} [hp : Fact p.Prime] {N : ℕ}

/-! ## 1. Sub-cells and saturation -/

/-- A **pattern sub-cell**: the HenselCount coefficient cell refined by per-coefficient
`p`-power floors `flo : ℕ → ℕ` (the x-adic shadow of a `FreshClusterPattern` coset). -/
def patternCell (P₀ : (ZMod (p ^ N))[X]) (d : ℕ) (flo : ℕ → ℕ) : Set ((ZMod (p ^ N))[X]) :=
  {P | P.Monic ∧ P.natDegree = d ∧ ∀ i, (p : ZMod (p ^ N)) ^ flo i ∣ (P - P₀).coeff i}

/-- `S` is **saturated at level `m`** (in degree `d`): perturbing a member coefficientwise by
`p^m`-multiples, within monics of `natDegree = d`, stays in `S`.  With `m = N - c` this is
exactly *kernel-saturation*: stability under translation by the `fiberEquivKer` kernel. -/
def Saturated (S : Set ((ZMod (p ^ N))[X])) (d m : ℕ) : Prop :=
  ∀ P ∈ S, ∀ Q : (ZMod (p ^ N))[X], Q.Monic → Q.natDegree = d →
    (∀ i, (p : ZMod (p ^ N)) ^ m ∣ (Q - P).coeff i) → Q ∈ S

theorem cell_eq_patternCell (P₀ : (ZMod (p ^ N))[X]) (d k : ℕ) :
    HenselCount.cell P₀ d k = patternCell P₀ d fun _ => k := rfl

theorem patternCell_subset_cell {P₀ : (ZMod (p ^ N))[X]} {d k : ℕ} {flo : ℕ → ℕ}
    (h : ∀ i, k ≤ flo i) : patternCell P₀ d flo ⊆ HenselCount.cell P₀ d k := fun _P hP =>
  ⟨hP.1, hP.2.1, fun i => dvd_trans (pow_dvd_pow _ (h i)) (hP.2.2 i)⟩

/-- Floor sub-cells are saturated at any level dominating every floor: the kernel translation
preserves the deeper floors **iff** the kernel vectors satisfy them. -/
theorem patternCell_saturated {P₀ : (ZMod (p ^ N))[X]} {d : ℕ} {flo : ℕ → ℕ} {m : ℕ}
    (h : ∀ i, flo i ≤ m) : Saturated (patternCell P₀ d flo) d m := by
  intro P hP Q hQmon hQdeg hdvd
  refine ⟨hQmon, hQdeg, fun i => ?_⟩
  have hsplit : Q - P₀ = (P - P₀) + (Q - P) := by ring
  rw [hsplit, Polynomial.coeff_add]
  exact dvd_add (hP.2.2 i) (dvd_trans (pow_dvd_pow _ (h i)) (hdvd i))

theorem cell_saturated {P₀ : (ZMod (p ^ N))[X]} {d k m : ℕ} (h : k ≤ m) :
    Saturated (HenselCount.cell P₀ d k) d m := by
  rw [cell_eq_patternCell]
  exact patternCell_saturated fun _ => h

theorem saturated_anti {S : Set ((ZMod (p ^ N))[X])} {d m m' : ℕ} (h : m ≤ m')
    (hS : Saturated S d m) : Saturated S d m' := fun P hP Q hQmon hQdeg hdvd =>
  hS P hP Q hQmon hQdeg fun i => dvd_trans (pow_dvd_pow _ h) (hdvd i)

/-! ## 2. Deliverable 1 — the two-block core on sub-cells -/

/-- **Restricted `fiber_card`.**  On kernel-saturated sub-cells of the `c+1`-cells, every
fiber of `(A, B) ↦ A·B` over its image still has exactly `p^c` points: the sub-cell fiber
coincides with the full-cell fiber, because `fiber_sub_dvd` bounds any second factorization
within `p^(N-c)` of the base point and saturation pulls it back into the sub-cells. -/
theorem pair_fiber_card {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    (hc : 2 * c < N) {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ HenselCount.cell A₀ a (c + 1)) (hSAsat : Saturated SA a (N - c))
    (hSB : SB ⊆ HenselCount.cell B₀ b (c + 1)) (hSBsat : Saturated SB b (N - c))
    {g : (ZMod (p ^ N))[X]}
    (hg : g ∈ (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) '' (SA ×ˢ SB)) :
    Nat.card {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
        AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = g} = p ^ c := by
  obtain ⟨⟨A, B⟩, hABmem, hgeq⟩ := hg
  rw [Set.mem_prod] at hABmem
  obtain ⟨hA, hB⟩ := hABmem
  have hgAB : A * B = g := hgeq
  have hAc := hSA hA
  have hBc := hSB hB
  have hdet : ∃ u : (ZMod (p ^ N))ˣ,
      (Polynomial.sylvester A B a b).det = (p : ZMod (p ^ N)) ^ c * u :=
    det_sylvester_stable hres hAc.2.2 hBc.2.2
  have hiff : ∀ AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X],
      (AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = g)
        ↔ (AB.1 ∈ HenselCount.cell A₀ a (c + 1) ∧ AB.2 ∈ HenselCount.cell B₀ b (c + 1)
            ∧ AB.1 * AB.2 = g) := by
    rintro ⟨A', B'⟩
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hSA h1, hSB h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hprod : A' * B' = A * B := h3.trans hgAB.symm
      obtain ⟨hα, hβ⟩ := fiber_sub_dvd hc hdet hAc hBc h1 h2 hprod
      exact ⟨hSAsat A hA A' h1.1 h1.2.1 hα, hSBsat B hB B' h2.1 h2.2.1 hβ, h3⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact fiber_card hres hc ⟨(A, B), Set.mem_prod.mpr ⟨hAc, hBc⟩, hgAB⟩

/-- **Deliverable 1 (`pair_card`)** — `image_card` restricted to sub-cells:
`card (image of S_A × S_B under mul) · p^c = card S_A · card S_B`. -/
theorem pair_card {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    (hc : 2 * c < N) {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ HenselCount.cell A₀ a (c + 1)) (hSAsat : Saturated SA a (N - c))
    (hSB : SB ⊆ HenselCount.cell B₀ b (c + 1)) (hSBsat : Saturated SB b (N - c)) :
    Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
        (SA ×ˢ SB)) * p ^ c
      = Nat.card SA * Nat.card SB := by
  classical
  set D : Set ((ZMod (p ^ N))[X] × (ZMod (p ^ N))[X]) := SA ×ˢ SB with hD
  set f : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] → (ZMod (p ^ N))[X] :=
    fun AB => AB.1 * AB.2 with hf
  have hSAfin : SA.Finite := (cell_finite A₀ a (c + 1)).subset hSA
  have hSBfin : SB.Finite := (cell_finite B₀ b (c + 1)).subset hSB
  have hDfin : D.Finite := hSAfin.prod hSBfin
  have hIfin : (f '' D).Finite := hDfin.image f
  haveI : Fintype ↥(f '' D) := hIfin.fintype
  haveI : Finite ↥D := hDfin.to_subtype
  let F : ↥D → ↥(f '' D) := fun x => ⟨f x.1, Set.mem_image_of_mem f x.2⟩
  have hcard : ∀ gg : ↥(f '' D), Nat.card {x : ↥D // F x = gg} = p ^ c := by
    intro gg
    have e : {x : ↥D // F x = gg}
        ≃ {AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] //
            AB.1 ∈ SA ∧ AB.2 ∈ SB ∧ AB.1 * AB.2 = gg.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1⟩, Subtype.ext y.2.2.2⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => rfl }
    rw [Nat.card_congr e]
    exact pair_fiber_card hres hc hSA hSAsat hSB hSBsat gg.2
  have h1 : Nat.card ↥D = Nat.card ↥(f '' D) * p ^ c := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
      Finset.sum_congr rfl fun gg _ => hcard gg, Finset.sum_const, smul_eq_mul,
      Finset.card_univ, Nat.card_eq_fintype_card]
  have h2 : Nat.card ↥D = Nat.card SA * Nat.card SB := by
    rw [hD, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  rw [← h1]
  exact h2

/-- Deliverable 1 for floor-defined pattern cosets, with the two floor hypotheses stated
explicitly: containment needs `c + 1 ≤ flo i`, kernel-saturation needs `flo i ≤ N - c`.
**Neither holds at any of the three d2-0 gate cells** (see the module docstring). -/
theorem pair_card_pattern {a b c : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    (hc : 2 * c < N) {floA floB : ℕ → ℕ}
    (hfloA1 : ∀ i, c + 1 ≤ floA i) (hfloA2 : ∀ i, floA i ≤ N - c)
    (hfloB1 : ∀ i, c + 1 ≤ floB i) (hfloB2 : ∀ i, floB i ≤ N - c) :
    Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
        (patternCell A₀ a floA ×ˢ patternCell B₀ b floB)) * p ^ c
      = Nat.card (patternCell A₀ a floA) * Nat.card (patternCell B₀ b floB) :=
  pair_card hres hc (patternCell_subset_cell hfloA1) (patternCell_saturated hfloA2)
    (patternCell_subset_cell hfloB1) (patternCell_saturated hfloB2)

/-! ## 3. Image sub-cell structure: containment and one-step Hensel lifting -/

theorem dvd_coeff_mul_right {k : ℕ} {P Q : (ZMod (p ^ N))[X]}
    (hQ : ∀ i, (p : ZMod (p ^ N)) ^ k ∣ Q.coeff i) (i : ℕ) :
    (p : ZMod (p ^ N)) ^ k ∣ (P * Q).coeff i := by
  have h := dvd_coeff_mul (x := (1 : ZMod (p ^ N))) (P := P) (fun j => one_dvd (P.coeff j)) hQ i
  rwa [one_mul] at h

theorem dvd_coeff_mul_left {k : ℕ} {P Q : (ZMod (p ^ N))[X]}
    (hP : ∀ i, (p : ZMod (p ^ N)) ^ k ∣ P.coeff i) (i : ℕ) :
    (p : ZMod (p ^ N)) ^ k ∣ (P * Q).coeff i := by
  have h := dvd_coeff_mul (y := (1 : ZMod (p ^ N))) (Q := Q) hP (fun j => one_dvd (Q.coeff j)) i
  rwa [mul_one] at h

/-- The image of two sub-cells multiplies into the cell around the product center, at the
common floor. -/
theorem mul_image_subset_cell {a b k : ℕ} {A₀ B₀ : (ZMod (p ^ N))[X]}
    {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ HenselCount.cell A₀ a k) (hSB : SB ⊆ HenselCount.cell B₀ b k) :
    (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) '' (SA ×ˢ SB)
      ⊆ HenselCount.cell (A₀ * B₀) (a + b) k := by
  rintro g ⟨⟨A, B⟩, hABmem, rfl⟩
  rw [Set.mem_prod] at hABmem
  have hA := hSA hABmem.1
  have hB := hSB hABmem.2
  refine ⟨hA.1.mul hB.1, ?_, fun i => ?_⟩
  · rw [hA.1.natDegree_mul hB.1, hA.2.1, hB.2.1]
  · have hsplit : A * B - A₀ * B₀ = A * (B - B₀) + (A - A₀) * B₀ := by ring
    show (p : ZMod (p ^ N)) ^ k ∣ (A * B - A₀ * B₀).coeff i
    rw [hsplit, Polynomial.coeff_add]
    exact dvd_add (dvd_coeff_mul_right hB.2.2 i) (dvd_coeff_mul_left hA.2.2 i)

/-- Products of two coefficientwise `p^k`-divisible polynomials vanish once `N ≤ k + k`. -/
theorem mul_eq_zero_of_coeff_dvd_of_le {k : ℕ} (hk : N ≤ k + k) {P Q : (ZMod (p ^ N))[X]}
    (hP : ∀ i, (p : ZMod (p ^ N)) ^ k ∣ P.coeff i)
    (hQ : ∀ i, (p : ZMod (p ^ N)) ^ k ∣ Q.coeff i) : P * Q = 0 := by
  ext i
  rw [Polynomial.coeff_zero]
  have h := dvd_coeff_mul hP hQ i
  rw [← pow_add] at h
  have hz : (p : ZMod (p ^ N)) ^ (k + k) = 0 := by
    have hN0 : (p : ZMod (p ^ N)) ^ N = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    calc (p : ZMod (p ^ N)) ^ (k + k)
        = (p : ZMod (p ^ N)) ^ N * (p : ZMod (p ^ N)) ^ (k + k - N) := by
          rw [← pow_add]; congr 1; omega
      _ = 0 := by rw [hN0, zero_mul]
  rw [hz] at h
  exact zero_dvd_iff.mp h

/-- **One-step Hensel lifting = saturation of the image.**  Under the *stronger* margin
`N ≤ 2·(m - c)` (one Newton step, no iteration: the adjugate solves the linearized equation
`B·α + A·β = v` exactly, and the quadratic correction `α·β` dies outright), the image of two
saturated sub-cells is saturated at every level `m ≥ c + max(m_A, m_B)`.  This is the
induction invariant supplier for the k-block fold. -/
theorem mul_image_saturated {a b c mA mB m : ℕ} (hN : 0 < N) {A₀ B₀ : (ZMod (p ^ N))[X]}
    (hres : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant A₀ B₀ a b = (p : ZMod (p ^ N)) ^ c * u)
    {SA SB : Set ((ZMod (p ^ N))[X])}
    (hSA : SA ⊆ HenselCount.cell A₀ a (c + 1)) (hSB : SB ⊆ HenselCount.cell B₀ b (c + 1))
    (hSAsat : Saturated SA a mA) (hSBsat : Saturated SB b mB)
    (hmA : mA + c ≤ m) (hmB : mB + c ≤ m) (hm2 : N ≤ 2 * (m - c)) :
    Saturated ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
      (SA ×ˢ SB)) (a + b) m := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow (by omega : N ≠ 0) hp.out.one_lt⟩
  rintro P hP Q hQmon hQdeg hQdvd
  obtain ⟨⟨A, B⟩, hABmem, hPeq⟩ := hP
  rw [Set.mem_prod] at hABmem
  obtain ⟨hA, hB⟩ := hABmem
  have hPeq' : A * B = P := hPeq
  subst hPeq'
  have hAc := hSA hA
  have hBc := hSB hB
  obtain ⟨u, hdet⟩ := det_sylvester_stable hres hAc.2.2 hBc.2.2
  have hABmon : (A * B).Monic := hAc.1.mul hBc.1
  have hABdeg : (A * B).natDegree = a + b := by
    rw [hAc.1.natDegree_mul hBc.1, hAc.2.1, hBc.2.1]
  have hvdeg : ∀ i, a + b ≤ i → (Q - A * B).coeff i = 0 := fun i hi =>
    sub_coeff_eq_zero_of_ge hQmon hABmon hQdeg hABdeg hi
  choose z hz using fun i : Fin (a + b) => hQdvd (i : ℕ)
  -- the adjugate solve: x with (sylvester A B) *ᵥ x = coefficient vector of Q - A*B
  set x : Fin (a + b) → ZMod (p ^ N) :=
    (Polynomial.sylvester A B a b).adjugate.mulVec
      (fun i => (↑u⁻¹ : ZMod (p ^ N)) * ((p : ZMod (p ^ N)) ^ (m - c) * z i)) with hx
  have hxdvd : ∀ i, (p : ZMod (p ^ N)) ^ (m - c) ∣ x i := by
    intro i
    rw [hx]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.dvd_sum fun j _ => ?_
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_mul_right _ (z j)) _) _
  have hMx : (Polynomial.sylvester A B a b).mulVec x
      = fun i : Fin (a + b) => (Q - A * B).coeff (i : ℕ) := by
    have h1 : (Polynomial.sylvester A B a b).mulVec x
        = ((Polynomial.sylvester A B a b) * (Polynomial.sylvester A B a b).adjugate).mulVec
            (fun i => (↑u⁻¹ : ZMod (p ^ N)) * ((p : ZMod (p ^ N)) ^ (m - c) * z i)) := by
      rw [hx, Matrix.mulVec_mulVec]
    funext i
    rw [h1, Matrix.mul_adjugate, hdet, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hcm : c + (m - c) = m := by omega
    calc (((p : ZMod (p ^ N)) ^ c * ↑u) •
            fun i => (↑u⁻¹ : ZMod (p ^ N)) * ((p : ZMod (p ^ N)) ^ (m - c) * z i)) i
        = (p : ZMod (p ^ N)) ^ c * ↑u * (↑u⁻¹ * ((p : ZMod (p ^ N)) ^ (m - c) * z i)) := rfl
      _ = (↑u * ↑u⁻¹) * ((p : ZMod (p ^ N)) ^ c * (p : ZMod (p ^ N)) ^ (m - c)) * z i := by
          ring
      _ = (p : ZMod (p ^ N)) ^ m * z i := by rw [Units.mul_inv, one_mul, ← pow_add, hcm]
      _ = (Q - A * B).coeff (i : ℕ) := (hz i).symm
  have hαdvd : ∀ i, (p : ZMod (p ^ N)) ^ (m - c) ∣ (polyOf (leftPart x)).coeff i := by
    intro i
    rw [coeff_polyOf]
    split_ifs with h
    · exact hxdvd _
    · exact dvd_zero _
  have hβdvd : ∀ i, (p : ZMod (p ^ N)) ^ (m - c) ∣ (polyOf (rightPart x)).coeff i := by
    intro i
    rw [coeff_polyOf]
    split_ifs with h
    · exact hxdvd _
    · exact dvd_zero _
  have hlin : A * polyOf (rightPart x) + B * polyOf (leftPart x) = Q - A * B := by
    have h1 := sylvesterMulVec_eq (le_of_eq hAc.2.1) (le_of_eq hBc.2.1) x
    rw [hMx, polyOf_coeff hvdeg] at h1
    exact h1.symm
  have hquad : polyOf (leftPart x) * polyOf (rightPart x) = 0 :=
    mul_eq_zero_of_coeff_dvd_of_le (by omega) hαdvd hβdvd
  have hαtop : ∀ i, a ≤ i → (polyOf (leftPart x)).coeff i = 0 :=
    fun _ hi => coeff_polyOf_of_le _ hi
  have hβtop : ∀ i, b ≤ i → (polyOf (rightPart x)).coeff i = 0 :=
    fun _ hi => coeff_polyOf_of_le _ hi
  obtain ⟨hA'mon, hA'deg⟩ := monic_add_of_coeff hAc.1 hAc.2.1 hαtop
  obtain ⟨hB'mon, hB'deg⟩ := monic_add_of_coeff hBc.1 hBc.2.1 hβtop
  have hA' : A + polyOf (leftPart x) ∈ SA := by
    refine hSAsat A hA _ hA'mon hA'deg fun i => ?_
    have he : A + polyOf (leftPart x) - A = polyOf (leftPart x) := by ring
    rw [he]
    exact dvd_trans (pow_dvd_pow _ (by omega : mA ≤ m - c)) (hαdvd i)
  have hB' : B + polyOf (rightPart x) ∈ SB := by
    refine hSBsat B hB _ hB'mon hB'deg fun i => ?_
    have he : B + polyOf (rightPart x) - B = polyOf (rightPart x) := by ring
    rw [he]
    exact dvd_trans (pow_dvd_pow _ (by omega : mB ≤ m - c)) (hβdvd i)
  refine ⟨(A + polyOf (leftPart x), B + polyOf (rightPart x)),
    Set.mem_prod.mpr ⟨hA', hB'⟩, ?_⟩
  show (A + polyOf (leftPart x)) * (B + polyOf (rightPart x)) = Q
  have hexp : (A + polyOf (leftPart x)) * (B + polyOf (rightPart x))
      = A * B + (A * polyOf (rightPart x) + B * polyOf (leftPart x))
        + polyOf (leftPart x) * polyOf (rightPart x) := by ring
  rw [hexp, hlin, hquad, add_zero]
  ring

/-! ## 4. Deliverable 2 — the k-block iteration -/

/-- A **block**: a center polynomial, its degree, and its (pattern-coset) sub-cell. -/
structure Block (p N : ℕ) where
  center : (ZMod (p ^ N))[X]
  deg : ℕ
  coset : Set ((ZMod (p ^ N))[X])

/-- Product of the block centers (the standard product representative). -/
noncomputable def prodCenter : List (Block p N) → (ZMod (p ^ N))[X]
  | [] => 1
  | b :: l => b.center * prodCenter l

/-- Total degree of a block list. -/
def sumDeg : List (Block p N) → ℕ
  | [] => 0
  | b :: l => b.deg + sumDeg l

/-- The image of the coset product under iterated multiplication. -/
noncomputable def imageSet : List (Block p N) → Set ((ZMod (p ^ N))[X])
  | [] => {1}
  | b :: l => (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
      (b.coset ×ˢ imageSet l)

@[simp] theorem prodCenter_nil : prodCenter ([] : List (Block p N)) = 1 := rfl

@[simp] theorem prodCenter_cons (b : Block p N) (l : List (Block p N)) :
    prodCenter (b :: l) = b.center * prodCenter l := rfl

@[simp] theorem sumDeg_nil : sumDeg ([] : List (Block p N)) = 0 := rfl

@[simp] theorem sumDeg_cons (b : Block p N) (l : List (Block p N)) :
    sumDeg (b :: l) = b.deg + sumDeg l := rfl

@[simp] theorem imageSet_nil : imageSet ([] : List (Block p N)) = {1} := rfl

@[simp] theorem imageSet_cons (b : Block p N) (l : List (Block p N)) :
    imageSet (b :: l)
      = (fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
          (b.coset ×ˢ imageSet l) := rfl

/-- The empty image `{1}` sits in every cell around the empty center. -/
theorem imageSet_nil_subset_cell (k : ℕ) :
    imageSet ([] : List (Block p N)) ⊆ HenselCount.cell 1 0 k := by
  intro P hP
  rw [imageSet_nil, Set.mem_singleton_iff] at hP
  subst hP
  exact mem_cell_self monic_one natDegree_one k

/-- The empty image `{1}` is saturated at every level (a monic of degree 0 is `1`). -/
theorem imageSet_nil_saturated (m : ℕ) :
    Saturated (imageSet ([] : List (Block p N))) 0 m := by
  intro P hP Q hQmon hQdeg _
  rw [imageSet_nil, Set.mem_singleton_iff]
  exact hQmon.natDegree_eq_zero.mp hQdeg

/-- Resultant of the empty center: `Res(G, 1, d, 0) = 1 = p^0 · unit`. -/
theorem resultant_nil_center (G : (ZMod (p ^ N))[X]) (d : ℕ) :
    ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant G (prodCenter ([] : List (Block p N))) d (sumDeg ([] : List (Block p N)))
        = (p : ZMod (p ^ N)) ^ 0 * u := by
  refine ⟨1, ?_⟩
  rw [prodCenter_nil, sumDeg_nil, Polynomial.resultant_one_right]
  simp

/-- **Resultant of a product against the next block = product of resultants**, in `p^c·unit`
form: the accumulated `hres` supplier from pairwise data (mathlib `resultant_mul_right` plus
degree bookkeeping). -/
theorem resultant_mul_p_pow {m b₁ b₂ c₁ c₂ : ℕ} {F G₁ G₂ : (ZMod (p ^ N))[X]}
    (hF : F.natDegree ≤ m) (hG₁deg : G₁.natDegree = b₁) (hG₂deg : G₂.natDegree = b₂)
    (h₁ : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant F G₁ m b₁ = (p : ZMod (p ^ N)) ^ c₁ * u)
    (h₂ : ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant F G₂ m b₂ = (p : ZMod (p ^ N)) ^ c₂ * u) :
    ∃ u : (ZMod (p ^ N))ˣ,
      Polynomial.resultant F (G₁ * G₂) m (b₁ + b₂) = (p : ZMod (p ^ N)) ^ (c₁ + c₂) * u := by
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  refine ⟨u₁ * u₂, ?_⟩
  have h := Polynomial.resultant_mul_right F G₁ G₂ m hF
  rw [hG₁deg, hG₂deg] at h
  rw [h, hu₁, hu₂, pow_add, Units.val_mul]
  ring

/-- **The chain invariant** for the k-block fold: at each step the next block's coset and the
accumulated image are sub-cells of the `c+1`-cells around their centers, kernel-saturated at
`N - c`, with `Res(center, partial product) = p^c · unit` and the Hensel margin `2c < N`.
The saturation/containment fields for the accumulated image are dischargeable via
`mul_image_subset_cell` and `mul_image_saturated` (margin-permitting) or case-specific
arguments — they are constructor fields precisely because the uniform margins compound. -/
inductive GoodChain : List (Block p N) → ℕ → Prop
  | nil : GoodChain [] 0
  | cons {l : List (Block p N)} {X : ℕ} (b : Block p N) (c : ℕ)
      (hres : ∃ u : (ZMod (p ^ N))ˣ,
        Polynomial.resultant b.center (prodCenter l) b.deg (sumDeg l)
          = (p : ZMod (p ^ N)) ^ c * u)
      (hc : 2 * c < N)
      (hbsub : b.coset ⊆ HenselCount.cell b.center b.deg (c + 1))
      (hbsat : Saturated b.coset b.deg (N - c))
      (hlsub : imageSet l ⊆ HenselCount.cell (prodCenter l) (sumDeg l) (c + 1))
      (hlsat : Saturated (imageSet l) (sumDeg l) (N - c))
      (hchain : GoodChain l X) : GoodChain (b :: l) (c + X)

/-- **Deliverable 2 (`blocks_card`)**: the k-block product law
`card (image of Π_i P_i under multiplication) · p^X = Π_i card P_i`,
`X = Σ (chain resultant valuations)` — deliverable 1 folded along the chain. -/
theorem blocks_card {l : List (Block p N)} {X : ℕ} (h : GoodChain l X) :
    Nat.card (imageSet l) * p ^ X = (l.map fun b => Nat.card b.coset).prod := by
  induction h with
  | nil =>
    show Nat.card ({1} : Set ((ZMod (p ^ N))[X])) * p ^ 0 = _
    rw [Nat.card_unique, pow_zero, one_mul, List.map_nil, List.prod_nil]
  | @cons l' X' b c hres hc hbsub hbsat hlsub hlsat hchain ih =>
    have hpair := pair_card hres hc hbsub hbsat hlsub hlsat
    calc Nat.card (imageSet (b :: l')) * p ^ (c + X')
        = (Nat.card ((fun AB : (ZMod (p ^ N))[X] × (ZMod (p ^ N))[X] => AB.1 * AB.2) ''
            (b.coset ×ˢ imageSet l')) * p ^ c) * p ^ X' := by
          rw [imageSet_cons, pow_add, mul_assoc]
      _ = (Nat.card b.coset * Nat.card (imageSet l')) * p ^ X' := by rw [hpair]
      _ = Nat.card b.coset * (Nat.card (imageSet l') * p ^ X') := by ring
      _ = Nat.card b.coset * (l'.map fun b => Nat.card b.coset).prod := by rw [ih]
      _ = ((b :: l').map fun b => Nat.card b.coset).prod := by
          rw [List.map_cons, List.prod_cons]

/-! ## 5. Deliverable 3 — the margin question at the d2-0 gates

`2c < N` (and with it the whole flat sub-cell frame) **fails at all three gate cells**; the
numbers, pinned as ℕ-facts.  See the module docstring for the full analysis: the gate's
verified law needs the graded (per-slot) W4d2′ margin, not the flat one. -/

/-- Case A (p=2, N=5, c=X=4): the Hensel margin fails: `2·4 ≥ 5`. -/
theorem gate_margin_A : ¬ (2 * 4 < 5) := by norm_num

/-- Case B (p=3, N=3, c=X=2): the Hensel margin fails: `2·2 ≥ 3`. -/
theorem gate_margin_B : ¬ (2 * 2 < 3) := by norm_num

/-- Case C (p=3, N=4, c=X=4): the Hensel margin fails: `2·4 ≥ 4`. -/
theorem gate_margin_C : ¬ (2 * 4 < 4) := by norm_num

/-- Case B floor check: the pattern coset's x-adic constant-slot floor is `2` (from
`θ³`-membership: `p² ∣ b₀`, `p ∣ b₁`), which is neither `≥ c + 1 = 3` (containment in the
Hensel cell fails) nor `≤ N - c = 1` (kernel-saturation fails). -/
theorem gate_floor_B : ¬ (3 ≤ 2) ∧ ¬ (2 ≤ 3 - 2) := by norm_num

section CaseBHres

/-- `scaleRoots` of a monic linear polynomial. -/
theorem scaleRoots_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (a s : R) :
    (X - C a).scaleRoots s = X - C (a * s) := by
  ext i
  rw [Polynomial.coeff_scaleRoots, natDegree_X_sub_C]
  match i with
  | 0 => simp [mul_comm]
  | 1 => simp
  | (k + 2) =>
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    simp

/-- The order-1, `h = 1` restart key `φ = X^e − c̃·p` IS the sparse twist of its linear
residual `y − c̃` at slope `1/e` — the bridge from `RphiRing.phi`-shaped standard product
representatives to the `SparseResultant` `hres` suppliers. -/
theorem phi_eq_sparseTwist (e : ℕ) (c : (ZMod (p ^ N))ˣ) (hN : 0 < N) :
    RphiRing.phi p N e 1 c
      = SparseResultant.sparseTwist (p : ZMod (p ^ N)) (X - C (c : ZMod (p ^ N))) e 1 := by
  haveI := RphiRing.nontrivial_base p N hN
  rw [RphiRing.phi_eq, pow_one]
  unfold SparseResultant.sparseTwist
  rw [pow_one, scaleRoots_X_sub_C, map_sub, Polynomial.expand_X, Polynomial.expand_C]

/-- The case-B second center's residual root `c̃ = 2` as a unit of `ZMod 27`. -/
def cB₂ : (ZMod (3 ^ 3))ˣ := ⟨2, 14, by decide, by decide⟩

/-- **Deliverable 3 (`hres` discharge at the gate's case-B cell)** (p=3, N=3, s=4, slope
−1/2, decided blocks `(y−1)`, `(y−2)`): at the standard product representative
`φ₁ = X² − 3`, `φ₂ = X² − 6`, the resultant is exactly `p² · unit` — `c = 2` (`= X = m₁m₂w`,
matching the gate's torsor `9 = 3²`).  Note `2c = 4 ≥ N = 3`: this `hres` does NOT feed
`pair_card` at case B's parameters (`gate_margin_B`); the law there is proved by direct
enumeration below. -/
theorem caseB_hres :
    ∃ u : (ZMod (3 ^ 3))ˣ,
      Polynomial.resultant (RphiRing.phi 3 3 2 1 1) (RphiRing.phi 3 3 2 1 cB₂) 2 2
        = ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 * (u : ZMod (3 ^ 3)) := by
  haveI : Fact (1 < 3 ^ 3) := ⟨by norm_num⟩
  have hd₁ : (X - C ((1 : (ZMod (3 ^ 3))ˣ) : ZMod (3 ^ 3))).natDegree = 1 :=
    natDegree_X_sub_C _
  have hd₂ : (X - C (cB₂ : ZMod (3 ^ 3))).natDegree = 1 := natDegree_X_sub_C _
  have hunit : IsUnit (Polynomial.resultant (X - C ((1 : (ZMod (3 ^ 3))ˣ) : ZMod (3 ^ 3)))
      (X - C (cB₂ : ZMod (3 ^ 3))) 1 1) := by
    rw [Polynomial.resultant_X_sub_C_left _ _ _ (le_of_eq hd₂)]
    have : Polynomial.eval ((1 : (ZMod (3 ^ 3))ˣ) : ZMod (3 ^ 3))
        (X - C (cB₂ : ZMod (3 ^ 3))) = -1 := by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      decide
    rw [this]
    exact isUnit_one.neg
  have h := SparseResultant.resultant_sparseTwist_isUnit hd₁ hd₂ 2 1 hunit
  rw [← phi_eq_sparseTwist 2 1 (by norm_num), ← phi_eq_sparseTwist 2 cB₂ (by norm_num)] at h
  simpa using h

end CaseBHres

/-! ## 6. Deliverable 4 — gate cross-checks

Case B (p=3, N=3): the law `card(image) · p^X = Π card P_i` at the gate's own parameters
(`2c ≥ N`: outside the banked margin), by **direct exhaustive enumeration** at the tuple
encoding of the two decided-block cosets, `decide`-only.  Encoding: a monic quadratic
`x² + a₁x + a₀` over `ZMod 27` is the pair `(a₀, a₁)`; the coset of the decided block
`(e, μ, c̃) = (2, 1, c̃)` is `{(a₀, a₁) | 9 ∣ a₀ + 3c̃, 3 ∣ a₁}` (the x-adic reading of the
`FreshClusterPattern` slot `β₀ ∈ (θ)³` through `RestartEquiv`'s slot dictionary applied to
`f = φ + b₀`); the product map is the coefficient convolution of
`(x²+a₁x+a₀)(x²+b₁x+b₀)`. -/

section GateB

/-- Case-B tuple coset of the first decided block `(2, 1, c̃=1)`: `9 ∣ a₀+3`, `3 ∣ a₁`. -/
def gateB_P₁ : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  Finset.univ.filter fun q => (q.1 + 3).val % 9 = 0 ∧ q.2.val % 3 = 0

/-- Case-B tuple coset of the second decided block `(2, 1, c̃=2)`: `9 ∣ a₀+6`, `3 ∣ a₁`. -/
def gateB_P₂ : Finset (ZMod (3 ^ 3) × ZMod (3 ^ 3)) :=
  Finset.univ.filter fun q => (q.1 + 6).val % 9 = 0 ∧ q.2.val % 3 = 0

/-- Coefficients `(c₀, c₁, c₂, c₃)` of `(x²+a₁x+a₀)(x²+b₁x+b₀)`. -/
def gateB_mul : (ZMod (3 ^ 3) × ZMod (3 ^ 3)) × (ZMod (3 ^ 3) × ZMod (3 ^ 3)) →
    ZMod (3 ^ 3) × ZMod (3 ^ 3) × ZMod (3 ^ 3) × ZMod (3 ^ 3) := fun q =>
  (q.1.1 * q.2.1, q.1.1 * q.2.2 + q.1.2 * q.2.1, q.1.1 + q.2.1 + q.1.2 * q.2.2,
    q.1.2 + q.2.2)

/-- The val-conditions defining `gateB_P₁` are honest ring divisibilities. -/
theorem gateB_P₁_mem_iff (q : ZMod (3 ^ 3) × ZMod (3 ^ 3)) :
    q ∈ gateB_P₁
      ↔ ((3 : ℕ) : ZMod (3 ^ 3)) ^ 2 ∣ q.1 + 3 ∧ ((3 : ℕ) : ZMod (3 ^ 3)) ^ 1 ∣ q.2 := by
  rw [gateB_P₁, Finset.mem_filter]
  rw [RestartEquiv.pow_dvd_iff_dvd_val 3 3 (by norm_num) (q.1 + 3),
    RestartEquiv.pow_dvd_iff_dvd_val 3 3 (by norm_num) q.2]
  have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  rw [h9, h3, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  simp [Finset.mem_univ]

set_option maxRecDepth 10000 in
/-- Gate B, coset cards: `|P₁| = 27` (matches `card_freshPattern` at (3,3,2,1): `3^3`). -/
theorem gateB_card_P₁ : gateB_P₁.card = 27 := by decide

set_option maxRecDepth 10000 in
/-- Gate B, coset cards: `|P₂| = 27`. -/
theorem gateB_card_P₂ : gateB_P₂.card = 27 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- Gate B, fiber card: the image of the coset product under multiplication has `81`
points — the gate's `|fiber| = 81`. -/
theorem gateB_image_card : ((gateB_P₁ ×ˢ gateB_P₂).image gateB_mul).card = 81 := by decide

/-- **Gate B, THE LAW** at the gate's own parameters (outside the banked margin):
`card(image) · p^X = |P₁| · |P₂|`, i.e. `81 · 3² = 27 · 27`. -/
theorem gateB_law :
    ((gateB_P₁ ×ˢ gateB_P₂).image gateB_mul).card * 3 ^ 2
      = gateB_P₁.card * gateB_P₂.card := by
  rw [gateB_image_card, gateB_card_P₁, gateB_card_P₂]
  norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- Gate B, the torsor at the standard product representative `φ₁·φ₂ = (x²−3)(x²−6)`
(tuple `(18, 0, 18, 0)`): exactly `9 = 3² = p^X` factorizations — the gate's torsor
constant, pointwise at the center.  (Pointwise uniformity over ALL `81` image points was
verified exhaustively by the d2-0 gate; the all-points `decide` exceeds the kernel budget,
so in-file we pin the census law `gateB_law` plus this representative fiber.) -/
theorem gateB_torsor_repr :
    ((gateB_P₁ ×ˢ gateB_P₂).filter fun q => gateB_mul q = (18, 0, 18, 0)).card = 9 := by
  decide

/-- Gate B closed form cross-check: the pattern-coset card of a decided `(e, μ) = (2, 1)`
block at (p, N) = (3, 3) is `27 = 3^(1·(3·2−1) − 2·1·2/2)`, for ANY residual root `c̃` —
`card_freshPattern` agrees with the tuple-level enumeration. -/
theorem gateB_coset_closed_form (c : (ZMod (3 ^ 3))ˣ) :
    Nat.card {β : Fin 1 → RphiRing.Rphi 3 3 2 1 c //
        RestartEquiv.FreshClusterPattern 3 3 2 1 c β} = 27 := by
  rw [RestartEquiv.card_freshPattern 3 3 2 1 c (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end GateB

section GateAC

/-- **Gate A cross-check via the closed forms** (p=2, N=5, blocks (1,2,1)+(2,2,1)):
`Π_i |P_i| = 2^5 · 2^12 = 131072 = 8192 · 2^4 = |fiber| · p^X` — `card_freshPattern` per
block against the gate's fiber `8192` and torsor `X = 4`. -/
theorem gateA_coset_product :
    Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 1 1 1 //
        RestartEquiv.FreshClusterPattern 2 5 1 2 1 β}
      * Nat.card {β : Fin 2 → RphiRing.Rphi 2 5 2 1 1 //
          RestartEquiv.FreshClusterPattern 2 5 2 2 1 β}
      = 8192 * 2 ^ 4 := by
  rw [RestartEquiv.card_freshPattern 2 5 1 2 1 (by norm_num) (by norm_num) (by norm_num),
    RestartEquiv.card_freshPattern 2 5 2 2 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The case-C second block's residual root `c̃ = 2` as a unit of `ZMod 81`. -/
def cC₂ : (ZMod (3 ^ 4))ˣ := ⟨2, 41, by decide, by decide⟩

/-- **Gate C cross-check via the closed forms** (p=3, N=4, blocks (2,2,1) child +
(2,1,2) decided): `Π_i |P_i| = 3^8 · 3^5 = 3^13 = 19683 · 3^4 = |fiber| · p^X`. -/
theorem gateC_coset_product :
    Nat.card {β : Fin 2 → RphiRing.Rphi 3 4 2 1 1 //
        RestartEquiv.FreshClusterPattern 3 4 2 2 1 β}
      * Nat.card {β : Fin 1 → RphiRing.Rphi 3 4 2 1 cC₂ //
          RestartEquiv.FreshClusterPattern 3 4 2 1 cC₂ β}
      = 19683 * 3 ^ 4 := by
  rw [RestartEquiv.card_freshPattern 3 4 2 2 1 (by norm_num) (by norm_num) (by norm_num),
    RestartEquiv.card_freshPattern 3 4 2 1 cC₂ (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end GateAC

end LeanUrat.OM.BlockProduct

