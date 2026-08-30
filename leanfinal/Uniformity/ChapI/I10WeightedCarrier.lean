/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C136l2e4

/-!
# Uniformity.ChapI.I10WeightedCarrier — UNIT WCC: the weighted convolution carrier

The generic counterpart of the S2-pinned μ₄ convolution `C136l2e4.s2Mu4Coeff_mul` at the
bare own-height normalized carrier is REFUTED
(`C136l2e4.fixedGrade_unweighted_add_forces_letter_one`): the absolute fixed-grade read
weights each summand by a letter power `η^offset` that the normalized read drops, and
identifying the two forces `η = 1` — true only in the card-2 keystone frame.  This file
lands the repair at a GENERAL tower level:

* §1 `WeightedCarrier` — the abstract engine pack: a support grading `supp` (the
  dv-grading is the weight bookkeeping) together with an ABSOLUTE graded read `read`
  whose multiplicativity at exact grades (`read_mul`) is the cocycle-coherent carry law.
  The weights of the refutation live INSIDE `read`; no unweighted identification is ever
  made.  `CarrierKey` packages the next key: monic, pinned support grade `kgrade`, the
  ROOT RELATION `read kgrade key = 0` (in S2 this is `eval 1 (X+1) = 0` — the evaluation
  point is a root of the key's residual polynomial, not a char-2 accident), the `+1`
  strictness `ℓ·kgrade < u` (S2: `85 = 2·42 + 1`), and the two D3AD-interface support
  laws for `%ₘ key` and `/ₘ key`.
* §4 ★ `wcoeff_mul` — the general weighted convolution law, uniform in the frame and in
  `q`: the next-level coefficient family `wcoeff` (abscissa-indexed, carry-free form) is
  multiplicative under pointwise line floors only — no exactness hypothesis.
* §5 the keystone coherence pin: instantiating the carrier at the S2 tower's landed μ₃
  mirror (`supp := dv2Supp … 21 2`, `read := eval 1 ∘ s2Mu3GradedRes`, `key := g8`,
  `kgrade := 42`, `(u,ℓ) := (85,2)`) re-derives the landed `s2Mu4Coeff_mul` statement
  as a corollary (`s2Mu4Coeff_mul_via_carrier`).

Uniformity note: §§1–4 carry no `residueCard`, no keystone numeral, and no `LevelDatum`;
every hypothesis is a field of the pack.  The remaining `LevelSiteBank` legs (depth
adapter, key lifting, B-1 grades) are exactly the per-rung instantiation obligations of
these packs — see `runs/wave-c/verdict_WCC.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10wcc

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp5 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d3ad
open Uniformity.Density.Tower.C136l2e4
open Uniformity.Density.Tower.C80

/-! ## §1 — the weighted convolution carrier and its key pack -/

/-- ★ **The weighted convolution carrier**: a support grading together with an ABSOLUTE
graded read.  The refutation's letter weights live inside `read` (it is the fixed-grade
read, not the own-height normalized one), so `read_mul` at exact grades is the
cocycle-coherent carry law and no unweighted identification is made anywhere. -/
structure WeightedCarrier (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (K : Type*) [CommRing K] where
  /-- the support grading (the dv-grading of the level below). -/
  supp : Polynomial O → ℕ∞
  /-- the absolute graded read at a requested grade. -/
  read : ℕ → Polynomial O → K
  /-- the zero polynomial has top support. -/
  supp_zero : supp 0 = ⊤
  /-- the support grading is multiplicative (with `⊤` conventions). -/
  supp_mul : ∀ g z : Polynomial O, supp (g * z) = supp g + supp z
  /-- the ultrametric inequality for the support grading. -/
  min_supp_le_add : ∀ g z : Polynomial O, min (supp g) (supp z) ≤ supp (g + z)
  /-- the zero polynomial reads zero at every grade. -/
  read_zero : ∀ m : ℕ, read m 0 = 0
  /-- the graded read is additive at a common cleared floor. -/
  read_add : ∀ {m : ℕ} {g z : Polynomial O}, (m : ℕ∞) ≤ supp g → (m : ℕ∞) ≤ supp z →
    read m (g + z) = read m g + read m z
  /-- a read strictly below the support vanishes. -/
  read_above : ∀ {m : ℕ} {g : Polynomial O}, (m : ℕ∞) < supp g → read m g = 0
  /-- ★ the carry law: the absolute read is multiplicative at exact grades. -/
  read_mul : ∀ {m₁ m₂ : ℕ} {g z : Polynomial O}, supp g = (m₁ : ℕ∞) →
    supp z = (m₂ : ℕ∞) → read (m₁ + m₂) (g * z) = read m₁ g * read m₂ z

/-- ★ **The carrier key pack** for the next tower level: the new key with its pinned
support grade, the root relation `read_key` (the next letter is a root of the key's
residual polynomial), the `+1` strictness `ℓ·kgrade < u`, and the two D3AD-interface
support laws for reduction and quotient by the key on small-degree products. -/
structure CarrierKey {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type*} [CommRing K] (C : WeightedCarrier O K) (u ℓ : ℕ) where
  /-- the next-level key polynomial. -/
  key : Polynomial O
  /-- the key's exact support grade (S2 keystone: `42`). -/
  kgrade : ℕ
  monic : key.Monic
  deg_pos : 0 < key.natDegree
  supp_key : C.supp key = (kgrade : ℕ∞)
  /-- ★ the root relation: the key's own absolute read at its exact grade vanishes. -/
  read_key : C.read kgrade key = 0
  ell_pos : 0 < ℓ
  /-- ★ the `+1` strictness mechanism (S2 keystone: `2·42 < 85`). -/
  strict : ℓ * kgrade < u
  /-- reduction mod the key preserves the support of a small-degree product. -/
  supp_mod : ∀ {a b : Polynomial O}, a.natDegree < key.natDegree →
    b.natDegree < key.natDegree → C.supp ((a * b) %ₘ key) = C.supp a + C.supp b
  /-- the sharp quotient support bound for a small-degree product. -/
  supp_quot : ∀ {a b : Polynomial O}, a.natDegree < key.natDegree →
    b.natDegree < key.natDegree →
    C.supp a + C.supp b ≤ (kgrade : ℕ∞) + C.supp ((a * b) /ₘ key)

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [CommRing K]

/-- **The next-level coefficient family** on the weighted carrier, abscissa-indexed
(carry-free form): at grade `β` and abscissa `J`, the absolute graded read of the `J`-th
key-development coefficient at the on-line inner grade `(β − u·J)/ℓ`, gated by the line
guard; `0` off the line. -/
noncomputable def wcoeff (C : WeightedCarrier O K) {u ℓ : ℕ} (P : CarrierKey C u ℓ)
    (β : ℕ) (f : Polynomial O) (J : ℕ) : K :=
  if u * J ≤ β ∧ ℓ ∣ (β - u * J) then C.read ((β - u * J) / ℓ) (dev P.key f J) else 0

/-- **The line floor**: the grade-`β` line lies below the `key`-development polygon of
`f` — the pointwise (per-abscissa) form, the weakest input the convolution law needs. -/
def LineFloor (C : WeightedCarrier O K) {u ℓ : ℕ} (P : CarrierKey C u ℓ)
    (β : ℕ) (f : Polynomial O) : Prop :=
  ∀ j : ℕ, (β : ℕ∞) ≤ (ℓ : ℕ∞) * C.supp (dev P.key f j) + ((u * j : ℕ) : ℕ∞)

/-! ## §2 — cast and lattice-arithmetic helpers -/

private theorem coe_le_add_of_le {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) ≤ x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) ≤ x + y := by
  push_cast
  exact add_le_add hx hy

private theorem coe_lt_add_of_lt_of_le {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) < x) (hy : (b : ℕ∞) ≤ y) : ((a + b : ℕ) : ℕ∞) < x + y := by
  rcases eq_or_ne x ⊤ with rfl | hx'
  · rw [top_add]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hx'
  rcases eq_or_ne y ⊤ with rfl | hy'
  · rw [add_top]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self (a + b))) le_top
  obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.1 hy'
  rw [← hv] at hx ⊢
  rw [← hw] at hy ⊢
  have h1 : a < v := by exact_mod_cast hx
  have h2 : b ≤ w := by exact_mod_cast hy
  calc
    ((a + b : ℕ) : ℕ∞) < ((v + w : ℕ) : ℕ∞) := Nat.cast_lt.mpr (by omega)
    _ = (v : ℕ∞) + (w : ℕ∞) := by push_cast; rfl

private theorem coe_lt_add_of_le_of_lt {a b : ℕ} {x y : ℕ∞}
    (hx : (a : ℕ∞) ≤ x) (hy : (b : ℕ∞) < y) : ((a + b : ℕ) : ℕ∞) < x + y := by
  rw [Nat.add_comm a b, add_comm x y]
  exact coe_lt_add_of_lt_of_le hy hx

/-- ceiling step: a non-divisible line value forces one full lattice step above the
truncated quotient. -/
private theorem succ_div_le {ℓ x c : ℕ} (hx : x ≤ ℓ * c) (hnd : ¬ ℓ ∣ x) :
    x / ℓ + 1 ≤ c := by
  have hmod : x % ℓ ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hdm : ℓ * (x / ℓ) + x % ℓ = x := Nat.div_add_mod x ℓ
  have hlt : ℓ * (x / ℓ) < ℓ * c := by omega
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

/-- the on-lattice main floor: any antidiagonal pair of line floors clears the product
lattice grade. -/
private theorem main_floor {u ℓ m J j A B β β' : ℕ} (hℓ : 0 < ℓ) (hj : j ≤ J)
    (hm : ℓ * m + u * J = β + β')
    (ha : β ≤ ℓ * A + u * j) (hb : β' ≤ ℓ * B + u * (J - j)) :
    m ≤ A + B := by
  have hxy : u * j + u * (J - j) = u * J := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  have h2 : ℓ * m ≤ ℓ * (A + B) := by rw [Nat.mul_add]; omega
  exact Nat.le_of_mul_le_mul_left h2 hℓ

/-- the lattice split: when both factor guards hold on an antidiagonal pair, the two
inner grades add exactly to the product's inner grade. -/
private theorem lattice_split {u ℓ m J j β β' : ℕ} (hℓ : 0 < ℓ) (hj : j ≤ J)
    (hm : ℓ * m + u * J = β + β')
    (hgj : u * j ≤ β) (hdj : ℓ ∣ (β - u * j))
    (hgz : u * (J - j) ≤ β') (hdz : ℓ ∣ (β' - u * (J - j))) :
    (β - u * j) / ℓ + (β' - u * (J - j)) / ℓ = m := by
  obtain ⟨k₁, hk₁⟩ := hdj
  obtain ⟨k₂, hk₂⟩ := hdz
  have hxy : u * j + u * (J - j) = u * J := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  rw [hk₁, hk₂, Nat.mul_div_cancel_left _ hℓ, Nat.mul_div_cancel_left _ hℓ]
  have hsum : ℓ * (k₁ + k₂) = ℓ * m := by rw [Nat.mul_add]; omega
  exact Nat.eq_of_mul_eq_mul_left hℓ hsum

/-- guard addition: two on-line factor guards produce the product guard. -/
private theorem guard_add {u ℓ J j β β' : ℕ} (hj : j ≤ J)
    (hgj : u * j ≤ β) (hdj : ℓ ∣ (β - u * j))
    (hgz : u * (J - j) ≤ β') (hdz : ℓ ∣ (β' - u * (J - j))) :
    u * J ≤ β + β' ∧ ℓ ∣ (β + β' - u * J) := by
  have hxy : u * j + u * (J - j) = u * J := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  refine ⟨by omega, ?_⟩
  have hsplit : β + β' - u * J = (β - u * j) + (β' - u * (J - j)) := by omega
  rw [hsplit]
  exact Nat.dvd_add hdj hdz

/-- the strict off-lattice kill: a pair failing either factor guard prices strictly
above the product lattice grade. -/
private theorem offlattice_strict {u ℓ m J j A B β β' : ℕ} (hℓ : 0 < ℓ) (hj : j ≤ J)
    (hm : ℓ * m + u * J = β + β')
    (ha : β ≤ ℓ * A + u * j) (hb : β' ≤ ℓ * B + u * (J - j))
    (hbad : ¬ ((u * j ≤ β ∧ ℓ ∣ (β - u * j))
      ∧ (u * (J - j) ≤ β' ∧ ℓ ∣ (β' - u * (J - j))))) :
    m + 1 ≤ A + B := by
  have hxy : u * j + u * (J - j) = u * J := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj]
  by_cases hga : u * j ≤ β
  · by_cases hgb : u * (J - j) ≤ β'
    · -- both range guards hold; a divisibility guard fails, hence BOTH fail.
      have hx' : β - u * j ≤ ℓ * A := by omega
      have hy' : β' - u * (J - j) ≤ ℓ * B := by omega
      have hsum : (β - u * j) + (β' - u * (J - j)) = ℓ * m := by omega
      have hdd : ℓ ∣ ((β - u * j) + (β' - u * (J - j))) := by
        rw [hsum]; exact Nat.dvd_mul_right ℓ m
      have hndj : ¬ ℓ ∣ (β - u * j) := by
        intro hdj
        exact hbad ⟨⟨hga, hdj⟩, ⟨hgb, (Nat.dvd_add_iff_right hdj).mpr hdd⟩⟩
      have hndz : ¬ ℓ ∣ (β' - u * (J - j)) := by
        intro hdz
        exact hndj ((Nat.dvd_add_iff_right hdz).mpr (by rwa [Nat.add_comm] at hdd))
      have hA := succ_div_le hx' hndj
      have hB := succ_div_le hy' hndz
      have hdmx : ℓ * ((β - u * j) / ℓ) + (β - u * j) % ℓ = β - u * j :=
        Nat.div_add_mod _ ℓ
      have hdmy : ℓ * ((β' - u * (J - j)) / ℓ) + (β' - u * (J - j)) % ℓ
          = β' - u * (J - j) := Nat.div_add_mod _ ℓ
      have hrx : (β - u * j) % ℓ ≠ 0 := fun h => hndj (Nat.dvd_of_mod_eq_zero h)
      have hry : (β' - u * (J - j)) % ℓ ≠ 0 := fun h => hndz (Nat.dvd_of_mod_eq_zero h)
      have hrxlt : (β - u * j) % ℓ < ℓ := Nat.mod_lt _ hℓ
      have hrylt : (β' - u * (J - j)) % ℓ < ℓ := Nat.mod_lt _ hℓ
      -- the two mods sum to a positive multiple of ℓ below 2ℓ, hence exactly ℓ
      have hd : ℓ ∣ ((β - u * j) % ℓ + (β' - u * (J - j)) % ℓ) := by
        have hq : ℓ ∣ (ℓ * ((β - u * j) / ℓ) + ℓ * ((β' - u * (J - j)) / ℓ)) :=
          Nat.dvd_add (Nat.dvd_mul_right ℓ _) (Nat.dvd_mul_right ℓ _)
        have h3 : ℓ ∣ ((β - u * j) % ℓ + (β' - u * (J - j)) % ℓ
            + (ℓ * ((β - u * j) / ℓ) + ℓ * ((β' - u * (J - j)) / ℓ))) := by
          have h4 : (β - u * j) % ℓ + (β' - u * (J - j)) % ℓ
              + (ℓ * ((β - u * j) / ℓ) + ℓ * ((β' - u * (J - j)) / ℓ))
              = ℓ * m := by omega
          rw [h4]; exact Nat.dvd_mul_right ℓ m
        exact (Nat.dvd_add_iff_left hq).mpr h3
      obtain ⟨w, hw⟩ := hd
      have hw1 : w = 1 := by
        rcases Nat.eq_zero_or_pos w with rfl | hpos
        · rw [Nat.mul_zero] at hw
          omega
        · by_contra hne
          have hge : 2 ≤ w := by omega
          have h2w : ℓ * 2 ≤ ℓ * w := Nat.mul_le_mul_left ℓ hge
          have hll : ℓ * 2 = ℓ + ℓ := by ring
          omega
      rw [hw1, Nat.mul_one] at hw
      have hfin : ℓ * ((β - u * j) / ℓ + (β' - u * (J - j)) / ℓ + 1) = ℓ * m := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega
      have := Nat.eq_of_mul_eq_mul_left hℓ hfin
      omega
    · -- z-side range overshoot: the g-side alone prices strictly above the grade
      have h5 : ℓ * m < ℓ * A := by omega
      have := Nat.lt_of_mul_lt_mul_left h5
      omega
  · -- g-side range overshoot: the z-side alone prices strictly above the grade
    have h5 : ℓ * m < ℓ * B := by omega
    have := Nat.lt_of_mul_lt_mul_left h5
    omega

/-- the strict carry kill: a carry-diagonal pair prices `kgrade` clear of the strict
floor — the `+1` mechanism `ℓ·s < u`. -/
private theorem carry_strict {u ℓ s m J j A B β β' : ℕ}
    (hstrict : ℓ * s < u) (hj : j + 1 ≤ J)
    (hm : ℓ * m + u * J = β + β')
    (ha : β ≤ ℓ * A + u * j) (hb : β' ≤ ℓ * B + u * (J - 1 - j)) :
    m + 1 + s ≤ A + B := by
  have hj' : j ≤ J - 1 := by omega
  have hxy : u * j + u * (J - 1 - j) = u * (J - 1) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hj']
  have hJ1 : u * (J - 1) + u = u * J := by
    have h6 : u * (J - 1) + u * 1 = u * J := by rw [← Nat.mul_add]; congr 1; omega
    simpa using h6
  have h1 : ℓ * (m + s) < ℓ * (A + B) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have := Nat.lt_of_mul_lt_mul_left h1
  omega

/-! ## §3 — derived carrier laws -/

variable (C : WeightedCarrier O K)

/-- the support floor passes to finite sums (ultrametric induction). -/
theorem le_supp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Polynomial O) {k : ℕ∞}
    (hf : ∀ i ∈ s, k ≤ C.supp (f i)) : k ≤ C.supp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, C.supp_zero]
      exact le_top
  | cons a t hat ih =>
      rw [Finset.sum_cons]
      exact le_trans (le_min (hf a (Finset.mem_cons_self a t))
          (ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))))
        (C.min_supp_le_add _ _)

/-- the graded read is additive over finite sums at a common cleared floor. -/
theorem read_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Polynomial O) {m : ℕ}
    (hf : ∀ i ∈ s, (m : ℕ∞) ≤ C.supp (f i)) :
    C.read m (∑ i ∈ s, f i) = ∑ i ∈ s, C.read m (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact C.read_zero m
  | cons a t hat ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        C.read_add (hf a (Finset.mem_cons_self a t))
          (le_supp_finsetSum C t f fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
        ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

/-- the carry law at floors: strict cases degenerate to `0 = 0`. -/
theorem read_mul_of_le {m₁ m₂ : ℕ} {g z : Polynomial O}
    (hg : (m₁ : ℕ∞) ≤ C.supp g) (hz : (m₂ : ℕ∞) ≤ C.supp z) :
    C.read (m₁ + m₂) (g * z) = C.read m₁ g * C.read m₂ z := by
  rcases lt_or_eq_of_le hg with hglt | hgeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < C.supp (g * z) := by
      rw [C.supp_mul]
      exact coe_lt_add_of_lt_of_le hglt hz
    rw [C.read_above habove, C.read_above hglt, zero_mul]
  rcases lt_or_eq_of_le hz with hzlt | hzeq
  · have habove : ((m₁ + m₂ : ℕ) : ℕ∞) < C.supp (g * z) := by
      rw [C.supp_mul]
      exact coe_lt_add_of_le_of_lt hg hzlt
    rw [C.read_above habove, C.read_above hzlt, mul_zero]
  · exact C.read_mul hgeq.symm hzeq.symm

variable {u ℓ : ℕ} (P : CarrierKey C u ℓ)

/-- the seam kill: every multiple of the key reads zero at any cleared grade — the
abstract form of the root relation. -/
theorem read_key_mul {m : ℕ} (Q : Polynomial O)
    (hm : (m : ℕ∞) ≤ C.supp (P.key * Q)) : C.read m (P.key * Q) = 0 := by
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact C.read_above hlt
  · have hsupp : C.supp (P.key * Q) = (m : ℕ∞) := heq.symm
    rw [C.supp_mul, P.supp_key] at hsupp
    have hQne : C.supp Q ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hsupp
      exact (by simp : (⊤ : ℕ∞) ≠ (m : ℕ∞)) hsupp
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hQne
    rw [← hc] at hsupp
    have hmc : P.kgrade + c = m := by exact_mod_cast hsupp
    rw [← hmc, C.read_mul P.supp_key hc.symm, P.read_key, zero_mul]

/-- reduction mod the key is invisible to the graded read of a small-degree product at
a cleared floor. -/
theorem read_mul_modByKey {m : ℕ} {a b : Polynomial O}
    (ha : a.natDegree < P.key.natDegree) (hb : b.natDegree < P.key.natDegree)
    (hm : (m : ℕ∞) ≤ C.supp a + C.supp b) :
    C.read m ((a * b) %ₘ P.key) = C.read m (a * b) := by
  have hmodfloor : (m : ℕ∞) ≤ C.supp ((a * b) %ₘ P.key) := by
    rw [P.supp_mod ha hb]; exact hm
  have hquotfloor : (m : ℕ∞) ≤ C.supp (P.key * ((a * b) /ₘ P.key)) := by
    rw [C.supp_mul, P.supp_key]
    exact le_trans hm (P.supp_quot ha hb)
  conv_rhs => rw [← Polynomial.modByMonic_add_div (a * b) P.key]
  rw [C.read_add hmodfloor hquotfloor, read_key_mul C P _ hquotfloor, add_zero]

/-- every key-development coefficient has degree below the key. -/
private theorem natDegree_dev_lt (f : Polynomial O) (j : ℕ) :
    (dev P.key f j).natDegree < P.key.natDegree := by
  rcases eq_or_ne (dev P.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    exact P.deg_pos
  · exact Polynomial.natDegree_lt_natDegree h0 (degree_dev_lt P.monic P.deg_pos f j)

/-- the quotient of a small-degree product by the key stays small. -/
private theorem natDegree_quot_lt {a b : Polynomial O}
    (ha : a.natDegree < P.key.natDegree) (hb : b.natDegree < P.key.natDegree) :
    ((a * b) /ₘ P.key).natDegree < P.key.natDegree := by
  rw [Polynomial.natDegree_divByMonic _ P.monic]
  have h := Polynomial.natDegree_mul_le (p := a) (q := b)
  omega

/-- the first development coefficient of a small-degree product is its key quotient. -/
private theorem dev_key_mul_one {a b : Polynomial O}
    (ha : a.natDegree < P.key.natDegree) (hb : b.natDegree < P.key.natDegree) :
    dev P.key (a * b) 1 = (a * b) /ₘ P.key := by
  have hunfold : dev P.key (a * b) 1 = dev P.key ((a * b) /ₘ P.key) 0 := rfl
  rw [hunfold, dev_zero_pin]
  rcases eq_or_ne ((a * b) /ₘ P.key) 0 with h0 | h0
  · rw [h0, Polynomial.zero_modByMonic]
  · exact (Polynomial.modByMonic_eq_self_iff P.monic).mpr
      (by rw [Polynomial.degree_eq_natDegree h0,
            Polynomial.degree_eq_natDegree P.monic.ne_zero]
          exact_mod_cast natDegree_quot_lt C P ha hb)

/-! ## §4 — ★ the general weighted convolution law -/

/-- a line floor reads in `ℕ` at any abscissa with finite support value. -/
private theorem lineFloor_nat {β : ℕ} {f : Polynomial O} (hf : LineFloor C P β f)
    {j A : ℕ} (hA : C.supp (dev P.key f j) = (A : ℕ∞)) : β ≤ ℓ * A + u * j := by
  have h := hf j
  rw [hA] at h
  exact_mod_cast h

/-- `ℕ∞` cancellation of a finite left summand. -/
private theorem le_of_add_coe_le {a s : ℕ} {x : ℕ∞}
    (h : ((a + s : ℕ) : ℕ∞) ≤ (s : ℕ∞) + x) : (a : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  have h1 : a + s ≤ s + c := by exact_mod_cast h
  exact_mod_cast (by omega : a ≤ c)

/-- the antidiagonal main floor in `ℕ∞`. -/
private theorem pair_supp_floor {β β' m : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) {J j : ℕ} (hj : j ≤ J)
    (hm : ℓ * m + u * J = β + β') :
    (m : ℕ∞) ≤ C.supp (dev P.key g j) + C.supp (dev P.key z (J - j)) := by
  rcases eq_or_ne (C.supp (dev P.key g j)) ⊤ with hT | hT
  · rw [hT, top_add]; exact le_top
  rcases eq_or_ne (C.supp (dev P.key z (J - j))) ⊤ with hT' | hT'
  · rw [hT', add_top]; exact le_top
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hT'
  rw [← hA, ← hB]
  exact_mod_cast main_floor P.ell_pos hj hm (lineFloor_nat C P hg hA.symm)
    (lineFloor_nat C P hz hB.symm)

/-- the strict off-lattice kill in `ℕ∞`. -/
private theorem pair_supp_strict {β β' m : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) {J j : ℕ} (hj : j ≤ J)
    (hm : ℓ * m + u * J = β + β')
    (hbad : ¬ ((u * j ≤ β ∧ ℓ ∣ (β - u * j))
      ∧ (u * (J - j) ≤ β' ∧ ℓ ∣ (β' - u * (J - j))))) :
    (m : ℕ∞) < C.supp (dev P.key g j) + C.supp (dev P.key z (J - j)) := by
  rcases eq_or_ne (C.supp (dev P.key g j)) ⊤ with hT | hT
  · rw [hT, top_add]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) le_top
  rcases eq_or_ne (C.supp (dev P.key z (J - j))) ⊤ with hT' | hT'
  · rw [hT', add_top]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) le_top
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hT'
  rw [← hA, ← hB]
  have h := offlattice_strict P.ell_pos hj hm (lineFloor_nat C P hg hA.symm)
    (lineFloor_nat C P hz hB.symm) hbad
  exact_mod_cast (by omega : m < A + B)

/-- the strict carry floor in `ℕ∞`: every carry-diagonal term clears `m + 1`. -/
private theorem carry_supp_floor {β β' m : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) {J j : ℕ} (hj : j + 1 ≤ J)
    (hm : ℓ * m + u * J = β + β') :
    ((m + 1 : ℕ) : ℕ∞)
      ≤ C.supp (dev P.key (dev P.key g j * dev P.key z (J - 1 - j)) 1) := by
  rw [dev_key_mul_one C P (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - 1 - j))]
  have hpair : ((m + 1 + P.kgrade : ℕ) : ℕ∞)
      ≤ C.supp (dev P.key g j) + C.supp (dev P.key z (J - 1 - j)) := by
    rcases eq_or_ne (C.supp (dev P.key g j)) ⊤ with hT | hT
    · rw [hT, top_add]; exact le_top
    rcases eq_or_ne (C.supp (dev P.key z (J - 1 - j))) ⊤ with hT' | hT'
    · rw [hT', add_top]; exact le_top
    obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
    obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hT'
    rw [← hA, ← hB]
    have h := carry_strict P.strict hj hm (lineFloor_nat C P hg hA.symm)
      (lineFloor_nat C P hz hB.symm)
    exact_mod_cast (by omega : m + 1 + P.kgrade ≤ A + B)
  exact le_of_add_coe_le (le_trans hpair (P.supp_quot (natDegree_dev_lt C P g j)
    (natDegree_dev_lt C P z (J - 1 - j))))

/-- the on-guard unfolding of `wcoeff`. -/
private theorem wcoeff_of_guard {β J : ℕ} {f : Polynomial O}
    (h1 : u * J ≤ β) (h2 : ℓ ∣ (β - u * J)) :
    wcoeff C P β f J = C.read ((β - u * J) / ℓ) (dev P.key f J) := if_pos ⟨h1, h2⟩

/-- the off-guard vanishing of `wcoeff`. -/
private theorem wcoeff_of_not_guard {β J : ℕ} {f : Polynomial O}
    (h : ¬ (u * J ≤ β ∧ ℓ ∣ (β - u * J))) : wcoeff C P β f J = 0 := if_neg h

/-- the factor grade floor at an on-guard slot. -/
private theorem wcoeff_grade_floor {β : ℕ} {f : Polynomial O} (hf : LineFloor C P β f)
    {j : ℕ} (h2 : ℓ ∣ (β - u * j)) :
    (((β - u * j) / ℓ : ℕ) : ℕ∞) ≤ C.supp (dev P.key f j) := by
  rcases eq_or_ne (C.supp (dev P.key f j)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hA]
  have hnat := lineFloor_nat C P hf hA.symm
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left _ P.ell_pos]
  have hkA : ℓ * k ≤ ℓ * A := by omega
  exact_mod_cast Nat.le_of_mul_le_mul_left hkA P.ell_pos

/-- ★★ **The weighted convolution law at a general tower level** (the generic repair of
the refuted unweighted `hconv`, uniform in the frame and in `q`): under pointwise line
floors alone — no exactness — the next-level coefficient family is multiplicative, with
the carry diagonal and every off-lattice term killed by the `+1` strictness pricing. -/
theorem wcoeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : LineFloor C P β g) (hz : LineFloor C P β' z) (J : ℕ) :
    wcoeff C P (β + β') (g * z) J
      = ∑ j ∈ Finset.range (J + 1), wcoeff C P β g j * wcoeff C P β' z (J - j) := by
  by_cases hguard : u * J ≤ β + β' ∧ ℓ ∣ (β + β' - u * J)
  · obtain ⟨hle, hdvd⟩ := hguard
    obtain ⟨m, hmdiv⟩ := hdvd
    have hmw : ℓ * m + u * J = β + β' := by omega
    have hdivm : (β + β' - u * J) / ℓ = m := by
      rw [hmdiv, Nat.mul_div_cancel_left _ P.ell_pos]
    have hLHS : wcoeff C P (β + β') (g * z) J = C.read m (dev P.key (g * z) J) := by
      rw [wcoeff_of_guard C P hle ⟨m, hmdiv⟩, hdivm]
    rw [hLHS, dev_mul_conv_split_monic P.monic P.deg_pos g z J]
    have hmainfloor : ∀ j ∈ Finset.range (J + 1),
        (m : ℕ∞) ≤ C.supp ((dev P.key g j * dev P.key z (J - j)) %ₘ P.key) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [P.supp_mod (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - j))]
      exact pair_supp_floor C P hg hz (by omega) hmw
    have hcarryfloor : ∀ j ∈ Finset.range J,
        ((m + 1 : ℕ) : ℕ∞)
          ≤ C.supp (dev P.key (dev P.key g j * dev P.key z (J - 1 - j)) 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      exact carry_supp_floor C P hg hz (by omega) hmw
    rw [C.read_add (le_supp_finsetSum C _ _ hmainfloor)
        (le_supp_finsetSum C _ _ fun j hj =>
          le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      read_finsetSum C _ _ hmainfloor,
      read_finsetSum C _ _ (fun j hj =>
        le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj))]
    have hcarryzero : (∑ j ∈ Finset.range J,
        C.read m (dev P.key (dev P.key g j * dev P.key z (J - 1 - j)) 1)) = 0 :=
      Finset.sum_eq_zero fun j hj => C.read_above
        (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) (hcarryfloor j hj))
    rw [hcarryzero, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hjJ : j ≤ J := by omega
    by_cases hgood : (u * j ≤ β ∧ ℓ ∣ (β - u * j))
        ∧ (u * (J - j) ≤ β' ∧ ℓ ∣ (β' - u * (J - j)))
    · obtain ⟨⟨hg1, hg2⟩, ⟨hz1, hz2⟩⟩ := hgood
      rw [wcoeff_of_guard C P hg1 hg2, wcoeff_of_guard C P hz1 hz2,
        read_mul_modByKey C P (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - j))
          (pair_supp_floor C P hg hz hjJ hmw),
        ← lattice_split P.ell_pos hjJ hmw hg1 hg2 hz1 hz2]
      exact read_mul_of_le C (wcoeff_grade_floor C P hg hg2) (wcoeff_grade_floor C P hz hz2)
    · have hzero : C.read m ((dev P.key g j * dev P.key z (J - j)) %ₘ P.key) = 0 := by
        refine C.read_above ?_
        rw [P.supp_mod (natDegree_dev_lt C P g j) (natDegree_dev_lt C P z (J - j))]
        exact pair_supp_strict C P hg hz hjJ hmw hgood
      rw [hzero]
      rcases not_and_or.mp hgood with hbad | hbad
      · rw [wcoeff_of_not_guard C P hbad, zero_mul]
      · rw [wcoeff_of_not_guard C P hbad, mul_zero]
  · rw [wcoeff_of_not_guard C P hguard]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    by_cases hgj : u * j ≤ β ∧ ℓ ∣ (β - u * j)
    · by_cases hgz : u * (J - j) ≤ β' ∧ ℓ ∣ (β' - u * (J - j))
      · exact absurd (guard_add (by omega) hgj.1 hgj.2 hgz.1 hgz.2) hguard
      · rw [wcoeff_of_not_guard C P hgz, mul_zero]
    · rw [wcoeff_of_not_guard C P hgj, zero_mul]

end Carrier

/-! ## §5 — the S2 keystone coherence pin -/

section S2Pin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

private theorem s2_supp_mul_local {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  obtain ⟨Hg, hHg⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) g 21 2
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hg)
  obtain ⟨Hz, hHz⟩ := exists_dv2SideMin_height ((s2Tower h2 hq).levelDatum h2) z 21 2
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hz)
  exact C132nv4.s2_dv2Supp_mul_at_21 h2 hq
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hg)
    (C132nv6.s2_dv2SideSet_nonempty_at_21 h2 hq hz) hHg hHz

private theorem s2_supp_mul_all (g z : Polynomial O) :
    dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) (g * z) 21 2
      = dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) g 21 2
        + dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) z 21 2 := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num), top_add]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num), add_top]
  exact s2_supp_mul_local h2 hq hg hz

/-- ★ **the S2 keystone carrier**: the landed μ₃ mirror as a `WeightedCarrier` — every
field is a landed S2 lemma. -/
noncomputable def s2Carrier : WeightedCarrier O ((s2DepthTwo h2 hq).fld 2) where
  supp f := dv2Supp ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) f 21 2
  read m f := Polynomial.eval (1 : (s2DepthTwo h2 hq).fld 2) (s2Mu3GradedRes h2 hq m f)
  supp_zero := dv2Supp_zero_eq_top ((s2Tower h2 hq).levelDatum h2)
    (s2DepthTwoKeyAt h2 hq 2) 21 (by norm_num)
  supp_mul := s2_supp_mul_all h2 hq
  min_supp_le_add g z := min_dv2Supp_le_dv2Supp_add ((s2Tower h2 hq).levelDatum h2)
    (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num) g z
  read_zero m := by rw [s2Mu3GradedRes_zero h2 hq m, Polynomial.eval_zero]
  read_add := fun hga hzb => by
    rw [C132rp3.s2Mu3GradedRes_add_of_le h2 hq hga hzb, Polynomial.eval_add]
  read_above := fun h => by
    rw [s2Mu3GradedRes_zero_of_above h2 hq
      ((S2Mu3AboveGrade_iff_dv2Supp h2 hq).mpr h), Polynomial.eval_zero]
  read_mul := fun h1 h2' => eval_one_mu3GradedRes_mul_of_exact h2 hq
    ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr h1)
    ((S2Mu3ExactGrade_iff_dv2Supp h2 hq).mpr h2')

/-- ★ **the S2 keystone key pack**: `g8` at grade `42`, slopes `(85,2)` — every field a
landed S2 lemma; the root relation is `eval 1 (X+1) = 0` in char 2. -/
noncomputable def s2Key : CarrierKey (s2Carrier h2 hq) 85 2 where
  key := g8 h2 hq
  kgrade := 42
  monic := s2g8_monic h2 hq
  deg_pos := by rw [s2g8_natDegree h2 hq]; norm_num
  supp_key := s2_dv2Supp_g8 h2 hq
  read_key := by
    have h := eval_one_mu3GradedRes_g8_mul h2 hq (m := 42) 1
      (by rw [mul_one]; exact le_of_eq (s2_dv2Supp_g8 h2 hq).symm)
    rwa [mul_one] at h
  ell_pos := by norm_num
  strict := by norm_num
  supp_mod := fun ha hb =>
    C136d3ad.dv2Supp_mul_modByKey_eq ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
      (fun _ _ hg' hz' => s2_supp_mul_local h2 hq hg' hz')
      (s2_isMu3Key_g8 h2 hq) ha hb
  supp_quot := fun ha hb => by
    have h := C136d3ad.dv2Supp_add_le_key_quot_add ((s2Tower h2 hq).levelDatum h2)
      (s2Φ₂_monic h2 hq) (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
      (fun _ _ hg' hz' => s2_supp_mul_local h2 hq hg' hz')
      (s2_isMu3Key_g8 h2 hq) ha hb
    rwa [s2_dv2Supp_g8 h2 hq] at h

/-- the S2 line floor from a μ₄ exact grade, via the landed `dv3Supp` term bound. -/
private theorem s2_lineFloor {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) :
    LineFloor (s2Carrier h2 hq) (s2Key h2 hq) β g := by
  intro j
  have hβ : (β : ℕ∞) ≤ dv3Supp ((s2Tower h2 hq).levelDatum h2)
      (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) g 85 2 :=
    le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg).symm
  have hterm := hβ.trans (C136d0.dv3Supp_le_term ((s2Tower h2 hq).levelDatum h2)
    (s2g8_monic h2 hq) (by rw [s2g8_natDegree h2 hq]; norm_num) 21
    (by norm_num) g 85 (by norm_num) j)
  rw [dv3Pin, dv3Hgt, nsmul_eq_mul] at hterm
  exact_mod_cast hterm

/-- the keystone dictionary: the landed μ₄ coefficient IS the carrier coefficient at the
parity abscissa. -/
private theorem s2Mu4Coeff_eq_wcoeff {β : ℕ} {g : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (t : ℕ) :
    s2Mu4Coeff h2 hq β g t
      = wcoeff (s2Carrier h2 hq) (s2Key h2 hq) β g (β % 2 + 2 * t) := by
  rcases Nat.lt_or_ge β (85 * (β % 2 + 2 * t)) with hlt | hge
  · rw [s2Mu4Coeff_eq_zero_of_grade_lt h2 hq hlt,
      wcoeff_of_not_guard _ _ (by omega)]
  · have hdvd : 2 ∣ (β - 85 * (β % 2 + 2 * t)) := by omega
    have hm2 : 2 * ((β - 85 * (β % 2 + 2 * t)) / 2) + 85 * (β % 2 + 2 * t) = β := by
      omega
    have hpin : (((β - 85 * (β % 2 + 2 * t)) / 2 : ℕ) : ℕ∞)
        ≤ dv3Pin ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2
          (g8 h2 hq) g (β % 2 + 2 * t) :=
      le_dv3Pin_of_le_dv3Supp h2 hq (by norm_num)
        (le_of_eq ((S2Mu4ExactGrade_iff_dv3Supp h2 hq).mp hg).symm) hm2
    rw [s2Mu4Coeff_eq_eval_of_le h2 hq hm2 hpin, wcoeff_of_guard _ _ hge hdvd]
    rfl

/-- ★★ **the keystone coherence pin**: the landed D3-10 statement
(`C136l2e4.s2Mu4Coeff_mul`, conclusion byte-identical) re-derived as a corollary of the
general weighted convolution law `wcoeff_mul`. -/
theorem s2Mu4Coeff_mul_via_carrier {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu4Coeff h2 hq (β + β') (g * z) (T + s2Mu4Carry β β')
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu4Coeff h2 hq β g t * s2Mu4Coeff h2 hq β' z (T - t) := by
  classical
  have hpar := s2Mu4Carry_parity β β'
  have hgz := S2Mu4ExactGrade_mul h2 hq hg hz
  rw [s2Mu4Coeff_eq_wcoeff h2 hq hgz (T + s2Mu4Carry β β'),
    wcoeff_mul _ _ (s2_lineFloor h2 hq hg) (s2_lineFloor h2 hq hz)]
  have hoff : ∀ j ∈ Finset.range ((β + β') % 2 + 2 * (T + s2Mu4Carry β β') + 1),
      wcoeff (s2Carrier h2 hq) (s2Key h2 hq) β g j
          * wcoeff (s2Carrier h2 hq) (s2Key h2 hq) β' z
            ((β + β') % 2 + 2 * (T + s2Mu4Carry β β') - j) ≠ 0 →
      j % 2 = β % 2 := by
    intro j hj hne
    by_contra hpar2
    exact hne (by rw [wcoeff_of_not_guard _ _ (by omega), zero_mul])
  rw [← Finset.sum_filter_of_ne hoff]
  have himg : (Finset.range ((β + β') % 2 + 2 * (T + s2Mu4Carry β β') + 1)).filter
      (fun j => j % 2 = β % 2)
      = (Finset.range (T + 1)).image (fun t => β % 2 + 2 * t) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hpar2⟩
      exact ⟨j / 2, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun a _ b _ hab => by omega)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show (β + β') % 2 + 2 * (T + s2Mu4Carry β β') - (β % 2 + 2 * t)
      = β' % 2 + 2 * (T - t) from by omega,
    ← s2Mu4Coeff_eq_wcoeff h2 hq hg t, ← s2Mu4Coeff_eq_wcoeff h2 hq hz (T - t)]

/-- anti-drift pin: the statement of `s2Mu4Coeff_mul_via_carrier` is interchangeable with
the landed D3-10 `C136l2e4.s2Mu4Coeff_mul` — the landed name closes it verbatim. -/
example {β β' : ℕ} {g z : Polynomial O}
    (hg : S2Mu4ExactGrade h2 hq β g) (hz : S2Mu4ExactGrade h2 hq β' z) (T : ℕ) :
    s2Mu4Coeff h2 hq (β + β') (g * z) (T + s2Mu4Carry β β')
      = ∑ t ∈ Finset.range (T + 1),
          s2Mu4Coeff h2 hq β g t * s2Mu4Coeff h2 hq β' z (T - t) :=
  s2Mu4Coeff_mul h2 hq hg hz T

end S2Pin

end Uniformity.Density.Tower.I10wcc

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10wcc.wcoeff_mul
#print axioms Uniformity.Density.Tower.I10wcc.read_key_mul
#print axioms Uniformity.Density.Tower.I10wcc.read_mul_modByKey
#print axioms Uniformity.Density.Tower.I10wcc.s2Carrier
#print axioms Uniformity.Density.Tower.I10wcc.s2Key
#print axioms Uniformity.Density.Tower.I10wcc.s2Mu4Coeff_mul_via_carrier

end AxCheck
