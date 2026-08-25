/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130rp2

/-!
# Uniformity.ChapC.C130rp4 — S2-source plan node RP-4 (CORE 2/4)

**S2-source plan node RP-4 (CORE 2/4 of `graded_mul`)** (`docs/in-progress/
S2_SOURCE_PLAN_2026-08-24.md` §6 row RP-4: "Recursive coefficient convolution formula for the
depth-two graded residual"), on RP-1's graded residual `s2GradedRes` (C130rp1) and RP-3's
endpoint chain (C130rp2), under the U14 adjudication
(`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md`): the operator is grade-anchored, the
arbitrary-grade S2 product law carries the parity twist `X^{(β%2)·(β′%2)}` (the repo's own
generalization of published Cor 4.12(2), NOT a transcription of it), and the printed plain
law holds exactly on the `PrevGrade` (even-second-grade) scope.

## The formula (every slot, not just the endpoint)

At exact grades `β` (of `g`) and `β′` (of `z`), with carry `c = (β%2)·(β′%2)`:

* ★ `s2GradedCoeff_mul` (**twist-normalized coefficient convolution**, the node's headline):
  for EVERY `T`,
  `Rgc_{β+β′}(g·z)(T + c) = Σ_{t ≤ T} Rgc_β(g)(t) · Rgc_{β′}(z)(T − t)`.
* ★ `s2GradedCoeff_mul_zero_of_odd`: in the odd×odd (carry) genre the ONE coefficient below
  the twist vanishes, `Rgc_{β+β′}(g·z)(0) = 0` — together the two determine every
  coefficient of `R_{β+β′}(g·z)`.
* `s2GradedCoeff_mul_of_prevGrade` (**the PrevGrade specialization**, published Cor 4.12(2)'s
  scope at S2): an even `β′` kills the carry and the convolution is plain at every `T`.
* `s2GradedRes_mul_coeff` / `s2GradedRes_mul_coeff_zero_of_odd` /
  `s2GradedRes_mul_coeff_of_prevGrade`: the same laws read against the coefficients of the
  PRODUCT POLYNOMIAL `R_β(g)·R_{β′}(z)` (`Polynomial.coeff_mul`) — the form RP-6 consumes.
* ★ `s2GradedRes_mul_of_exact`: the assembled polynomial identity at exact grades,
  `R_{β+β′}(g·z) = X^{(β%2)·(β′%2)} · (R_β(g) · R_{β′}(z))` — the U14 §8.2 shape; and
  `s2GradedRes_mul_of_prevGrade`: its plain no-carry form.  RP-6's assembly row adds the
  exact-grade conjunct and the arbitrary-input (junk) handling on top of these.

## The proof (the convolution, slot by slot)

The `(T+c)`-th coefficient of `R_{β+β′}(g·z)` reads the development slot
`S = (β+β′)%2 + 2(T+c)` at the on-line height `m = (β+β′−5S)/2`; RP-2's floor bridge
(`s2GradedCoeff_eq_twistRead_of_le`) makes this read unconditional on the gate, because the
product's cleared support is exactly `β+β′` (NV-4's `s2_dvSupp_mul`).  The NEW generic split
`dev_mul_conv_split` decomposes the slot into the reduced convolution diagonal
`Σ_{j+i=S} (g_j·z_i) %ₘ Φ′` plus the carry diagonal `Σ_{j+i=S−1} dev(g_j·z_i)(1)` (the
`Φ′`-quotient digits).  Reading at `m` through the NEW finite-sum ϖ-read additivity
(`twistRead_finsetSum_of_le`, iterating RP-2's two-term law over the ultrametric
`KeyFrame.min_stageHeight_le_add`):

* every carry term is priced `≥ m+1` (its digit is `C(a₁b₁)`, `s2_dev_mul_one`, of height
  `2v(a₁)+2v(b₁)`; the grade lines price `v(a₁) ≥ ⌊⌈(β−5j)/2⌉/2⌋`) — it reads `0`;
* every OFF-parity main term (`j ≢ β mod 2`) is priced `≥ m+1` (two odd half-gaps merge) —
  it reads `0`;
* every ON-parity main term with an out-of-grade slot (`5j > β` or `5i > β′`) is priced
  `≥ m+1`, matching the vanishing graded coefficient on the other side;
* the surviving ON-parity in-grade terms read as products by RP-3's survival core
  (`s2_twistRead_mul_modByMonic`) at the exact on-line heights `m = Ha + Hb`, and the floor
  bridge converts each factor read back into the factor's graded coefficient.

The pricing floors come from the NEW `ceil_le_dvHgt_of_le_dvSupp` (every slot of a
grade-floored polynomial sits at or above the ROUNDED-UP on-line height — no parity or
membership hypothesis) and the NEW `≥` half of the survival core
(`le_stageHeight_mul_modByMonic`, the companion of NV-3's `≤` half): the reduced remainder
of a product of short digits cannot fall below the sum of the cleared floors.

## Teeth (regressions against RP-1/RP-2's landed values)

`tooth_conv_carry`: at `(5,5)`, `T = 0`, the general formula reproduces the endpoint carry
`Rgc_{10}(Φ′²)(1) = 1 = 1·1`.  `tooth_conv_low`: `Rgc_{10}(Φ′²)(0) = 0` — consistent with
the landed `R₁₀(Φ′²) = X`.  `tooth_conv_prevGrade`: the plain law at `(5,2)` gives
`Rgc₇(Φ′·x)(0) = 1`, and `tooth_conv_prevGrade_matches` pins it against the landed
`R₇(x·Φ′) = 1`.  `tooth_mul_poly`/`tooth_mul_poly_check`: the polynomial identity at `(5,5)`
re-derives `R₁₀(Φ′²) = X^1·1·1 = X`.

## What this node does NOT claim (honesty scope)

* No exact-grade conjunct `S2ExactGrade (β+β′) (g·z)` bundling and no arbitrary-input
  (junk-grade) product law: RP-6's assembly.
* No inner residual product beyond the S2 short-digit case and no twist normalization
  against `normalizedResidual`: RP-5/RP-8 (B39a `resPoly_mul_gen` route).
* No exact-grade nonvanishing (RP-7), no `FGMNSourceData`/`FGMNSourceLaws` instance (FD-0).
* The ϖ-read ↔ `ε(α)·R(a)(z)` dictionary stays on C.22/C.25's recorded faithfulness
  boundary.  The twisted law is the repo's OWN arbitrary-grade generalization (U14 §5); only
  its PrevGrade specialization may be cited as published Cor 4.12(2).

**Flagged for human review** (parent CLAUDE.md trust boundary — new general statements):
`dev_mul_conv_split` (the two-diagonal split of a product development slot, any corpus
frame), `le_stageHeight_finsetSum`/`twistRead_finsetSum_of_le` (finite-sum ultrametric floor
and ϖ-read additivity), `ceil_le_dvHgt_of_le_dvSupp`, `le_stageHeight_mul_modByMonic`,
`s2_dev_mul_one`.  The teeth regression-test the chain against the landed hand computations.

**DEPENDS.** C130rp2 (floor bridge, survival core, `twistRead_zero`/`twistRead_add_of_le`/
`twistRead_eq_zero_of_lt`, `le_dvHgt_of_le_dvSupp`, teeth) · C130rp1 (`s2GradedCoeff`/
`s2GradedRes` + master law + zero laws + teeth) · C130rp0 (`S2ExactGrade` normal forms,
grade teeth) · C130nv3 (`s2_mul_modByMonic`, `s2_stageHeight_linear`, `s2_dvSupp_mul`) ·
C130nv2 (`weight_read`, `dev_zero_pin`) · C131y (`dvSupp_le_term`) · C127
(`KeyFrame.min_stageHeight_le_add`, `stageHeight_zero`) · C35b (`key_eq`, `s2Key_deg`,
`sh_C`) · C.97 (`s2Frame`, `s2Frame_pin`, `s2Key`, `s2Key_monic`, `s2Key_natDegree`) ·
B.02/B.04/B35a (`dev`, `dev_eq_zero_of_lt`, `dev_mul_pow`, `dev_mul_pow_of_lt`,
`dev_finsetSum`) · B.05 (`sum_dev_eq`) · B.03 (`degree_dev_lt`) · mathlib
(`div_modByMonic_unique`, `coeff_mul`, `addVal_mul`, `addVal_add`, `addVal_uniformizer`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130rp4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130rp2

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — the generic convolution split of a product development slot

`g·z`'s `s`-th `Φ′`-development digit is the reduced convolution diagonal plus the carry
diagonal: expanding both factors through their developments (B.05) and reading slot `s` of
each product term (B35a's shift laws), only `j+i = s` (the reduced product of the two
digits) and `j+i = s−1` (the `Φ′`-quotient digit of the two-digit product) survive — a
product of two digits has degree `< 2·deg Φ′`, so its own development stops at index 1. -/

/-- development digits have degree below the key (with the zero digit included). -/
private theorem natDegree_dev_le (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) :
    (dev F.key f j).natDegree ≤ F.key.natDegree - 1 := by
  rcases eq_or_ne (dev F.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]
    omega
  · have h := Polynomial.natDegree_lt_natDegree h0
      (degree_dev_lt F.hmonic F.natDegree_key_pos f j)
    omega

/-- the development of a two-digit product stops at index 1: its degree is
`< 2·deg Φ′`, so every index `≥ 2` vanishes (B.04). -/
private theorem dev_dev_mul_eq_zero (F : KeyFrame O π) (g z : Polynomial O) (j i : ℕ)
    {t : ℕ} (ht : 2 ≤ t) :
    dev F.key (dev F.key g j * dev F.key z i) t = 0 := by
  refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos _ t ?_
  have h1 := natDegree_dev_le F g j
  have h2 := natDegree_dev_le F z i
  have h3 := Polynomial.natDegree_mul_le (p := dev F.key g j) (q := dev F.key z i)
  have hkeypos := F.natDegree_key_pos
  calc (dev F.key g j * dev F.key z i).natDegree
      ≤ (dev F.key g j).natDegree + (dev F.key z i).natDegree := h3
    _ < 2 * F.key.natDegree := by omega
    _ ≤ t * F.key.natDegree := Nat.mul_le_mul_right _ ht

/-- ★ **the convolution split** (generic): the `s`-th development digit of `g·z` is the
reduced main diagonal plus the carry diagonal,
`dev (g·z) s = Σ_{j≤s} (g_j·z_{s−j}) %ₘ Φ′ + Σ_{j≤s−1} dev (g_j·z_{s−1−j}) 1`. -/
theorem dev_mul_conv_split (F : KeyFrame O π) (g z : Polynomial O) (s : ℕ) :
    dev F.key (g * z) s
      = (∑ j ∈ Finset.range (s + 1),
          (dev F.key g j * dev F.key z (s - j)) %ₘ F.key)
        + ∑ j ∈ Finset.range s,
            dev F.key (dev F.key g j * dev F.key z (s - 1 - j)) 1 := by
  classical
  have hkeypos := F.natDegree_key_pos
  set N := g.natDegree + z.natDegree + 1 + s with hN
  have hgN : g.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hzN : z.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev F.key g j * F.key ^ j)
        * (∑ i ∈ Finset.range N, dev F.key z i * F.key ^ i) := by
      rw [sum_dev_eq F.hmonic hkeypos g hgN, sum_dev_eq F.hmonic hkeypos z hzN]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hdev : dev F.key (g * z) s
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) s := by
    conv_lhs => rw [hrep]
    exact dev_finsetSum F.hmonic _ _ s
  -- classify each convolution-square term into the two diagonals
  have hterm : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) s
        = (if p.1 + p.2 = s then (dev F.key g p.1 * dev F.key z p.2) %ₘ F.key else 0)
          + (if p.1 + p.2 + 1 = s
             then dev F.key (dev F.key g p.1 * dev F.key z p.2) 1 else 0) := by
    intro p _
    rcases lt_trichotomy (p.1 + p.2) s with hlt | heq | hgt
    · rcases eq_or_ne (p.1 + p.2 + 1) s with heq1 | hne1
      · -- the carry diagonal
        rw [if_neg (by omega), if_pos heq1, zero_add]
        have h := dev_mul_pow F.hmonic (p.1 + p.2) (dev F.key g p.1 * dev F.key z p.2) 1
        rw [heq1] at h
        exact h
      · -- deep below: index ≥ 2 of a two-digit product vanishes
        rw [if_neg (by omega), if_neg (by omega), add_zero]
        have h := dev_mul_pow F.hmonic (p.1 + p.2) (dev F.key g p.1 * dev F.key z p.2)
          (s - (p.1 + p.2))
        rw [show p.1 + p.2 + (s - (p.1 + p.2)) = s from by omega] at h
        rw [h]
        exact dev_dev_mul_eq_zero F g z p.1 p.2 (by omega)
    · -- the main diagonal
      rw [if_pos heq, if_neg (by omega), add_zero, ← heq]
      have h := dev_mul_pow F.hmonic (p.1 + p.2) (dev F.key g p.1 * dev F.key z p.2) 0
      rw [Nat.add_zero] at h
      rw [h, dev_zero_pin]
    · -- above the diagonal: nothing sits left of the key-power shift
      rw [if_neg (by omega), if_neg (by omega), add_zero]
      exact dev_mul_pow_of_lt F.hmonic (p.1 + p.2) _ s hgt
  rw [hdev, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  · -- the main diagonal reindexed by the first coordinate
    rw [← Finset.sum_filter]
    have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = s)
        = (Finset.range (s + 1)).image (fun j => (j, s - j)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, hsum⟩
        exact ⟨p.1, by omega, by
          rw [Prod.ext_iff]
          exact ⟨rfl, by omega⟩⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => by
      have := congrArg Prod.fst hab
      simpa using this)]
  · -- the carry diagonal reindexed by the first coordinate
    rw [← Finset.sum_filter]
    have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 + 1 = s)
        = (Finset.range s).image (fun j => (j, s - 1 - j)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨hp1, hp2⟩, hsum⟩
        exact ⟨p.1, by omega, by
          rw [Prod.ext_iff]
          exact ⟨rfl, by omega⟩⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => by
      have := congrArg Prod.fst hab
      simpa using this)]

/-! ## Part 2 — the finite-sum ϖ-read additivity (RP-2's two-term law, iterated) -/

/-- **a common floor passes to finite sums** — C127's two-term ultrametric
`KeyFrame.min_stageHeight_le_add`, iterated. -/
theorem le_stageHeight_finsetSum (F : KeyFrame O π) {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial O) {k : ℕ∞} (hf : ∀ i ∈ s, k ≤ F.stageHeight (f i)) :
    k ≤ F.stageHeight (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, F.stageHeight_zero]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    exact le_trans (le_min (hf a (Finset.mem_cons_self a t))
        (ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))))
      (F.min_stageHeight_le_add _ _)

/-- ★ **finite-sum ϖ-read additivity at a common height floor** (RP-2's
`twistRead_add_of_le`, iterated): if every summand clears height `k`, the height-`k` read
of the sum is the sum of the reads. -/
theorem twistRead_finsetSum_of_le (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {ι : Type*} (s : Finset ι) (f : ι → Polynomial O) {k : ℕ}
    (hf : ∀ i ∈ s, (k : ℕ∞) ≤ F.stageHeight (f i)) :
    F.twistRead H₀ hpin k (∑ i ∈ s, f i) = ∑ i ∈ s, F.twistRead H₀ hpin k (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact twistRead_zero F hπ H₀ hpin k
  | cons a t hat ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      twistRead_add_of_le F hπ H₀ hpin (hf a (Finset.mem_cons_self a t))
        (le_stageHeight_finsetSum F t f fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
      ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

end Generic

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 3 — the parity-robust slot floors

RP-2's `le_dvHgt_of_le_dvSupp` requires the slot to sit exactly on a line (`2m + 5j = β`);
the convolution runs over ALL slots, so the floor here is the rounded-up on-line height
`⌈(β − 5j)/2⌉` — a wrong-parity slot lands half a step (i.e. one `ℕ` step, after rounding)
strictly above the line, which is exactly the pricing the off-parity kill needs. -/

/-- **the parity-robust slot floor**: a cleared-support floor `β ≤ h₂(f)` prices EVERY
development slot at or above the rounded-up on-line height — no line membership, parity, or
range hypothesis. -/
theorem ceil_le_dvHgt_of_le_dvSupp {β : ℕ} {f : Polynomial O} (j : ℕ)
    (hβ : (β : ℕ∞) ≤ dvSupp (s2Frame h2 hq) f 5 2) :
    (((β - 5 * j + 1) / 2 : ℕ) : ℕ∞) ≤ dvHgt (s2Frame h2 hq) f j := by
  have h := le_trans hβ
    (C131y.dvSupp_le_term (s2Frame h2 hq) f 5 (by norm_num : (0 : ℕ) < 2) j)
  rcases eq_or_ne (dvHgt (s2Frame h2 hq) f j) ⊤ with hT | hT
  · rw [hT]
    exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hc, weight_read] at h
  rw [← hc]
  have hnat : β ≤ 2 * c + 5 * j := by exact_mod_cast h
  exact_mod_cast (by omega : (β - 5 * j + 1) / 2 ≤ c)

/-- S2 development digits are short: `natDegree (dev Φ′ f j) ≤ 1` (the key has degree 2). -/
private theorem natDegree_dev_le_one (f : Polynomial O) (j : ℕ) :
    (dev (s2Frame h2 hq).key f j).natDegree ≤ 1 := by
  have h := natDegree_dev_le (s2Frame h2 hq) f j
  have hk : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [key_eq h2 hq]
    exact s2Key_natDegree
  omega

/-- private copy of RP23's even-side parity floor (the private-copy pattern):
`a ≤ 2x` forces `⌈a/2⌉ ≤ x`. -/
private theorem coe_le_of_le_two_smul {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x) :
    (((a + 1) / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) = ((2 * c : ℕ) : ℕ∞) by
    rw [nsmul_eq_mul]; push_cast; ring] at h
  have hnat : a ≤ 2 * c := by exact_mod_cast h
  exact_mod_cast (by omega : (a + 1) / 2 ≤ c)

/-- private copy of RP23's odd-side parity floor: `a ≤ 2x + 1` forces `⌊a/2⌋ ≤ x`. -/
private theorem coe_le_of_le_two_smul_add_one {a : ℕ} {x : ℕ∞} (h : (a : ℕ∞) ≤ 2 • x + 1) :
    ((a / 2 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hx
  rw [← hc] at h ⊢
  rw [show (2 : ℕ) • ((c : ℕ) : ℕ∞) + 1 = ((2 * c + 1 : ℕ) : ℕ∞) by
    rw [nsmul_eq_mul]; push_cast; ring] at h
  have hnat : a ≤ 2 * c + 1 := by exact_mod_cast h
  exact_mod_cast (by omega : a / 2 ≤ c)

/-! ## Part 4 — the two height engines: the `≥` half of the survival core, and the carry
digit -/

/-- ★ **the `≥` half of the survival core** (the companion of NV-3's
`s2_stageHeight_mul_modByMonic_le`): the reduced remainder of a product of two short digits
cannot fall BELOW the sum of cleared-height floors — each remainder coefficient is a sum of
coefficient products, priced by the ultrametric at or above `Ha + Hb`. -/
theorem le_stageHeight_mul_modByMonic {a b : Polynomial O} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) {Ha Hb : ℕ}
    (hA : (Ha : ℕ∞) ≤ (s2Frame h2 hq).stageHeight a)
    (hB : (Hb : ℕ∞) ≤ (s2Frame h2 hq).stageHeight b) :
    ((Ha + Hb : ℕ) : ℕ∞)
      ≤ (s2Frame h2 hq).stageHeight ((a * b) %ₘ (s2Frame h2 hq).key) := by
  rw [s2_stageHeight_linear h2 hq ha] at hA
  rw [s2_stageHeight_linear h2 hq hb] at hB
  have hA0 : (((Ha + 1) / 2 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 0) :=
    coe_le_of_le_two_smul (le_trans hA (min_le_left _ _))
  have hA1 : ((Ha / 2 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hA (min_le_right _ _))
  have hB0 : (((Hb + 1) / 2 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 0) :=
    coe_le_of_le_two_smul (le_trans hB (min_le_left _ _))
  have hB1 : ((Hb / 2 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hB (min_le_right _ _))
  have hmono2 : Monotone (fun x : ℕ∞ => (2 : ℕ) • x) :=
    fun x y hxy => nsmul_le_nsmul_right hxy 2
  have hmono2' : Monotone (fun x : ℕ∞ => (2 : ℕ) • x + 1) :=
    fun x y hxy => add_le_add (nsmul_le_nsmul_right hxy 2) le_rfl
  rw [key_eq h2 hq, s2_mul_modByMonic a b ha hb,
    s2_stageHeight_linear h2 hq natDegree_linear_le]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, mul_zero, mul_one, Polynomial.coeff_C, one_ne_zero, if_false,
    zero_add, add_zero]
  refine le_min ?_ ?_
  · -- the even (constant-slot) branch: `a₀b₀ + 2·a₁b₁`
    have h1 : ((Ha + Hb : ℕ) : ℕ∞) ≤ 2 • addVal O (a.coeff 0 * b.coeff 0) := by
      rw [addVal_mul]
      calc ((Ha + Hb : ℕ) : ℕ∞)
          ≤ ((2 * ((Ha + 1) / 2 + (Hb + 1) / 2) : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
        _ = 2 • ((((Ha + 1) / 2 : ℕ) : ℕ∞) + (((Hb + 1) / 2 : ℕ) : ℕ∞)) := by
            rw [two_nsmul]; push_cast; ring
        _ ≤ 2 • (addVal O (a.coeff 0) + addVal O (b.coeff 0)) :=
            nsmul_le_nsmul_right (add_le_add hA0 hB0) 2
    have h2' : ((Ha + Hb : ℕ) : ℕ∞) ≤ 2 • addVal O (2 * (a.coeff 1 * b.coeff 1)) := by
      rw [addVal_mul, addVal_mul, addVal_uniformizer h2]
      calc ((Ha + Hb : ℕ) : ℕ∞)
          ≤ ((2 * (1 + (Ha / 2 + Hb / 2)) : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
        _ = 2 • ((1 : ℕ∞) + (((Ha / 2 : ℕ) : ℕ∞) + ((Hb / 2 : ℕ) : ℕ∞))) := by
            rw [two_nsmul]; push_cast; ring
        _ ≤ 2 • (1 + (addVal O (a.coeff 1) + addVal O (b.coeff 1))) :=
            nsmul_le_nsmul_right (add_le_add le_rfl (add_le_add hA1 hB1)) 2
    calc ((Ha + Hb : ℕ) : ℕ∞)
        ≤ min (2 • addVal O (a.coeff 0 * b.coeff 0))
            (2 • addVal O (2 * (a.coeff 1 * b.coeff 1))) := le_min h1 h2'
      _ = 2 • min (addVal O (a.coeff 0 * b.coeff 0))
            (addVal O (2 * (a.coeff 1 * b.coeff 1))) := (hmono2.map_min).symm
      _ ≤ 2 • addVal O (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1)) :=
          nsmul_le_nsmul_right IsDiscreteValuationRing.addVal_add 2
  · -- the odd (linear-slot) branch: `a₀b₁ + a₁b₀`
    have h1 : ((Ha + Hb : ℕ) : ℕ∞) ≤ 2 • addVal O (a.coeff 0 * b.coeff 1) + 1 := by
      rw [addVal_mul]
      calc ((Ha + Hb : ℕ) : ℕ∞)
          ≤ ((2 * ((Ha + 1) / 2 + Hb / 2) + 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
        _ = 2 • ((((Ha + 1) / 2 : ℕ) : ℕ∞) + ((Hb / 2 : ℕ) : ℕ∞)) + 1 := by
            rw [two_nsmul]; push_cast; ring
        _ ≤ 2 • (addVal O (a.coeff 0) + addVal O (b.coeff 1)) + 1 :=
            add_le_add (nsmul_le_nsmul_right (add_le_add hA0 hB1) 2) le_rfl
    have h2' : ((Ha + Hb : ℕ) : ℕ∞) ≤ 2 • addVal O (a.coeff 1 * b.coeff 0) + 1 := by
      rw [addVal_mul]
      calc ((Ha + Hb : ℕ) : ℕ∞)
          ≤ ((2 * (Ha / 2 + (Hb + 1) / 2) + 1 : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
        _ = 2 • (((Ha / 2 : ℕ) : ℕ∞) + (((Hb + 1) / 2 : ℕ) : ℕ∞)) + 1 := by
            rw [two_nsmul]; push_cast; ring
        _ ≤ 2 • (addVal O (a.coeff 1) + addVal O (b.coeff 0)) + 1 :=
            add_le_add (nsmul_le_nsmul_right (add_le_add hA1 hB0) 2) le_rfl
    calc ((Ha + Hb : ℕ) : ℕ∞)
        ≤ min (2 • addVal O (a.coeff 0 * b.coeff 1) + 1)
            (2 • addVal O (a.coeff 1 * b.coeff 0) + 1) := le_min h1 h2'
      _ = 2 • min (addVal O (a.coeff 0 * b.coeff 1))
            (addVal O (a.coeff 1 * b.coeff 0)) + 1 := (hmono2'.map_min).symm
      _ ≤ 2 • addVal O (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) + 1 :=
          add_le_add (nsmul_le_nsmul_right IsDiscreteValuationRing.addVal_add 2) le_rfl

/-- **the carry digit is the top-coefficient product**: for short digits `a, b`,
`dev Φ′ (a·b) 1 = C(a₁·b₁)` — the `Φ′`-quotient of a product of two linear polynomials is
the constant `a₁b₁` (division uniqueness against NV-3's explicit remainder). -/
theorem s2_dev_mul_one {a b : Polynomial O} (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    dev (s2Frame h2 hq).key (a * b) 1 = Polynomial.C (a.coeff 1 * b.coeff 1) := by
  have hdiv : (a * b) /ₘ s2Key O = Polynomial.C (a.coeff 1 * b.coeff 1) := by
    refine (Polynomial.div_modByMonic_unique (Polynomial.C (a.coeff 1 * b.coeff 1))
      (Polynomial.C (a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0) * Polynomial.X
        + Polynomial.C (a.coeff 0 * b.coeff 0 + 2 * (a.coeff 1 * b.coeff 1)))
      s2Key_monic ⟨?_, ?_⟩).1
    · conv_rhs => rw [eq_X_add_C_of_natDegree_le_one ha, eq_X_add_C_of_natDegree_le_one hb]
      simp only [s2Key, Polynomial.C_add, Polynomial.C_mul]
      ring
    · refine lt_of_le_of_lt degree_linear_le ?_
      rw [s2Key_deg]
      decide
  show dev (s2Frame h2 hq).key ((a * b) /ₘ (s2Frame h2 hq).key) 0 = _
  rw [dev_zero_pin, key_eq h2 hq, hdiv]
  exact (Polynomial.modByMonic_eq_self_iff s2Key_monic).mpr
    (lt_of_le_of_lt Polynomial.degree_C_le (by rw [s2Key_deg]; decide))

/-- **the carry-digit height floor**: `dv(dev Φ′ (a·b) 1) ≥ 2⌊Ha/2⌋ + 2⌊Hb/2⌋` — the carry
digit `C(a₁b₁)` sits at twice the top coefficients' valuations. -/
private theorem carry_floor {a b : Polynomial O} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) {Ha Hb : ℕ}
    (hA : (Ha : ℕ∞) ≤ (s2Frame h2 hq).stageHeight a)
    (hB : (Hb : ℕ∞) ≤ (s2Frame h2 hq).stageHeight b) :
    ((2 * (Ha / 2) + 2 * (Hb / 2) : ℕ) : ℕ∞)
      ≤ (s2Frame h2 hq).stageHeight (dev (s2Frame h2 hq).key (a * b) 1) := by
  rw [s2_stageHeight_linear h2 hq ha] at hA
  rw [s2_stageHeight_linear h2 hq hb] at hB
  have hA1 : ((Ha / 2 : ℕ) : ℕ∞) ≤ addVal O (a.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hA (min_le_right _ _))
  have hB1 : ((Hb / 2 : ℕ) : ℕ∞) ≤ addVal O (b.coeff 1) :=
    coe_le_of_le_two_smul_add_one (le_trans hB (min_le_right _ _))
  rw [s2_dev_mul_one h2 hq ha hb, sh_C h2 hq, addVal_mul]
  calc ((2 * (Ha / 2) + 2 * (Hb / 2) : ℕ) : ℕ∞)
      = 2 • (((Ha / 2 : ℕ) : ℕ∞) + ((Hb / 2 : ℕ) : ℕ∞)) := by
        rw [two_nsmul]; push_cast; ring
    _ ≤ 2 • (addVal O (a.coeff 1) + addVal O (b.coeff 1)) :=
        nsmul_le_nsmul_right (add_le_add hA1 hB1) 2

/-! ## Part 5 — ★ NODE RP-4: the coefficient convolution formula

The auxiliary form carries the carry as an ABSTRACT `c` pinned by the linear parity relation
`β%2 + β′%2 = (β+β′)%2 + 2c` (so every arithmetic goal below stays linear); the public
headline instantiates `c = (β%2)·(β′%2)` by the four-way parity check. -/

private theorem s2GradedCoeff_mul_aux {β β' c : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hcpar : β % 2 + β' % 2 = (β + β') % 2 + 2 * c) (T : ℕ) :
    s2GradedCoeff h2 hq (β + β') (g * z) (T + c)
      = ∑ t ∈ Finset.range (T + 1),
          s2GradedCoeff h2 hq β g t * s2GradedCoeff h2 hq β' z (T - t) := by
  have hsuppg : dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hg
  have hsuppz : dvSupp (s2Frame h2 hq) z 5 2 = (β' : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hz
  have hsupp : dvSupp (s2Frame h2 hq) (g * z) 5 2 = ((β + β' : ℕ) : ℕ∞) := by
    rw [s2_dvSupp_mul h2 hq, hsuppg, hsuppz]
    push_cast
    ring
  rcases Nat.lt_or_ge (β + β') (5 * ((β + β') % 2 + 2 * (T + c))) with hcase | hcase
  · -- the grade line is exhausted: both sides vanish
    rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq hcase]
    refine (Finset.sum_eq_zero fun t ht => ?_).symm
    rw [Finset.mem_range] at ht
    rcases (by omega : β < 5 * (β % 2 + 2 * t) ∨ β' < 5 * (β' % 2 + 2 * (T - t)))
      with h | h
    · rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq h, zero_mul]
    · rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq h, mul_zero]
  · -- the convolution case
    obtain ⟨m, hm⟩ : ∃ m, 2 * m + 5 * ((β + β') % 2 + 2 * (T + c)) = β + β' :=
      ⟨(β + β' - 5 * ((β + β') % 2 + 2 * (T + c))) / 2, by omega⟩
    -- the product-side floor bridge, then the convolution split
    rw [s2GradedCoeff_eq_twistRead_of_le h2 hq hm
        (le_dvHgt_of_le_dvSupp (by norm_num) (le_of_eq hsupp.symm) hm),
      dev_mul_conv_split (s2Frame h2 hq) g z ((β + β') % 2 + 2 * (T + c))]
    obtain ⟨S, hSdef⟩ : ∃ S, (β + β') % 2 + 2 * (T + c) = S := ⟨_, rfl⟩
    rw [hSdef] at hm ⊢
    -- per-slot floors on the two diagonals
    have hmainfloor : ∀ j ∈ Finset.range (S + 1),
        (m : ℕ∞) ≤ (s2Frame h2 hq).stageHeight
          ((dev (s2Frame h2 hq).key g j * dev (s2Frame h2 hq).key z (S - j))
            %ₘ (s2Frame h2 hq).key) := by
      intro j hj
      have hle := le_stageHeight_mul_modByMonic h2 hq (natDegree_dev_le_one h2 hq g j)
        (natDegree_dev_le_one h2 hq z (S - j))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq j (le_of_eq hsuppg.symm))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (S - j) (le_of_eq hsuppz.symm))
      refine le_trans (Nat.cast_le.mpr ?_) hle
      rw [Finset.mem_range] at hj
      omega
    have hcarryfloor : ∀ j ∈ Finset.range S,
        ((m + 1 : ℕ) : ℕ∞) ≤ (s2Frame h2 hq).stageHeight
          (dev (s2Frame h2 hq).key
            (dev (s2Frame h2 hq).key g j * dev (s2Frame h2 hq).key z (S - 1 - j)) 1) := by
      intro j hj
      have hle := carry_floor h2 hq (natDegree_dev_le_one h2 hq g j)
        (natDegree_dev_le_one h2 hq z (S - 1 - j))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq j (le_of_eq hsuppg.symm))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (S - 1 - j) (le_of_eq hsuppz.symm))
      refine le_trans (Nat.cast_le.mpr ?_) hle
      rw [Finset.mem_range] at hj
      omega
    -- read the split: additivity over the two diagonals, then over each sum
    rw [twistRead_add_of_le (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
        (le_stageHeight_finsetSum (s2Frame h2 hq) _ _ hmainfloor)
        (le_stageHeight_finsetSum (s2Frame h2 hq) _ _ fun j hj =>
          le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj)),
      twistRead_finsetSum_of_le (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) _ _ hmainfloor,
      twistRead_finsetSum_of_le (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) _ _
        (fun j hj => le_trans (Nat.cast_le.mpr (Nat.le_succ m)) (hcarryfloor j hj))]
    -- the carry diagonal reads zero
    have hcarryzero : (∑ j ∈ Finset.range S,
        (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m
          (dev (s2Frame h2 hq).key
            (dev (s2Frame h2 hq).key g j * dev (s2Frame h2 hq).key z (S - 1 - j)) 1)) = 0 :=
      Finset.sum_eq_zero fun j hj =>
        twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq)
          (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m)) (hcarryfloor j hj))
    rw [hcarryzero, add_zero]
    -- the main diagonal: off-parity terms read zero, on-parity terms reindex to `t`
    have hoff : ∀ j ∈ Finset.range (S + 1),
        (s2Frame h2 hq).twistRead 1 (s2Frame_pin h2 hq) m
          ((dev (s2Frame h2 hq).key g j * dev (s2Frame h2 hq).key z (S - j))
            %ₘ (s2Frame h2 hq).key) ≠ 0 → j % 2 = β % 2 := by
      intro j hj hne
      by_contra hpar
      refine hne (twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) ?_)
      have hle := le_stageHeight_mul_modByMonic h2 hq (natDegree_dev_le_one h2 hq g j)
        (natDegree_dev_le_one h2 hq z (S - j))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq j (le_of_eq hsuppg.symm))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (S - j) (le_of_eq hsuppz.symm))
      refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m))
        (le_trans (Nat.cast_le.mpr ?_) hle)
      rw [Finset.mem_range] at hj
      omega
    rw [← Finset.sum_filter_of_ne hoff]
    have himg : (Finset.range (S + 1)).filter (fun j => j % 2 = β % 2)
        = (Finset.range (T + 1)).image (fun t => β % 2 + 2 * t) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hj, hpar⟩
        exact ⟨j / 2, by omega, by omega⟩
      · rintro ⟨t, ht, rfl⟩
        omega
    rw [himg, Finset.sum_image (fun a _ b _ hab => by omega)]
    -- termwise: the surviving read IS the product of graded coefficients
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [show S - (β % 2 + 2 * t) = β' % 2 + 2 * (T - t) from by omega]
    rcases Nat.lt_or_ge β (5 * (β % 2 + 2 * t)) with hbig | hok
    · -- the g-side slot is past its grade line: both sides vanish
      rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq hbig, zero_mul]
      refine twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) ?_
      have hle := le_stageHeight_mul_modByMonic h2 hq
        (natDegree_dev_le_one h2 hq g (β % 2 + 2 * t))
        (natDegree_dev_le_one h2 hq z (β' % 2 + 2 * (T - t)))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (β % 2 + 2 * t) (le_of_eq hsuppg.symm))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsuppz.symm))
      exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m))
        (le_trans (Nat.cast_le.mpr (by omega)) hle)
    rcases Nat.lt_or_ge β' (5 * (β' % 2 + 2 * (T - t))) with hbig' | hok'
    · -- the z-side slot is past its grade line: both sides vanish
      rw [s2GradedCoeff_eq_zero_of_grade_lt h2 hq hbig', mul_zero]
      refine twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) ?_
      have hle := le_stageHeight_mul_modByMonic h2 hq
        (natDegree_dev_le_one h2 hq g (β % 2 + 2 * t))
        (natDegree_dev_le_one h2 hq z (β' % 2 + 2 * (T - t)))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (β % 2 + 2 * t) (le_of_eq hsuppg.symm))
        (ceil_le_dvHgt_of_le_dvSupp h2 hq (β' % 2 + 2 * (T - t)) (le_of_eq hsuppz.symm))
      exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m))
        (le_trans (Nat.cast_le.mpr (by omega)) hle)
    · -- the survival core at the two on-line heights
      obtain ⟨Ha, hHa⟩ : ∃ Ha, 2 * Ha + 5 * (β % 2 + 2 * t) = β :=
        ⟨(β - 5 * (β % 2 + 2 * t)) / 2, by omega⟩
      obtain ⟨Hb, hHb⟩ : ∃ Hb, 2 * Hb + 5 * (β' % 2 + 2 * (T - t)) = β' :=
        ⟨(β' - 5 * (β' % 2 + 2 * (T - t))) / 2, by omega⟩
      have hfg : (Ha : ℕ∞) ≤ dvHgt (s2Frame h2 hq) g (β % 2 + 2 * t) :=
        le_dvHgt_of_le_dvSupp (by norm_num) (le_of_eq hsuppg.symm) hHa
      have hfz : (Hb : ℕ∞) ≤ dvHgt (s2Frame h2 hq) z (β' % 2 + 2 * (T - t)) :=
        le_dvHgt_of_le_dvSupp (by norm_num) (le_of_eq hsuppz.symm) hHb
      rw [show m = Ha + Hb from by omega,
        s2_twistRead_mul_modByMonic h2 hq (natDegree_dev_le_one h2 hq g _)
          (natDegree_dev_le_one h2 hq z _) hfg hfz,
        s2GradedCoeff_eq_twistRead_of_le h2 hq hHa hfg,
        s2GradedCoeff_eq_twistRead_of_le h2 hq hHb hfz]
      rfl

/-- ★ **NODE RP-4, the headline — the twist-normalized coefficient convolution** (the
general-slot form of RP23's endpoint law; with `s2GradedCoeff_mul_zero_of_odd` it determines
every coefficient of `R_{β+β′}(g·z)`): at exact grades, for EVERY `T`,
`Rgc_{β+β′}(g·z)(T + (β%2)(β′%2)) = Σ_{t≤T} Rgc_β(g)(t)·Rgc_{β′}(z)(T−t)`. -/
theorem s2GradedCoeff_mul {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) (T : ℕ) :
    s2GradedCoeff h2 hq (β + β') (g * z) (T + β % 2 * (β' % 2))
      = ∑ t ∈ Finset.range (T + 1),
          s2GradedCoeff h2 hq β g t * s2GradedCoeff h2 hq β' z (T - t) :=
  s2GradedCoeff_mul_aux h2 hq hg hz (by
    rcases Nat.mod_two_eq_zero_or_one β with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one β' with h' | h' <;> rw [h, h'] <;> omega) T

/-- ★ **the below-twist coefficient vanishes** (the odd×odd companion): in the carry genre
the product's `y⁰`-coefficient is `0` — its slot `0` prices strictly above the line (the two
odd half-gaps merge into a full step). -/
theorem s2GradedCoeff_mul_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    s2GradedCoeff h2 hq (β + β') (g * z) 0 = 0 := by
  have hsuppg : dvSupp (s2Frame h2 hq) g 5 2 = (β : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hg
  have hsuppz : dvSupp (s2Frame h2 hq) z 5 2 = (β' : ℕ∞) :=
    (S2ExactGrade_iff_dvSupp h2 hq).mp hz
  have hsupp : dvSupp (s2Frame h2 hq) (g * z) 5 2 = ((β + β' : ℕ) : ℕ∞) := by
    rw [s2_dvSupp_mul h2 hq, hsuppg, hsuppz]
    push_cast
    ring
  obtain ⟨m, hm⟩ : ∃ m, 2 * m + 5 * ((β + β') % 2 + 2 * 0) = β + β' :=
    ⟨(β + β') / 2, by omega⟩
  rw [s2GradedCoeff_eq_twistRead_of_le h2 hq hm
      (le_dvHgt_of_le_dvSupp (by norm_num) (le_of_eq hsupp.symm) hm),
    dev_mul_conv_split (s2Frame h2 hq) g z ((β + β') % 2 + 2 * 0),
    show (β + β') % 2 + 2 * 0 = 0 from by omega, Finset.range_one, Finset.sum_singleton,
    Finset.range_zero, Finset.sum_empty, add_zero, show (0 : ℕ) - 0 = 0 from rfl]
  refine twistRead_eq_zero_of_lt (s2Frame h2 hq) h2 1 (s2Frame_pin h2 hq) ?_
  have hle := le_stageHeight_mul_modByMonic h2 hq (natDegree_dev_le_one h2 hq g 0)
    (natDegree_dev_le_one h2 hq z 0)
    (ceil_le_dvHgt_of_le_dvSupp h2 hq 0 (le_of_eq hsuppg.symm))
    (ceil_le_dvHgt_of_le_dvSupp h2 hq 0 (le_of_eq hsuppz.symm))
  exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self m))
    (le_trans (Nat.cast_le.mpr (by omega)) hle)

/-- **the PrevGrade specialization** (published Cor 4.12(2)'s scope at S2, per U14: the
even second grade is the S2 reading of `β′ ∈ Γ₁`): no carry, the convolution is plain at
every `T`. -/
theorem s2GradedCoeff_mul_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) (T : ℕ) :
    s2GradedCoeff h2 hq (β + β') (g * z) T
      = ∑ t ∈ Finset.range (T + 1),
          s2GradedCoeff h2 hq β g t * s2GradedCoeff h2 hq β' z (T - t) := by
  have h := s2GradedCoeff_mul_aux h2 hq hg hz (c := 0) (by omega) T
  rwa [Nat.add_zero] at h

/-! ## Part 6 — the product-polynomial coefficient forms (what RP-6 consumes) -/

/-- ★ **the convolution against the product polynomial**: the `(T + carry)`-th coefficient
of `R_{β+β′}(g·z)` IS the `T`-th coefficient of `R_β(g)·R_{β′}(z)` — RP-6's assembly form
(`Polynomial.coeff_mul` + the master law). -/
theorem s2GradedRes_mul_coeff {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) (T : ℕ) :
    (s2GradedRes h2 hq (β + β') (g * z)).coeff (T + β % 2 * (β' % 2))
      = (s2GradedRes h2 hq β g * s2GradedRes h2 hq β' z).coeff T := by
  rw [s2GradedRes_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, s2GradedCoeff_mul h2 hq hg hz T]
  exact Finset.sum_congr rfl fun t _ => by rw [s2GradedRes_coeff, s2GradedRes_coeff]

/-- the below-twist coefficient of the polynomial, odd×odd genre. -/
theorem s2GradedRes_mul_coeff_zero_of_odd {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hβ : β % 2 = 1) (hβ' : β' % 2 = 1) :
    (s2GradedRes h2 hq (β + β') (g * z)).coeff 0 = 0 := by
  rw [s2GradedRes_coeff]
  exact s2GradedCoeff_mul_zero_of_odd h2 hq hg hz hβ hβ'

/-- the PrevGrade form against the product polynomial: every coefficient matches plainly. -/
theorem s2GradedRes_mul_coeff_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z)
    (hβ' : β' % 2 = 0) (T : ℕ) :
    (s2GradedRes h2 hq (β + β') (g * z)).coeff T
      = (s2GradedRes h2 hq β g * s2GradedRes h2 hq β' z).coeff T := by
  have h := s2GradedRes_mul_coeff h2 hq hg hz T
  rwa [hβ', mul_zero, Nat.add_zero] at h

/-! ## Part 7 — the assembled polynomial identities at exact grades

The coefficient convolution plus the below-twist vanish determine the polynomial: the U14
§8.2 twisted law, and its plain PrevGrade specialization.  (RP-6's assembly row adds the
exact-grade conjunct `S2ExactGrade (β+β′) (g·z)` and the arbitrary-input handling.) -/

/-- ★ **the S2 arbitrary-grade product law at exact grades** (U14 §8.2; the repo's OWN
carry-twist generalization of published Cor 4.12(2), NOT a transcription of it):
`R_{β+β′}(g·z) = X^{(β%2)·(β′%2)} · (R_β(g) · R_{β′}(z))`. -/
theorem s2GradedRes_mul_of_exact {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) :
    s2GradedRes h2 hq (β + β') (g * z)
      = Polynomial.X ^ (β % 2 * (β' % 2))
        * (s2GradedRes h2 hq β g * s2GradedRes h2 hq β' z) := by
  rcases Nat.mod_two_eq_zero_or_one β with hpb | hpb
  · refine Polynomial.ext fun T => ?_
    rw [hpb, zero_mul, pow_zero, one_mul]
    have h := s2GradedRes_mul_coeff h2 hq hg hz T
    rwa [hpb, zero_mul, Nat.add_zero] at h
  · rcases Nat.mod_two_eq_zero_or_one β' with hpb' | hpb'
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_zero, pow_zero, one_mul]
      have h := s2GradedRes_mul_coeff h2 hq hg hz T
      rwa [hpb', mul_zero, Nat.add_zero] at h
    · refine Polynomial.ext fun T => ?_
      rw [hpb, hpb', mul_one, pow_one]
      match T with
      | 0 =>
        rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
        exact s2GradedRes_mul_coeff_zero_of_odd h2 hq hg hz hpb hpb'
      | T + 1 =>
        rw [Polynomial.coeff_X_mul]
        have h := s2GradedRes_mul_coeff h2 hq hg hz T
        rwa [hpb, hpb', mul_one] at h

/-- **the plain PrevGrade product law at exact grades** (published Cor 4.12(2)'s scope):
an even `β′` gives `R_{β+β′}(g·z) = R_β(g)·R_{β′}(z)` on the nose. -/
theorem s2GradedRes_mul_of_prevGrade {β β' : ℕ} {g z : Polynomial O}
    (hg : S2ExactGrade h2 hq β g) (hz : S2ExactGrade h2 hq β' z) (hβ' : β' % 2 = 0) :
    s2GradedRes h2 hq (β + β') (g * z)
      = s2GradedRes h2 hq β g * s2GradedRes h2 hq β' z := by
  have h := s2GradedRes_mul_of_exact h2 hq hg hz
  rwa [hβ', mul_zero, pow_zero, one_mul] at h

/-! ## Part 8 — teeth (regressions against RP-1/RP-2's landed values) -/

/-- the landed value `Rgc₅(Φ′)(0) = 1` (RP-1's tooth, read coefficientwise). -/
theorem tooth_coeff_key_zero :
    s2GradedCoeff h2 hq 5 ((s2Frame h2 hq).key : Polynomial O) 0 = 1 := by
  rw [← s2GradedRes_coeff, tooth_gradedRes_key h2 hq, Polynomial.coeff_one_zero]

/-- the landed value `Rgc₂(x)(0) = 1` (RP23's tooth, read coefficientwise). -/
theorem tooth_coeff_X_zero :
    s2GradedCoeff h2 hq 2 (Polynomial.X : Polynomial O) 0 = 1 := by
  rw [← s2GradedRes_coeff, tooth_gradedRes_X h2 hq, Polynomial.coeff_one_zero]

/-- **tooth (the carry genre through the GENERAL formula)**: at `(5,5)`, `T = 0`, the
convolution reproduces the endpoint carry `Rgc₁₀(Φ′²)(1) = 1·1 = 1`. -/
theorem tooth_conv_carry :
    s2GradedCoeff h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 1 = 1 := by
  have h := s2GradedCoeff_mul h2 hq (tooth_key h2 hq) (tooth_key h2 hq) 0
  rw [Finset.sum_range_one, show (5 : ℕ) + 5 = 10 from rfl,
    show 0 + 5 % 2 * (5 % 2) = 1 from rfl, show (0 : ℕ) - 0 = 0 from rfl] at h
  rw [h, tooth_coeff_key_zero h2 hq, mul_one]

/-- **tooth (the below-twist vanish fires)**: `Rgc₁₀(Φ′²)(0) = 0` — consistent with the
landed `R₁₀(Φ′²) = X` (whose `y⁰`-coefficient is `0`). -/
theorem tooth_conv_low :
    s2GradedCoeff h2 hq 10
      (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key) 0 = 0 := by
  have h := s2GradedCoeff_mul_zero_of_odd h2 hq (tooth_key h2 hq) (tooth_key h2 hq) rfl rfl
  rwa [show (5 : ℕ) + 5 = 10 from rfl] at h

/-- **tooth (the plain PrevGrade law fires)**: at `(5,2)`, `Rgc₇(Φ′·x)(0) = 1·1 = 1`. -/
theorem tooth_conv_prevGrade :
    s2GradedCoeff h2 hq 7
      (((s2Frame h2 hq).key : Polynomial O) * Polynomial.X) 0 = 1 := by
  have h := s2GradedCoeff_mul_of_prevGrade h2 hq (tooth_key h2 hq) (tooth_X h2 hq) rfl 0
  rw [Finset.sum_range_one, show (5 : ℕ) + 2 = 7 from rfl,
    show (0 : ℕ) - 0 = 0 from rfl] at h
  rw [h, tooth_coeff_key_zero h2 hq, tooth_coeff_X_zero h2 hq, mul_one]

/-- the same value against RP-1's landed tooth `R₇(x·Φ′) = 1` (commutativity): the general
law agrees with the landed hand computation. -/
theorem tooth_conv_prevGrade_matches :
    s2GradedRes h2 hq 7 (((s2Frame h2 hq).key : Polynomial O) * Polynomial.X) = 1 := by
  rw [mul_comm]
  exact tooth_gradedRes_X_mul_key h2 hq

/-- **tooth (the polynomial identity at the carry pair)**: `R₁₀(Φ′²) = X^{1·1}·(R₅(Φ′))²`. -/
theorem tooth_mul_poly :
    s2GradedRes h2 hq 10 (((s2Frame h2 hq).key : Polynomial O) * (s2Frame h2 hq).key)
      = Polynomial.X ^ (5 % 2 * (5 % 2))
        * (s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)
          * s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)) := by
  have h := s2GradedRes_mul_of_exact h2 hq (tooth_key h2 hq) (tooth_key h2 hq)
  rwa [show (5 : ℕ) + 5 = 10 from rfl] at h

/-- the right side of `tooth_mul_poly` evaluates against the landed values to `X` — the
general law re-derives RP-1's `R₁₀(Φ′²) = X` (and hence the plain-shape refutation). -/
theorem tooth_mul_poly_check :
    Polynomial.X ^ (5 % 2 * (5 % 2))
        * (s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O)
          * s2GradedRes h2 hq 5 ((s2Frame h2 hq).key : Polynomial O))
      = (Polynomial.X : Polynomial ((s2DepthTwo h2 hq).fld 2)) := by
  rw [tooth_gradedRes_key h2 hq, mul_one, show 5 % 2 * (5 % 2) = 1 from rfl, pow_one,
    mul_one]

end S2

end Uniformity.Density.Tower.C130rp4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130rp4.dev_mul_conv_split
#print axioms Uniformity.Density.Tower.C130rp4.le_stageHeight_finsetSum
#print axioms Uniformity.Density.Tower.C130rp4.twistRead_finsetSum_of_le
#print axioms Uniformity.Density.Tower.C130rp4.ceil_le_dvHgt_of_le_dvSupp
#print axioms Uniformity.Density.Tower.C130rp4.le_stageHeight_mul_modByMonic
#print axioms Uniformity.Density.Tower.C130rp4.s2_dev_mul_one
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedCoeff_mul
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedCoeff_mul_zero_of_odd
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedCoeff_mul_of_prevGrade
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedRes_mul_coeff
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedRes_mul_coeff_zero_of_odd
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedRes_mul_coeff_of_prevGrade
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedRes_mul_of_exact
#print axioms Uniformity.Density.Tower.C130rp4.s2GradedRes_mul_of_prevGrade
#print axioms Uniformity.Density.Tower.C130rp4.tooth_coeff_key_zero
#print axioms Uniformity.Density.Tower.C130rp4.tooth_coeff_X_zero
#print axioms Uniformity.Density.Tower.C130rp4.tooth_conv_carry
#print axioms Uniformity.Density.Tower.C130rp4.tooth_conv_low
#print axioms Uniformity.Density.Tower.C130rp4.tooth_conv_prevGrade
#print axioms Uniformity.Density.Tower.C130rp4.tooth_conv_prevGrade_matches
#print axioms Uniformity.Density.Tower.C130rp4.tooth_mul_poly
#print axioms Uniformity.Density.Tower.C130rp4.tooth_mul_poly_check

end AxCheck
