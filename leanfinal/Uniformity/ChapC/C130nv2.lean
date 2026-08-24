/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39a
import Uniformity.ChapB.B43
import Uniformity.ChapC.C34
import Uniformity.ChapC.C127
import Uniformity.ChapC.C131y
import Uniformity.ChapC.C130nv

/-!
# Uniformity.ChapC.C130nv2 — S2-source plan node NV-2 (CORE 1/4)

**S2-source plan node NV-2 (CORE 1/4 of the level-two product law)**
(`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §4, §6 row NV-2): for nonzero `g, z`, CHOOSE
the minimizing outer-development slots and prove the endpoint lemma — the sum of the chosen
minimizers is a product minimizer, with the value bound in BOTH directions that NV-3's
convolution step consumes.

## The minimizer choice (the tie ruling this node fixes)

The outer development of `A` at the frame key is B.02's `dev F.key A ·`; slot `j` carries the
`(u, ℓ)`-weight `ℓ • dvHgt F A j + u·j` (C.06), and `dvSupp F A u ℓ` is their minimum.  The
minimizing slots are C.07's landed `dvSideSet` (attainment + finite height), and **the chosen
minimizer is `dvSideMin`, the LEFTMOST minimizing slot** (`Finset.min'`).  Ties between
minimizing slots are therefore resolved LEFT.  This is the choice that serves NV-3/NV-4
(end-to-end criterion): left endpoints ADD under products (B39a's `sideMin` precedent, one
level up), every slot strictly left of the choice is strictly off-minimum
(`not_dvOnSide_of_lt_dvSideMin`), and the decomposition `j + i = jg + jz` with both factors
on-side forces `(j, i) = (jg, jz)` (`dvOnSide_endpoint_unique`) — the "unique lowest
convolution term" of NV-3's row is this endpoint pair.

## What NV-3 consumes (the exit surface)

* **Reads at the chosen minimizers**: `dvOnSide_dvSideMin`, `exists_dvSideMin_height`,
  `dvSupp_eq_of_dvOnSide` (the weight identity `dvSupp = ℓ·H + u·j` at any on-side slot),
  `le_dvWeight`/`lt_dvWeight` (the polygon lies on/strictly above the support line, ℕ-cleared).
* **The level-one engine at the frame**: `stageHeight_mul` (the UNIVERSAL first-augmentation
  product law, NV-1's `suppVal_mul_univ` at the frame's own side), and the finite-sum
  ultrametric `le_weight_stageHeight_sum`.
* **The one-step MacLane expansion** (`stageHeight_le_modByMonic`,
  `stageHeight_le_divByMonic`, `stageHeight_eq_min_mod_div`): the stage value of `w` is
  EXACTLY `min (dv(w %ₘ Φ′), dv(w /ₘ Φ′) + dv(Φ′))` — the non-cancellation half is the new
  content (witnessed at the product side's right endpoint through B39a's general product law
  and the frame key's purity).  This is what compensates the CARRY of the outer convolution.
* **The convolution term estimates, both directions**: `stageHeight_dev_mul_eq` (the endpoint
  term's EXACT value `Hg + Hz`, both directions at once, via `stageHeight_mul`);
  `le_line_dev_term` (every term of the outer convolution of `g·z` at every slot weighs at
  least `Sg + Sz`, carries included — needs the ADMISSIBILITY `ℓ·dv(Φ′) ≤ u`, S2: `2·2 ≤ 5`);
  `lt_line_dev_term` (every term other than the on-side exact-slot pairs weighs at least
  `Sg + Sz + 1` — needs STRICT admissibility `ℓ·dv(Φ′) < u`, S2: `4 < 5`).
* **The endpoint theorem**: `dvSupp_add_le_dvSupp_mul` (★ the full `≥` direction of NV-4,
  universal, all zero cases — the level-two B.33) and the assembly lemmas
  `dvSupp_mul_of_endpoint_le` / `dvOnSide_mul_endpoint` / `dvSideMin_mul_le` /
  `dvSupp_mul_eq_add_of_endpoint_le`: given NV-3's one missing input — the endpoint slot's
  height upper bound `dv₂(dev (g·z) (jg+jz)) ≤ Hg + Hz` — the sum of the chosen minimizers IS
  a product minimizer, bounds `dvSideMin (g·z)` above, and the level-two product law
  `dvSupp (g·z) = dvSupp g + dvSupp z` fires in NV-4's exact shape.

## What this node does NOT claim (honesty scope)

* No unconditional level-two product law: the endpoint height upper bound (the survival of
  the unique lowest convolution term against residual cancellation, FGMN's `ψ ∤ R(a)R(b)`
  degree argument) is NV-3's row and enters here only as the hypothesis `hup`.
* No claim at degenerate frames: the engine needs `0 < F.h` (the corpus frame; C130nv's
  scope note applies) and the augmentation admissibility `ℓ · dv(Φ′) ≤ u` (strict for the
  strict bank) — both DISCHARGED at S2 (`s2_h_pos`, `s2_stageHeight_key`, `2·2 = 4 < 5`).

**Flagged for human review** (new general statements, parent CLAUDE.md trust boundary): the
one-step expansion exactness and the admissibility-gated term estimates are asserted
generically — any frame with `0 < F.h` and `ℓ·dv(Φ′) ≤ u` — strictly more than the S2
instance needs.  Nothing here is a signed §-node statement; every declaration is
infrastructure, and the S2 teeth (`h₂(x·Φ′) = 7 = 2 + 5`) regression-test the chain against
hand computation.

**DEPENDS.** C.06/C.07 (`dvHgt`, `dvSupp`, `DvOnSide`, `dvSideSet`, `dvSideMin`) · C.34
(`dvSideSet_nonempty`, `KeyFrame.stageHeight_ne_top`) · C131y (`dvSupp_le_term`,
`dvHgt_eq_top_of_natDegree_lt`) · C130nv (`suppVal_mul_univ`, `suppVal_add_eq`, `toZ_add`) ·
C130s6 (`dvSupp` bank, `toZ` dictionary, `s2Hgt₂` + teeth) · C.127
(`KeyFrame.min_stageHeight_le_add`, `natDegree_key_pos`, `stageHeight_zero`) · C118a
(`smul_top_pos`) · B39a (`suppVal_eq_of_onSide`, `sideMin_mul_gen`, `sideDeg_mul_gen`,
`mem_sideSet_of_onSide`, `nsmul_add_cast_gen`) · B.20 (`sideMax_eq`, `onSide_of_mem_sideSet`) ·
B43 (`suppVal_ne_top_of_ne_zero`, `exists_sideMin_height`) · B39b (`sideSet_nonempty_gen`) ·
B.02–B.06 (`dev` vocabulary) · B83Kit (`GateKit.isKey_X`, `gaussVal_C`, `addVal_one`) ·
C35b (S2 frame numerals, `sh_X`, `addVal_two_pow`) · C.97 (`s2Key` coefficients).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130nv2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Leaf.GateKit
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130nv

/-! ## Part 0 — the weight normal form -/

/-- The `(u, ℓ)`-weight of a finite slot read, cleared to a single `ℕ`-cast (C.06's coercion
seam `(u * j : ℕ∞)` = product of casts, bridged once here). -/
theorem weight_read (ℓ u j H : ℕ) :
    ℓ • (H : ℕ∞) + (u * j : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
  rw [show ((u : ℕ∞) * (j : ℕ∞)) = ((u * j : ℕ) : ℕ∞) by push_cast; rfl]
  exact nsmul_add_cast_gen ℓ H (u * j)

section Generic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — the minimizer choice: reads and strictness at `dvSideMin` -/

/-- Membership in C.07's `dvSideSet` projects to the on-side predicate (public here; C.08's
and C131y's copies are private). -/
theorem dvOnSide_of_mem_dvSideSet {F : KeyFrame O π} {f : Polynomial O} {u ℓ j : ℕ}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

/-- An on-side slot lies in `dvSideSet`: the finiteness guard bounds it into the range. -/
theorem mem_dvSideSet_of_dvOnSide {F : KeyFrame O π} {f : Polynomial O} {u ℓ j : ℕ}
    (hj : DvOnSide F f u ℓ j) : j ∈ dvSideSet F f u ℓ := by
  classical
  simp only [dvSideSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hj⟩
  by_contra hdeg
  exact hj.2 (dvHgt_eq_top_of_natDegree_lt F f (by omega))

/-- **The chosen minimizer is on-side**: `dvSideMin` attains the weighted minimum with a
finite height. -/
theorem dvOnSide_dvSideMin (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    DvOnSide F f u ℓ (dvSideMin F f u ℓ hne) :=
  dvOnSide_of_mem_dvSideSet (Finset.min'_mem _ hne)

/-- The chosen minimizer is the LEFTMOST on-side slot. -/
theorem dvSideMin_le_of_dvOnSide {F : KeyFrame O π} {f : Polynomial O} {u ℓ j : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) (hj : DvOnSide F f u ℓ j) :
    dvSideMin F f u ℓ hne ≤ j :=
  Finset.min'_le _ _ (mem_dvSideSet_of_dvOnSide hj)

/-- **The tie ruling's teeth**: every slot strictly left of the chosen minimizer is strictly
off the side. -/
theorem not_dvOnSide_of_lt_dvSideMin {F : KeyFrame O π} {f : Polynomial O} {u ℓ j : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) (hlt : j < dvSideMin F f u ℓ hne) :
    ¬ DvOnSide F f u ℓ j :=
  fun hj => absurd (dvSideMin_le_of_dvOnSide hne hj) (by omega)

/-- **The unique lowest convolution pair** (NV-3's endpoint identification): an on-side
decomposition of the SUM of the chosen minimizers is the pair of chosen minimizers. -/
theorem dvOnSide_endpoint_unique {F : KeyFrame O π} {g z : Polynomial O} {u ℓ j i : ℕ}
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hsum : j + i = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)
    (hj : DvOnSide F g u ℓ j) (hi : DvOnSide F z u ℓ i) :
    j = dvSideMin F g u ℓ hng ∧ i = dvSideMin F z u ℓ hnz := by
  have h1 := dvSideMin_le_of_dvOnSide hng hj
  have h2 := dvSideMin_le_of_dvOnSide hnz hi
  omega

/-- The height at the chosen minimizer is a natural number (the read NV-3 opens with). -/
theorem exists_dvSideMin_height (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ H : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (H : ℕ∞) :=
  ENat.ne_top_iff_exists.1 (dvOnSide_dvSideMin F f u ℓ hne).2 |>.imp fun _ h => h.symm

/-- **The support value, read off any on-side slot** (the weight identity, cast-cleared). -/
theorem dvSupp_eq_of_dvOnSide {F : KeyFrame O π} {f : Polynomial O} {u ℓ j H : ℕ}
    (hH : dvHgt F f j = (H : ℕ∞)) (hj : DvOnSide F f u ℓ j) :
    dvSupp F f u ℓ = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
  rw [hj.1, hH, weight_read]

/-- **The support line lies below the level polygon**, ℕ-cleared (level-two
`le_weight_gen`). -/
theorem le_dvWeight {F : KeyFrame O π} {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {S H j : ℕ} (hS : dvSupp F f u ℓ = (S : ℕ∞)) (hH : dvHgt F f j = (H : ℕ∞)) :
    S ≤ ℓ * H + u * j := by
  have h := dvSupp_le_term F f u hℓ j
  rw [hS, hH, weight_read] at h
  exact_mod_cast h

/-- **Off the side the support line is strictly below the polygon** (level-two
`lt_weight_gen`; the strictness NV-3's non-endpoint terms consume). -/
theorem lt_dvWeight {F : KeyFrame O π} {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {S H j : ℕ} (hS : dvSupp F f u ℓ = (S : ℕ∞)) (hH : dvHgt F f j = (H : ℕ∞))
    (hns : ¬ DvOnSide F f u ℓ j) : S < ℓ * H + u * j := by
  rcases eq_or_lt_of_le (le_dvWeight hℓ hS hH) with heq | hlt
  · refine absurd ⟨?_, hH ▸ ENat.coe_ne_top H⟩ hns
    rw [hS, hH, weight_read, ← heq]
  · exact hlt

/-! ## Part 2 — the level-one engine at the frame -/

/-- ★ **The universal level-one product law at the frame** (NV-1's `suppVal_mul_univ` read
as the stage value): `dv(A·B) = dv(A) + dv(B)` for ALL `A B`, all zero cases included.  This
is the engine of every convolution estimate below. -/
theorem stageHeight_mul (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    (A B : Polynomial O) :
    F.stageHeight (A * B) = F.stageHeight A + F.stageHeight B :=
  suppVal_mul_univ hπ isKey_X hh F.he₁ F.hcop A B

/-- The finite-sum ultrametric, in the weighted form the outer convolution consumes: a
uniform lower bound on every summand's weight is a lower bound on the sum's weight. -/
theorem le_weight_stageHeight_sum (F : KeyFrame O π) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {ι : Type*} (s : Finset ι) (G : ι → Polynomial O) {c d : ℕ∞}
    (hall : ∀ p ∈ s, c ≤ ℓ • F.stageHeight (G p) + d) :
    c ≤ ℓ • F.stageHeight (∑ p ∈ s, G p) + d := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, F.stageHeight_zero, C118a.smul_top_pos hℓ, top_add]
    exact le_top
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    have hmono : Monotone (fun x : ℕ∞ => ℓ • x + d) :=
      fun x y hxy => add_le_add (nsmul_le_nsmul_right hxy ℓ) le_rfl
    calc c ≤ min (ℓ • F.stageHeight (G a) + d) (ℓ • F.stageHeight (∑ p ∈ t, G p) + d) :=
          le_min (hall a (Finset.mem_cons_self a t))
            (ih fun p hp => hall p (Finset.mem_cons.2 (Or.inr hp)))
      _ = ℓ • min (F.stageHeight (G a)) (F.stageHeight (∑ p ∈ t, G p)) + d :=
          (hmono.map_min).symm
      _ ≤ ℓ • F.stageHeight (G a + ∑ p ∈ t, G p) + d :=
          hmono (F.min_stageHeight_le_add _ _)

/-! ## Part 3 — the one-step MacLane expansion (the carry compensation)

The private core is the NON-CANCELLATION witness: adding a remainder of degree below the key
cannot raise the stage value of `q·Φ′` past itself, because the product side's RIGHT endpoint
(≥ `deg Φ′` by B39a's endpoint additivity and the frame key's purity) is an abscissa the
remainder cannot reach. -/

/-- **The non-cancellation core (private).**  For `q ≠ 0` and `deg r < deg Φ′`,
`dv(r + q·Φ′) ≤ dv(q·Φ′)`: witnessed at the right endpoint of the side of `q·Φ′`. -/
private theorem stageHeight_add_mul_key_le (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) {q r : Polynomial O} (hq : q ≠ 0)
    (hr : r.natDegree < F.key.natDegree) :
    F.stageHeight (r + q * F.key) ≤ F.stageHeight (q * F.key) := by
  have hd : 0 < (X : Polynomial O).natDegree := by
    rw [natDegree_X]; exact Nat.one_pos
  have hkey0 : F.key ≠ 0 := F.hmonic.ne_zero
  have hqk : q * F.key ≠ 0 := mul_ne_zero hq hkey0
  have htq : suppVal X q F.h F.e₁ ≠ ⊤ := suppVal_ne_top_of_ne_zero monic_X hd hq
  have htk : suppVal X F.key F.h F.e₁ ≠ ⊤ := suppVal_ne_top_of_ne_zero monic_X hd hkey0
  have htqk : suppVal X (q * F.key) F.h F.e₁ ≠ ⊤ := suppVal_ne_top_of_ne_zero monic_X hd hqk
  have hnq : (sideSet X q F.h F.e₁).Nonempty := sideSet_nonempty_gen _ _ _ _
  have hnk : (sideSet X F.key F.h F.e₁).Nonempty := F.hne
  have hnqk : (sideSet X (q * F.key) F.h F.e₁).Nonempty := sideSet_nonempty_gen _ _ _ _
  obtain ⟨Hq, hHq⟩ := exists_sideMin_height F.he₁ htq hnq
  obtain ⟨Hk, hHk⟩ := exists_sideMin_height F.he₁ htk hnk
  -- the right endpoint of `q·Φ′`'s side is at least `deg Φ′`
  have hminmul := sideMin_mul_gen hπ isKey_X hh F.he₁ F.hcop htq htk hnq hnk hHq hHk hnqk
  have hdegmul := sideDeg_mul_gen hπ isKey_X hh F.he₁ F.hcop htq htk hnq hnk hHq hHk hnqk
  have hmaxk := sideMax_eq F.he₁ F.hcop htk hnk
  have hmaxqk := sideMax_eq F.he₁ F.hcop htqk hnqk
  have hpure2 : OnSide X F.key F.h F.e₁ F.key.natDegree := by
    have h := F.hpure.2
    rwa [natDegree_X, Nat.div_one] at h
  have hdegk_le : F.key.natDegree ≤ sideMax X F.key F.h F.e₁ hnk :=
    Finset.le_max' _ _ (mem_sideSet_of_onSide monic_X hd F.he₁ htk hpure2)
  have hage : F.key.natDegree ≤ sideMax X (q * F.key) F.h F.e₁ hnqk := by
    rw [hmaxqk, hminmul, hdegmul]
    calc F.key.natDegree
        ≤ sideMin X F.key F.h F.e₁ hnk + F.e₁ * sideDeg X F.key F.h F.e₁ hnk :=
          hmaxk ▸ hdegk_le
      _ ≤ (sideMin X F.key F.h F.e₁ hnk + F.e₁ * sideDeg X F.key F.h F.e₁ hnk)
            + (sideMin X q F.h F.e₁ hnq + F.e₁ * sideDeg X q F.h F.e₁ hnq) :=
          Nat.le_add_right _ _
      _ = sideMin X q F.h F.e₁ hnq + sideMin X F.key F.h F.e₁ hnk
            + F.e₁ * (sideDeg X q F.h F.e₁ hnq + sideDeg X F.key F.h F.e₁ hnk) := by ring
  -- read the support value of `q·Φ′` at that endpoint
  set a := sideMax X (q * F.key) F.h F.e₁ hnqk with ha
  have hona : OnSide X (q * F.key) F.h F.e₁ a :=
    onSide_of_mem_sideSet (Finset.max'_mem _ hnqk)
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide F.he₁ htqk hona)
  have hread : suppVal X (q * F.key) F.h F.e₁ = ((F.e₁ * Ha + F.h * a : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHa.symm hona
  -- the remainder cannot reach the endpoint abscissa
  have hnp : npHgt X (r + q * F.key) a = npHgt X (q * F.key) a := by
    rw [npHgt, npHgt, dev_X, dev_X, coeff_add,
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hr hage), zero_add]
  calc F.stageHeight (r + q * F.key)
      ≤ F.e₁ • npHgt X (r + q * F.key) a + ((F.h * a : ℕ) : ℕ∞) :=
        suppVal_le_weight monic_X hd F.he₁ F.h (r + q * F.key) a
    _ = ((F.e₁ * Ha + F.h * a : ℕ) : ℕ∞) := by
        rw [hnp, ← hHa, nsmul_add_cast_gen]
    _ = F.stageHeight (q * F.key) := hread.symm

/-- **Both one-step expansion inequalities (private)**: the stage value of `w` is at most
that of its reduced remainder AND at most that of its quotient term. -/
private theorem stageHeight_le_parts (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) (w : Polynomial O) :
    F.stageHeight w ≤ F.stageHeight (w %ₘ F.key)
      ∧ F.stageHeight w ≤ F.stageHeight ((w /ₘ F.key) * F.key) := by
  have hdec : w %ₘ F.key + (w /ₘ F.key) * F.key = w := by
    have h := modByMonic_add_div w F.key
    rw [mul_comm F.key (w /ₘ F.key)] at h
    exact h
  by_cases hq0 : w /ₘ F.key = 0
  · have heq : w %ₘ F.key = w := by
      rw [hq0, zero_mul, add_zero] at hdec
      exact hdec
    constructor
    · rw [heq]
    · rw [hq0, zero_mul, F.stageHeight_zero]
      exact le_top
  by_cases hr0 : w %ₘ F.key = 0
  · have heq : (w /ₘ F.key) * F.key = w := by
      rw [hr0, zero_add] at hdec
      exact hdec
    constructor
    · rw [hr0, F.stageHeight_zero]
      exact le_top
    · rw [heq]
  have hd : 0 < (X : Polynomial O).natDegree := by rw [natDegree_X]; exact Nat.one_pos
  have hrdeg : (w %ₘ F.key).natDegree < F.key.natDegree :=
    natDegree_lt_natDegree hr0 (degree_modByMonic_lt w F.hmonic)
  rcases eq_or_ne (F.stageHeight (w %ₘ F.key)) (F.stageHeight ((w /ₘ F.key) * F.key))
    with heq | hne
  · -- tie: the non-cancellation core
    have hcore : F.stageHeight w ≤ F.stageHeight ((w /ₘ F.key) * F.key) := by
      conv_lhs => rw [← hdec]
      exact stageHeight_add_mul_key_le hπ F hh hq0 hrdeg
    refine ⟨?_, hcore⟩
    rw [heq]
    exact hcore
  · -- off tie: the landed ultrametric equality
    have hne' : suppVal X (w %ₘ F.key) F.h F.e₁
        ≠ suppVal X ((w /ₘ F.key) * F.key) F.h F.e₁ := hne
    have hmin : F.stageHeight w
        = min (F.stageHeight (w %ₘ F.key)) (F.stageHeight ((w /ₘ F.key) * F.key)) := by
      conv_lhs => rw [← hdec]
      exact suppVal_add_eq monic_X hd F.he₁ F.h hne'
    constructor
    · rw [hmin]
      exact min_le_left _ _
    · rw [hmin]
      exact min_le_right _ _

/-- **One-step expansion, remainder half**: `dv(w) ≤ dv(w %ₘ Φ′)`. -/
theorem stageHeight_le_modByMonic (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) (w : Polynomial O) :
    F.stageHeight w ≤ F.stageHeight (w %ₘ F.key) :=
  (stageHeight_le_parts hπ F hh w).1

/-- **One-step expansion, carry half**: `dv(w) ≤ dv(w /ₘ Φ′) + dv(Φ′)`. -/
theorem stageHeight_le_divByMonic (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) (w : Polynomial O) :
    F.stageHeight w ≤ F.stageHeight (w /ₘ F.key) + F.stageHeight F.key := by
  have h := (stageHeight_le_parts hπ F hh w).2
  rwa [stageHeight_mul hπ F hh] at h

/-- ★ **The one-step MacLane expansion is EXACT**: the stage value of any `w` is the minimum
of its two `Φ′`-adic parts' values.  (`≥` is the ultrametric; `≤` on each part is the
non-cancellation content proved above.) -/
theorem stageHeight_eq_min_mod_div (hπ : Irreducible π) (F : KeyFrame O π)
    (hh : 0 < F.h) (w : Polynomial O) :
    F.stageHeight w
      = min (F.stageHeight (w %ₘ F.key)) (F.stageHeight (w /ₘ F.key) + F.stageHeight F.key) := by
  refine le_antisymm
    (le_min (stageHeight_le_modByMonic hπ F hh w) (stageHeight_le_divByMonic hπ F hh w)) ?_
  have hdec : w %ₘ F.key + (w /ₘ F.key) * F.key = w := by
    have h := modByMonic_add_div w F.key
    rw [mul_comm F.key (w /ₘ F.key)] at h
    exact h
  calc min (F.stageHeight (w %ₘ F.key)) (F.stageHeight (w /ₘ F.key) + F.stageHeight F.key)
      = min (F.stageHeight (w %ₘ F.key)) (F.stageHeight ((w /ₘ F.key) * F.key)) := by
        rw [stageHeight_mul hπ F hh]
    _ ≤ F.stageHeight (w %ₘ F.key + (w /ₘ F.key) * F.key) := F.min_stageHeight_le_add _ _
    _ = F.stageHeight w := by rw [hdec]

/-! ### 3a. The outer development of a short polynomial has two slots -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Slot 0 of the outer development is the reduced remainder (B.02 anti-drift pin). -/
theorem dev_zero_pin (φ A : Polynomial O) : dev φ A 0 = A %ₘ φ := rfl

/-- Slot 1 of the outer development of a SHORT polynomial (degree `< 2·deg Φ′`) is the bare
quotient: the quotient is already reduced. -/
theorem dev_one_of_natDegree_lt (F : KeyFrame O π) {w : Polynomial O}
    (hw : w.natDegree < 2 * F.key.natDegree) :
    dev F.key w 1 = w /ₘ F.key := by
  show (w /ₘ F.key) %ₘ F.key = w /ₘ F.key
  by_cases hq0 : w /ₘ F.key = 0
  · rw [hq0, zero_modByMonic]
  refine (modByMonic_eq_self_iff F.hmonic).2 ?_
  have hdeg : (w /ₘ F.key).natDegree < F.key.natDegree := by
    rw [natDegree_divByMonic w F.hmonic]
    omega
  calc (w /ₘ F.key).degree = ((w /ₘ F.key).natDegree : WithBot ℕ) := degree_eq_natDegree hq0
    _ < (F.key.natDegree : WithBot ℕ) := by exact_mod_cast hdeg
    _ = F.key.degree := (degree_eq_natDegree F.hmonic.ne_zero).symm

/-- Beyond slot 1 the outer development of a short polynomial vanishes. -/
theorem dev_eq_zero_of_short (F : KeyFrame O π) {w : Polynomial O}
    (hw : w.natDegree < 2 * F.key.natDegree) {s : ℕ} (hs : 2 ≤ s) :
    dev F.key w s = 0 := by
  refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos w s ?_
  calc w.natDegree < 2 * F.key.natDegree := hw
    _ ≤ s * F.key.natDegree := Nat.mul_le_mul_right _ hs

/-! ### 3b. The per-slot carry compensation (the admissibility bridge) -/

/-- **The per-slot bridge**: under the augmentation admissibility `ℓ·dv(Φ′) ≤ u`, the
`(u, ℓ)`-weight of every outer slot of a short `w` dominates `ℓ·dv(w)`. -/
theorem le_weight_dev_slot (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm : ℓ * V ≤ u) {w : Polynomial O} (hw : w.natDegree < 2 * F.key.natDegree)
    (s : ℕ) :
    ℓ • F.stageHeight w ≤ ℓ • F.stageHeight (dev F.key w s) + (u * s : ℕ∞) := by
  match s with
  | 0 =>
    rw [dev_zero_pin]
    calc ℓ • F.stageHeight w ≤ ℓ • F.stageHeight (w %ₘ F.key) :=
          nsmul_le_nsmul_right (stageHeight_le_modByMonic hπ F hh w) ℓ
      _ ≤ ℓ • F.stageHeight (w %ₘ F.key) + (u * 0 : ℕ∞) := le_self_add
  | 1 =>
    rw [dev_one_of_natDegree_lt F hw]
    calc ℓ • F.stageHeight w
        ≤ ℓ • (F.stageHeight (w /ₘ F.key) + F.stageHeight F.key) :=
          nsmul_le_nsmul_right (stageHeight_le_divByMonic hπ F hh w) ℓ
      _ = ℓ • F.stageHeight (w /ₘ F.key) + ℓ • F.stageHeight F.key := nsmul_add _ _ ℓ
      _ = ℓ • F.stageHeight (w /ₘ F.key) + ((ℓ * V : ℕ) : ℕ∞) := by
          rw [hV, nsmul_eq_mul]; push_cast; ring
      _ ≤ ℓ • F.stageHeight (w /ₘ F.key) + (u * 1 : ℕ∞) := by
          refine add_le_add le_rfl ?_
          rw [mul_one]
          exact_mod_cast hadm
  | (s + 2) =>
    rw [dev_eq_zero_of_short F hw (by omega), F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top

/-- **The per-slot bridge, strict at the carries**: with STRICT admissibility `ℓ·dv(Φ′) < u`,
every POSITIVE outer slot of a short `w` weighs strictly more than `ℓ·dv(w)`. -/
theorem lt_weight_dev_slot (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm' : ℓ * V < u) {w : Polynomial O} (hw : w.natDegree < 2 * F.key.natDegree)
    {s : ℕ} (hs : 0 < s) :
    ℓ • F.stageHeight w + 1 ≤ ℓ • F.stageHeight (dev F.key w s) + (u * s : ℕ∞) := by
  match s with
  | 1 =>
    rw [dev_one_of_natDegree_lt F hw]
    rcases eq_or_ne (F.stageHeight (w /ₘ F.key)) ⊤ with hT | hT
    · rw [hT, C118a.smul_top_pos hℓ, top_add]
      exact le_top
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hT
    have hle : F.stageHeight w ≤ ((c + V : ℕ) : ℕ∞) := by
      calc F.stageHeight w ≤ F.stageHeight (w /ₘ F.key) + F.stageHeight F.key :=
            stageHeight_le_divByMonic hπ F hh w
        _ = ((c + V : ℕ) : ℕ∞) := by rw [← hc, hV]; push_cast; ring
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top _) hle)
    have hac : a ≤ c + V := by rw [← ha] at hle; exact_mod_cast hle
    rw [← ha, ← hc, nsmul_eq_mul, nsmul_eq_mul]
    have hnat : ℓ * a + 1 ≤ ℓ * c + u * 1 := by
      have h1 : ℓ * a ≤ ℓ * (c + V) := Nat.mul_le_mul_left ℓ hac
      have h2 : ℓ * (c + V) = ℓ * c + ℓ * V := by ring
      omega
    exact_mod_cast hnat
  | (s + 2) =>
    rw [dev_eq_zero_of_short F hw (by omega), F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top

/-! ## Part 4 — the convolution term estimates (both directions) -/

/-- ★ **The endpoint term's EXACT value** (both directions at once): the stage value of the
product of two finite-height outer digits is the SUM of their heights — the level-one product
law read on the convolution's surviving term. -/
theorem stageHeight_dev_mul_eq (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {g z : Polynomial O} {j i Ha Hb : ℕ}
    (hHa : dvHgt F g j = (Ha : ℕ∞)) (hHb : dvHgt F z i = (Hb : ℕ∞)) :
    F.stageHeight (dev F.key g j * dev F.key z i) = ((Ha + Hb : ℕ) : ℕ∞) := by
  rw [stageHeight_mul hπ F hh]
  have h1 : F.stageHeight (dev F.key g j) = (Ha : ℕ∞) := hHa
  have h2 : F.stageHeight (dev F.key z i) = (Hb : ℕ∞) := hHb
  rw [h1, h2]
  push_cast
  ring

/-- A product of two outer digits is SHORT (degree `< 2·deg Φ′`). -/
theorem natDegree_dev_mul_lt (F : KeyFrame O π) {g z : Polynomial O} {j i : ℕ}
    (hgj : dev F.key g j ≠ 0) (hzi : dev F.key z i ≠ 0) :
    (dev F.key g j * dev F.key z i).natDegree < 2 * F.key.natDegree := by
  rw [natDegree_mul hgj hzi]
  have h1 : (dev F.key g j).natDegree < F.key.natDegree :=
    natDegree_lt_natDegree hgj (degree_dev_lt F.hmonic F.natDegree_key_pos g j)
  have h2 : (dev F.key z i).natDegree < F.key.natDegree :=
    natDegree_lt_natDegree hzi (degree_dev_lt F.hmonic F.natDegree_key_pos z i)
  omega

/-- ★ **The convolution term estimate** (the `≥`-direction bank, carries included): every
term of the outer convolution of `g·z` weighs at least `Sg + Sz` at every slot `J`.  Needs
the admissibility `ℓ·dv(Φ′) ≤ u` (S2: `2·2 ≤ 5`). -/
theorem le_line_dev_term (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm : ℓ * V ≤ u) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    (J j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i * F.key ^ (j + i)) J)
          + (u * J : ℕ∞) := by
  by_cases hgj : dev F.key g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  by_cases hzi : dev F.key z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1
    (show dvHgt F g j ≠ ⊤ from F.stageHeight_ne_top hgj)
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1
    (show dvHgt F z i ≠ ⊤ from F.stageHeight_ne_top hzi)
  have h1 : Sg ≤ ℓ * Ha + u * j := le_dvWeight hℓ hSg hHa.symm
  have h2 : Sz ≤ ℓ * Hb + u * i := le_dvWeight hℓ hSz hHb.symm
  have hw : F.stageHeight (dev F.key g j * dev F.key z i) = ((Ha + Hb : ℕ) : ℕ∞) :=
    stageHeight_dev_mul_eq hπ F hh hHa.symm hHb.symm
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt F.hmonic (j + i) _ J hJlt, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow F.hmonic (j + i) _ s]
  have hslot := le_weight_dev_slot hπ F hh hℓ hV hadm (natDegree_dev_mul_lt F hgj hzi) s
  have hstep : ((Sg + Sz : ℕ) : ℕ∞)
      ≤ ℓ • F.stageHeight (dev F.key g j * dev F.key z i) + (u * (j + i) : ℕ∞) := by
    rw [hw, nsmul_eq_mul]
    have hnat : Sg + Sz ≤ ℓ * (Ha + Hb) + u * (j + i) := by
      calc Sg + Sz ≤ (ℓ * Ha + u * j) + (ℓ * Hb + u * i) := Nat.add_le_add h1 h2
        _ = ℓ * (Ha + Hb) + u * (j + i) := by ring
    exact_mod_cast hnat
  refine le_trans hstep (le_trans (add_le_add hslot le_rfl) (le_of_eq ?_))
  push_cast
  ring

/-- ★ **The strict convolution term estimate** (the survival direction): every term of the
outer convolution OTHER than an exact-slot on-side pair weighs at least `Sg + Sz + 1`.  Needs
STRICT admissibility `ℓ·dv(Φ′) < u` (S2: `4 < 5`). -/
theorem lt_line_dev_term (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm' : ℓ * V < u) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {J j i : ℕ} (hbad : ¬ (j + i = J ∧ DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞)
      ≤ ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i * F.key ^ (j + i)) J)
          + (u * J : ℕ∞) := by
  by_cases hgj : dev F.key g j = 0
  · rw [hgj, zero_mul, zero_mul, dev_of_zero, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  by_cases hzi : dev F.key z i = 0
  · rw [hzi, mul_zero, zero_mul, dev_of_zero, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨Ha, hHa⟩ := ENat.ne_top_iff_exists.1
    (show dvHgt F g j ≠ ⊤ from F.stageHeight_ne_top hgj)
  obtain ⟨Hb, hHb⟩ := ENat.ne_top_iff_exists.1
    (show dvHgt F z i ≠ ⊤ from F.stageHeight_ne_top hzi)
  have hw : F.stageHeight (dev F.key g j * dev F.key z i) = ((Ha + Hb : ℕ) : ℕ∞) :=
    stageHeight_dev_mul_eq hπ F hh hHa.symm hHb.symm
  rcases Nat.lt_or_ge J (j + i) with hJlt | hJge
  · rw [dev_mul_pow_of_lt F.hmonic (j + i) _ J hJlt, F.stageHeight_zero,
      C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hJge
  rw [dev_mul_pow F.hmonic (j + i) _ s]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- exact slot: one factor is off-side, so its weight is strict
    have hoff : ¬ DvOnSide F g u ℓ j ∨ ¬ DvOnSide F z u ℓ i := by
      by_contra hcon
      push Not at hcon
      exact hbad ⟨by omega, hcon.1, hcon.2⟩
    have hstrict : Sg + Sz + 1 ≤ ℓ * (Ha + Hb) + u * (j + i) := by
      rcases hoff with hng | hnz
      · have h1 : Sg < ℓ * Ha + u * j := lt_dvWeight hℓ hSg hHa.symm hng
        have h2 : Sz ≤ ℓ * Hb + u * i := le_dvWeight hℓ hSz hHb.symm
        calc Sg + Sz + 1 ≤ (ℓ * Ha + u * j) + (ℓ * Hb + u * i) := by omega
          _ = ℓ * (Ha + Hb) + u * (j + i) := by ring
      · have h1 : Sg ≤ ℓ * Ha + u * j := le_dvWeight hℓ hSg hHa.symm
        have h2 : Sz < ℓ * Hb + u * i := lt_dvWeight hℓ hSz hHb.symm hnz
        calc Sg + Sz + 1 ≤ (ℓ * Ha + u * j) + (ℓ * Hb + u * i) := by omega
          _ = ℓ * (Ha + Hb) + u * (j + i) := by ring
    have hmod := stageHeight_le_modByMonic hπ F hh (dev F.key g j * dev F.key z i)
    rw [hw] at hmod
    have hstep : ((Sg + Sz + 1 : ℕ) : ℕ∞)
        ≤ ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 0)
            + (u * (j + i) : ℕ∞) := by
      refine le_trans ?_ (add_le_add (nsmul_le_nsmul_right
        (show ((Ha + Hb : ℕ) : ℕ∞) ≤ F.stageHeight
          (dev F.key (dev F.key g j * dev F.key z i) 0) by
            rw [dev_zero_pin]; exact hmod) ℓ) le_rfl)
      rw [nsmul_eq_mul]
      exact_mod_cast hstrict
    refine le_trans hstep (le_of_eq ?_)
    push_cast
    ring
  · -- carry slot: strict admissibility supplies the slack
    have h1 : Sg ≤ ℓ * Ha + u * j := le_dvWeight hℓ hSg hHa.symm
    have h2 : Sz ≤ ℓ * Hb + u * i := le_dvWeight hℓ hSz hHb.symm
    have hslot := lt_weight_dev_slot hπ F hh hℓ hV hadm'
      (natDegree_dev_mul_lt F hgj hzi) hs
    have hstep : ((Sg + Sz + 1 : ℕ) : ℕ∞)
        ≤ (ℓ • F.stageHeight (dev F.key g j * dev F.key z i) + 1)
            + (u * (j + i) : ℕ∞) := by
      rw [hw, nsmul_eq_mul]
      have hnat : Sg + Sz + 1 ≤ (ℓ * (Ha + Hb) + 1) + u * (j + i) := by
        have h3 : Sg + Sz ≤ (ℓ * Ha + u * j) + (ℓ * Hb + u * i) := Nat.add_le_add h1 h2
        have h4 : (ℓ * Ha + u * j) + (ℓ * Hb + u * i)
            = ℓ * (Ha + Hb) + u * (j + i) := by ring
        omega
      exact_mod_cast hnat
    refine le_trans hstep (le_trans (add_le_add hslot le_rfl) (le_of_eq ?_))
    push_cast
    ring

/-- Weight-to-height extraction (for NV-3's ultrametric step): a strict weight bound at a
slot on the line extracts a strict height bound. -/
theorem succ_le_of_weight_succ_le {ℓ u J c : ℕ} {x : ℕ∞}
    (h : ((ℓ * c + u * J + 1 : ℕ) : ℕ∞) ≤ ℓ • x + (u * J : ℕ∞)) :
    ((c : ℕ) : ℕ∞) + 1 ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [weight_read] at h
  have hnat : ℓ * c + u * J + 1 ≤ ℓ * a + u * J := by exact_mod_cast h
  have : c + 1 ≤ a := by
    have hca : ℓ * c < ℓ * a := by omega
    have := Nat.lt_of_mul_lt_mul_left hca
    omega
  exact_mod_cast this

/-! ## Part 5 — the endpoint theorem -/

/-- ★ **NODE NV-2, the `≥` direction (the level-two B.33)**: the cleared level-two support of
a product dominates the sum of the supports — UNIVERSAL, all zero cases included.  Under the
frame's admissibility, every slot of `g·z` weighs at least `Sg + Sz`, by the double
development, the finite-sum ultrametric, and the carry-compensated term estimate. -/
theorem dvSupp_add_le_dvSupp_mul (hπ : Irreducible π) (F : KeyFrame O π) (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm : ℓ * V ≤ u) (g z : Polynomial O) :
    dvSupp F g u ℓ + dvSupp F z u ℓ ≤ dvSupp F (g * z) u ℓ := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [zero_mul, dvSupp_zero_eq_top F u hℓ]
    exact le_top
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, dvSupp_zero_eq_top F u hℓ]
    exact le_top
  obtain ⟨Sg, hSg⟩ := ENat.ne_top_iff_exists.1 (dvSupp_ne_top_of_ne_zero F u ℓ hg)
  obtain ⟨Sz, hSz⟩ := ENat.ne_top_iff_exists.1 (dvSupp_ne_top_of_ne_zero F u ℓ hz)
  rw [← hSg, ← hSz, ← Nat.cast_add]
  -- the double development of the product
  have hkeypos := F.natDegree_key_pos
  set N := g.natDegree + z.natDegree + 1 with hN
  have hgN : g.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hzN : z.natDegree < N * F.key.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hkeypos)
  have hgrep : ∑ j ∈ Finset.range N, dev F.key g j * F.key ^ j = g :=
    sum_dev_eq F.hmonic hkeypos g hgN
  have hzrep : ∑ i ∈ Finset.range N, dev F.key z i * F.key ^ i = z :=
    sum_dev_eq F.hmonic hkeypos z hzN
  have hrep : g * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2) := by
    have h1 : g * z = (∑ j ∈ Finset.range N, dev F.key g j * F.key ^ j)
        * (∑ i ∈ Finset.range N, dev F.key z i * F.key ^ i) := by rw [hgrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  -- every slot weighs at least Sg + Sz
  rw [dvSupp]
  refine Finset.le_inf fun J _ => ?_
  have hdev : dvHgt F (g * z) J
      = F.stageHeight (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) J) := by
    show F.stageHeight (dev F.key (g * z) J) = _
    rw [show dev F.key (g * z) J = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) J by
      conv_lhs => rw [hrep]
      exact dev_finsetSum F.hmonic _ _ J]
  rw [hdev]
  exact le_weight_stageHeight_sum F hℓ _ _
    (fun p _ => le_line_dev_term hπ F hh hℓ hV hadm hSg.symm hSz.symm J p.1 p.2)

section Endpoint

variable {F : KeyFrame O π} {u ℓ : ℕ} {g z : Polynomial O}

/-- ★ **NODE NV-2, the endpoint lemma (value form)**: given NV-3's endpoint height bound —
the outer digit of `g·z` at the SUM of the chosen minimizers has stage value at most
`Hg + Hz` — the product's cleared support is EXACTLY the sum of the factors' supports, read
at that slot.  (The `≥` half is `dvSupp_add_le_dvSupp_mul`; the `≤` half is the endpoint
weight.) -/
theorem dvSupp_mul_of_endpoint_le (hπ : Irreducible π) (hh : 0 < F.h)
    (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm : ℓ * V ≤ u)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞))
    (hup : F.stageHeight (dev F.key (g * z)
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞)) :
    dvSupp F (g * z) u ℓ
      = ((ℓ * (Hg + Hz) + u * (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz) : ℕ) : ℕ∞) := by
  set jg := dvSideMin F g u ℓ hng with hjg
  set jz := dvSideMin F z u ℓ hnz with hjz
  have hSg : dvSupp F g u ℓ = ((ℓ * Hg + u * jg : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin F g u ℓ hng)
  have hSz : dvSupp F z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin F z u ℓ hnz)
  refine le_antisymm ?_ ?_
  · -- ≤ : the endpoint slot's weight
    refine le_trans (dvSupp_le_term F (g * z) u hℓ (jg + jz)) ?_
    refine le_trans (add_le_add (nsmul_le_nsmul_right hup ℓ) le_rfl) (le_of_eq ?_)
    rw [nsmul_eq_mul]
    push_cast
    ring
  · -- ≥ : the universal product inequality
    refine le_trans (le_of_eq ?_) (dvSupp_add_le_dvSupp_mul hπ F hh hℓ hV hadm g z)
    rw [hSg, hSz]
    push_cast
    ring

/-- ★ **NODE NV-2, the endpoint lemma (minimizer form)**: under the same endpoint height
bound, the sum of the chosen minimizers IS a product minimizer. -/
theorem dvOnSide_mul_endpoint (hπ : Irreducible π) (hh : 0 < F.h)
    (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm : ℓ * V ≤ u)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞))
    (hup : F.stageHeight (dev F.key (g * z)
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞)) :
    DvOnSide F (g * z) u ℓ (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz) := by
  set jg := dvSideMin F g u ℓ hng with hjg
  set jz := dvSideMin F z u ℓ hnz with hjz
  have hval := dvSupp_mul_of_endpoint_le hπ hh hℓ hV hadm hng hnz hHg hHz hup
  have hup' : dvHgt F (g * z) (jg + jz) ≤ ((Hg + Hz : ℕ) : ℕ∞) := hup
  -- the endpoint height is exactly Hg + Hz
  have hlow := dvSupp_le_term F (g * z) u hℓ (jg + jz)
  rw [hval] at hlow
  have hhgt_ne : dvHgt F (g * z) (jg + jz) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hup'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hhgt_ne
  have hcle : c ≤ Hg + Hz := by
    rw [← hc] at hup'
    exact_mod_cast hup'
  have hcge : Hg + Hz ≤ c := by
    rw [← hc, nsmul_eq_mul] at hlow
    have hnat : ℓ * (Hg + Hz) + u * (jg + jz) ≤ ℓ * c + u * (jg + jz) := by
      exact_mod_cast hlow
    have hmul : ℓ * (Hg + Hz) ≤ ℓ * c := by omega
    exact Nat.le_of_mul_le_mul_left hmul hℓ
  have hcexact : dvHgt F (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [← hc]
    exact_mod_cast (show c = Hg + Hz by omega)
  refine ⟨?_, by rw [hcexact]; exact ENat.coe_ne_top _⟩
  rw [hval, hcexact, nsmul_eq_mul]
  push_cast
  ring

/-- The chosen product minimizer is BOUNDED BY the sum of the factors' minimizers (the
row's "(a slot bounded by)" clause; the reverse bound is NV-3's decomposition). -/
theorem dvSideMin_mul_le (hπ : Irreducible π) (hh : 0 < F.h)
    (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm : ℓ * V ≤ u)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞))
    (hup : F.stageHeight (dev F.key (g * z)
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞))
    (hne : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMin F (g * z) u ℓ hne ≤ dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz :=
  dvSideMin_le_of_dvOnSide hne
    (dvOnSide_mul_endpoint hπ hh hℓ hV hadm hng hnz hHg hHz hup)

/-- ★ **The NV-4 consumption shape**: given NV-3's endpoint height bound, the level-two
product law fires — `dvSupp (g·z) = dvSupp g + dvSupp z`. -/
theorem dvSupp_mul_eq_add_of_endpoint_le (hπ : Irreducible π) (hh : 0 < F.h)
    (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm : ℓ * V ≤ u)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dvHgt F g (dvSideMin F g u ℓ hng) = (Hg : ℕ∞))
    (hHz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Hz : ℕ∞))
    (hup : F.stageHeight (dev F.key (g * z)
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz)) ≤ ((Hg + Hz : ℕ) : ℕ∞)) :
    dvSupp F (g * z) u ℓ = dvSupp F g u ℓ + dvSupp F z u ℓ := by
  rw [dvSupp_mul_of_endpoint_le hπ hh hℓ hV hadm hng hnz hHg hHz hup,
    dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin F g u ℓ hng),
    dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin F z u ℓ hnz)]
  push_cast
  ring

end Endpoint

end Generic

/-! ## Part 6 — the S2 instantiation (all side conditions discharged) -/

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- The S2 frame's slope numerator is positive (the engine's `hh`, discharged). -/
theorem s2_h_pos : 0 < (s2Frame h2 hq).h := by
  rw [C35b.h_eq h2 hq]
  exact Nat.one_pos

/-- **The S2 frame key's stage value**: `dv(Φ′) = dv(x² − 2) = min(2·1 + 0, ⊤, 0 + 2) = 2`.
With the S2 level-two side `(u₂, ℓ₂) = (5, 2)` this discharges the admissibility
`ℓ₂ · dv(Φ′) = 4 ≤ 5 = u₂` — STRICTLY, so the strict bank fires too. -/
theorem s2_stageHeight_key :
    (s2Frame h2 hq).stageHeight ((s2Frame h2 hq).key) = ((2 : ℕ) : ℕ∞) := by
  rw [KeyFrame.stageHeight_eq_inf]
  have hdeg : ((s2Frame h2 hq).key : Polynomial O).natDegree = 2 := by
    rw [C35b.key_eq h2 hq, s2Key_natDegree]
  rw [hdeg, show Finset.range (2 + 1) = {0, 1, 2} by decide,
    Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton]
  have hc0 : ((s2Frame h2 hq).key : Polynomial O).coeff 0 = -2 := by
    rw [C35b.key_eq h2 hq]; exact s2Key_coeff0
  have hc1 : ((s2Frame h2 hq).key : Polynomial O).coeff 1 = 0 := by
    rw [C35b.key_eq h2 hq]; exact s2Key_coeff1
  have hc2 : ((s2Frame h2 hq).key : Polynomial O).coeff 2 = 1 := by
    rw [C35b.key_eq h2 hq]; exact s2Key_coeff2
  rw [hc0, hc1, hc2, C35b.e1_eq h2 hq, C35b.h_eq h2 hq]
  have hg0 : gaussVal (Polynomial.C (-2 : O)) = (1 : ℕ∞) := by
    rw [gaussVal_C, C131y.addVal_neg]
    have h := C35b.addVal_two_pow h2 1
    rwa [pow_one, Nat.cast_one] at h
  have hg1 : gaussVal (Polynomial.C (0 : O)) = ⊤ := by
    rw [map_zero]
    exact gaussVal_eq_top_iff.2 rfl
  have hg2 : gaussVal (Polynomial.C (1 : O)) = (0 : ℕ∞) := by
    rw [gaussVal_C, addVal_one h2]
  rw [hg0, hg1, hg2, C118a.smul_top_pos (by norm_num : (0 : ℕ) < 2), top_add,
    min_eq_right le_top]
  simp [nsmul_eq_mul]

/-- ★ **The S2 `≥` direction, fully discharged**: at the S2 frame and level-two side
`(5, 2)`, the cleared level-two support of a product dominates the sum — UNIVERSAL. -/
theorem s2_dvSupp_mul_ge (A B : Polynomial O) :
    dvSupp (s2Frame h2 hq) A 5 2 + dvSupp (s2Frame h2 hq) B 5 2
      ≤ dvSupp (s2Frame h2 hq) (A * B) 5 2 :=
  dvSupp_add_le_dvSupp_mul h2 (s2Frame h2 hq) (s2_h_pos h2 hq) (by norm_num)
    (s2_stageHeight_key h2 hq) (by norm_num) A B

/-- ★ The S2 `≥` direction in the CARRIER (E.10's `WithTop ℤ`, the `s2Hgt₂` table):
`h₂(A) + h₂(B) ≤ h₂(A·B)` for ALL `A B`. -/
theorem s2Hgt₂_mul_ge (A B : Polynomial O) :
    s2Hgt₂ h2 hq A + s2Hgt₂ h2 hq B ≤ s2Hgt₂ h2 hq (A * B) := by
  rw [s2Hgt₂, s2Hgt₂, s2Hgt₂, ← toZ_add]
  exact toZ_le_toZ_iff.mpr (s2_dvSupp_mul_ge h2 hq A B)

/-! ### 6a. Teeth — the endpoint machinery on landed values -/

/-- The landed value `h₂(x) = 2`, read back in `ℕ∞` (via the carrier dictionary). -/
theorem s2_dvSupp_X : dvSupp (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2
    = ((2 : ℕ) : ℕ∞) := by
  refine toZ_inj ?_
  have h := s2Hgt₂_X h2 hq (O := O)
  rw [s2Hgt₂] at h
  rw [h, toZ_coe]
  norm_num

/-- The landed value `h₂(Φ′) = 5 = u₂`, read back in `ℕ∞`. -/
theorem s2_dvSupp_key : dvSupp (s2Frame h2 hq) ((s2Frame h2 hq).key : Polynomial O) 5 2
    = ((5 : ℕ) : ℕ∞) := by
  refine toZ_inj ?_
  have h := s2Hgt₂_key h2 hq (O := O)
  rw [s2Hgt₂] at h
  rw [h, toZ_coe]
  norm_num

/-- **tooth (the endpoint law, end to end)**: `h₂(x · Φ′) = 7 = 2 + 5` — the `≥` half by
`s2_dvSupp_mul_ge`, the `≤` half by the endpoint slot `j = 1`'s weight
`2·dv(x) + 5·1 = 7`. -/
theorem s2_dvSupp_X_mul_key :
    dvSupp (s2Frame h2 hq) ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 5 2
      = ((7 : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · -- ≤ 7: the weight at slot 1
    have hdev : dev ((s2Frame h2 hq).key) ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 1
        = Polynomial.X := by
      have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (Polynomial.X : Polynomial O) 0
      rw [pow_one, Nat.add_zero] at h
      rw [h, dev_zero_pin]
      refine (modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).2 ?_
      have hdeg : ((s2Frame h2 hq).key : Polynomial O).degree = 2 := by
        rw [C35b.key_eq h2 hq]
        exact degree_X_pow_sub_C (by norm_num) 2
      rw [hdeg, Polynomial.degree_X]
      norm_num
    have hle := dvSupp_le_term (s2Frame h2 hq)
      ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 5 (by norm_num : (0 : ℕ) < 2) 1
    have hhgt : dvHgt (s2Frame h2 hq)
        ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 1 = ((1 : ℕ) : ℕ∞) := by
      show (s2Frame h2 hq).stageHeight
        (dev ((s2Frame h2 hq).key) ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key) 1)
        = ((1 : ℕ) : ℕ∞)
      rw [hdev, C35b.sh_X h2 hq]
      rfl
    rw [hhgt, weight_read] at hle
    exact le_trans hle (by norm_num)
  · -- 7 ≤: the universal product inequality
    have h := s2_dvSupp_mul_ge h2 hq (Polynomial.X : Polynomial O) ((s2Frame h2 hq).key)
    rw [s2_dvSupp_X h2 hq, s2_dvSupp_key h2 hq, ← Nat.cast_add] at h
    exact_mod_cast h

/-- **tooth (carrier form)**: `h₂(x·Φ′) = 7` in the `s2Hgt₂` table — a NEW table value
produced by the NV-2 endpoint machinery alone. -/
theorem s2Hgt₂_X_mul_key :
    s2Hgt₂ h2 hq ((Polynomial.X : Polynomial O) * (s2Frame h2 hq).key)
      = ((7 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₂, s2_dvSupp_X_mul_key h2 hq, toZ_coe]
  norm_num

end S2

end Uniformity.Density.Tower.C130nv2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130nv2.weight_read
#print axioms Uniformity.Density.Tower.C130nv2.dvOnSide_of_mem_dvSideSet
#print axioms Uniformity.Density.Tower.C130nv2.mem_dvSideSet_of_dvOnSide
#print axioms Uniformity.Density.Tower.C130nv2.dvOnSide_dvSideMin
#print axioms Uniformity.Density.Tower.C130nv2.dvSideMin_le_of_dvOnSide
#print axioms Uniformity.Density.Tower.C130nv2.not_dvOnSide_of_lt_dvSideMin
#print axioms Uniformity.Density.Tower.C130nv2.dvOnSide_endpoint_unique
#print axioms Uniformity.Density.Tower.C130nv2.exists_dvSideMin_height
#print axioms Uniformity.Density.Tower.C130nv2.dvSupp_eq_of_dvOnSide
#print axioms Uniformity.Density.Tower.C130nv2.le_dvWeight
#print axioms Uniformity.Density.Tower.C130nv2.lt_dvWeight
#print axioms Uniformity.Density.Tower.C130nv2.stageHeight_mul
#print axioms Uniformity.Density.Tower.C130nv2.le_weight_stageHeight_sum
#print axioms Uniformity.Density.Tower.C130nv2.stageHeight_le_modByMonic
#print axioms Uniformity.Density.Tower.C130nv2.stageHeight_le_divByMonic
#print axioms Uniformity.Density.Tower.C130nv2.stageHeight_eq_min_mod_div
#print axioms Uniformity.Density.Tower.C130nv2.dev_zero_pin
#print axioms Uniformity.Density.Tower.C130nv2.dev_one_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C130nv2.dev_eq_zero_of_short
#print axioms Uniformity.Density.Tower.C130nv2.le_weight_dev_slot
#print axioms Uniformity.Density.Tower.C130nv2.lt_weight_dev_slot
#print axioms Uniformity.Density.Tower.C130nv2.stageHeight_dev_mul_eq
#print axioms Uniformity.Density.Tower.C130nv2.natDegree_dev_mul_lt
#print axioms Uniformity.Density.Tower.C130nv2.le_line_dev_term
#print axioms Uniformity.Density.Tower.C130nv2.lt_line_dev_term
#print axioms Uniformity.Density.Tower.C130nv2.succ_le_of_weight_succ_le
#print axioms Uniformity.Density.Tower.C130nv2.dvSupp_add_le_dvSupp_mul
#print axioms Uniformity.Density.Tower.C130nv2.dvSupp_mul_of_endpoint_le
#print axioms Uniformity.Density.Tower.C130nv2.dvOnSide_mul_endpoint
#print axioms Uniformity.Density.Tower.C130nv2.dvSideMin_mul_le
#print axioms Uniformity.Density.Tower.C130nv2.dvSupp_mul_eq_add_of_endpoint_le
#print axioms Uniformity.Density.Tower.C130nv2.s2_h_pos
#print axioms Uniformity.Density.Tower.C130nv2.s2_stageHeight_key
#print axioms Uniformity.Density.Tower.C130nv2.s2_dvSupp_mul_ge
#print axioms Uniformity.Density.Tower.C130nv2.s2Hgt₂_mul_ge
#print axioms Uniformity.Density.Tower.C130nv2.s2_dvSupp_X
#print axioms Uniformity.Density.Tower.C130nv2.s2_dvSupp_key
#print axioms Uniformity.Density.Tower.C130nv2.s2_dvSupp_X_mul_key
#print axioms Uniformity.Density.Tower.C130nv2.s2Hgt₂_X_mul_key

end AxCheck
