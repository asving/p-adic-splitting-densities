/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh1
import Uniformity.ChapC.C130rp2
import Uniformity.ChapC.C130rp4
import Uniformity.ChapC.C08
import Uniformity.ChapC.C23
import Uniformity.ChapC.C26

/-!
# Uniformity.ChapC.C133mh3 — `[MH.3, 2026-08-27/28]`: Theorem M LANDED — the root M1′,
the mixed residual product law (τ = 1), and the `fgmn_dv_exact_mul` derivation

**Nodes MH.1 (completion) + MH.2 + MH.3** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md`
§§2–3 at the `[MHFIX 2026-08-27]` state; §9 rows MH.1–MH.3; §9.2 the cite-retirement
payoff).  This file proves, UNCONDITIONALLY (Lean-core footprints throughout):

* **the corrected root M1′, all three clauses** — `m1DigitFaithful`, `m1SlotCarryLaw`,
  `m1TwistProductLaw` discharge the three statement shapes pinned in C133mh1, closing
  MH.1's remaining gap (the doc's one open Lean piece after `verdict_MHFIX`);
* **Theorem M, clauses 1–3** — `dvSupp_mul`, `dvSideMin_mul`/`dvSideMax_mul`/
  `dvSideDeg_mul` (MH.2, including the doc's PROOF-OUTLINE-grade `dvSideMax` half), and
  `dvResPoly_mul_gen` = the τ = 1 mixed residual product law `R(gz) = R(g)·R(z)` for ALL
  nonzero `g, z` (MH.3), packaged as `mixedResidualLaw : MixedResidualLawTauOneStatement`;
* **the §9.2 payoff** — `fgmn_dv_exact_mul_thm`: the declared cite's statement as a
  THEOREM at `0 < F.h` (see the honest-fence note below).

## Architecture (two layers, by design)

Parts 1–9 build the ASSEMBLY layer: everything proved from the single pinned hypothesis
`h1 : C133mh1.M1TwistProductLawStatement O` (`_of_twistLaw` names) — so the assembly is
independently auditable against MH.1's shapes.  Part 10 proves the ROOT itself along the
doc §3.1′'s coefficientwise route: a local FULL read (`fullRead`, the C.21 window without
the `t < f₁` fence), under which the key's symbol dies (`fullRead_key`: `ψ(η) = 0` via
`AdjoinRoot.eval₂_root`, on MH.0a's exact key height, both proved here), and the
convolution law `fullRead_mul_of_le` carries the TW-δ cocycle exactly.  Part 11
instantiates the assembly on the root.

## The honest `h = 0` fence (a statement-level finding of this unit)

`KeyFrame` admits the DEGENERATE `h = 0` frame (C.01's docstring), and the cite
`fgmn_dv_exact_mul` quantifies over it, while Theorem M (doc §2) is `hh : 0 < F.h`-fenced.
`fgmn_dv_exact_mul_thm` therefore carries `hh` as its one extra hypothesis: byte-identical
retirement of the axiom still needs a separate `h = 0` leg (C.05's degenerate dictionary +
the landed order-1 exact chain) — previously unrecorded in §9.2's retirement claim.

No `sorry`, no new axiom, statements of C133mh1's shapes consumed by name (never
restated); C66b untouched.

## Contents

* `m1DigitFaithful` (★ PROVED, unconditional): a digit at exact finite stage height has a
  nonzero ϖ-read — M1′(3), subsuming old M1(1)'s faithfulness content.
* `digit_stageHeight_modKey_of_twistLaw`: M1′'s height form — `dv((a·b) %ₘ Φ′) = ka + kb`
  at exact digit heights (the survival supply for the endpoint assembly), given `h1`.
* Theorem M clauses 1–2 (`_of_twistLaw`): `dvSupp_mul`, `dvSideMin_mul`, `dvSideMax_mul`,
  `dvSideDeg_mul`, and the pin law `dvHgt_dvSideMin_mul` — §3.2's assembly on the landed
  C130nv2 endpoint bank, with the survival head priced by the height form and the
  `dvSideMax` half by the same strict convolution pricing at the `(jmax, jmax)` pair.
* Theorem M clause 3 (`dvResPoly_mul_gen_of_twistLaw`): the mixed residual product law,
  τ = 1, for ALL nonzero `g, z` — §3.3's coefficientwise assembly on `dev_mul_conv_split`
  (C130rp4), the read additivity/vanishing stack (C130rp2/rp4), and `h1` on the surviving
  on-side pairs.  Packaged as `MixedResidualLawTauOneStatement` (the probe's shape,
  declared here — MH.3's territory per `verdict_MH1.md`) via `mixedResidualLaw_of_twistLaw`,
  with the ∃-τ weakening `existsUnit_of_tauOne` for the §2 record.
* **The payoff (§9.2)**: `fgmn_dv_exact_mul_of_twistLaw` — the DECLARED CITE's statement
  (C66b.lean:90) proved from Theorem M: purity closure from clause 2 + the landed C.35
  pure-endpoint lemmas, residual multiplicativity from clause 3.
* **Part 10, THE ROOT** (`fullRead` calculus → `m1SlotCarryLaw`/`m1TwistProductLaw`,
  with `stageHeight_key_eq` = MH.0a, `pin_eq` `H₀ = h·f₁`, `fullRead_key` = `ψ(η) = 0`,
  and `fullRead_mul_of_le` = the TW-δ convolution law) and **Part 11, the unconditional
  instantiations** (`dvSupp_mul` … `dvResPoly_mul_gen`, `mixedResidualLaw`,
  `isDvPure_mul`, `fgmn_dv_exact_mul_thm`).

## DEPENDS

C133mh1 (shapes; TW-δ + bridge available to consumers) · C130nv2 (endpoint bank,
`stageHeight_mul`, division calculus, line pricing) · C130rp2 (read additivity/vanishing,
`dev_mul_endpoint_split` pattern) · C130rp4 (`dev_mul_conv_split`,
`twistRead_finsetSum_of_le`, `le_stageHeight_finsetSum`) · C131y (`dvSupp_le_term`,
strict stability) · C130s6 (`dvSupp` top laws) · C.23 (`slotRes_ne_zero`) · C.26
(residual degree law) · C.35 (pure endpoints) · C.08 (`dvSideLen_eq`, `dvOnSide_modEq`).

**Status:** sorry-free, zero new axiom, footprint Lean-core only (AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh3

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C131y
open Uniformity.Density.Tower.C130nv2 Uniformity.Density.Tower.C130rp2
open Uniformity.Density.Tower.C130rp4 Uniformity.Density.Tower.C133mh1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 0 — D9 plumbing (private; re-declared per the standing convention) -/

/-- Local D9 reconstruction (C.04 exports no global instance; standing convention at
C.04/C.12/C.26/C.47/C.80/C.97/C133mh1). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- Every outer digit is a digit: `deg (dev Φ′ f j) < D′ = e₁f₁` (C.26's private twin). -/
private theorem natDegree_dev_lt_frame (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) :
    (dev F.key f j).natDegree < F.e₁ * F.f₁ := by
  have hpos : 0 < F.key.natDegree := F.natDegree_key_pos
  have hlt : (dev F.key f j).degree < F.key.degree := degree_dev_lt F.hmonic hpos f j
  rw [← F.hdeg]
  rcases eq_or_ne (dev F.key f j) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hpos
  · refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
    rwa [Polynomial.degree_eq_natDegree F.hmonic.ne_zero] at hlt

/-- The frame key's stage height is a natural number `≤ D′·h` (the top coefficient reads
`e₁·v(1) + h·D′`); under the engine's strict floor `ℓ·(D′·h) < u` this yields the C130nv2
bank's strict admissibility data `(V, hV, hadm')` with no MH.0a exactness needed. -/
private theorem exists_key_height_lt (F : KeyFrame O π) {u ℓ : ℕ}
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) :
    ∃ V : ℕ, F.stageHeight F.key = (V : ℕ∞) ∧ ℓ * V < u := by
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 (F.stageHeight_ne_top F.hmonic.ne_zero)
  have htop : F.stageHeight F.key ≤ ((F.h * F.key.natDegree : ℕ) : ℕ∞) := by
    rw [F.stageHeight_eq_inf]
    refine le_trans (Finset.inf_le (Finset.self_mem_range_succ F.key.natDegree)) ?_
    rw [F.hmonic.coeff_natDegree, GateKit.gaussVal_C, addVal_one, smul_zero, zero_add,
      Nat.cast_mul]
  rw [← hV] at htop
  have hVle : V ≤ F.h * F.key.natDegree := by exact_mod_cast htop
  refine ⟨V, hV.symm, ?_⟩
  calc ℓ * V ≤ ℓ * (F.h * F.key.natDegree) := Nat.mul_le_mul_left ℓ hVle
    _ = ℓ * ((F.e₁ * F.f₁) * F.h) := by rw [F.hdeg]; ring
    _ < u := hfloor

/-! ## Part 1 — ★ M1′ clause (3) PROVED: digit read faithfulness (unconditional) -/

/-- ★ **PROVED — `C133mh1.M1DigitFaithfulStatement` holds**: a digit at exact finite stage
height has a nonzero ϖ-read there.  This is M1′ clause (3), discharged from the landed
C.23 `slotRes_ne_zero` (the attained-height nonvanishing) through the C.22 twist (a unit).
One of MH.1's three clauses is hereby CLOSED unconditionally. -/
theorem m1DigitFaithful : C133mh1.M1DigitFaithfulStatement O := by
  intro π F hπ _hh H₀ hpin a ha ka hka
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hη := F.stageLetter_ne_zero hπ H₀ hpin
  have hslot := F.slotRes_ne_zero hπ H₀ hpin ha hka
  have hbody : F.twistRead H₀ hpin ka a
      = (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp ka) * F.slotRes H₀ hpin ka a := rfl
  rw [hbody]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hη)) hslot

/-! ## Part 2 — ℕ∞ weight helpers (private) -/

/-- The non-strict companion of C130nv2's `succ_le_of_weight_succ_le` (single-cast form). -/
private theorem le_of_weight_le {ℓ u J c : ℕ} {x : ℕ∞} (hℓ : 0 < ℓ)
    (h : ((ℓ * c + u * J : ℕ) : ℕ∞) ≤ ℓ • x + ((u * J : ℕ) : ℕ∞)) :
    ((c : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : ℓ * c + u * J ≤ ℓ * a + u * J := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : ℓ * c ≤ ℓ * a) hℓ

set_option linter.unusedVariables false in
/-- The strict companion (single-cast form; positivity carried for signature symmetry). -/
private theorem succ_le_of_weight_succ_le' {ℓ u J c : ℕ} {x : ℕ∞} (hℓ : 0 < ℓ)
    (h : ((ℓ * c + u * J + 1 : ℕ) : ℕ∞) ≤ ℓ • x + ((u * J : ℕ) : ℕ∞)) :
    ((c + 1 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← ha] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : ℓ * c + u * J + 1 ≤ ℓ * a + u * J := by exact_mod_cast h
  have hca : c < a := Nat.lt_of_mul_lt_mul_left (by omega : ℓ * c < ℓ * a)
  exact_mod_cast hca

/-- Off-side slots price strictly above the support line (ℕ∞ form, `⊤` included). -/
private theorem succ_dvSupp_le_of_not_dvOnSide {F : KeyFrame O π} {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {S : ℕ} (hS : dvSupp F f u ℓ = (S : ℕ∞)) {j : ℕ}
    (hoff : ¬ DvOnSide F f u ℓ j) :
    ((S + 1 : ℕ) : ℕ∞) ≤ ℓ • dvHgt F f j + (u * j : ℕ∞) := by
  rcases eq_or_ne (dvHgt F f j) ⊤ with hT | hT
  · rw [hT, C118a.smul_top_pos hℓ, top_add]
    exact le_top
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
  have hlt := lt_dvWeight hℓ hS hH.symm hoff
  rw [← hH, weight_read]
  exact_mod_cast hlt

/-! ## Part 3 — M1′'s height form, given the twist law (the survival supply) -/

/-- **M1′'s height/exactness form** (old M1(1)), given the twist law: the reduced product of
two digits at exact finite heights sits at EXACTLY the added height.  `≥` is landed
(`stageHeight_mul` + the division calculus); `≤` is faithfulness of the nonzero product
read (`m1DigitFaithful` + `twistRead_eq_zero_of_lt`). -/
theorem digit_stageHeight_modKey_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {a b : Polynomial O} (ha : a.natDegree < F.e₁ * F.f₁) (hb : b.natDegree < F.e₁ * F.f₁)
    {ka kb : ℕ} (hka : F.stageHeight a = (ka : ℕ∞)) (hkb : F.stageHeight b = (kb : ℕ∞)) :
    F.stageHeight ((a * b) %ₘ F.key) = ((ka + kb : ℕ) : ℕ∞) := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hge : ((ka + kb : ℕ) : ℕ∞) ≤ F.stageHeight ((a * b) %ₘ F.key) := by
    refine le_trans (le_of_eq ?_) (stageHeight_le_modByMonic hπ F hh (a * b))
    rw [stageHeight_mul hπ F hh, hka, hkb, Nat.cast_add]
  have hread : F.twistRead H₀ hpin (ka + kb) ((a * b) %ₘ F.key) ≠ 0 := by
    rw [h1 π F hπ hh H₀ hpin a b ha hb ka kb (le_of_eq hka.symm) (le_of_eq hkb.symm)]
    exact mul_ne_zero (m1DigitFaithful π F hπ hh H₀ hpin a ha ka hka)
      (m1DigitFaithful π F hπ hh H₀ hpin b hb kb hkb)
  by_contra hne
  exact hread (twistRead_eq_zero_of_lt F hπ H₀ hpin
    (lt_of_le_of_ne hge (fun h => hne h.symm)))

/-! ## Part 4 — convolution-pair line pricing (private, twist-law-free) -/

/-- Both factors clear their support lines: the pair prices at `≥ Sg + Sz`. -/
private theorem pair_line_le {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞)) (j i : ℕ) :
    ((Sg + Sz : ℕ) : ℕ∞) ≤ ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
  have hg' := dvSupp_le_term F g u hℓ j
  have hz' := dvSupp_le_term F z u hℓ i
  rw [hSg] at hg'
  rw [hSz] at hz'
  calc ((Sg + Sz : ℕ) : ℕ∞) = (Sg : ℕ∞) + (Sz : ℕ∞) := by push_cast; ring
    _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
        add_le_add hg' hz'
    _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
        rw [nsmul_add]
        push_cast
        ring

/-- A pair that is NOT both-on-side prices STRICTLY above `Sg + Sz`. -/
private theorem pair_line_lt {F : KeyFrame O π} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞)) {j i : ℕ}
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
  rcases not_and_or.mp hbad with hoff | hoff
  · have hg' := succ_dvSupp_le_of_not_dvOnSide hℓ hSg hoff
    have hz' := dvSupp_le_term F z u hℓ i
    rw [hSz] at hz'
    calc ((Sg + Sz + 1 : ℕ) : ℕ∞) = ((Sg + 1 : ℕ) : ℕ∞) + (Sz : ℕ∞) := by push_cast; ring
      _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
          add_le_add hg' hz'
      _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring
  · have hg' := dvSupp_le_term F g u hℓ j
    have hz' := succ_dvSupp_le_of_not_dvOnSide hℓ hSz hoff
    rw [hSg] at hg'
    calc ((Sg + Sz + 1 : ℕ) : ℕ∞) = (Sg : ℕ∞) + ((Sz + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ (ℓ • dvHgt F g j + (u * j : ℕ∞)) + (ℓ • dvHgt F z i + (u * i : ℕ∞)) :=
          add_le_add hg' hz'
      _ = ℓ • (dvHgt F g j + dvHgt F z i) + ((u * (j + i) : ℕ) : ℕ∞) := by
          rw [nsmul_add]
          push_cast
          ring

/-- The reduced main-diagonal term's height floor: `ℓ·κ + u·s = Sg + Sz`, `j + i = s` give
`κ ≤ dv((dev g j · dev z i) %ₘ Φ′)`. -/
private theorem modKey_term_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz) :
    (κ : ℕ∞) ≤ F.stageHeight ((dev F.key g j * dev F.key z i) %ₘ F.key) := by
  have hp := pair_line_le hℓ hSg hSz j i
  rw [hs, show Sg + Sz = ℓ * κ + u * s from hκ.symm] at hp
  have hx : ((κ : ℕ) : ℕ∞) ≤ dvHgt F g j + dvHgt F z i := le_of_weight_le hℓ hp
  refine le_trans hx (le_trans (le_of_eq ?_) (stageHeight_le_modByMonic hπ F hh _))
  exact (stageHeight_mul hπ F hh (dev F.key g j) (dev F.key z i)).symm

/-- The reduced main-diagonal term's STRICT height floor at a not-both-on-side pair. -/
private theorem modKey_term_succ_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz)
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((κ + 1 : ℕ) : ℕ∞) ≤ F.stageHeight ((dev F.key g j * dev F.key z i) %ₘ F.key) := by
  have hp := pair_line_lt hℓ hSg hSz hbad
  rw [hs, show Sg + Sz + 1 = ℓ * κ + u * s + 1 by omega] at hp
  have hx : ((κ + 1 : ℕ) : ℕ∞) ≤ dvHgt F g j + dvHgt F z i :=
    succ_le_of_weight_succ_le' hℓ hp
  refine le_trans hx (le_trans (le_of_eq ?_) (stageHeight_le_modByMonic hπ F hh _))
  exact (stageHeight_mul hπ F hh (dev F.key g j) (dev F.key z i)).symm

/-- The carry-diagonal term's STRICT height floor (the strict floor `ℓ·V < u` pays here). -/
private theorem carry_term_floor (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ} (hV : F.stageHeight F.key = (V : ℕ∞))
    (hadm' : ℓ * V < u) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i + 1 = s) (hκ : ℓ * κ + u * s = Sg + Sz) :
    ((κ + 1 : ℕ) : ℕ∞) ≤ F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1) := by
  rcases eq_or_ne (dev F.key g j) 0 with h0 | h0
  · rw [h0, zero_mul, dev_of_zero F.key 1, F.stageHeight_zero]
    exact le_top
  rcases eq_or_ne (dev F.key z i) 0 with h0' | h0'
  · rw [h0', mul_zero, dev_of_zero F.key 1, F.stageHeight_zero]
    exact le_top
  have hshort : (dev F.key g j * dev F.key z i).natDegree < 2 * F.key.natDegree :=
    natDegree_dev_mul_lt F h0 h0'
  have hslot := lt_weight_dev_slot hπ F hh hℓ hV hadm' hshort (s := 1) Nat.one_pos
  have hp := pair_line_le hℓ hSg hSz j i
  rw [show ℓ • (dvHgt F g j + dvHgt F z i)
      = ℓ • F.stageHeight (dev F.key g j * dev F.key z i) from by
    rw [stageHeight_mul hπ F hh]; rfl] at hp
  have key : ((ℓ * κ + u * s + 1 : ℕ) : ℕ∞)
      ≤ ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
        + ((u * s : ℕ) : ℕ∞) := by
    calc ((ℓ * κ + u * s + 1 : ℕ) : ℕ∞)
        = ((Sg + Sz : ℕ) : ℕ∞) + 1 := by rw [hκ]; push_cast; ring
      _ ≤ (ℓ • F.stageHeight (dev F.key g j * dev F.key z i)
            + ((u * (j + i) : ℕ) : ℕ∞)) + 1 := add_le_add hp le_rfl
      _ = (ℓ • F.stageHeight (dev F.key g j * dev F.key z i) + 1)
            + ((u * (j + i) : ℕ) : ℕ∞) := add_right_comm _ _ _
      _ ≤ (ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
            + (u * 1 : ℕ∞)) + ((u * (j + i) : ℕ) : ℕ∞) := add_le_add hslot le_rfl
      _ = ℓ • F.stageHeight (dev F.key (dev F.key g j * dev F.key z i) 1)
            + ((u * s : ℕ) : ℕ∞) := by
          rw [← hs]
          push_cast
          ring
  exact succ_le_of_weight_succ_le' hℓ key

/-- **The read-kill lemma**: on the product's side line at pin `κ`, a convolution pair that
is not both-on-side has vanishing reduced read (strict pricing + `twistRead_eq_zero_of_lt`).
Twist-law-free. -/
private theorem read_kill (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞))
    {j i κ s : ℕ} (hs : j + i = s) (hκ : ℓ * κ + u * s = Sg + Sz)
    (hbad : ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    F.twistRead H₀ hpin κ ((dev F.key g j * dev F.key z i) %ₘ F.key) = 0 := by
  have hx := modKey_term_succ_floor hπ hh hℓ hSg hSz hs hκ hbad
  refine twistRead_eq_zero_of_lt F hπ H₀ hpin (lt_of_lt_of_le ?_ hx)
  exact_mod_cast Nat.lt_succ_self κ

/-- **No on-side pair ⟹ the slot prices strictly above the sum line** (feeds both endpoint
bounds of clause 2; twist-law-free). -/
private theorem line_succ_le_of_no_pair (hπ : Irreducible π) {F : KeyFrame O π}
    (hh : 0 < F.h) {u ℓ : ℕ} (hℓ : 0 < ℓ) {V : ℕ}
    (hV : F.stageHeight F.key = (V : ℕ∞)) (hadm' : ℓ * V < u)
    {g z : Polynomial O} {Sg Sz : ℕ}
    (hSg : dvSupp F g u ℓ = (Sg : ℕ∞)) (hSz : dvSupp F z u ℓ = (Sz : ℕ∞)) {J : ℕ}
    (hno : ∀ j i : ℕ, j + i = J → ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i)) :
    ((Sg + Sz + 1 : ℕ) : ℕ∞) ≤ ℓ • dvHgt F (g * z) J + (u * J : ℕ∞) := by
  classical
  have hkeypos := F.natDegree_key_pos
  set N := g.natDegree + z.natDegree + 1 with hN
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
  have hdev : dvHgt F (g * z) J
      = F.stageHeight (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) J) := by
    show F.stageHeight (dev F.key (g * z) J) = _
    rw [show dev F.key (g * z) J = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        dev F.key (dev F.key g p.1 * dev F.key z p.2 * F.key ^ (p.1 + p.2)) J by
      conv_lhs => rw [hrep]
      exact dev_finsetSum F.hmonic _ _ J]
  rw [hdev]
  refine le_weight_stageHeight_sum F hℓ _ _ fun p _ => ?_
  have hbad : ¬ (p.1 + p.2 = J ∧ DvOnSide F g u ℓ p.1 ∧ DvOnSide F z u ℓ p.2) := by
    rintro ⟨hsum, hb1, hb2⟩
    exact hno p.1 p.2 hsum ⟨hb1, hb2⟩
  exact lt_line_dev_term hπ F hh hℓ hV hadm' hSg hSz hbad

/-! ## Part 5 — Theorem M clauses 1–2 (§3.2's assembly, given the twist law) -/

/-- **The endpoint-pair survival, both endpoints at once** (§3.2's mechanism): at a
convolution-unique on-side pair `(jg, jz)`, the product's outer digit prices EXACTLY at the
added heights — the head is exact (the height form), every other main and carry term is
strictly above (line pricing + strict floor), and strict ultrametric stability reads it. -/
theorem dvHgt_mul_pair_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} {jg jz Hg Hz : ℕ}
    (hjg : DvOnSide F g u ℓ jg) (hjz : DvOnSide F z u ℓ jz)
    (hHg : dvHgt F g jg = (Hg : ℕ∞)) (hHz : dvHgt F z jz = (Hz : ℕ∞))
    (huniq : ∀ j i : ℕ, j + i = jg + jz →
      DvOnSide F g u ℓ j → DvOnSide F z u ℓ i → j = jg ∧ i = jz) :
    dvHgt F (g * z) (jg + jz) = ((Hg + Hz : ℕ) : ℕ∞) := by
  classical
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  have hSg : dvSupp F g u ℓ = ((ℓ * Hg + u * jg : ℕ) : ℕ∞) := dvSupp_eq_of_dvOnSide hHg hjg
  have hSz : dvSupp F z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) := dvSupp_eq_of_dvOnSide hHz hjz
  have hκ : ℓ * (Hg + Hz) + u * (jg + jz) = (ℓ * Hg + u * jg) + (ℓ * Hz + u * jz) := by ring
  have hjg_mem : jg ∈ Finset.range (jg + jz + 1) := Finset.mem_range.mpr (by omega)
  have hhead : F.stageHeight ((dev F.key g jg * dev F.key z (jg + jz - jg)) %ₘ F.key)
      = ((Hg + Hz : ℕ) : ℕ∞) := by
    rw [show jg + jz - jg = jz by omega]
    exact digit_stageHeight_modKey_of_twistLaw h1 hπ hh H₀ hpin
      (natDegree_dev_lt_frame F g jg) (natDegree_dev_lt_frame F z jz) hHg hHz
  have hrest : ((Hg + Hz + 1 : ℕ) : ℕ∞) ≤ F.stageHeight
      ((∑ j ∈ (Finset.range (jg + jz + 1)).erase jg,
          (dev F.key g j * dev F.key z (jg + jz - j)) %ₘ F.key)
        + ∑ j ∈ Finset.range (jg + jz),
            dev F.key (dev F.key g j * dev F.key z (jg + jz - 1 - j)) 1) := by
    refine le_trans (le_min ?_ ?_) (F.min_stageHeight_le_add _ _)
    · refine le_stageHeight_finsetSum F _ _ fun j hj => ?_
      obtain ⟨hjne, hjmem⟩ := Finset.mem_erase.mp hj
      have hjle : j ≤ jg + jz := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
      refine modKey_term_succ_floor hπ hh hℓ hSg hSz
        (show j + (jg + jz - j) = jg + jz by omega) hκ ?_
      rintro ⟨hb1, hb2⟩
      obtain ⟨e1, -⟩ := huniq j (jg + jz - j) (by omega) hb1 hb2
      exact hjne e1
    · refine le_stageHeight_finsetSum F _ _ fun j hj => ?_
      have hjlt : j < jg + jz := Finset.mem_range.mp hj
      exact carry_term_floor hπ hh hℓ hV hadm' hSg hSz
        (show j + (jg + jz - 1 - j) + 1 = jg + jz by omega) hκ
  have hassemble : dev F.key (g * z) (jg + jz)
      = (dev F.key g jg * dev F.key z (jg + jz - jg)) %ₘ F.key
        + ((∑ j ∈ (Finset.range (jg + jz + 1)).erase jg,
              (dev F.key g j * dev F.key z (jg + jz - j)) %ₘ F.key)
          + ∑ j ∈ Finset.range (jg + jz),
              dev F.key (dev F.key g j * dev F.key z (jg + jz - 1 - j)) 1) := by
    rw [dev_mul_conv_split F g z (jg + jz),
      ← Finset.add_sum_erase _ _ hjg_mem, add_assoc]
  show F.stageHeight (dev F.key (g * z) (jg + jz)) = ((Hg + Hz : ℕ) : ℕ∞)
  rw [hassemble, stageHeight_add_eq_left_of_lt F (by
    rw [hhead]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (Hg + Hz)) hrest), hhead]

/-- ★ **Theorem M clause 1** (`W(gz) = W(g) + W(z)`), given the twist law. -/
theorem dvSupp_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dvSupp F (g * z) u ℓ = dvSupp F g u ℓ + dvSupp F z u ℓ := by
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  have hng := dvSideSet_nonempty F hg u hℓ
  have hnz := dvSideSet_nonempty F hz u hℓ
  obtain ⟨Hg, hHg⟩ := exists_dvSideMin_height F g u ℓ hng
  obtain ⟨Hz, hHz⟩ := exists_dvSideMin_height F z u ℓ hnz
  have hpair := dvHgt_mul_pair_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor
    (dvOnSide_dvSideMin F g u ℓ hng) (dvOnSide_dvSideMin F z u ℓ hnz) hHg hHz
    (fun j i hsum hb1 hb2 => dvOnSide_endpoint_unique hng hnz hsum hb1 hb2)
  exact dvSupp_mul_eq_add_of_endpoint_le hπ hh hℓ hV (le_of_lt hadm') hng hnz hHg hHz
    (le_of_eq hpair)

/-- ★ **Theorem M clause 2, minimizers**: `dvSideMin` is additive, given the twist law. -/
theorem dvSideMin_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMin F (g * z) u ℓ hngz = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz := by
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  obtain ⟨Hg, hHg⟩ := exists_dvSideMin_height F g u ℓ hng
  obtain ⟨Hz, hHz⟩ := exists_dvSideMin_height F z u ℓ hnz
  have hpair := dvHgt_mul_pair_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor
    (dvOnSide_dvSideMin F g u ℓ hng) (dvOnSide_dvSideMin F z u ℓ hnz) hHg hHz
    (fun j i hsum hb1 hb2 => dvOnSide_endpoint_unique hng hnz hsum hb1 hb2)
  have hle : dvSideMin F (g * z) u ℓ hngz ≤ dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz :=
    dvSideMin_mul_le hπ hh hℓ hV (le_of_lt hadm') hng hnz hHg hHz (le_of_eq hpair) hngz
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hSg : dvSupp F g u ℓ = ((ℓ * Hg + u * dvSideMin F g u ℓ hng : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHg (dvOnSide_dvSideMin F g u ℓ hng)
  have hSz : dvSupp F z u ℓ = ((ℓ * Hz + u * dvSideMin F z u ℓ hnz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHz (dvOnSide_dvSideMin F z u ℓ hnz)
  have hW : dvSupp F (g * z) u ℓ
      = ((ℓ * Hg + u * dvSideMin F g u ℓ hng + (ℓ * Hz + u * dvSideMin F z u ℓ hnz) : ℕ) : ℕ∞) := by
    rw [dvSupp_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz, hSg, hSz]
    push_cast
    ring
  have hJon := dvOnSide_dvSideMin F (g * z) u ℓ hngz
  have hno : ∀ j i : ℕ, j + i = dvSideMin F (g * z) u ℓ hngz →
      ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i) := by
    rintro j i hsum ⟨hb1, hb2⟩
    have h1' := dvSideMin_le_of_dvOnSide hng hb1
    have h2' := dvSideMin_le_of_dvOnSide hnz hb2
    omega
  have hs := line_succ_le_of_no_pair hπ hh hℓ hV hadm' hSg hSz hno
  rw [hJon.1] at hW
  rw [hW] at hs
  have hnat : ℓ * Hg + u * dvSideMin F g u ℓ hng + (ℓ * Hz + u * dvSideMin F z u ℓ hnz) + 1
      ≤ ℓ * Hg + u * dvSideMin F g u ℓ hng + (ℓ * Hz + u * dvSideMin F z u ℓ hnz) := by
    exact_mod_cast hs
  omega

/-- **The pin law**: the product's `dvSideMin` height is the SUM of the factors' pin
heights, given the twist law. -/
theorem dvHgt_dvSideMin_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) {Mg Mz : ℕ}
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞)) :
    dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = ((Mg + Mz : ℕ) : ℕ∞) := by
  rw [dvSideMin_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz hng hnz hngz]
  exact dvHgt_mul_pair_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor
    (dvOnSide_dvSideMin F g u ℓ hng) (dvOnSide_dvSideMin F z u ℓ hnz) hpg hpz
    (fun j i hsum hb1 hb2 => dvOnSide_endpoint_unique hng hnz hsum hb1 hb2)

set_option linter.unusedVariables false in
/-- ★ **Theorem M clause 2, maximizers**: `dvSideMax` is additive, given the twist law.
(`hcop` is carried for clause-2 signature uniformity.) -/
theorem dvSideMax_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMax F (g * z) u ℓ hngz = dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz := by
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  have hjgON : DvOnSide F g u ℓ (dvSideMax F g u ℓ hng) :=
    dvOnSide_of_mem_dvSideSet (Finset.max'_mem (dvSideSet F g u ℓ) hng)
  have hjzON : DvOnSide F z u ℓ (dvSideMax F z u ℓ hnz) :=
    dvOnSide_of_mem_dvSideSet (Finset.max'_mem (dvSideSet F z u ℓ) hnz)
  obtain ⟨HgM, hHgM⟩ := ENat.ne_top_iff_exists.1 hjgON.2
  obtain ⟨HzM, hHzM⟩ := ENat.ne_top_iff_exists.1 hjzON.2
  have huniq : ∀ j i : ℕ, j + i = dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz →
      DvOnSide F g u ℓ j → DvOnSide F z u ℓ i →
      j = dvSideMax F g u ℓ hng ∧ i = dvSideMax F z u ℓ hnz := by
    intro j i hsum hb1 hb2
    have h1' : j ≤ dvSideMax F g u ℓ hng :=
      Finset.le_max' (dvSideSet F g u ℓ) j (mem_dvSideSet_of_dvOnSide hb1)
    have h2' : i ≤ dvSideMax F z u ℓ hnz :=
      Finset.le_max' (dvSideSet F z u ℓ) i (mem_dvSideSet_of_dvOnSide hb2)
    omega
  have hpair := dvHgt_mul_pair_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hjgON hjzON
    hHgM.symm hHzM.symm huniq
  have hSg : dvSupp F g u ℓ = ((ℓ * HgM + u * dvSideMax F g u ℓ hng : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHgM.symm hjgON
  have hSz : dvSupp F z u ℓ = ((ℓ * HzM + u * dvSideMax F z u ℓ hnz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hHzM.symm hjzON
  have hW : dvSupp F (g * z) u ℓ
      = ((ℓ * HgM + u * dvSideMax F g u ℓ hng
          + (ℓ * HzM + u * dvSideMax F z u ℓ hnz) : ℕ) : ℕ∞) := by
    rw [dvSupp_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz, hSg, hSz]
    push_cast
    ring
  have hONmax : DvOnSide F (g * z) u ℓ (dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz) := by
    refine ⟨?_, ?_⟩
    · rw [hW]
      show _ = ℓ • dvHgt F (g * z) (dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz) + _
      rw [hpair, weight_read]
      push_cast
      ring
    · show dvHgt F (g * z) _ ≠ ⊤
      rw [hpair]
      exact ENat.coe_ne_top _
  have hge : dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz ≤ dvSideMax F (g * z) u ℓ hngz :=
    Finset.le_max' (dvSideSet F (g * z) u ℓ) _ (mem_dvSideSet_of_dvOnSide hONmax)
  refine le_antisymm ?_ hge
  by_contra hlt
  push Not at hlt
  have hJon : DvOnSide F (g * z) u ℓ (dvSideMax F (g * z) u ℓ hngz) :=
    dvOnSide_of_mem_dvSideSet (Finset.max'_mem (dvSideSet F (g * z) u ℓ) hngz)
  have hno : ∀ j i : ℕ, j + i = dvSideMax F (g * z) u ℓ hngz →
      ¬ (DvOnSide F g u ℓ j ∧ DvOnSide F z u ℓ i) := by
    rintro j i hsum ⟨hb1, hb2⟩
    have h1' : j ≤ dvSideMax F g u ℓ hng :=
      Finset.le_max' (dvSideSet F g u ℓ) j (mem_dvSideSet_of_dvOnSide hb1)
    have h2' : i ≤ dvSideMax F z u ℓ hnz :=
      Finset.le_max' (dvSideSet F z u ℓ) i (mem_dvSideSet_of_dvOnSide hb2)
    omega
  have hs := line_succ_le_of_no_pair hπ hh hℓ hV hadm' hSg hSz hno
  rw [hJon.1] at hW
  rw [hW] at hs
  have hnat : ℓ * HgM + u * dvSideMax F g u ℓ hng + (ℓ * HzM + u * dvSideMax F z u ℓ hnz) + 1
      ≤ ℓ * HgM + u * dvSideMax F g u ℓ hng + (ℓ * HzM + u * dvSideMax F z u ℓ hnz) := by
    exact_mod_cast hs
  omega

/-- ★ **Theorem M clause 2, degrees**: `dvSideDeg` is additive, given the twist law. -/
theorem dvSideDeg_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideDeg F (g * z) u ℓ hngz = dvSideDeg F g u ℓ hng + dvSideDeg F z u ℓ hnz := by
  have hmin := dvSideMin_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz hng hnz hngz
  have hmax := dvSideMax_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg hz hng hnz hngz
  have hlg : dvSideMax F g u ℓ hng - dvSideMin F g u ℓ hng = ℓ * dvSideDeg F g u ℓ hng := by
    have := dvSideLen_eq F hℓ hcop hng
    rwa [dvSideLen] at this
  have hlz : dvSideMax F z u ℓ hnz - dvSideMin F z u ℓ hnz = ℓ * dvSideDeg F z u ℓ hnz := by
    have := dvSideLen_eq F hℓ hcop hnz
    rwa [dvSideLen] at this
  have hlgz : dvSideMax F (g * z) u ℓ hngz - dvSideMin F (g * z) u ℓ hngz
      = ℓ * dvSideDeg F (g * z) u ℓ hngz := by
    have := dvSideLen_eq F hℓ hcop hngz
    rwa [dvSideLen] at this
  have hmm_g : dvSideMin F g u ℓ hng ≤ dvSideMax F g u ℓ hng :=
    Finset.min'_le _ _ (Finset.max'_mem _ hng)
  have hmm_z : dvSideMin F z u ℓ hnz ≤ dvSideMax F z u ℓ hnz :=
    Finset.min'_le _ _ (Finset.max'_mem _ hnz)
  have hkey : ℓ * dvSideDeg F (g * z) u ℓ hngz
      = ℓ * dvSideDeg F g u ℓ hng + ℓ * dvSideDeg F z u ℓ hnz := by omega
  have hkey' : ℓ * dvSideDeg F (g * z) u ℓ hngz
      = ℓ * (dvSideDeg F g u ℓ hng + dvSideDeg F z u ℓ hnz) := by
    rw [hkey, Nat.mul_add]
  exact Nat.eq_of_mul_eq_mul_left hℓ hkey'

/-! ## Part 6 — residual coefficient extraction (private) -/

/-- In-range coefficient of `dvResPoly` (C.25's body, read off). -/
private theorem dvResPoly_coeff_of_le {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hp₂).coeff t
      = F.twistRead H₀ hpin (M₀ - t * u) (dev F.key f (dvSideMin F f u ℓ hne₂ + t * ℓ)) := by
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_of_le ht)]

/-- Beyond-range coefficient of `dvResPoly` vanishes. -/
private theorem dvResPoly_coeff_of_gt {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : dvSideDeg F f u ℓ hne₂ < t) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hp₂).coeff t = 0 := by
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]

/-! ## Part 7 — ★ Theorem M clause 3: the mixed residual product law (τ = 1) -/

/-- ★ **Theorem M clause 3 — `dvResPoly_mul_gen`, τ = 1** (§3.3's coefficientwise assembly,
given the twist law): for ALL nonzero `g, z` — no monicity, purity, or degree fence —
`R(gz) = R(g) · R(z)` at the `dvSideMin` pins, EXACTLY (the C.25 reads are C.22's
inverse-twisted reads, and the twist trivializes the carry cocycle). -/
theorem dvResPoly_mul_gen_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) {Mg Mz Mgz : ℕ}
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)) :
    dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
      = dvResPoly F H₀ hpin g u ℓ hng Mg hpg * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz := by
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  obtain ⟨V, hV, hadm'⟩ := exists_key_height_lt F hfloor
  have hminmul : dvSideMin F (g * z) u ℓ hngz
      = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz :=
    dvSideMin_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz hng hnz hngz
  have hdegmul : dvSideDeg F (g * z) u ℓ hngz
      = dvSideDeg F g u ℓ hng + dvSideDeg F z u ℓ hnz :=
    dvSideDeg_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg hz hng hnz hngz
  have hMsum : Mgz = Mg + Mz := by
    have hpin2 := dvHgt_dvSideMin_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz
      hng hnz hngz hpg hpz
    rw [hpgz] at hpin2
    exact_mod_cast hpin2
  -- the side-line pin bound `u·d ≤ M₀`
  have hbound : ∀ (f : Polynomial O) (hne : (dvSideSet F f u ℓ).Nonempty) (M : ℕ),
      dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) → u * dvSideDeg F f u ℓ hne ≤ M := by
    intro f hne M hp
    have hmaxON : DvOnSide F f u ℓ (dvSideMax F f u ℓ hne) :=
      dvOnSide_of_mem_dvSideSet (Finset.max'_mem (dvSideSet F f u ℓ) hne)
    obtain ⟨HM, hHM⟩ := ENat.ne_top_iff_exists.1 hmaxON.2
    have hSf : dvSupp F f u ℓ = ((ℓ * M + u * dvSideMin F f u ℓ hne : ℕ) : ℕ∞) :=
      dvSupp_eq_of_dvOnSide hp (dvOnSide_dvSideMin F f u ℓ hne)
    have hSf' : dvSupp F f u ℓ = ((ℓ * HM + u * dvSideMax F f u ℓ hne : ℕ) : ℕ∞) :=
      dvSupp_eq_of_dvOnSide hHM.symm hmaxON
    have heq : ℓ * M + u * dvSideMin F f u ℓ hne = ℓ * HM + u * dvSideMax F f u ℓ hne := by
      rw [hSf] at hSf'
      exact_mod_cast hSf'
    have hlen : dvSideMax F f u ℓ hne - dvSideMin F f u ℓ hne = ℓ * dvSideDeg F f u ℓ hne := by
      have := dvSideLen_eq F hℓ hcop hne
      rwa [dvSideLen] at this
    have hmm : dvSideMin F f u ℓ hne ≤ dvSideMax F f u ℓ hne :=
      Finset.min'_le _ _ (Finset.max'_mem _ hne)
    have hmaxe : dvSideMax F f u ℓ hne
        = dvSideMin F f u ℓ hne + ℓ * dvSideDeg F f u ℓ hne := by omega
    rw [hmaxe, Nat.mul_add] at heq
    have hM' : ℓ * M = ℓ * HM + u * (ℓ * dvSideDeg F f u ℓ hne) := by omega
    have hM'' : ℓ * M = ℓ * (HM + u * dvSideDeg F f u ℓ hne) := by rw [hM']; ring
    have := Nat.eq_of_mul_eq_mul_left hℓ hM''
    omega
  -- the ℓ-progression height floors at both factors
  have hfloorG : ∀ t₁ : ℕ, t₁ ≤ dvSideDeg F g u ℓ hng →
      ((Mg - t₁ * u : ℕ) : ℕ∞) ≤ dvHgt F g (dvSideMin F g u ℓ hng + t₁ * ℓ) := by
    intro t₁ ht₁
    have hSf : dvSupp F g u ℓ = ((ℓ * Mg + u * dvSideMin F g u ℓ hng : ℕ) : ℕ∞) :=
      dvSupp_eq_of_dvOnSide hpg (dvOnSide_dvSideMin F g u ℓ hng)
    have hub := hbound g hng Mg hpg
    have hut : t₁ * u ≤ Mg := by
      have h2' : t₁ * u ≤ dvSideDeg F g u ℓ hng * u := Nat.mul_le_mul_right u ht₁
      have h3' := Nat.mul_comm (dvSideDeg F g u ℓ hng) u
      omega
    refine le_dvHgt_of_le_dvSupp hℓ (le_of_eq hSf.symm) ?_
    obtain ⟨m, hm⟩ : ∃ m, Mg = m + t₁ * u := ⟨Mg - t₁ * u, by omega⟩
    rw [show Mg - t₁ * u = m by omega, hm]
    ring
  have hfloorZ : ∀ t₂ : ℕ, t₂ ≤ dvSideDeg F z u ℓ hnz →
      ((Mz - t₂ * u : ℕ) : ℕ∞) ≤ dvHgt F z (dvSideMin F z u ℓ hnz + t₂ * ℓ) := by
    intro t₂ ht₂
    have hSf : dvSupp F z u ℓ = ((ℓ * Mz + u * dvSideMin F z u ℓ hnz : ℕ) : ℕ∞) :=
      dvSupp_eq_of_dvOnSide hpz (dvOnSide_dvSideMin F z u ℓ hnz)
    have hub := hbound z hnz Mz hpz
    have hut : t₂ * u ≤ Mz := by
      have h2' : t₂ * u ≤ dvSideDeg F z u ℓ hnz * u := Nat.mul_le_mul_right u ht₂
      have h3' := Nat.mul_comm (dvSideDeg F z u ℓ hnz) u
      omega
    refine le_dvHgt_of_le_dvSupp hℓ (le_of_eq hSf.symm) ?_
    obtain ⟨m, hm⟩ : ∃ m, Mz = m + t₂ * u := ⟨Mz - t₂ * u, by omega⟩
    rw [show Mz - t₂ * u = m by omega, hm]
    ring
  -- the two pins as support values
  have hSg : dvSupp F g u ℓ = ((ℓ * Mg + u * dvSideMin F g u ℓ hng : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hpg (dvOnSide_dvSideMin F g u ℓ hng)
  have hSz : dvSupp F z u ℓ = ((ℓ * Mz + u * dvSideMin F z u ℓ hnz : ℕ) : ℕ∞) :=
    dvSupp_eq_of_dvOnSide hpz (dvOnSide_dvSideMin F z u ℓ hnz)
  -- the coefficientwise identity
  refine Polynomial.ext fun t => ?_
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  by_cases htle : t ≤ dvSideDeg F (g * z) u ℓ hngz
  case neg =>
    rw [dvResPoly_coeff_of_gt H₀ hpin hngz hpgz (by omega)]
    symm
    refine Finset.sum_eq_zero fun t₁ ht₁ => ?_
    have ht₁' : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
    rcases Nat.lt_or_ge (dvSideDeg F g u ℓ hng) t₁ with hgt | hle₁
    · rw [dvResPoly_coeff_of_gt H₀ hpin hng hpg hgt, zero_mul]
    · rw [dvResPoly_coeff_of_gt H₀ hpin hnz hpz (by omega), mul_zero]
  case pos =>
    have hutz : t * u ≤ Mgz := by
      have h1' := hbound (g * z) hngz Mgz hpgz
      have h2' : t * u ≤ dvSideDeg F (g * z) u ℓ hngz * u := Nat.mul_le_mul_right u htle
      have h3' := Nat.mul_comm (dvSideDeg F (g * z) u ℓ hngz) u
      omega
    have hκnat : ℓ * (Mgz - t * u)
        + u * (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ)
        = (ℓ * Mg + u * dvSideMin F g u ℓ hng) + (ℓ * Mz + u * dvSideMin F z u ℓ hnz) := by
      obtain ⟨m, hm⟩ : ∃ m, Mgz = m + t * u := ⟨Mgz - t * u, by omega⟩
      rw [show Mgz - t * u = m by omega]
      have hMM : Mg + Mz = m + t * u := by omega
      calc ℓ * m + u * (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ)
          = ℓ * (m + t * u) + u * dvSideMin F g u ℓ hng + u * dvSideMin F z u ℓ hnz := by
            ring
        _ = ℓ * (Mg + Mz) + u * dvSideMin F g u ℓ hng + u * dvSideMin F z u ℓ hnz := by
            rw [hMM]
        _ = (ℓ * Mg + u * dvSideMin F g u ℓ hng) + (ℓ * Mz + u * dvSideMin F z u ℓ hnz) := by
            ring
    rw [dvResPoly_coeff_of_le H₀ hpin hngz hpgz htle, hminmul]
    -- distribute the read over the convolution split
    have hmainfl : ∀ j ∈ Finset.range
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ + 1),
        ((Mgz - t * u : ℕ) : ℕ∞) ≤ F.stageHeight ((dev F.key g j
          * dev F.key z (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ - j)) %ₘ F.key) := by
      intro j hj
      have hjle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact modKey_term_floor hπ hh hℓ hSg hSz (by omega) hκnat
    have hcarryfl : ∀ j ∈ Finset.range
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ),
        ((Mgz - t * u : ℕ) : ℕ∞) ≤ F.stageHeight (dev F.key (dev F.key g j
          * dev F.key z (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ - 1 - j)) 1) := by
      intro j hj
      have hjlt := Finset.mem_range.mp hj
      refine le_trans (by exact_mod_cast Nat.le_succ (Mgz - t * u))
        (carry_term_floor hπ hh hℓ hV hadm' hSg hSz (by omega) hκnat)
    rw [dev_mul_conv_split F g z
      (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ)]
    rw [twistRead_add_of_le F hπ H₀ hpin
      (le_stageHeight_finsetSum F _ _ hmainfl) (le_stageHeight_finsetSum F _ _ hcarryfl),
      twistRead_finsetSum_of_le F hπ H₀ hpin _ _ hmainfl,
      twistRead_finsetSum_of_le F hπ H₀ hpin _ _ hcarryfl]
    have hcarry0 : ∑ j ∈ Finset.range
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ),
        F.twistRead H₀ hpin (Mgz - t * u) (dev F.key (dev F.key g j
          * dev F.key z (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ - 1 - j)) 1) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjlt := Finset.mem_range.mp hj
      refine twistRead_eq_zero_of_lt F hπ H₀ hpin (lt_of_lt_of_le ?_
        (carry_term_floor hπ hh hℓ hV hadm' hSg hSz (by omega) hκnat))
      exact_mod_cast Nat.lt_succ_self (Mgz - t * u)
    rw [hcarry0, add_zero]
    -- reindex the surviving main diagonal to the ℓ-progression
    have himg : ((Finset.range (t + 1)).image fun t₁ => dvSideMin F g u ℓ hng + t₁ * ℓ)
        ⊆ Finset.range (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ + 1) := by
      intro j hj
      obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hj
      have ht₁' : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁)
      have hmle : t₁ * ℓ ≤ t * ℓ := Nat.mul_le_mul_right ℓ ht₁'
      exact Finset.mem_range.mpr (by omega)
    have hvanish : ∀ j ∈ Finset.range
        (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ + 1),
        j ∉ ((Finset.range (t + 1)).image fun t₁ => dvSideMin F g u ℓ hng + t₁ * ℓ) →
        F.twistRead H₀ hpin (Mgz - t * u) ((dev F.key g j
          * dev F.key z (dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ - j)) %ₘ F.key)
          = 0 := by
      intro j hj hnot
      have hjle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      refine read_kill hπ hh H₀ hpin hℓ hSg hSz (by omega) hκnat ?_
      rintro ⟨hb1, hb2⟩
      refine hnot ?_
      have hjge : dvSideMin F g u ℓ hng ≤ j := dvSideMin_le_of_dvOnSide hng hb1
      obtain ⟨t₁, ht₁⟩ := (Nat.modEq_iff_dvd' hjge).mp
        (dvOnSide_modEq F hℓ hcop (dvOnSide_dvSideMin F g u ℓ hng) hb1)
      have hcomm := Nat.mul_comm ℓ t₁
      have hjform : j = dvSideMin F g u ℓ hng + t₁ * ℓ := by omega
      have hige : dvSideMin F z u ℓ hnz
          ≤ dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ - j :=
        dvSideMin_le_of_dvOnSide hnz hb2
      have ht₁le : t₁ ≤ t := by
        by_contra hgt
        push Not at hgt
        have h1' : (t + 1) * ℓ ≤ t₁ * ℓ := Nat.mul_le_mul_right ℓ (by omega)
        have h2' : (t + 1) * ℓ = t * ℓ + ℓ := by ring
        omega
      exact Finset.mem_image.mpr ⟨t₁, Finset.mem_range.mpr (by omega), hjform.symm⟩
    rw [← Finset.sum_subset himg hvanish,
      Finset.sum_image (fun x _ y _ hxy => by
        have hx : x * ℓ = y * ℓ := by omega
        exact Nat.eq_of_mul_eq_mul_right hℓ hx)]
    -- termwise identification
    refine Finset.sum_congr rfl fun t₁ ht₁mem => ?_
    have ht₁t : t₁ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht₁mem)
    have hmle : t₁ * ℓ ≤ t * ℓ := Nat.mul_le_mul_right ℓ ht₁t
    have hsplitℓ : t₁ * ℓ + (t - t₁) * ℓ = t * ℓ := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have hi : dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz + t * ℓ
        - (dvSideMin F g u ℓ hng + t₁ * ℓ) = dvSideMin F z u ℓ hnz + (t - t₁) * ℓ := by
      omega
    by_cases hc1 : t₁ ≤ dvSideDeg F g u ℓ hng
    · by_cases hc2 : t - t₁ ≤ dvSideDeg F z u ℓ hnz
      · -- the surviving genre: the twist law fires
        rw [hi]
        have hka := hfloorG t₁ hc1
        have hkb := hfloorZ (t - t₁) hc2
        have hut1 : t₁ * u ≤ Mg := by
          have hub := hbound g hng Mg hpg
          have h2' : t₁ * u ≤ dvSideDeg F g u ℓ hng * u := Nat.mul_le_mul_right u hc1
          have h3' := Nat.mul_comm (dvSideDeg F g u ℓ hng) u
          omega
        have hut2 : (t - t₁) * u ≤ Mz := by
          have hub := hbound z hnz Mz hpz
          have h2' : (t - t₁) * u ≤ dvSideDeg F z u ℓ hnz * u := Nat.mul_le_mul_right u hc2
          have h3' := Nat.mul_comm (dvSideDeg F z u ℓ hnz) u
          omega
        have hsplitu : t₁ * u + (t - t₁) * u = t * u := by
          rw [← Nat.add_mul]
          congr 1
          omega
        have hκsplit : (Mg - t₁ * u) + (Mz - (t - t₁) * u) = Mgz - t * u := by omega
        rw [← hκsplit,
          h1 π F hπ hh H₀ hpin (dev F.key g (dvSideMin F g u ℓ hng + t₁ * ℓ))
            (dev F.key z (dvSideMin F z u ℓ hnz + (t - t₁) * ℓ))
            (natDegree_dev_lt_frame F g _) (natDegree_dev_lt_frame F z _)
            (Mg - t₁ * u) (Mz - (t - t₁) * u) hka hkb,
          dvResPoly_coeff_of_le H₀ hpin hng hpg hc1,
          dvResPoly_coeff_of_le H₀ hpin hnz hpz hc2]
      · -- the z-side overflow: both sides vanish
        rw [dvResPoly_coeff_of_gt H₀ hpin hnz hpz (by omega), mul_zero]
        refine read_kill hπ hh H₀ hpin hℓ hSg hSz (by omega) hκnat ?_
        rintro ⟨hb1, hb2⟩
        rw [hi] at hb2
        have hle' : dvSideMin F z u ℓ hnz + (t - t₁) * ℓ ≤ dvSideMax F z u ℓ hnz :=
          Finset.le_max' _ _ (mem_dvSideSet_of_dvOnSide hb2)
        have hlenz : dvSideMax F z u ℓ hnz - dvSideMin F z u ℓ hnz
            = ℓ * dvSideDeg F z u ℓ hnz := by
          have := dvSideLen_eq F hℓ hcop hnz
          rwa [dvSideLen] at this
        have h2' : (dvSideDeg F z u ℓ hnz + 1) * ℓ ≤ (t - t₁) * ℓ :=
          Nat.mul_le_mul_right ℓ (by omega)
        have h3' : (dvSideDeg F z u ℓ hnz + 1) * ℓ = ℓ * dvSideDeg F z u ℓ hnz + ℓ := by
          ring
        omega
    · -- the g-side overflow: both sides vanish
      rw [dvResPoly_coeff_of_gt H₀ hpin hng hpg (by omega), zero_mul]
      refine read_kill hπ hh H₀ hpin hℓ hSg hSz (by omega) hκnat ?_
      rintro ⟨hb1, hb2⟩
      have hle' : dvSideMin F g u ℓ hng + t₁ * ℓ ≤ dvSideMax F g u ℓ hng :=
        Finset.le_max' _ _ (mem_dvSideSet_of_dvOnSide hb1)
      have hleng : dvSideMax F g u ℓ hng - dvSideMin F g u ℓ hng
          = ℓ * dvSideDeg F g u ℓ hng := by
        have := dvSideLen_eq F hℓ hcop hng
        rwa [dvSideLen] at this
      have h2' : (dvSideDeg F g u ℓ hng + 1) * ℓ ≤ t₁ * ℓ :=
        Nat.mul_le_mul_right ℓ (by omega)
      have h3' : (dvSideDeg F g u ℓ hng + 1) * ℓ = ℓ * dvSideDeg F g u ℓ hng + ℓ := by ring
      omega

/-! ## Part 8 — the packaged statement shapes (probe-verbatim; MH.3's territory) -/

/-- ★ STATEMENT SHAPE — **Theorem M clause 3, corrected: τ = 1** (the mixed residual
product law is EXACTLY multiplicative in the C.25 twist normalization). -/
def MixedResidualLawTauOneStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
  ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) (Mg Mz Mgz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)),
    dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
      = dvResPoly F H₀ hpin g u ℓ hng Mg hpg * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz

/-- ★ **MH.3 packaged**: the twist law (MH.1's remaining clause) implies the full τ = 1
mixed residual law. -/
theorem mixedResidualLaw_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O) :
    MixedResidualLawTauOneStatement O :=
  fun _π _F hπ hh H₀ hpin _u _ℓ hℓ hcop hfloor _g _z hg hz hng hnz hngz _Mg _Mz _Mgz hpg hpz hpgz =>
    dvResPoly_mul_gen_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg hz hng hnz hngz
      hpg hpz hpgz

/-- The MHENS ∃-τ shape (probe-verbatim), for the §2 record. -/
def MixedResidualLawExistsUnitStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
  ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) (Mg Mz Mgz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)),
    ∃ τ : (F.stageField H₀ hpin)ˣ,
      dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
        = Polynomial.C (τ : F.stageField H₀ hpin)
          * (dvResPoly F H₀ hpin g u ℓ hng Mg hpg
             * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz)

/-- ★ PROVED — τ = 1 refines the ∃-τ shape (witness τ := 1; probe-verbatim). -/
theorem existsUnit_of_tauOne (h : MixedResidualLawTauOneStatement O) :
    MixedResidualLawExistsUnitStatement O := by
  intro π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g z hg hz hng hnz hngz Mg Mz Mgz hpg hpz hpgz
  exact ⟨1, by
    rw [h π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g z hg hz hng hnz hngz Mg Mz Mgz hpg hpz hpgz]
    simp⟩

/-! ## Part 9 — the §9.2 payoff: the declared cite's statement, derived from Theorem M -/

set_option linter.unusedVariables false in
/-- **Purity closure** (the cite's first conjunct): pure × pure with `D′ ∣ deg` is pure,
from clause 2's endpoint additivity + the landed C.35 pure-endpoint lemmas.  (`hdz` is
carried for the cite's hypothesis-list parity; `hdg` alone splits the ℕ-division.) -/
theorem isDvPure_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdz : F.e₁ * F.f₁ ∣ z.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpz : IsDvPure F z u ℓ) :
    IsDvPure F (g * z) u ℓ := by
  have hng := dvSideSet_nonempty F hg u hℓ
  have hnz := dvSideSet_nonempty F hz u hℓ
  have hngz := dvSideSet_nonempty F (mul_ne_zero hg hz) u hℓ
  have hminz : dvSideMin F (g * z) u ℓ hngz = 0 := by
    rw [dvSideMin_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hfloor hg hz hng hnz hngz,
      dvSideMin_eq_zero_of_isDvPure hpg hng, dvSideMin_eq_zero_of_isDvPure hpz hnz]
  have hmaxv : dvSideMax F (g * z) u ℓ hngz = (g * z).natDegree / (F.e₁ * F.f₁) := by
    rw [dvSideMax_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg hz hng hnz hngz,
      dvSideMax_eq_of_isDvPure hpg hng, dvSideMax_eq_of_isDvPure hpz hnz,
      Polynomial.natDegree_mul hg hz, Nat.add_div_of_dvd_right hdg]
  constructor
  · have h0 : dvSideMin F (g * z) u ℓ hngz ∈ dvSideSet F (g * z) u ℓ :=
      Finset.min'_mem _ hngz
    rwa [hminz] at h0
  · have h0 : dvSideMax F (g * z) u ℓ hngz ∈ dvSideSet F (g * z) u ℓ :=
      Finset.max'_mem _ hngz
    rwa [hmaxv] at h0

set_option linter.unusedVariables false in
/-- ★ **THE §9.2 PAYOFF — the declared cite `fgmn_dv_exact_mul` (C66b.lean:90), statement
matched, derived from Theorem M** — conditional on TWO explicitly carried hypotheses beyond
the axiom's own list:

1. `h1` — MH.1's remaining twist-law clause (`C133mh1.M1TwistProductLawStatement O`); and
2. `hh : 0 < F.h` — **a statement-level finding of this unit**: `KeyFrame` admits the
   DEGENERATE `h = 0` frame (C.01's docstring), which the cite's quantifier includes but
   Theorem M (doc §2, hypothesis `hh`) does not.  Full retirement (axiom → theorem,
   byte-identical) therefore needs, besides MH.1, a separate `h = 0` leg through the C.05
   degenerate dictionary and the landed order-1 exact chain — previously unrecorded in
   §9.2's retirement claim.

Once both land, instantiating here retires the cite — the §9.2 allowlist reduction.  The
unused-binder linter is off: `hpos`/`hpos'` are carried solely for the match with the
axiom's hypothesis list. -/
theorem fgmn_dv_exact_mul_of_twistLaw (h1 : C133mh1.M1TwistProductLawStatement O)
    {F : KeyFrame O π} (hh : 0 < F.h) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ) :
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp
            * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp' := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have hg0' : g' ≠ 0 := hg'.ne_zero
  refine ⟨isDvPure_mul_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg0 hg0'
    hdg hdg' hpg hpg', ?_⟩
  intro hne hne' hne'' M₀ M₀' M₀'' hp hp' hp''
  exact dvResPoly_mul_gen_of_twistLaw h1 hπ hh H₀ hpin hℓ hcop hfloor hg0 hg0'
    hne hne' hne'' hp hp' hp''

/-! ## Part 10 — THE UNCONDITIONAL ROOT: M1′ clause (1) proved

The remaining MH.1 clause (`M1TwistProductLawStatement`), proved here per the doc §3.1′'s
coefficientwise route (no `gr` construction): a local FULL read (the C.21 window without
the `t < f₁` fence), under which the key's symbol dies by `ψ(η) = 0`
(`AdjoinRoot.eval₂_root`), the convolution splits with the TW-δ carry, and the digit law
follows.  Everything below is new; consumed landed inputs: C.15/C.16 specs, C.02's unfold,
B.21–B.25 digit calculus, B.28/B.29 (`resCoeff`/`resPoly`), C130nv2's `stageHeight_mul` +
division calculus, C133mh1's TW-δ + bridge, frame fields. -/

section UnconditionalRoot

/-! ### 10.1 digit-calculus helpers (private) -/

/-- `π^k ∣ x` from a valuation floor (private-copy pattern: C131y/C131ae/C.26/C130rp2). -/
private theorem dvd_of_le_addVal (hπ : Irreducible π) {k : ℕ} {x : O}
    (h : (k : ℕ∞) ≤ addVal O x) : π ^ k ∣ x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]
  exact h

/-- `digAt` of the zero element (B.24's private helper, re-derived). -/
private theorem digAt_zero_elem (hπ : Irreducible π) (k : ℕ) : digAt π k (0 : O) = 0 := by
  rw [digAt_eq hπ (show (0 : O) = π ^ k * 0 by rw [mul_zero]), map_zero]

/-- `digAt` of a finite sum of `π^m`-divisible terms (B.22's `digAt_add`, iterated). -/
private theorem digAt_finsetSum (hπ : Irreducible π) {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → O) (hf : ∀ i ∈ s, π ^ m ∣ f i) :
    digAt π m (∑ i ∈ s, f i) = ∑ i ∈ s, digAt π m (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [digAt_zero_elem hπ]
  | cons a t hat ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      digAt_add hπ (hf a (Finset.mem_cons_self a t))
        (Finset.dvd_sum fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))),
      ih fun i hi => hf i (Finset.mem_cons.2 (Or.inr hi))]

/-- `digAt` multiplies at an exact depth split (B.22's `digAt_eq` + `residue` is a hom). -/
private theorem digAt_mul_split (hπ : Irreducible π) {m₁ m₂ : ℕ} {x y : O}
    (hx : π ^ m₁ ∣ x) (hy : π ^ m₂ ∣ y) :
    digAt π (m₁ + m₂) (x * y) = digAt π m₁ x * digAt π m₂ y := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  rw [digAt_eq hπ (show π ^ m₁ * x' * (π ^ m₂ * y') = π ^ (m₁ + m₂) * (x' * y') by
      rw [pow_add]; ring),
    digAt_eq hπ (rfl : π ^ m₁ * x' = π ^ m₁ * x'),
    digAt_eq hπ (rfl : π ^ m₂ * y' = π ^ m₂ * y'), map_mul]

/-- The coefficientwise line floor: a stage-height floor prices every coefficient on or
above the `(e₁, h)`-line (C.02's unfold, consumable form). -/
private theorem line_floor (F : KeyFrame O π) {B : Polynomial O} {k : ℕ}
    (hk : (k : ℕ∞) ≤ F.stageHeight B) (n : ℕ) :
    (k : ℕ∞) ≤ F.e₁ • addVal O (B.coeff n) + ((n * F.h : ℕ) : ℕ∞) := by
  refine le_trans hk ?_
  by_cases hn : n ≤ B.natDegree
  · rw [F.stageHeight_eq_inf]
    refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))) ?_
    rw [GateKit.gaussVal_C]
    exact le_of_eq (by push_cast; ring)
  · rw [B.coeff_eq_zero_of_natDegree_lt (by omega), addVal_zero,
      C118a.smul_top_pos F.he₁, top_add]
    exact le_top

/-- The exact depth at an aligned on-or-below-line index. -/
private theorem depth_spec (F : KeyFrame O π) {k n : ℕ}
    (halign : n * F.h ≡ k [MOD F.e₁]) (hnh : n * F.h ≤ k) :
    F.e₁ * ((k - n * F.h) / F.e₁) + n * F.h = k := by
  have hdvd : F.e₁ ∣ k - n * F.h := (Nat.modEq_iff_dvd' hnh).mp halign
  rw [Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hnh]

/-- Alignment is the slot-index congruence: `n % e₁ = i(k) ↔ n·h ≡ k (mod e₁)` (C.16's
uniqueness through `hcop`). -/
private theorem aligned_iff (F : KeyFrame O π) (k n : ℕ) :
    n % F.e₁ = F.slotIdx k ↔ n * F.h ≡ k [MOD F.e₁] := by
  have hspec := F.slotIdx_spec k
  constructor
  · intro h
    calc n * F.h ≡ n % F.e₁ * F.h [MOD F.e₁] :=
          (Nat.ModEq.mul_right F.h (Nat.mod_modEq n F.e₁)).symm
      _ = F.slotIdx k * F.h := by rw [h]
      _ ≡ k [MOD F.e₁] := hspec.2
  · intro h
    have h1 : n % F.e₁ * F.h ≡ F.slotIdx k * F.h [MOD F.e₁] :=
      ((Nat.ModEq.mul_right F.h (Nat.mod_modEq n F.e₁)).trans h).trans hspec.2.symm
    have h2 : n % F.e₁ ≡ F.slotIdx k [MOD F.e₁] :=
      Nat.ModEq.cancel_right_of_coprime F.hcop.symm h1
    have h3 : n % F.e₁ < F.e₁ := Nat.mod_lt n F.he₁
    have h4 : F.slotIdx k < F.e₁ := hspec.1
    have h5 : n % F.e₁ % F.e₁ = F.slotIdx k % F.e₁ := h2
    rwa [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] at h5

/-- The aligned coefficient's exact-depth valuation floor (rp2's private
`addVal_coeff_of_le_stageHeight`, re-derived from `line_floor`). -/
private theorem aligned_val_floor (F : KeyFrame O π) {B : Polynomial O} {k n q : ℕ}
    (hspec : F.e₁ * q + n * F.h = k) (hk : (k : ℕ∞) ≤ F.stageHeight B) :
    (q : ℕ∞) ≤ addVal O (B.coeff n) := by
  have h := line_floor F hk n
  rcases eq_or_ne (addVal O (B.coeff n)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : k ≤ F.e₁ * v + n * F.h := by exact_mod_cast h
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : F.e₁ * q ≤ F.e₁ * v) F.he₁

/-- The STRICT side floor at a bad index: off-alignment or an above-line abscissa prices
the coefficient strictly above the line. -/
private theorem side_strict (F : KeyFrame O π) {B : Polynomial O} {kb n : ℕ}
    (hk : (kb : ℕ∞) ≤ F.stageHeight B)
    (hbad : ¬ (n % F.e₁ = F.slotIdx kb ∧ n * F.h ≤ kb)) :
    ((kb + 1 : ℕ) : ℕ∞) ≤ F.e₁ • addVal O (B.coeff n) + ((n * F.h : ℕ) : ℕ∞) := by
  have h := line_floor F hk n
  rcases eq_or_ne (addVal O (B.coeff n)) ⊤ with hT | hT
  · rw [hT, C118a.smul_top_pos F.he₁, top_add]
    exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at h ⊢
  rw [nsmul_eq_mul] at h ⊢
  have hnat : kb ≤ F.e₁ * v + n * F.h := by exact_mod_cast h
  have hne : F.e₁ * v + n * F.h ≠ kb := by
    intro heq
    rcases not_and_or.mp hbad with hal | hup
    · refine hal ((aligned_iff F kb n).mpr ?_)
      calc n * F.h ≡ F.e₁ * v + n * F.h [MOD F.e₁] :=
            (Nat.modEq_iff_dvd' (by omega)).mpr ⟨v, by omega⟩
        _ = kb := heq
    · exact hup (by omega)
  have : kb + 1 ≤ F.e₁ * v + n * F.h := by omega
  exact_mod_cast this

/-! ### 10.2 the full read (the fence-free window sum) -/

/-- The FULL height-`k` read of an arbitrary polynomial: the C.21 window sum without the
`t < f₁` fence — every aligned on-or-below-line coefficient contributes, with `η`-powers
beyond the power basis reduced in `K`.  On digits this IS `slotRes` (`fullRead_eq_slotRes`);
on the key it is `ψ(η) = 0` (`fullRead_key`) — precisely the leak that made bare-window
reasoning fail in the withdrawn M1(2). -/
private noncomputable def fullRead (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (k : ℕ) (P : Polynomial O) : F.stageField H₀ hpin :=
  ∑ n ∈ (Finset.range (P.natDegree + 1)).filter
      (fun n => n % F.e₁ = F.slotIdx k ∧ n * F.h ≤ k),
    algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π ((k - n * F.h) / F.e₁) (P.coeff n)))
      * (F.stageLetter H₀ hpin) ^ ((n - F.slotIdx k) / F.e₁)

/-- The full read of `0` vanishes. -/
private theorem fullRead_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) (k : ℕ) : fullRead F H₀ hpin k (0 : Polynomial O) = 0 := by
  rw [fullRead]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Polynomial.coeff_zero, digAt_zero_elem hπ, map_zero, map_zero, zero_mul]

/-- ℕ∞ strictness upgrade: `k < x` gives the `k + 1` floor. -/
private theorem succ_le_of_coe_lt {k : ℕ} {x : ℕ∞} (hk : (k : ℕ∞) < x) :
    ((k + 1 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hw] at hk ⊢
  exact_mod_cast (by exact_mod_cast hk : k < w)

/-- The STRICT exact-depth valuation floor: one step above the line, one more `π`. -/
private theorem strict_depth_val (F : KeyFrame O π) {B : Polynomial O} {k n m : ℕ}
    (hk1 : ((k + 1 : ℕ) : ℕ∞) ≤ F.stageHeight B) (hspec : F.e₁ * m + n * F.h = k) :
    ((m + 1 : ℕ) : ℕ∞) ≤ addVal O (B.coeff n) := by
  have h := line_floor F hk1 n
  rcases eq_or_ne (addVal O (B.coeff n)) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at h ⊢
  rw [nsmul_eq_mul] at h
  have hnat : k + 1 ≤ F.e₁ * v + n * F.h := by exact_mod_cast h
  have hmv : m < v := Nat.lt_of_mul_lt_mul_left (a := F.e₁) (by omega)
  exact_mod_cast hmv

/-- The full read at a height strictly below the stage height vanishes. -/
private theorem fullRead_eq_zero_of_lt (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {k : ℕ} {P : Polynomial O} (hk : (k : ℕ∞) < F.stageHeight P) :
    fullRead F H₀ hpin k P = 0 := by
  rw [fullRead]
  refine Finset.sum_eq_zero fun n hn => ?_
  obtain ⟨-, halign, hnh⟩ := Finset.mem_filter.mp hn
  have hspec := depth_spec F ((aligned_iff F k n).mp halign) hnh
  have hval := strict_depth_val F (succ_le_of_coe_lt hk) (by omega :
    F.e₁ * ((k - n * F.h) / F.e₁) + n * F.h = k)
  have hdvd : π ^ ((k - n * F.h) / F.e₁) ∣ P.coeff n :=
    dvd_of_le_addVal hπ (le_trans (by exact_mod_cast Nat.le_succ _) hval)
  have hdvd1 : π ^ ((k - n * F.h) / F.e₁ + 1) ∣ P.coeff n := dvd_of_le_addVal hπ hval
  rw [(digAt_eq_zero_iff hπ hdvd).mpr hdvd1, map_zero, map_zero, zero_mul]

/-- The full read is range-stable: any range bound past the degree computes it. -/
private theorem fullRead_eq_sum_range (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) (k : ℕ) (P : Polynomial O) {N : ℕ} (hN : P.natDegree < N) :
    fullRead F H₀ hpin k P
      = ∑ n ∈ (Finset.range N).filter
          (fun n => n % F.e₁ = F.slotIdx k ∧ n * F.h ≤ k),
          algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
              (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
                (digAt π ((k - n * F.h) / F.e₁) (P.coeff n)))
            * (F.stageLetter H₀ hpin) ^ ((n - F.slotIdx k) / F.e₁) := by
  classical
  rw [fullRead]
  refine Finset.sum_subset (Finset.filter_subset_filter _
    (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega)))) fun n hn hn' => ?_
  obtain ⟨hnr, hcond⟩ := Finset.mem_filter.mp hn
  have hgt : P.natDegree < n := by
    by_contra hle
    exact hn' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcond⟩)
  rw [P.coeff_eq_zero_of_natDegree_lt hgt, digAt_zero_elem hπ, map_zero, map_zero, zero_mul]

/-- On digits the full read IS the C.21 slot read (the `t < f₁` fence is inactive). -/
private theorem fullRead_eq_slotRes (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {P : Polynomial O} (hdeg : P.natDegree < F.e₁ * F.f₁) (k : ℕ) :
    fullRead F H₀ hpin k P = F.slotRes H₀ hpin k P := by
  classical
  rw [fullRead, KeyFrame.slotRes]
  have hvan : ∀ t ∈ F.slotWindow k,
      t ∉ (F.slotWindow k).filter (fun t => F.slotIdx k + F.e₁ * t ≤ P.natDegree) →
      algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
            (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
              (P.coeff (F.slotIdx k + F.e₁ * t))))
        * (F.stageLetter H₀ hpin) ^ t = 0 := by
    intro t ht ht'
    have hgt : P.natDegree < F.slotIdx k + F.e₁ * t := by
      by_contra hle
      exact ht' (Finset.mem_filter.mpr ⟨ht, by omega⟩)
    rw [P.coeff_eq_zero_of_natDegree_lt hgt, digAt_zero_elem hπ, map_zero, map_zero,
      zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hvan]
  refine Finset.sum_nbij' (fun n => (n - F.slotIdx k) / F.e₁)
    (fun t => F.slotIdx k + F.e₁ * t) ?_ ?_ ?_ ?_ ?_
  · -- forward membership: aligned n ↦ its slot
    intro n hn
    obtain ⟨hnr, halign, hnh⟩ := Finset.mem_filter.mp hn
    have hnle : n ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnr)
    have hrec : F.slotIdx k + F.e₁ * ((n - F.slotIdx k) / F.e₁) = n := by
      have hd := Nat.div_add_mod n F.e₁
      have hik : F.slotIdx k ≤ n := halign ▸ Nat.mod_le n F.e₁
      have : n - F.slotIdx k = F.e₁ * (n / F.e₁) := by omega
      rw [this, Nat.mul_div_cancel_left _ F.he₁]
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_range.mpr ?_
      have hlt : F.slotIdx k + F.e₁ * ((n - F.slotIdx k) / F.e₁) < F.e₁ * F.f₁ := by
        rw [hrec]; omega
      have := (F.slotIdx_spec k).1
      by_contra hge
      push Not at hge
      have : F.e₁ * F.f₁ ≤ F.e₁ * ((n - F.slotIdx k) / F.e₁) :=
        Nat.mul_le_mul_left _ hge
      omega
    · rw [KeyFrame.slotWindow] at *
      rw [hrec]
      exact hnh
    · rw [hrec]
      exact hnle
  · -- backward membership: a slot within the degree ↦ its aligned index
    intro t ht
    obtain ⟨htw, htd⟩ := Finset.mem_filter.mp ht
    have htw' := Finset.mem_filter.mp (by simpa only [KeyFrame.slotWindow] using htw)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (F.slotIdx_spec k).1]
    · exact htw'.2
  · -- left inverse
    intro n hn
    obtain ⟨-, halign, -⟩ := Finset.mem_filter.mp hn
    have hik : F.slotIdx k ≤ n := halign ▸ Nat.mod_le n F.e₁
    have hd := Nat.div_add_mod n F.e₁
    have h1 : n - F.slotIdx k = F.e₁ * (n / F.e₁) := by omega
    rw [h1, Nat.mul_div_cancel_left _ F.he₁]
    omega
  · -- right inverse
    intro t ht
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ F.he₁]
  · -- value compatibility
    intro n hn
    obtain ⟨-, halign, -⟩ := Finset.mem_filter.mp hn
    have hik : F.slotIdx k ≤ n := halign ▸ Nat.mod_le n F.e₁
    have hd := Nat.div_add_mod n F.e₁
    have h1 : n - F.slotIdx k = F.e₁ * (n / F.e₁) := by omega
    have hrec : F.slotIdx k + F.e₁ * ((n - F.slotIdx k) / F.e₁) = n := by
      rw [h1, Nat.mul_div_cancel_left _ F.he₁]
      omega
    rw [hrec]

/-- Full-read additivity at a common height floor (`slotRes_add_of_le`'s twin). -/
private theorem fullRead_add_of_le (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ F.stageHeight A) (hB : (k : ℕ∞) ≤ F.stageHeight B) :
    fullRead F H₀ hpin k (A + B)
      = fullRead F H₀ hpin k A + fullRead F H₀ hpin k B := by
  classical
  set N := (A + B).natDegree + A.natDegree + B.natDegree + 1 with hN
  rw [fullRead_eq_sum_range F hπ H₀ hpin k (A + B) (show (A + B).natDegree < N by
      have := Polynomial.natDegree_add_le A B
      omega),
    fullRead_eq_sum_range F hπ H₀ hpin k A (N := N) (by omega),
    fullRead_eq_sum_range F hπ H₀ hpin k B (N := N) (by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨-, halign, hnh⟩ := Finset.mem_filter.mp hn
  have hspec := depth_spec F ((aligned_iff F k n).mp halign) hnh
  have hdA : π ^ ((k - n * F.h) / F.e₁) ∣ A.coeff n :=
    dvd_of_le_addVal hπ (aligned_val_floor F hspec hA)
  have hdB : π ^ ((k - n * F.h) / F.e₁) ∣ B.coeff n :=
    dvd_of_le_addVal hπ (aligned_val_floor F hspec hB)
  rw [Polynomial.coeff_add, digAt_add hπ hdA hdB, map_add, map_add, add_mul]

/-! ### 10.4 the key's symbol dies: `MH.0a` + the pin + `ψ(η) = 0` -/

/-- **MH.0a** — the frame key's EXACT stage height `D′·h`, from purity's right endpoint and
the monic top coefficient. -/
private theorem stageHeight_key_eq (F : KeyFrame O π) :
    F.stageHeight F.key = ((F.h * (F.e₁ * F.f₁) : ℕ) : ℕ∞) := by
  have h2 : OnSide Polynomial.X F.key F.h F.e₁ F.key.natDegree := by
    have := F.hpure.2
    rwa [Polynomial.natDegree_X, Nat.div_one] at this
  have h3 : F.e₁ • npHgt Polynomial.X F.key F.key.natDegree
      + ((F.h * F.key.natDegree : ℕ) : ℕ∞) = suppVal Polynomial.X F.key F.h F.e₁ := h2
  rw [npHgt, dev_X, GateKit.gaussVal_C, F.hmonic.coeff_natDegree, addVal_one, smul_zero,
    zero_add] at h3
  show suppVal Polynomial.X F.key F.h F.e₁ = _
  rw [← h3, F.hdeg]

/-- The key's level-1 side starts at abscissa `0` (purity's left endpoint). -/
private theorem sideMin_key_eq_zero (F : KeyFrame O π) :
    sideMin Polynomial.X F.key F.h F.e₁ F.hne = 0 := by
  classical
  have hmem : (0 : ℕ) ∈ sideSet Polynomial.X F.key F.h F.e₁ := by
    show (0 : ℕ) ∈ Finset.filter (OnSide Polynomial.X F.key F.h F.e₁)
      (Finset.range (F.key.natDegree + 1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), F.hpure.1⟩
  exact Nat.le_zero.mp (Finset.min'_le _ _ hmem)

/-- The pin numeral is `h·f₁` (the key's left-endpoint height, forced by MH.0a). -/
private theorem pin_eq (F : KeyFrame O π) {H₀ : ℕ} (hpin : F.Pin H₀) :
    H₀ = F.h * F.f₁ := by
  have hp : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne)
      = (H₀ : ℕ∞) := hpin
  rw [sideMin_key_eq_zero] at hp
  have h1 : F.e₁ • npHgt Polynomial.X F.key 0 + ((F.h * 0 : ℕ) : ℕ∞)
      = suppVal Polynomial.X F.key F.h F.e₁ := F.hpure.1
  have h2 : suppVal Polynomial.X F.key F.h F.e₁ = ((F.h * (F.e₁ * F.f₁) : ℕ) : ℕ∞) :=
    stageHeight_key_eq F
  rw [hp, h2, Nat.mul_zero, Nat.cast_zero, add_zero, nsmul_eq_mul] at h1
  have hnat : F.e₁ * H₀ = F.h * (F.e₁ * F.f₁) := by exact_mod_cast h1
  have hnat' : F.e₁ * H₀ = F.e₁ * (F.h * F.f₁) := by rw [hnat]; ring
  exact Nat.eq_of_mul_eq_mul_left F.he₁ hnat'

set_option linter.unusedVariables false in
/-- `digPoly` of a constant is the constant of the digit (`hπ` carried for call-site
uniformity). -/
private theorem digPoly_C (hπ : Irreducible π) (m : ℕ) (c : O) :
    digPoly π m (Polynomial.C c) = Polynomial.C (digAt π m c) := by
  rw [digPoly, Polynomial.natDegree_C]
  simp [Polynomial.coeff_C_zero]

/-- The frame residual's coefficients ARE the full read's digit reads of the key (B.28/B.29
unwound at `φ = X` under the purity pins). -/
private theorem frameRes_coeff_eq (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {j : ℕ} (hj : j ≤ F.f₁) :
    (F.frameRes H₀ hpin).coeff j
      = algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π (H₀ - F.h * j) (F.key.coeff (F.e₁ * j))) := by
  classical
  have hψne : F.frameRes H₀ hpin ≠ 0 := (F.hresirr H₀ hpin).1.ne_zero
  have hψdeg : (F.frameRes H₀ hpin).natDegree = F.f₁ := (F.hresirr H₀ hpin).2
  have hfsd : F.f₁ ≤ sideDeg Polynomial.X F.key F.h F.e₁ F.hne := by
    by_contra hlt
    push Not at hlt
    have hzero : (F.frameRes H₀ hpin).coeff F.f₁ = 0 := by
      show (resPoly π Polynomial.X F.key F.h F.e₁ F.hne H₀).coeff F.f₁ = 0
      rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg (by omega)]
    have hne0 : (F.frameRes H₀ hpin).coeff F.f₁ ≠ 0 := by
      rw [← hψdeg]
      exact Polynomial.leadingCoeff_ne_zero.mpr hψne
    exact hne0 hzero
  show (resPoly π Polynomial.X F.key F.h F.e₁ F.hne H₀).coeff j = _
  rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_pos (by omega),
    resCoeff, sideMin_key_eq_zero, Nat.zero_add, dev_X, resMk, digPoly_C hπ,
    AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/-- ★ **The key's symbol dies**: the full read of the key at its exact height `D′·h` is
`ψ(η) = 0` — the mechanism the withdrawn M1(2) hand-waved, made exact. -/
private theorem fullRead_key (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) :
    fullRead F H₀ hpin (F.h * (F.e₁ * F.f₁)) F.key = 0 := by
  classical
  have hik : F.slotIdx (F.h * (F.e₁ * F.f₁)) = 0 := by
    have h0 : (0 : ℕ) % F.e₁ = F.slotIdx (F.h * (F.e₁ * F.f₁)) :=
      (aligned_iff F _ 0).mpr (by
        show 0 * F.h ≡ F.h * (F.e₁ * F.f₁) [MOD F.e₁]
        rw [Nat.zero_mul]
        exact (Nat.modEq_zero_iff_dvd.mpr ⟨F.h * F.f₁, by ring⟩).symm)
    rw [Nat.zero_mod] at h0
    exact h0.symm
  have hkey : fullRead F H₀ hpin (F.h * (F.e₁ * F.f₁)) F.key
      = ∑ j ∈ Finset.range (F.f₁ + 1),
          algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
            ((F.frameRes H₀ hpin).coeff j) * (F.stageLetter H₀ hpin) ^ j := by
    rw [fullRead]
    refine Finset.sum_nbij' (fun n => n / F.e₁) (fun j => F.e₁ * j) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hnr, halign, -⟩ := Finset.mem_filter.mp hn
      rw [hik] at halign
      have hdvd : F.e₁ ∣ n := Nat.dvd_of_mod_eq_zero halign
      have hnle : n ≤ F.key.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnr)
      rw [F.hdeg] at hnle
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      obtain ⟨c, rfl⟩ := hdvd
      rw [Nat.mul_div_cancel_left _ F.he₁]
      exact Nat.le_of_mul_le_mul_left hnle F.he₁
    · intro j hj
      have hjle : j ≤ F.f₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
      · rw [F.hdeg]
        have : F.e₁ * j ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left _ hjle
        omega
      · rw [hik, Nat.mul_mod_right]
      · calc F.e₁ * j * F.h ≤ F.e₁ * F.f₁ * F.h :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hjle)
          _ = F.h * (F.e₁ * F.f₁) := by ring
    · intro n hn
      obtain ⟨-, halign, -⟩ := Finset.mem_filter.mp hn
      rw [hik] at halign
      obtain ⟨c, rfl⟩ := Nat.dvd_of_mod_eq_zero halign
      rw [Nat.mul_div_cancel_left _ F.he₁]
    · intro j hj
      rw [Nat.mul_div_cancel_left _ F.he₁]
    · intro n hn
      obtain ⟨hnr, halign, hnh⟩ := Finset.mem_filter.mp hn
      rw [hik] at halign
      obtain ⟨c, rfl⟩ := Nat.dvd_of_mod_eq_zero halign
      have hcle : c ≤ F.f₁ := by
        have hnle : F.e₁ * c ≤ F.key.natDegree :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hnr)
        rw [F.hdeg] at hnle
        exact Nat.le_of_mul_le_mul_left hnle F.he₁
      have e1 : F.e₁ * c / F.e₁ = c := Nat.mul_div_cancel_left _ F.he₁
      have e2 : (F.h * (F.e₁ * F.f₁) - F.e₁ * c * F.h) / F.e₁ = H₀ - F.h * c := by
        have h1 : F.h * c ≤ F.h * F.f₁ := Nat.mul_le_mul_left _ hcle
        have hsub : F.h * (F.e₁ * F.f₁) - F.e₁ * c * F.h
            = F.e₁ * (F.h * F.f₁ - F.h * c) := by
          zify [h1, show F.e₁ * c * F.h ≤ F.h * (F.e₁ * F.f₁) from by
            calc F.e₁ * c * F.h ≤ F.e₁ * F.f₁ * F.h :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcle)
              _ = F.h * (F.e₁ * F.f₁) := by ring]
          ring
        rw [hsub, Nat.mul_div_cancel_left _ F.he₁, pin_eq F hpin]
      have e3 : (F.e₁ * c - F.slotIdx (F.h * (F.e₁ * F.f₁))) / F.e₁ = c := by
        rw [hik, Nat.sub_zero, Nat.mul_div_cancel_left _ F.he₁]
      rw [e2, e3, e1, frameRes_coeff_eq F hπ H₀ hpin hcle]
  rw [hkey]
  have heval : ∑ j ∈ Finset.range (F.f₁ + 1),
      algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        ((F.frameRes H₀ hpin).coeff j) * (F.stageLetter H₀ hpin) ^ j
      = Polynomial.eval₂
          (algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin))
          (F.stageLetter H₀ hpin) (F.frameRes H₀ hpin) := by
    have hdeg' : (F.frameRes H₀ hpin).natDegree = F.f₁ := (F.hresirr H₀ hpin).2
    rw [Polynomial.eval₂_eq_sum_range, hdeg']
  rw [heval, KeyFrame.stageLetter, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root _

/-! ### 10.5 the convolution law with carry (M1′'s engine) -/

/-- Depth extraction from an `e₁`-weighted line floor. -/
private theorem extract_depth {e₁ h' k n m : ℕ} {x : ℕ∞} (he : 0 < e₁)
    (hspec : e₁ * m + n * h' = k) (hx : (k : ℕ∞) ≤ e₁ • x + ((n * h' : ℕ) : ℕ∞)) :
    (m : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at hx ⊢
  rw [nsmul_eq_mul] at hx
  have hnat : k ≤ e₁ * v + n * h' := by exact_mod_cast hx
  exact_mod_cast Nat.le_of_mul_le_mul_left (by omega : e₁ * m ≤ e₁ * v) he

set_option linter.unusedVariables false in
/-- Strict depth extraction: one step above the line, one more `π` (`he` carried for
signature symmetry with `extract_depth`). -/
private theorem extract_depth_strict {e₁ h' k n m : ℕ} {x : ℕ∞} (he : 0 < e₁)
    (hspec : e₁ * m + n * h' = k) (hx : ((k + 1 : ℕ) : ℕ∞) ≤ e₁ • x + ((n * h' : ℕ) : ℕ∞)) :
    ((m + 1 : ℕ) : ℕ∞) ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hT
  · exact le_top
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hv] at hx ⊢
  rw [nsmul_eq_mul] at hx
  have hnat : k + 1 ≤ e₁ * v + n * h' := by exact_mod_cast hx
  exact_mod_cast Nat.lt_of_mul_lt_mul_left (a := e₁) (by omega)

/-- **The pair kill**: a convolution pair with a bad side (off-aligned, or above its line)
digit-reads `0` at the joint depth. -/
private theorem pair_read_kill (F : KeyFrame O π) (hπ : Irreducible π)
    {P R : Polynomial O} {kp kr n₁ n₂ m : ℕ}
    (hP : (kp : ℕ∞) ≤ F.stageHeight P) (hR : (kr : ℕ∞) ≤ F.stageHeight R)
    (hspec : F.e₁ * m + (n₁ + n₂) * F.h = kp + kr)
    (hbad : ¬ ((n₁ % F.e₁ = F.slotIdx kp ∧ n₁ * F.h ≤ kp)
      ∧ (n₂ % F.e₁ = F.slotIdx kr ∧ n₂ * F.h ≤ kr))) :
    digAt π m (P.coeff n₁ * R.coeff n₂) = 0 := by
  have hstrict : ((kp + kr + 1 : ℕ) : ℕ∞)
      ≤ F.e₁ • (addVal O (P.coeff n₁) + addVal O (R.coeff n₂))
        + (((n₁ + n₂) * F.h : ℕ) : ℕ∞) := by
    rcases not_and_or.mp hbad with hb | hb
    · calc ((kp + kr + 1 : ℕ) : ℕ∞)
          = ((kp + 1 : ℕ) : ℕ∞) + ((kr : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (F.e₁ • addVal O (P.coeff n₁) + ((n₁ * F.h : ℕ) : ℕ∞))
            + (F.e₁ • addVal O (R.coeff n₂) + ((n₂ * F.h : ℕ) : ℕ∞)) :=
            add_le_add (side_strict F hP hb) (line_floor F hR n₂)
        _ = F.e₁ • (addVal O (P.coeff n₁) + addVal O (R.coeff n₂))
            + (((n₁ + n₂) * F.h : ℕ) : ℕ∞) := by
            rw [nsmul_add]
            push_cast
            ring
    · calc ((kp + kr + 1 : ℕ) : ℕ∞)
          = ((kp : ℕ) : ℕ∞) + ((kr + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ (F.e₁ • addVal O (P.coeff n₁) + ((n₁ * F.h : ℕ) : ℕ∞))
            + (F.e₁ • addVal O (R.coeff n₂) + ((n₂ * F.h : ℕ) : ℕ∞)) :=
            add_le_add (line_floor F hP n₁) (side_strict F hR hb)
        _ = F.e₁ • (addVal O (P.coeff n₁) + addVal O (R.coeff n₂))
            + (((n₁ + n₂) * F.h : ℕ) : ℕ∞) := by
            rw [nsmul_add]
            push_cast
            ring
  have hval : ((m + 1 : ℕ) : ℕ∞) ≤ addVal O (P.coeff n₁ * R.coeff n₂) := by
    rw [addVal_mul]
    exact extract_depth_strict F.he₁ hspec hstrict
  have hdvd : π ^ m ∣ P.coeff n₁ * R.coeff n₂ :=
    dvd_of_le_addVal hπ (le_trans (by exact_mod_cast Nat.le_succ m) hval)
  exact (digAt_eq_zero_iff hπ hdvd).mpr (dvd_of_le_addVal hπ hval)

/-- ★ **The full-read convolution law with the TW-δ carry** (M1′'s engine, ALL
polynomials, floors only): `fullRead (kp+kr) (P·R) = η^δ · fullRead kp P · fullRead kr R`,
`δ` the slot-index carry bit. -/
private theorem fullRead_mul_of_le (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {P R : Polynomial O} {kp kr δ : ℕ}
    (hδi : F.slotIdx kp + F.slotIdx kr = F.slotIdx (kp + kr) + F.e₁ * δ)
    (hP : (kp : ℕ∞) ≤ F.stageHeight P) (hR : (kr : ℕ∞) ≤ F.stageHeight R) :
    fullRead F H₀ hpin (kp + kr) (P * R)
      = F.stageLetter H₀ hpin ^ δ
        * (fullRead F H₀ hpin kp P * fullRead F H₀ hpin kr R) := by
  classical
  rcases eq_or_ne P 0 with rfl | hP0
  · simp only [zero_mul, fullRead_zero F hπ H₀ hpin, mul_zero]
  rcases eq_or_ne R 0 with rfl | hR0
  · simp only [mul_zero, fullRead_zero F hπ H₀ hpin, mul_zero]
  rw [fullRead, fullRead, fullRead]
  set SP := (Finset.range (P.natDegree + 1)).filter
    (fun n => n % F.e₁ = F.slotIdx kp ∧ n * F.h ≤ kp) with hSP
  set SR := (Finset.range (R.natDegree + 1)).filter
    (fun n => n % F.e₁ = F.slotIdx kr ∧ n * F.h ≤ kr) with hSR
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  have hmaps : ∀ q ∈ SP ×ˢ SR, q.1 + q.2
      ∈ (Finset.range ((P * R).natDegree + 1)).filter
        (fun n => n % F.e₁ = F.slotIdx (kp + kr) ∧ n * F.h ≤ kp + kr) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    obtain ⟨hr1, ha1, hh1⟩ := Finset.mem_filter.mp hq1
    obtain ⟨hr2, ha2, hh2⟩ := Finset.mem_filter.mp hq2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
    · rw [Polynomial.natDegree_mul hP0 hR0]
      have h1' := Finset.mem_range.mp hr1
      have h2' := Finset.mem_range.mp hr2
      omega
    · rw [Nat.add_mod, ha1, ha2, hδi, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (F.slotIdx_spec (kp + kr)).1]
    · rw [Nat.add_mul]
      omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hnr, halign, hnh⟩ := Finset.mem_filter.mp hn
  have hspec := depth_spec F ((aligned_iff F (kp + kr) n).mp halign) hnh
  have hdvd_all : ∀ q ∈ Finset.antidiagonal n,
      π ^ ((kp + kr - n * F.h) / F.e₁) ∣ P.coeff q.1 * R.coeff q.2 := by
    intro q hq
    have hqsum : q.1 + q.2 = n := Finset.mem_antidiagonal.mp hq
    have hline : ((kp + kr : ℕ) : ℕ∞)
        ≤ F.e₁ • (addVal O (P.coeff q.1) + addVal O (R.coeff q.2))
          + ((n * F.h : ℕ) : ℕ∞) := by
      calc ((kp + kr : ℕ) : ℕ∞) = ((kp : ℕ) : ℕ∞) + ((kr : ℕ) : ℕ∞) := by
            push_cast; ring
        _ ≤ (F.e₁ • addVal O (P.coeff q.1) + ((q.1 * F.h : ℕ) : ℕ∞))
            + (F.e₁ • addVal O (R.coeff q.2) + ((q.2 * F.h : ℕ) : ℕ∞)) :=
            add_le_add (line_floor F hP q.1) (line_floor F hR q.2)
        _ = F.e₁ • (addVal O (P.coeff q.1) + addVal O (R.coeff q.2))
            + ((n * F.h : ℕ) : ℕ∞) := by
            rw [nsmul_add, ← hqsum, Nat.add_mul]
            push_cast
            ring
    refine dvd_of_le_addVal hπ ?_
    rw [addVal_mul]
    exact extract_depth F.he₁ hspec hline
  rw [Polynomial.coeff_mul, digAt_finsetSum hπ _ _ hdvd_all, map_sum, map_sum,
    Finset.sum_mul,
    ← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal n)
      (fun q => q.1 ∈ SP ∧ q.2 ∈ SR)]
  have hbad0 : ∑ q ∈ (Finset.antidiagonal n).filter (fun q => ¬ (q.1 ∈ SP ∧ q.2 ∈ SR)),
      algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
            (digAt π ((kp + kr - n * F.h) / F.e₁) (P.coeff q.1 * R.coeff q.2)))
        * F.stageLetter H₀ hpin ^ ((n - F.slotIdx (kp + kr)) / F.e₁) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hqa, hqbad⟩ := Finset.mem_filter.mp hq
    have hqsum : q.1 + q.2 = n := Finset.mem_antidiagonal.mp hqa
    have hkill : digAt π ((kp + kr - n * F.h) / F.e₁)
        (P.coeff q.1 * R.coeff q.2) = 0 := by
      by_cases hd1 : q.1 ≤ P.natDegree
      · by_cases hd2 : q.2 ≤ R.natDegree
        · refine pair_read_kill F hπ hP hR (by rw [hqsum]; exact hspec) ?_
          rintro ⟨hc1, hc2⟩
          exact hqbad ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc2⟩⟩
        · rw [R.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, digAt_zero_elem hπ]
      · rw [P.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, digAt_zero_elem hπ]
    rw [hkill, map_zero, map_zero, zero_mul]
  rw [hbad0, add_zero]
  have hsets : (Finset.antidiagonal n).filter (fun q => q.1 ∈ SP ∧ q.2 ∈ SR)
      = (SP ×ˢ SR).filter (fun q => q.1 + q.2 = n) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_product]
    tauto
  rw [hsets]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hqmem, hqsum⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqmem
  obtain ⟨hr1, ha1, hh1⟩ := Finset.mem_filter.mp hq1
  obtain ⟨hr2, ha2, hh2⟩ := Finset.mem_filter.mp hq2
  have hspec1 := depth_spec F ((aligned_iff F kp q.1).mp ha1) hh1
  have hspec2 := depth_spec F ((aligned_iff F kr q.2).mp ha2) hh2
  have hmsplit : (kp - q.1 * F.h) / F.e₁ + (kr - q.2 * F.h) / F.e₁
      = (kp + kr - n * F.h) / F.e₁ := by
    have hn' : n * F.h = q.1 * F.h + q.2 * F.h := by rw [← hqsum, Nat.add_mul]
    refine Nat.eq_of_mul_eq_mul_left F.he₁ ?_
    rw [Nat.mul_add]
    omega
  have hdvd1 : π ^ ((kp - q.1 * F.h) / F.e₁) ∣ P.coeff q.1 :=
    dvd_of_le_addVal hπ (aligned_val_floor F hspec1 hP)
  have hdvd2 : π ^ ((kr - q.2 * F.h) / F.e₁) ∣ R.coeff q.2 :=
    dvd_of_le_addVal hπ (aligned_val_floor F hspec2 hR)
  have hdig : digAt π ((kp + kr - n * F.h) / F.e₁) (P.coeff q.1 * R.coeff q.2)
      = digAt π ((kp - q.1 * F.h) / F.e₁) (P.coeff q.1)
        * digAt π ((kr - q.2 * F.h) / F.e₁) (R.coeff q.2) := by
    rw [← hmsplit]
    exact digAt_mul_split hπ hdvd1 hdvd2
  have hq1e : q.1 = F.e₁ * (q.1 / F.e₁) + F.slotIdx kp := by
    conv_lhs => rw [← Nat.div_add_mod q.1 F.e₁]
    rw [ha1]
  have hq2e : q.2 = F.e₁ * (q.2 / F.e₁) + F.slotIdx kr := by
    conv_lhs => rw [← Nat.div_add_mod q.2 F.e₁]
    rw [ha2]
  have hexp1 : (q.1 - F.slotIdx kp) / F.e₁ = q.1 / F.e₁ := by
    rw [show q.1 - F.slotIdx kp = F.e₁ * (q.1 / F.e₁) by omega,
      Nat.mul_div_cancel_left _ F.he₁]
  have hexp2 : (q.2 - F.slotIdx kr) / F.e₁ = q.2 / F.e₁ := by
    rw [show q.2 - F.slotIdx kr = F.e₁ * (q.2 / F.e₁) by omega,
      Nat.mul_div_cancel_left _ F.he₁]
  have hexpn : (n - F.slotIdx (kp + kr)) / F.e₁ = q.1 / F.e₁ + q.2 / F.e₁ + δ := by
    have hsum : n = F.e₁ * (q.1 / F.e₁ + q.2 / F.e₁ + δ) + F.slotIdx (kp + kr) := by
      calc n = q.1 + q.2 := hqsum.symm
        _ = (F.e₁ * (q.1 / F.e₁) + F.slotIdx kp)
            + (F.e₁ * (q.2 / F.e₁) + F.slotIdx kr) := by rw [← hq1e, ← hq2e]
        _ = F.e₁ * (q.1 / F.e₁) + F.e₁ * (q.2 / F.e₁)
            + (F.slotIdx kp + F.slotIdx kr) := by ring
        _ = F.e₁ * (q.1 / F.e₁) + F.e₁ * (q.2 / F.e₁)
            + (F.slotIdx (kp + kr) + F.e₁ * δ) := by rw [hδi]
        _ = F.e₁ * (q.1 / F.e₁ + q.2 / F.e₁ + δ) + F.slotIdx (kp + kr) := by ring
    rw [hsum, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ F.he₁]
  rw [hdig, map_mul, map_mul, hexpn, hexp1, hexp2, pow_add, pow_add]
  ring

/-! ### 10.6 THE ROOT: M1′ clauses (2) and (1), unconditional -/

/-- ★ **PROVED — `C133mh1.M1SlotCarryLawStatement` holds**: the corrected slot-carry
product law at digits, `slotRes (ka+kb) ((a·b) %ₘ Φ′) = η^δ · slotRes ka a · slotRes kb b`.
MH.1's last two clauses close here: split `a·b = E + Φ′·Q`, the key term's full read dies
(`fullRead_key`, exact height by MH.0a — or vanishes above the line), and the convolution
law fires with the TW-δ carry. -/
theorem m1SlotCarryLaw : C133mh1.M1SlotCarryLawStatement O := by
  intro π F hπ hh H₀ hpin a b ha hb ka kb δ hka hkb hq
  classical
  obtain ⟨δ₀, hδ₀le, hq₀, hi₀⟩ := C133mh1.twistExp_add_carry F ka kb
  have hδeq : δ = δ₀ := by omega
  rw [← hδeq] at hi₀
  have hmod := Polynomial.modByMonic_add_div (a * b) F.key
  have hwab : ((ka + kb : ℕ) : ℕ∞) ≤ F.stageHeight (a * b) := by
    rw [stageHeight_mul hπ F hh, Nat.cast_add]
    exact add_le_add hka hkb
  have hwE : ((ka + kb : ℕ) : ℕ∞) ≤ F.stageHeight ((a * b) %ₘ F.key) :=
    le_trans hwab (stageHeight_le_modByMonic hπ F hh _)
  have hwKQ : ((ka + kb : ℕ) : ℕ∞) ≤ F.stageHeight (F.key * ((a * b) /ₘ F.key)) := by
    calc ((ka + kb : ℕ) : ℕ∞) ≤ F.stageHeight (a * b) := hwab
      _ ≤ F.stageHeight ((a * b) /ₘ F.key) + F.stageHeight F.key :=
          stageHeight_le_divByMonic hπ F hh _
      _ = F.stageHeight (F.key * ((a * b) /ₘ F.key)) := by
          rw [stageHeight_mul hπ F hh, add_comm]
  have hsplit : fullRead F H₀ hpin (ka + kb) (a * b)
      = fullRead F H₀ hpin (ka + kb) ((a * b) %ₘ F.key)
        + fullRead F H₀ hpin (ka + kb) (F.key * ((a * b) /ₘ F.key)) := by
    conv_lhs => rw [← hmod]
    exact fullRead_add_of_le F hπ H₀ hpin hwE hwKQ
  have hkq : fullRead F H₀ hpin (ka + kb) (F.key * ((a * b) /ₘ F.key)) = 0 := by
    rcases lt_or_ge ((ka + kb : ℕ) : ℕ∞)
      (F.stageHeight (F.key * ((a * b) /ₘ F.key))) with hlt | hge
    · exact fullRead_eq_zero_of_lt F hπ H₀ hpin hlt
    · have heq : F.stageHeight (F.key * ((a * b) /ₘ F.key)) = ((ka + kb : ℕ) : ℕ∞) :=
        le_antisymm hge hwKQ
      have hV := stageHeight_key_eq F
      have hQfin : F.stageHeight ((a * b) /ₘ F.key) ≠ ⊤ := by
        intro hT
        rw [stageHeight_mul hπ F hh, hT, add_top] at heq
        exact (ENat.coe_ne_top (ka + kb)) heq.symm
      obtain ⟨wq, hwq⟩ := ENat.ne_top_iff_exists.1 hQfin
      have hsum : F.h * (F.e₁ * F.f₁) + wq = ka + kb := by
        rw [stageHeight_mul hπ F hh, hV, ← hwq] at heq
        exact_mod_cast heq
      obtain ⟨δ', -, -, hi'⟩ := C133mh1.twistExp_add_carry F wq (F.h * (F.e₁ * F.f₁))
      have hfire := fullRead_mul_of_le F hπ H₀ hpin
        (P := (a * b) /ₘ F.key) (R := F.key)
        (kp := wq) (kr := F.h * (F.e₁ * F.f₁)) (δ := δ') hi'
        (le_of_eq hwq) (le_of_eq hV.symm)
      rw [mul_comm F.key ((a * b) /ₘ F.key),
        show ka + kb = wq + F.h * (F.e₁ * F.f₁) by omega, hfire,
        fullRead_key F hπ H₀ hpin, mul_zero, mul_zero]
  have hab : fullRead F H₀ hpin (ka + kb) (a * b)
      = F.stageLetter H₀ hpin ^ δ
        * (fullRead F H₀ hpin ka a * fullRead F H₀ hpin kb b) :=
    fullRead_mul_of_le F hπ H₀ hpin hi₀ hka hkb
  have hdegE : ((a * b) %ₘ F.key).natDegree < F.e₁ * F.f₁ := by
    rw [← dev_zero_pin F.key (a * b)]
    exact natDegree_dev_lt_frame F (a * b) 0
  have hE : fullRead F H₀ hpin (ka + kb) ((a * b) %ₘ F.key)
      = F.stageLetter H₀ hpin ^ δ
        * (fullRead F H₀ hpin ka a * fullRead F H₀ hpin kb b) := by
    have h' := hsplit
    rw [hkq, add_zero] at h'
    rw [← h', hab]
  rw [← fullRead_eq_slotRes F hπ H₀ hpin hdegE, ← fullRead_eq_slotRes F hπ H₀ hpin ha,
    ← fullRead_eq_slotRes F hπ H₀ hpin hb]
  exact hE

/-- ★ **PROVED — `C133mh1.M1TwistProductLawStatement` holds**: the corrected M1 root,
twist form — MH.1's remaining clause is CLOSED.  The carry law + the landed C133mh1
bridge (`twistRead_mul_of_slotRes_carry`). -/
theorem m1TwistProductLaw : C133mh1.M1TwistProductLawStatement O := by
  intro π F hπ hh H₀ hpin a b ha hb ka kb hka hkb
  obtain ⟨δ, -, hq, -⟩ := C133mh1.twistExp_add_carry F ka kb
  exact C133mh1.twistRead_mul_of_slotRes_carry F hπ H₀ hpin hq
    (m1SlotCarryLaw π F hπ hh H₀ hpin a b ha hb ka kb δ hka hkb hq)

end UnconditionalRoot

/-! ## Part 11 — Theorem M and the cite derivation, UNCONDITIONAL

With the root landed (`m1TwistProductLaw`), every `_of_twistLaw` theorem above
instantiates.  The headline consumers: -/

/-- ★ **Theorem M clause 1, LANDED**: `W(gz) = W(g) + W(z)`, all nonzero `g, z`. -/
theorem dvSupp_mul (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0) :
    dvSupp F (g * z) u ℓ = dvSupp F g u ℓ + dvSupp F z u ℓ :=
  dvSupp_mul_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hfloor hg hz

/-- ★ **Theorem M clause 2, LANDED**: `dvSideMin` additivity. -/
theorem dvSideMin_mul (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMin F (g * z) u ℓ hngz = dvSideMin F g u ℓ hng + dvSideMin F z u ℓ hnz :=
  dvSideMin_mul_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hfloor hg hz hng hnz hngz

/-- ★ **Theorem M clause 2, LANDED**: `dvSideMax` additivity. -/
theorem dvSideMax_mul (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideMax F (g * z) u ℓ hngz = dvSideMax F g u ℓ hng + dvSideMax F z u ℓ hnz :=
  dvSideMax_mul_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hcop hfloor hg hz
    hng hnz hngz

/-- ★ **Theorem M clause 2, LANDED**: `dvSideDeg` additivity. -/
theorem dvSideDeg_mul (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) :
    dvSideDeg F (g * z) u ℓ hngz = dvSideDeg F g u ℓ hng + dvSideDeg F z u ℓ hnz :=
  dvSideDeg_mul_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hcop hfloor hg hz
    hng hnz hngz

/-- ★ **Theorem M clause 3, LANDED — `dvResPoly_mul_gen`** (the doc §9 MH.3 name): the
mixed residual product law, τ = 1, ALL nonzero `g, z` — no monicity, purity, or degree
fence — UNCONDITIONAL. -/
theorem dvResPoly_mul_gen (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) {Mg Mz Mgz : ℕ}
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)) :
    dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
      = dvResPoly F H₀ hpin g u ℓ hng Mg hpg * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz :=
  dvResPoly_mul_gen_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hcop hfloor hg hz
    hng hnz hngz hpg hpz hpgz

/-- ★ the packaged τ = 1 mixed residual law HOLDS. -/
theorem mixedResidualLaw : MixedResidualLawTauOneStatement O :=
  mixedResidualLaw_of_twistLaw m1TwistProductLaw

/-- ★ hence the MHENS ∃-τ shape holds (τ = 1). -/
theorem mixedResidualLawExistsUnit : MixedResidualLawExistsUnitStatement O :=
  existsUnit_of_tauOne mixedResidualLaw

/-- ★ **purity closure, LANDED** (the cite's first conjunct, unconditional). -/
theorem isDvPure_mul (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    {g z : Polynomial O} (hg : g ≠ 0) (hz : z ≠ 0)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdz : F.e₁ * F.f₁ ∣ z.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpz : IsDvPure F z u ℓ) :
    IsDvPure F (g * z) u ℓ :=
  isDvPure_mul_of_twistLaw m1TwistProductLaw hπ hh H₀ hpin hℓ hcop hfloor hg hz
    hdg hdz hpg hpz

set_option linter.unusedVariables false in
/-- ★ **THE §9.2 PAYOFF, LANDED at `0 < F.h`: the declared cite `fgmn_dv_exact_mul`'s
statement as a THEOREM** (C66b.lean:90; hypothesis list matched plus the ONE honest extra
`hh : 0 < F.h`).  The remaining gap for byte-identical retirement of the axiom is ONLY the
DEGENERATE `h = 0` frame leg (C.01 admits it; Theorem M is `hh`-fenced; the doc's §9.2
claim missed this) — at `h = 0` the engine is the landed order-1 chain and the leg should
route through C.05's degenerate dictionary.  `hpos`/`hpos'` carried for the hypothesis-list
match. -/
theorem fgmn_dv_exact_mul_thm {F : KeyFrame O π} (hh : 0 < F.h) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ) :
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp
            * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp' :=
  fgmn_dv_exact_mul_of_twistLaw m1TwistProductLaw hh hπ H₀ hpin hg hg' hℓ hcop hfloor
    hdg hdg' hpos hpos' hpg hpg'

end Uniformity.Density.Tower.C133mh3

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh3.m1DigitFaithful
#print axioms Uniformity.Density.Tower.C133mh3.digit_stageHeight_modKey_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvSupp_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvSideMin_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvSideMax_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvSideDeg_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvResPoly_mul_gen_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.mixedResidualLaw_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.existsUnit_of_tauOne
#print axioms Uniformity.Density.Tower.C133mh3.isDvPure_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.fgmn_dv_exact_mul_of_twistLaw
#print axioms Uniformity.Density.Tower.C133mh3.m1SlotCarryLaw
#print axioms Uniformity.Density.Tower.C133mh3.m1TwistProductLaw
#print axioms Uniformity.Density.Tower.C133mh3.dvSupp_mul
#print axioms Uniformity.Density.Tower.C133mh3.dvSideMin_mul
#print axioms Uniformity.Density.Tower.C133mh3.dvSideMax_mul
#print axioms Uniformity.Density.Tower.C133mh3.dvSideDeg_mul
#print axioms Uniformity.Density.Tower.C133mh3.dvResPoly_mul_gen
#print axioms Uniformity.Density.Tower.C133mh3.mixedResidualLaw
#print axioms Uniformity.Density.Tower.C133mh3.mixedResidualLawExistsUnit
#print axioms Uniformity.Density.Tower.C133mh3.isDvPure_mul
#print axioms Uniformity.Density.Tower.C133mh3.fgmn_dv_exact_mul_thm

end AxCheck
