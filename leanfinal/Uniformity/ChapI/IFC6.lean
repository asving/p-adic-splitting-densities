/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I02
import Uniformity.ChapI.I03
import Uniformity.Density.CoveringMenus
import Uniformity.ChapG.G54
import Uniformity.ChapH.H73w
import Uniformity.ChapH.H97b

/-!
# Uniformity.ChapI.IFC6 — CHA supply pass on the unattacked capstone fields

**[CHA 2026-08-28]** — unit CHA (`docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md`,
rows `a0`/`a1`/`jd0`/`genhnBox2`/window/HE/Tow1; verdict `runs/wave-c/verdict_CHA.md`).

**⚠ TRUST BOUNDARY — every `def`/`theorem` STATEMENT here is NEW**, flagged for the
standing review (`docs/REVIEW_QUEUE_2026-08-26.md`, CHA rows).  Nothing here is signed;
nothing binds into leanspec; no landed file is touched.  Zero `sorry`, zero new axiom;
AxCheck footer expects Lean core only.

## §1 — THE `a1` FIELD IS CLOSED AT EVERY DEGREE: `menuLawAt_all : ∀ n, MenuLawAt n`

The supply map's `a1` row (2026-08-26) sized general `n` as the multi-node MENU-FAMILY
campaign: "Chapter H's induction/menu production supplies the covering-menu half, but a
uniform A1-family extraction must be added."  Both halves are in fact ALREADY LANDED, in
pieces the map did not connect:

* **The uniform menu.**  CN-22 (`Density/CoveringMenus.lean`, `exists_coveringMenu`)
  proves `∀ O, ∃ S, CoveringMenu O n S` — with the existential INSIDE the `O` binder.
  But its construction of `S` (the clamped `Sym`-grid image) depends on `n` ALONE; the
  `O`-dependence is statement shape, not content.  §1 re-derives the construction with
  `S` hoisted OUT of the `O` binder and filtered to exact degree `n`
  (`exists_uniform_coveringMenu`).  The degree filter is what `MenuLawAt`'s third
  conjunct demands and CN-22's raw image does not supply; membership survives the filter
  by `typeOf_degree`.  Per CN-22's spec note (REJECTED R8: the menu is not to be named),
  the menu stays EXISTENTIALLY bound — no public `def` names it.
* **The label family.**  I.03's own gate-(6) three-cell pattern generalizes verbatim: at
  `r = 0` every `Fin 0`-indexed `A1Cell` field is `Fin.elim0`, so ANY finite menu `S`
  yields the enumerating family `S.toList.map a1LabelCell`
  (`menuLawAt_of_uniformMenu`).

**Honesty note (what closing `a1` does and does not certify).**  `MenuLawAt` as SIGNED
(A-I.1) states menu + shape + labels ONLY: I.03's ⚠ SIGNATURE NOTE places the
exact-weights half of HYP.26 with the `A1Cell.coeff` field plus the count laws
(C.114/H §7), OPEN-MATH rows HYP.23/32/35 — deliberately NOT in this carrier.  So
`menuLawAt_all` closes the FIELD `a1` at ledger strength without touching the weight
tie, exactly as the signed carrier scopes itself.  The label cells carry `coeff = 1`
placeholders (I.03 audit item (4)'s disclosure, inherited verbatim).

Consumption: `CapstoneHypotheses.a1` at every degree is supplied by
`menuLawAt_all n`; the `n = 2`/`n = 3` wrappers (`menuLawAt_two`/`menuLawAt_three`)
are unchanged and now redundant-but-harmless anchors.

## §2 — GENHN-HE (I.06): the μ = 3 stage-level decision menu, packaged

H73w (OM-7) landed the five-leaf enum `StageLeaf3`, the dictionary `stageSigma3`, and the
five-type exhaustiveness `stageType3_complete`, but no declaration packages them in the
DECISION shape the future `GenhnHEAt` body's μ = 3 leg will consume.  §2 lands that
corollary (`mu3_stage_sigma_decided`): every positive stage type of mass 3 transports, at
every genre, to one of the five dictionary values.  Pure repackaging — the stage-leaf
BRIDGE (tying an actual degree-`n` polynomial stage to a `StageLeaf3` value; no such tie
exists in the tree) and the `μ ≥ 4` dictionary (HE3-BOX-6, HYP.143) remain the open
remainder, and the I.06 body itself stays the signed `True` placeholder (I-D12).

## §3 — A0-CUBIC (I.02 at n = 3): the exact reduction socket

`DecidedSliceAt 3` is blocked on exactly one missing genre of theorem: the five exact
cubic density VALUES (the degree-3 analogue of G48's `genuineDensity_two_exact`; the
HM3.D rationals are transcribed under G61's "lower bounds, NOT the densities" honesty
rider and are PROVED NOWHERE).  Everything else is landed: the type enumeration
(G53 `typeOf_three_cases`), the off-menu zero (G54 `genuineDensity_three_eq_zero`), and
the degree-3 drainage tie (H97b `genuineDensity_three_eq_decidedDensity`).  §3 makes that
remainder machine-readable: `CubicValueLaw σ` names the exact-value law for one cubic
type in `uniformityStatement_two`'s shape (G51), and `decidedSliceAt_three_of_values`
PROVES that the five value laws imply the capstone field `a0 : DecidedSliceAt 3`
(off-menu types drain to `0 = 0/1`).  ⚠ NOTHING here supplies a value: the five
`CubicValueLaw` hypotheses are the A0-CUBIC campaign's exact target list.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC6

open IsLocalRing Polynomial

/-! ## §1 `a1` closed: the uniform covering menu and the generic label family -/

/-- **The uniform-menu hoist of CN-22** (`exists_coveringMenu`, `Density/CoveringMenus.lean`),
plus the exact-degree filter: ONE finite menu, depending on `n` alone, whose members all have
degree `n`, covering every complete-DVR base at once.  The construction is CN-22's clamped
`Sym`-grid image (its proof body is replayed here with `S` hoisted out of the `O` binder);
the filter's membership leg is `typeOf_degree`.  R8 discipline: the menu is existentially
bound, never named. -/
theorem exists_uniform_coveringMenu (n : ℕ) :
    ∃ S : Finset FactorizationType, (∀ σ ∈ S, σ.degree = n) ∧
      ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)],
        CoveringMenu O n S := by
  classical
  -- the clamp of a pair of naturals into the `(n+1) × (n+1)` grid (CN-22's φ, verbatim)
  set φ : ℕ × ℕ → Fin (n + 1) × Fin (n + 1) :=
    fun p => (⟨min p.1 n, by omega⟩, ⟨min p.2 n, by omega⟩) with hφ
  refine ⟨(Finset.image
      (fun s : (k : Fin (n + 1)) × Sym (Fin (n + 1) × Fin (n + 1)) (k : ℕ) =>
        (⟨(s.2 : Multiset (Fin (n + 1) × Fin (n + 1))).map
          (fun q => ((q.1 : ℕ), (q.2 : ℕ)))⟩ : FactorizationType))
      Finset.univ).filter (fun σ => σ.degree = n), ?_, ?_⟩
  · intro σ hσ
    exact (Finset.mem_filter.1 hσ).2
  · intro O _ _ _ _ a
    have hmon : (monicPoly a).Monic := monicPoly_monic a
    have hdeg : (monicPoly a).natDegree = n := monicPoly_natDegree a
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · -- image membership: CN-22's proof body, replayed with `S` already hoisted
      set M : Multiset (ℕ × ℕ) := (typeOf (monicPoly a)).data with hM
      have hbound : ∀ p ∈ M, p.1 ≤ n ∧ p.2 ≤ n := by
        intro p hp
        obtain ⟨h1, h2⟩ := efPair_pos_of_mem hmon hp
        have hle : p.1 * p.2 ≤ n := by
          have h := efPair_mul_le_natDegree hmon hp
          rwa [hdeg] at h
        refine ⟨le_trans (Nat.le_mul_of_pos_right _ h2) hle, ?_⟩
        exact le_trans (le_trans (Nat.le_mul_of_pos_right _ h1)
          (le_of_eq (Nat.mul_comm _ _))) hle
      have hsum : (M.map (fun p : ℕ × ℕ => p.1 * p.2)).sum = n := by
        have h := typeOf_degree hmon
        rw [hdeg] at h
        simp only [FactorizationType.degree] at h
        rwa [← hM] at h
      have hcard : Multiset.card M ≤ n := by
        have h1 : ∀ x ∈ M.map (fun p : ℕ × ℕ => p.1 * p.2), 1 ≤ x := by
          rintro x hx
          obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
          obtain ⟨h1, h2⟩ := efPair_pos_of_mem hmon hp
          exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        have h2 := Multiset.card_nsmul_le_sum h1
        rw [Multiset.card_map, smul_eq_mul, mul_one, hsum] at h2
        exact h2
      refine Finset.mem_image.2 ⟨⟨⟨Multiset.card M, by omega⟩, ⟨M.map φ, by simp⟩⟩,
        Finset.mem_univ _, ?_⟩
      refine FactorizationType.ext ?_
      show (M.map φ).map (fun q : Fin (n + 1) × Fin (n + 1) => ((q.1 : ℕ), (q.2 : ℕ))) = M
      have hstep : ∀ p ∈ M, (((φ p).1 : ℕ), ((φ p).2 : ℕ)) = id p := by
        intro p hp
        obtain ⟨h1, h2⟩ := hbound p hp
        simp [hφ, min_eq_left h1, min_eq_left h2]
      calc (M.map φ).map (fun q : Fin (n + 1) × Fin (n + 1) => ((q.1 : ℕ), (q.2 : ℕ)))
          = M.map (fun p => (((φ p).1 : ℕ), ((φ p).2 : ℕ))) := by rw [Multiset.map_map]; rfl
        _ = M.map id := Multiset.map_congr rfl hstep
        _ = M := Multiset.map_id M
    · -- the degree leg: `typeOf` conserves degree, and `monicPoly a` has degree exactly `n`
      rw [typeOf_degree hmon, hdeg]

/-- I.03 gate-(6)'s label cell, redeclared `private` (the I02_I03w precedent): at `r = 0`
every `Fin 0`-indexed field is `Fin.elim0`; `expConst`/`visConst`/`coeff` are the three
content-free placeholder choices (`0`, `0`, `1`).  Carries the σ-label and nothing else
(I.03 audit item (4)'s disclosure). -/
private def a1LabelCell (σ : FactorizationType) : Induction.A1Cell 0 where
  offset := fun i => i.elim0
  stride := fun i => i.elim0
  stride_pos := fun i => i.elim0
  expCoeff := fun i => i.elim0
  expCoeff_pos := fun i => i.elim0
  expConst := 0
  visCoeff := fun i => i.elim0
  visConst := 0
  coeff := 1
  σ := σ

/-- **The generic A1 label family**: any finite degree-`n` menu that covers uniformly yields
`MenuLawAt n`, via I.03's own gate-(6) `r = 0` label-cell pattern applied to `S.toList`.
This is the "uniform A1-family extraction" the supply map priced as a campaign half —
it is generic in `S`. -/
theorem menuLawAt_of_uniformMenu {n : ℕ} (S : Finset FactorizationType)
    (hdeg : ∀ σ ∈ S, σ.degree = n)
    (hmenu : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S) : MenuLawAt n := by
  classical
  refine ⟨0, S.toList.map a1LabelCell, S, ?_, ?_, hdeg, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_map] at hC
    obtain ⟨σ, hσ, rfl⟩ := hC
    simpa [a1LabelCell] using Finset.mem_toList.1 hσ
  · intro σ hσ
    refine ⟨a1LabelCell σ, ?_, rfl⟩
    simp only [id_eq, List.mem_map]
    exact ⟨σ, Finset.mem_toList.2 hσ, rfl⟩
  · intro O _ _ _ _ _
    exact hmenu O

/-- ★ **`A1_n` HOLDS AT EVERY DEGREE** — the capstone field `a1 : MenuLawAt n` is SUPPLIED,
for all `n`, Lean-core.  (Ledger strength per the signed carrier: menu + shape + labels;
the weight-correctness tie stays at its own OPEN-MATH rows, untouched.) -/
theorem menuLawAt_all (n : ℕ) : MenuLawAt n := by
  obtain ⟨S, hdeg, hmenu⟩ := exists_uniform_coveringMenu n
  refine menuLawAt_of_uniformMenu S hdeg ?_
  intro O _ _ _ _ _
  exact hmenu O

/-- the capstone-field consumption shape, pinned: the `a1` field of any future
`CapstoneHypotheses n` witness costs nothing beyond this file. -/
example (n : ℕ) : MenuLawAt n := menuLawAt_all n

/-! ## §2 GENHN-HE (I.06): the μ = 3 stage-level decision menu -/

/-- **The μ = 3 σ-decision slice at stage level** (supplier corollary of H73w/OM-7, shaped
for the future `GenhnHEAt` body's μ = 3 leg): every positive stage type of mass 3
transports, at EVERY genre, to one of the five `StageLeaf3` dictionary values.  Pure
repackaging of `stageType3_complete` through `stageSigma3`; the stage-leaf bridge and the
`μ ≥ 4` tail (HYP.143) are the open remainder, and `GenhnHEAt` itself is UNTOUCHED. -/
theorem mu3_stage_sigma_decided (G : Induction.GenreDatum) (τ : Multiset (ℕ × ℕ))
    (hpos : ∀ p ∈ τ, 1 ≤ p.1 ∧ 1 ≤ p.2) (hmass : Induction.stageMass τ = 3) :
    ∃ l : Induction.StageLeaf3,
      Induction.heTransport G τ = Induction.stageSigma3 G l := by
  obtain ⟨l, hl⟩ := Induction.stageType3_complete τ hpos hmass
  exact ⟨l, by rw [hl]; rfl⟩

/-! ## §3 A0-CUBIC (I.02 at n = 3): the exact reduction socket -/

/-- **The exact-value law for ONE cubic type**, in `uniformityStatement_two`'s shape (G51):
one rational function of the residue cardinality, with a globally nonzero denominator that
is nonzero at every residue cardinality, equals the GENUINE degree-3 density uniformly over
complete DVRs.  (Genuine = decided at degree 3 by H97b's landed drainage tie, consumed in
the reduction below — so five of these close the capstone's `a0` field at `n = 3`.)
⚠ This `def` asserts nothing; the five instances are the A0-CUBIC campaign's target list. -/
def CubicValueLaw (σ : FactorizationType) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        genuineDensity O 3 σ
          = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-- **The A0-CUBIC reduction socket**: the five exact cubic value laws imply the capstone
field `a0 : DecidedSliceAt 3` outright.  On the five-type menu each law converts through
H97b's tie `genuineDensity_three_eq_decidedDensity`; off the menu the density is `0` by
G54's `genuineDensity_three_eq_zero` and the same tie, packaged as `0/1`.  The honest
remainder of the map's A0-CUBIC row is therefore EXACTLY the five hypotheses. -/
theorem decidedSliceAt_three_of_values
    (h1 : CubicValueLaw c3split) (h2 : CubicValueLaw c3linInert)
    (h3 : CubicValueLaw c3inert) (h4 : CubicValueLaw c3linRam)
    (h5 : CubicValueLaw c3ram) : DecidedSliceAt 3 := by
  classical
  intro σ _hσ
  by_cases e1 : σ = c3split
  · subst e1
    obtain ⟨num, den, hden, hlaw⟩ := h1
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨ha, hb⟩ := hlaw O
    exact ⟨ha, by rw [← genuineDensity_three_eq_decidedDensity]; exact hb⟩
  by_cases e2 : σ = c3linInert
  · subst e2
    obtain ⟨num, den, hden, hlaw⟩ := h2
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨ha, hb⟩ := hlaw O
    exact ⟨ha, by rw [← genuineDensity_three_eq_decidedDensity]; exact hb⟩
  by_cases e3 : σ = c3inert
  · subst e3
    obtain ⟨num, den, hden, hlaw⟩ := h3
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨ha, hb⟩ := hlaw O
    exact ⟨ha, by rw [← genuineDensity_three_eq_decidedDensity]; exact hb⟩
  by_cases e4 : σ = c3linRam
  · subst e4
    obtain ⟨num, den, hden, hlaw⟩ := h4
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨ha, hb⟩ := hlaw O
    exact ⟨ha, by rw [← genuineDensity_three_eq_decidedDensity]; exact hb⟩
  by_cases e5 : σ = c3ram
  · subst e5
    obtain ⟨num, den, hden, hlaw⟩ := h5
    refine ⟨num, den, hden, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨ha, hb⟩ := hlaw O
    exact ⟨ha, by rw [← genuineDensity_three_eq_decidedDensity]; exact hb⟩
  · -- off the five-type menu: the density is `0`, packaged as `0/1`
    refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    rw [← genuineDensity_three_eq_decidedDensity,
      genuineDensity_three_eq_zero e1 e2 e3 e4 e5]
    simp

end Uniformity.Density.IFC6

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFC6.exists_uniform_coveringMenu
#print axioms Uniformity.Density.IFC6.menuLawAt_of_uniformMenu
#print axioms Uniformity.Density.IFC6.menuLawAt_all
#print axioms Uniformity.Density.IFC6.mu3_stage_sigma_decided
#print axioms Uniformity.Density.IFC6.CubicValueLaw
#print axioms Uniformity.Density.IFC6.decidedSliceAt_three_of_values
