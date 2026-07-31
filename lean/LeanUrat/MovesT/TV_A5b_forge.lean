/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1
import LeanUrat.MovesT.G1_toyGate

/-! # TV-A5b FORGE — the compiled realizable root nodes + the stray countermodel witness

UNIT FORGE-B (2026-07-31; instance-forge round follow-up, the "ONE realizable root
node" blocked record of `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` [UNIFYING
AUTONOMOUS UNIT item (b)]). This module builds the missing artifact class — compiled
REALIZABLE ROOT NODES (length-1 `HistoryCoherent` + vacuous `Realizable` + full
`IsCanonPres`) — and discharges TV-A5b's fenced existence statement
`stray_countermodel_attempt` (MovesT/TV_A5b.lean:73) AS-IS via
`stray_countermodel_witness` below (byte-identical ∃-statement).

CARRIER DESIGN (n = 2, p = 2, F = ZMod 2, N = 1, m = 2, χ = id):
* Stage: `toyStage : Stage 2 (ZMod 2)` REUSED from MovesT/G1_toyGate.lean:161 (the
  established builder idiom — itself the transport of the built HC2/U31 `bStage`;
  Φ = X, degree 1, sorry-free cone). Provenance note: the unit charge said
  "from-scratch Stage"; the from-scratch BUILD already exists as G1's compiled
  transport, so it is REUSED rather than duplicated (repo dedup discipline).
* Nodes: TWO root-species node literals `forgeNodeA`/`forgeNodeB` (G1's `toyHead`
  idiom at (e,h,s,t) = (1,1,1,0), (g,μ) = (1,1), ψ = X − C 1, Ranch = 1 + X,
  lift = 0), differing only in the window position s0 (0 vs 1) and the induced
  (a, line, gam) data — the s0 difference keys `forgeTrack` (A ↦ X, B ↦ X + 1).
* Tree: every box point carries BOTH nodes as root children everywhere
  (`forgeChild o ν x := ν = A ∨ ν = B`); the only realized nonempty states are the
  two singleton histories (`forgeMem`), each REALIZABLE (the forged content:
  `realizableA`/`realizableB` prove `HistoryCoherent ∧ Realizable ∧ IsCanonPres`
  at length 1, incl. the `canonRoot` computation `canonRootA`/`canonRootB`).
* Cells: `Cell = Unit`, constant reads, branch set {A, B} (TV-A5a's carrier
  pattern); `child_cover` holds EXACTLY: the repeated-reduction cells at n = 2
  are g = (0,0) (X² = X·X, track X → A) and g = (1,0) (X²+1 = (X+1)², track
  X+1 → B); the other two reductions are separable (derivative 1), hence
  squarefree — no repeated factor to cover.
* THE STRAY: at the g = (0,0) cell the child `forgeNodeB` rides track X + 1,
  which has multiplicity 0 in X² — `TrackRepOn` FAILS at g ≡ 0. So
  ¬(TrackUniqOn ∧ TrackRepOn) at a full `CellAssign` carrier: the (U)∧(R) pair
  is NOT derivable from the `CellData`/`CellAssign` laws, certifying the pair's
  NECESSITY as named hypotheses (the sealed prediction of E5_rootSplit.lean:311-342
  risk R4, docstring of TV_A5b).

M1 COEXISTENCE CHECK (recorded): the witness refutes no sorried universal in its
import cone. TV_A1 is sorry-free; G1_toyGate's four sorries (`toyModel.mem_realizable`
×2 BLOCKED-FALSE at G1's OWN tables, `twoNodeKcardH`, `toy_v8_wchain`) are
carrier-specific obligations of G1's toy tables, not universals over carriers — this
module's witness carrier is disjoint from them and proves nothing about them. The
proved-conditional KB12/KB13 (TrackUniqOn/TrackRepOn from named laws at canonical
carriers) are NOT imported here and are not contradicted: this carrier violates their
`RootTrackMem` premise (B is a child everywhere, incl. off-track cells).

deps: TV-A1 (the pair), G1_toyGate (toyStage + char-2 idioms). Consumed by: TV_A5b
(the sorry at :87 discharges to `exact stray_countermodel_witness`). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ## §1 char-2 identities over `ZMod 2` (the G1 `toyK_*` idiom, at the base field) -/

private lemma z2_two_poly : (2 : Polynomial (ZMod 2)) = 0 := by
  have h2 : (2 : Polynomial (ZMod 2)) = Polynomial.C (2 : ZMod 2) :=
    Eq.symm (Polynomial.C_ofNat 2)
  rw [h2, show (2 : ZMod 2) = 0 by decide, map_zero]

/-- `X − C 1 = X + 1` over `ZMod 2`. -/
private lemma z2_X_sub_C : (X - Polynomial.C 1 : Polynomial (ZMod 2)) = X + 1 := by
  rw [Polynomial.C_1]
  linear_combination -z2_two_poly

/-- `X² + 1 = (X − C 1)²` over `ZMod 2` — the g = (1,0) repeated square. -/
private lemma z2_sq : (X ^ 2 + 1 : Polynomial (ZMod 2)) = (X - Polynomial.C 1) ^ 2 := by
  rw [Polynomial.C_1]
  linear_combination X * z2_two_poly

/-- derivative (X² + X) = 1 over `ZMod 2` (char 2 kills 2X). -/
private lemma z2_deriv_x2x :
    Polynomial.derivative (X ^ 2 + X : Polynomial (ZMod 2)) = 1 := by
  rw [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_X,
    show ((2 : ℕ) : ZMod 2) = 0 by decide]
  simp

/-- derivative (X² + (1 + X)) = 1 over `ZMod 2`. -/
private lemma z2_deriv_x2x1 :
    Polynomial.derivative (X ^ 2 + (1 + X) : Polynomial (ZMod 2)) = 1 := by
  rw [Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.derivative_X_pow,
    Polynomial.derivative_one, Polynomial.derivative_X,
    show ((2 : ℕ) : ZMod 2) = 0 by decide]
  simp

private lemma z2_ne_x2x : (X ^ 2 + X : Polynomial (ZMod 2)) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 2) h
  simp [Polynomial.coeff_X] at hc

private lemma z2_ne_x2x1 : (X ^ 2 + (1 + X) : Polynomial (ZMod 2)) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 2) h
  simp [Polynomial.coeff_X, Polynomial.coeff_one] at hc

/-- A polynomial over `ZMod 2` with derivative 1 is separable, hence squarefree:
every normalized-factor count is ≤ 1 (the two non-repeated reduction cells). -/
private lemma count_le_one_of_deriv_one (f : Polynomial (ZMod 2)) (hf : f ≠ 0)
    (hd : Polynomial.derivative f = 1) (ψ : Polynomial (ZMod 2)) :
    Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors f) ≤ 1 := by
  have hsep : f.Separable := by
    change IsCoprime f (Polynomial.derivative f)
    rw [hd]
    exact isCoprime_one_right
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf).mp
    hsep.squarefree
  exact Multiset.nodup_iff_count_le_one.mp hnd ψ

/-! ## §2 the two realizable ROOT node literals (G1 `toyHead`/`toyLeafA` idiom)

Both: root species over `toyStage` (Φ = X, degree 1), (e,h,s,t) = (1,1,1,0),
(g,μ) = (1,1), ψ = X − C 1 (deg 1 irreducible; zbar = 1 its root), pat ≡ 1,
Ranch = 1 + X = ψ·1 (ord_ψ exactly 1), lift = 0 (the constant `forgePol` policy).
They differ ONLY in the window slot s0 (0 vs 1) and the induced (a, line, gam):
* A: s0 = 0 — hAnchor a = 0; line ⟨1,1⟩, u* = 1 − 1·1 = 0, γ = 0 + (0+1)·1 = 1.
* B: s0 = 1 — hAnchor a = 1; line ⟨2,1⟩, u* = 2 − 1·2 = 0, γ = 0 + (1+1)·1 = 2. -/

/-- **realizable root node A** (track X): s0 = 0. -/
noncomputable def forgeNodeA : Node 2 (ZMod 2) :=
  { species := ReadSpecies.root, σ := toyStage,
    e := 1, h := 1, s := 1, t := 0, g := 1, μ := 1, a := 0,
    s0 := 0, wSide := 1, Dwidth := 1,
    line := ⟨1, 1⟩, ustar := 0, gam := 1,
    zbar := 1, center := 1, lift := 0,
    ψ := X - Polynomial.C 1,
    pat := fun _ => 1,
    Ranch := 1 + X,
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num,
    hbez := by norm_num, hbezCanon := by norm_num,
    hg := le_refl 1, hμ := le_refl 1, hEdvd := one_dvd 1,
    hDwidth := by
      rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
        Polynomial.natDegree_X],
    hψmonic := monic_X_sub_C 1, hψdeg := natDegree_X_sub_C 1,
    hψirr := irreducible_X_sub_C 1,
    hRanch := by
      norm_num [Finset.sum_range_succ],
    hpat0 := one_ne_zero,
    hpatTop := one_ne_zero,
    hAnchor := by norm_num,
    hLineU := by norm_num [Line.at],
    hOrd := by
      constructor
      · exact toyK_leaf_ord.dvd
      · intro hdvd
        have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
          rw [← toyK_leaf_ord]
          exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
        have hle := Polynomial.natDegree_le_of_dvd hdvd hne
        have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
          rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
        have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
          apply le_trans (Polynomial.natDegree_add_le _ _)
          simp
        omega,
    hzbarRoot := by simp,
    hspecInc := by intro h; simp at h,
    hspecRec := by intro h; simp at h,
    hspecRecCenter := by intro h; simp at h }

/-- **realizable root node B** (track X + 1): s0 = 1. -/
noncomputable def forgeNodeB : Node 2 (ZMod 2) :=
  { species := ReadSpecies.root, σ := toyStage,
    e := 1, h := 1, s := 1, t := 0, g := 1, μ := 1, a := 1,
    s0 := 1, wSide := 1, Dwidth := 1,
    line := ⟨2, 1⟩, ustar := 0, gam := 2,
    zbar := 1, center := 1, lift := 0,
    ψ := X - Polynomial.C 1,
    pat := fun _ => 1,
    Ranch := 1 + X,
    he := le_refl 1, hh := le_refl 1, hcop := by norm_num,
    hbez := by norm_num, hbezCanon := by norm_num,
    hg := le_refl 1, hμ := le_refl 1, hEdvd := one_dvd 1,
    hDwidth := by
      rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
        Polynomial.natDegree_X],
    hψmonic := monic_X_sub_C 1, hψdeg := natDegree_X_sub_C 1,
    hψirr := irreducible_X_sub_C 1,
    hRanch := by
      norm_num [Finset.sum_range_succ],
    hpat0 := one_ne_zero,
    hpatTop := one_ne_zero,
    hAnchor := by norm_num,
    hLineU := by norm_num [Line.at],
    hOrd := by
      constructor
      · exact toyK_leaf_ord.dvd
      · intro hdvd
        have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
          rw [← toyK_leaf_ord]
          exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
        have hle := Polynomial.natDegree_le_of_dvd hdvd hne
        have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
          rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
        have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
          apply le_trans (Polynomial.natDegree_add_le _ _)
          simp
        omega,
    hzbarRoot := by simp,
    hspecInc := by intro h; simp at h,
    hspecRec := by intro h; simp at h,
    hspecRecCenter := by intro h; simp at h }

-- projection read-off lemmas (structure-literal rfl)
private lemma A_species : forgeNodeA.species = ReadSpecies.root := rfl
private lemma A_σ : forgeNodeA.σ = toyStage := rfl
private lemma A_e : forgeNodeA.e = 1 := rfl
private lemma A_h : forgeNodeA.h = 1 := rfl
private lemma A_s0 : forgeNodeA.s0 = 0 := rfl
private lemma A_wSide : forgeNodeA.wSide = 1 := rfl
private lemma A_Dwidth : forgeNodeA.Dwidth = 1 := rfl
private lemma A_slope : forgeNodeA.line.slope = 1 := rfl
private lemma A_ustar : forgeNodeA.ustar = 0 := rfl
private lemma A_gam : forgeNodeA.gam = 1 := rfl
private lemma A_lift : forgeNodeA.lift = 0 := rfl
private lemma A_zbar : forgeNodeA.zbar = 1 := rfl

private lemma B_species : forgeNodeB.species = ReadSpecies.root := rfl
private lemma B_σ : forgeNodeB.σ = toyStage := rfl
private lemma B_e : forgeNodeB.e = 1 := rfl
private lemma B_h : forgeNodeB.h = 1 := rfl
private lemma B_s0 : forgeNodeB.s0 = 1 := rfl
private lemma B_wSide : forgeNodeB.wSide = 1 := rfl
private lemma B_Dwidth : forgeNodeB.Dwidth = 1 := rfl
private lemma B_slope : forgeNodeB.line.slope = 1 := rfl
private lemma B_ustar : forgeNodeB.ustar = 0 := rfl
private lemma B_gam : forgeNodeB.gam = 2 := rfl
private lemma B_lift : forgeNodeB.lift = 0 := rfl
private lemma B_zbar : forgeNodeB.zbar = 1 := rfl

/-- the two nodes are distinct (they differ at s0). -/
theorem forgeNode_ne : forgeNodeA ≠ forgeNodeB := fun h =>
  absurd (A_s0.symm.trans ((congrArg Node.s0 h).trans B_s0)) (by norm_num)

/-- the L1 track accessor of the countermodel: keyed off the s0 difference —
A rides track X, B rides track X + 1. -/
noncomputable def forgeTrack : Node 2 (ZMod 2) → Polynomial (ZMod 2) :=
  fun ν => if ν.s0 = 0 then Polynomial.X else Polynomial.X + 1

theorem forgeTrack_A : forgeTrack forgeNodeA = Polynomial.X := if_pos A_s0

theorem forgeTrack_B : forgeTrack forgeNodeB = Polynomial.X + 1 :=
  if_neg (by rw [B_s0]; norm_num)

/-- the designated level-0 chart at m = 2 (identity). -/
def forgeχ : Fin 2 → Fin 2 := fun b => b

/-- the constant-0 canonical-lift policy (blind by constancy); both nodes carry
lift = 0, so `IsCanon` holds at the singleton histories. -/
noncomputable def forgePol : CanonPolicy 2 (ZMod 2) := ⟨fun _ => 0, fun _ _ => rfl⟩

/-! ## §3 the realizability content: canonRoot + the length-1 triple -/

/-- instance-generalized singleton min computation (canonRoot's classical instances
differ from the canonical `ZMod.decidableEq` — EXPLICIT instance binders keep the
`rw` pattern's instances as metavariables, so it matches canonRoot's own). -/
private lemma min_image_toFinset_singleton {α β : Type*} [LinearOrder β]
    (instα : DecidableEq α) (instβ : DecidableEq β) (a : α) (f : α → β) :
    (@Finset.image α β instβ f (@Multiset.toFinset α instα {a})).min
      = (f a : WithTop β) := by
  rw [show (@Multiset.toFinset α instα {a}) = {a} from Multiset.toFinset_singleton a,
    show (@Finset.image α β instβ f {a}) = {f a} from Finset.image_singleton f a,
    Finset.min_singleton]

private lemma psiImage_A : ψImage forgeNodeA = X - Polynomial.C 1 := by
  change (X - Polynomial.C 1 : Polynomial ↥toyStage.K).map toyStage.K.subtype
    = X - Polynomial.C 1
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_one]

private lemma psiImage_B : ψImage forgeNodeB = X - Polynomial.C 1 := by
  change (X - Polynomial.C 1 : Polynomial ↥toyStage.K).map toyStage.K.subtype
    = X - Polynomial.C 1
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_one]

private lemma canonRoot_of_psiImage (ν : Node 2 (ZMod 2))
    (hψ : ψImage ν = X - Polynomial.C 1) : canonRoot ν = 1 := by
  unfold canonRoot
  rw [hψ, Polynomial.roots_X_sub_C, min_image_toFinset_singleton _ _ 1 (fieldEnum (ZMod 2))]
  exact Equiv.symm_apply_apply _ 1

private lemma canonRootA : canonRoot forgeNodeA = 1 := canonRoot_of_psiImage _ psiImage_A

private lemma canonRootB : canonRoot forgeNodeB = 1 := canonRoot_of_psiImage _ psiImage_B

private lemma toyStage_deg : toyStage.Φ.natDegree = 1 := by
  rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]

/-- **the forged content, node A**: the singleton history [A] is coherent,
(vacuously) realizable, and canonically presented under `forgePol`. -/
private lemma realizableA (H : History 2 (ZMod 2)) (hH : H.nodes = [forgeNodeA]) :
    HistoryCoherent H ∧ Realizable H ∧ forgePol.IsCanonPres H := by
  obtain ⟨nodes, hne, hri⟩ := H
  change nodes = [forgeNodeA] at hH
  subst hH
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- root Φ-degree 1
    intro hj
    simp only [List.getElem_cons_zero]
    rw [A_σ]
    exact toyStage_deg
  · -- the slope law at i = 0: 1·(1·1·1) = 1
    intro i hi
    simp only [List.length_singleton] at hi
    have h0 : i = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    norm_num [History.strFrame, A_slope, A_e, A_Dwidth, A_h]
  · -- the γ-tie at i = 0: 1 = 1·(1·0) + (0+1)·1
    intro i hi
    simp only [List.length_singleton] at hi
    have h0 : i = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    norm_num [History.strFrame, A_gam, A_e, A_ustar, A_s0, A_wSide, A_h]
  · -- transitions: vacuous at length 1
    intro i hi
    simp only [List.length_singleton] at hi
    exact absurd hi (by omega)
  · -- Realizable: vacuous at length 1
    intro i hi
    simp only [List.length_singleton] at hi
    exact absurd hi (by omega)
  · -- IsCanon: lift = 0 = liftOf
    intro r hr
    simp only [List.length_singleton] at hr
    have h0 : r = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    rfl
  · -- canonical residue root: zbar = 1 = canonRoot
    intro r hr
    simp only [List.length_singleton] at hr
    have h0 : r = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    rw [A_zbar, canonRootA]
    exact Units.val_one

/-- **the forged content, node B** (same script at B's data). -/
private lemma realizableB (H : History 2 (ZMod 2)) (hH : H.nodes = [forgeNodeB]) :
    HistoryCoherent H ∧ Realizable H ∧ forgePol.IsCanonPres H := by
  obtain ⟨nodes, hne, hri⟩ := H
  change nodes = [forgeNodeB] at hH
  subst hH
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hj
    simp only [List.getElem_cons_zero]
    rw [B_σ]
    exact toyStage_deg
  · intro i hi
    simp only [List.length_singleton] at hi
    have h0 : i = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    norm_num [History.strFrame, B_slope, B_e, B_Dwidth, B_h]
  · -- the γ-tie at i = 0: 2 = 1·(1·0) + (1+1)·1
    intro i hi
    simp only [List.length_singleton] at hi
    have h0 : i = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    norm_num [History.strFrame, B_gam, B_e, B_ustar, B_s0, B_wSide, B_h]
  · intro i hi
    simp only [List.length_singleton] at hi
    exact absurd hi (by omega)
  · intro i hi
    simp only [List.length_singleton] at hi
    exact absurd hi (by omega)
  · intro r hr
    simp only [List.length_singleton] at hr
    have h0 : r = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    rfl
  · intro r hr
    simp only [List.length_singleton] at hr
    have h0 : r = 0 := by omega
    subst h0
    simp only [List.getElem_cons_zero]
    rw [B_zbar, canonRootB]
    exact Units.val_one

/-! ## §4 the countermodel tree -/

/-- membership: the root everywhere; the two singleton histories everywhere. -/
def forgeMem : Option (History 2 (ZMod 2)) → Box 2 2 → Prop
  | none, _ => True
  | some H, _ => H.nodes = [forgeNodeA] ∨ H.nodes = [forgeNodeB]

/-- children: both forged nodes are children of EVERY state at EVERY point (the
some-state legs are dead via the species-root clash in `mem_snoc`). -/
def forgeChild : Option (History 2 (ZMod 2)) → Node 2 (ZMod 2) → Box 2 2 → Prop :=
  fun _ ν _ => ν = forgeNodeA ∨ ν = forgeNodeB

private lemma snoc_ne_single (H : History 2 (ZMod 2)) (ν ν' : Node 2 (ZMod 2))
    (hν : ν.species ≠ ReadSpecies.root) : (H.snoc ν hν).nodes ≠ [ν'] := by
  intro h
  have hlen := congrArg List.length h
  simp only [History.snoc, List.length_append, List.length_cons,
    List.length_nil] at hlen
  exact H.nonempty (List.eq_nil_of_length_eq_zero (by omega))

/-- **the countermodel TreeModel** at (n, N, m) = (2, 1, 2). -/
noncomputable def forgeTree : TreeModel 2 (ZMod 2) 2 1 2 forgePol where
  mem := forgeMem
  child := forgeChild
  root_mem := fun _ => trivial
  mem_single := fun ν h1 x => by
    simp [forgeMem, forgeChild]
  mem_snoc := fun H ν hν x => by
    constructor
    · intro h
      rcases h with h | h
      · exact absurd h (snoc_ne_single H ν forgeNodeA hν)
      · exact absurd h (snoc_ne_single H ν forgeNodeB hν)
    · rintro ⟨-, hc⟩
      rcases hc with rfl | rfl
      · exact absurd A_species hν
      · exact absurd B_species hν
  mem_realizable := fun H x h => by
    rcases h with h | h
    · exact realizableA H h
    · exact realizableB H h

/-! ## §5 the cell layer (TV-A5a's `Unit`-cell pattern, branch set {A, B}) -/

/-- the constant branch set {A, B} (nodup by the s0 difference). -/
noncomputable def forgeBranchSet : Finset (Node 2 (ZMod 2)) :=
  ⟨{forgeNodeA, forgeNodeB}, by simp [forgeNode_ne]⟩

private lemma mem_forgeBranchSet {ν : Node 2 (ZMod 2)} :
    ν ∈ forgeBranchSet ↔ (ν = forgeNodeA ∨ ν = forgeNodeB) := by
  simp [forgeBranchSet, Finset.mem_mk]

/-- the level-0 reduction on the countermodel chart, at a point of the g-cell. -/
private lemma forge_redPoly (g : Fin 2 → ZMod 2) (x : Box 2 2)
    (hx : x ∈ rootCell forgeχ g) :
    redPoly forgeχ x = X ^ 2 + (Polynomial.C (g 0) + Polynomial.C (g 1) * X) := by
  change Polynomial.X ^ 2
      + ∑ b : Fin 2, Polynomial.C (x (forgeχ b)) * Polynomial.X ^ (b : ℕ)
    = _
  rw [Fin.sum_univ_two, show x (forgeχ 0) = g 0 from hx 0,
    show x (forgeχ 1) = g 1 from hx 1]
  norm_num

/-- **the full `CellAssign` carrier of the countermodel**: `Unit` cells, constant
reads, branch set {A, B}; `child_cover` EXACT — the two repeated cells (g = (0,0):
X² with track X ↦ A; g = (1,0): (X+1)² with track X+1 ↦ B) are covered, the two
separable cells have no repeated factor. -/
noncomputable def forgeCells :
    CellAssign 2 (ZMod 2) 2 1 2 forgePol forgeTree forgeχ forgeTrack where
  Cell := Unit
  hCellFin := inferInstance
  cellOf := fun _ _ => ()
  cellLevel := fun _ => 0
  levelOf := fun _ => 0
  cell_local := fun _ _ _ _ => rfl
  branchSetOf := fun _ => forgeBranchSet
  child_cell := fun H ν x hmem => by
    change (ν = forgeNodeA ∨ ν = forgeNodeB) ↔ ν ∈ forgeBranchSet
    exact mem_forgeBranchSet.symm
  child_root_sub := fun ν x h => mem_forgeBranchSet.mpr h
  child_cell_red := fun χ' g ψ ν x hx h => mem_forgeBranchSet.mp h
  child_red_uniform := fun _ _ _ _ _ _ => Iff.rfl
  branchCellOf := fun _ _ _ => ()
  branch_cell_joint := fun _ _ _ _ _ => rfl
  child_cover := by
    intro g x hx ψ hmem hcnt
    have hred := forge_redPoly g x hx
    have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hz (g 0) with hg0 | hg0 <;> rcases hz (g 1) with hg1 | hg1
    · -- g = (0,0): X², repeated track X, covered by A
      rw [hg0, hg1] at hred
      simp only [map_zero, zero_mul, add_zero] at hred
      rw [hred, UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible Polynomial.irreducible_X,
        Polynomial.Monic.normalize_eq_self Polynomial.monic_X] at hmem
      have hψX : ψ = Polynomial.X :=
        Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hmem).2
      exact ⟨forgeNodeA, by rw [forgeTrack_A, hψX], Or.inl rfl,
        mem_forgeBranchSet.mpr (Or.inl rfl)⟩
    · -- g = (0,1): X² + X separable — no repeated factor
      rw [hg0, hg1] at hred
      simp only [map_zero, map_one, one_mul, zero_add] at hred
      rw [hred] at hcnt
      have hle := count_le_one_of_deriv_one _ z2_ne_x2x z2_deriv_x2x ψ
      omega
    · -- g = (1,0): X² + 1 = (X − C 1)², repeated track X + 1, covered by B
      rw [hg0, hg1] at hred
      simp only [map_zero, map_one, zero_mul, add_zero] at hred
      rw [hred, z2_sq, UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C 1),
        Polynomial.Monic.normalize_eq_self (monic_X_sub_C 1)] at hmem
      have hψ1 : ψ = Polynomial.X + 1 := by
        have h' := Multiset.mem_singleton.mp (Multiset.mem_nsmul.mp hmem).2
        rw [h', z2_X_sub_C]
      exact ⟨forgeNodeB, by rw [forgeTrack_B, hψ1], Or.inr rfl,
        mem_forgeBranchSet.mpr (Or.inr rfl)⟩
    · -- g = (1,1): X² + (1 + X) separable — no repeated factor
      rw [hg0, hg1] at hred
      simp only [map_one, one_mul] at hred
      rw [hred] at hcnt
      have hle := count_le_one_of_deriv_one _ z2_ne_x2x1 z2_deriv_x2x1 ψ
      omega

/-! ## §6 the witness -/

/-- the stray point: the all-0 box point (its own root cell is g ≡ 0, reduction X²). -/
def forgeY : Box 2 2 := fun _ => 0

/-- **TV-A5b's countermodel-existence statement, DISCHARGED** (byte-identical ∃ to
`stray_countermodel_attempt`, MovesT/TV_A5b.lean:73): a full `CellAssign` carrier
at n = 2 over `ZMod 2` at which the TV-A1 pair FAILS. The failing conjunct is (R):
at the g ≡ 0 root cell the realized child `forgeNodeB` rides track X + 1, of
multiplicity 0 in the reduction X² — the STRAY of the sealed prediction. -/
theorem stray_countermodel_witness :
    ∃ (N m : ℕ) (pol : CanonPolicy 2 (ZMod 2))
      (T : TreeModel 2 (ZMod 2) 2 N m pol)
      (χ : Fin 2 → Fin m) (trackOf : Node 2 (ZMod 2) → Polynomial (ZMod 2))
      (_ : CellAssign 2 (ZMod 2) 2 N m pol T χ trackOf)
      (g : Fin 2 → ZMod 2),
      ¬ (TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) := by
  refine ⟨1, 2, forgePol, forgeTree, forgeχ, forgeTrack, forgeCells, fun _ => 0, ?_⟩
  rintro ⟨-, hR⟩
  have hy : forgeY ∈ rootCell forgeχ (fun _ => 0) := fun b => rfl
  have hchild : forgeTree.child none forgeNodeB forgeY := Or.inr rfl
  have hcnt := hR forgeY hy forgeNodeB hchild
  have hred : redPoly forgeχ forgeY = Polynomial.X ^ 2 := by
    have h := forge_redPoly (fun _ => 0) forgeY hy
    simpa using h
  rw [hred, forgeTrack_B, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible Polynomial.irreducible_X,
    Polynomial.Monic.normalize_eq_self Polynomial.monic_X,
    Multiset.count_nsmul, Multiset.count_singleton] at hcnt
  rw [if_neg ?hne] at hcnt
  case hne =>
    intro h
    have hc := congrArg (fun q => Polynomial.coeff q 0) h
    simp [Polynomial.coeff_one, Polynomial.coeff_X] at hc
  omega

end LeanUrat.MovesT
