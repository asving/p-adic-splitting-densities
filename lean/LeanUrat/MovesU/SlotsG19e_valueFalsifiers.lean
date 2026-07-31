/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG18_relPack

/-!
# IB-G19a — VALUE-LEVEL falsifiers for the D-SC carrier slots (bridge BP1, †23)

The three VALUE-LEVEL falsifiers the G19c header left open after the degenerate
class closed (G19c/G19d, 2026-07-31) — the non-vacuity class degenerate
falsifiers cannot certify: each filled slot is FALSE at a CONTENT-BEARING
carrier (nonempty events, positive cell mass, an inhabited leg roster) whose
VALUES are wrong, so the refutation is value-borne, never degeneracy-borne.

THE SHARED CARRIER (one site, one data pack — every wrong value baked into one
content-bearing instance):
* `diracSite p` — the G2 BLOCKED record's own junk site, now the falsifier
  witness exactly as the D-SC design promised (G14 header R-7: "a degenerate
  site (Dirac condMass) remains constructible, BY DESIGN: it is the rel2b
  falsifier witness").  Continuation points = the F_p-digit atom `↥(Fsub p 1)`
  (p ≥ 2 points), FULL powerset event algebra, `cellMass = 1` (the positive-cell
  guard FIRES), and the two-valued Dirac conditional `diracMass` at the digit 0.
* `wrongValuedData p Sp AD` — the data pack over it: constant `Θ`, IDENTITY
  ambient trees (`ambTcan = nodeCorr = id` — the composite is NON-constant)
  against a CONSTANT target `tgtTcan`, verdict readers separating the two
  square legs, `TgtRealizes ≡ True` (the realization event is the FULL box
  event — realizable, `BoxVol`-certified mass 1), and the β-table reading the
  CONSTANT 2.

THE THREE FALSIFIERS (each against the CANONICAL filled `SitedSlot_*`):
* (F1) `sitedSlot_rel2b_refuted_at_diracSite` — the INVERTED-DIRAC pricing
  falsifier: against EVERY data pack and EVERY cylinder-pinned `BoxVol` target
  (the `vol_cyl` field prices the level-1 cylinder at (p·…)⁻¹ = p⁻¹ here), the
  Dirac site's two-valued conditional cannot meet the pricing clause — with the
  guard FIRING and the pullback IN the ambient algebra (`diracSite_events_total`),
  so the priced EQUALITY is the failing leg.
* (F2) `sitedSlot_rel2d_refuted_at_wrongValued` — the NON-CONSTANT-COMPOSITE
  square falsifier: `nodeCorr ∘ ambTcan = id` is non-constant
  (`wrongValued_composite_nonconstant`) while `tgtTcan ∘ Θ ∘ domIdent` is
  constant, and the broken square is VERDICT-visible ([true] vs [] — the
  compiled mismatch `wrongValued_verdict_mismatch`); the word/read/verdict/
  wiring/R-17 legs all HOLD (`wrongValued_rel2d_nonsquare_legs`), so the square
  is the unique failing leg.
* (F3) `sitedSlot_rel2e_refuted_at_betaTwo` — the β ≡ 2 VALUE falsifier (the
  G19c-header assignment for rel2e; G17's "β ≡ 2 against any BoxVol with
  vol ≤ 1" at the sharpest event): the β-table reads 2 where the certified
  `BoxVol` mass of the (full, realizable) realization event is pinned at 1 by
  the target's own `vol_univ` law — at EVERY convention, EVERY `consumed`, and
  EVERY CI; the (e1)/(e4)/(e5) legs HOLD at the pinned non-degenerate exports
  (`wrongValued_rel2e_nonvalue_legs`), so MASS = ENTRY is the unique failing
  leg.  PLUS the rel3 co-assignee: `sitedSlot_rel3_refuted_at_betaTwo` — the
  ONE-LEG JUNK PACK (G17 header's named falsifier): a populated, covering-shaped
  single-leg display pack over the one-site family whose assignment carries the
  β ≡ 2 table refutes `SitedSlot_rel3` through the per-leg certification value.

M1 FENCE CHECK (run at landing): the negation targets `SitedSlot_rel2b/2d/2e`
and `SitedSlot_rel3` are the FILLED, sorry-free canonical definitions (H-phase
fill 2026-07-31, Q5 ACCEPT) — no sorried universal these witnesses refute
shares this import environment (grep-verified; the four G2 `Slot_rel2*` sorries
transitively imported are unfilled Prop DEFINITIONS, not refuted statements).
No probe-local copies are needed — everything here consumes the canonical defs.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

open scoped Classical

/-! ## The shared content-bearing carrier: the Dirac site and its wrong-valued pack -/

/-- The Dirac conditional at the digit 0 of the F_p-atom: the two-valued
`μ(E │ Σ_c)` of the G2 record's junk site (a genuine finitely-additive
conditional content — see the laws below — that no cylinder-pinned `BoxVol`
can price). -/
noncomputable def diracMass (p : ℕ) [Fact p.Prime] (E : Set ↥(Fsub p 1)) : ℚ :=
  if (0 : ↥(Fsub p 1)) ∈ E then 1 else 0

private lemma diracMass_nonneg (p : ℕ) [Fact p.Prime] (E : Set ↥(Fsub p 1)) :
    0 ≤ diracMass p E := by
  unfold diracMass; split_ifs <;> norm_num

private lemma diracMass_empty (p : ℕ) [Fact p.Prime] :
    diracMass p (∅ : Set ↥(Fsub p 1)) = 0 := by
  unfold diracMass; simp

private lemma diracMass_univ (p : ℕ) [Fact p.Prime] :
    diracMass p (Set.univ : Set ↥(Fsub p 1)) = 1 := by
  unfold diracMass; simp

private lemma diracMass_add (p : ℕ) [Fact p.Prime] (E E' : Set ↥(Fsub p 1))
    (hd : Disjoint E E') : diracMass p (E ∪ E') = diracMass p E + diracMass p E' := by
  unfold diracMass
  by_cases h : (0 : ↥(Fsub p 1)) ∈ E
  · have h' : (0 : ↥(Fsub p 1)) ∉ E' := fun h' => Set.disjoint_left.mp hd h h'
    rw [if_pos (Set.mem_union_left _ h), if_pos h, if_neg h']; ring
  · by_cases h' : (0 : ↥(Fsub p 1)) ∈ E'
    · rw [if_pos (Set.mem_union_right _ h'), if_neg h, if_pos h']; ring
    · have hu : (0 : ↥(Fsub p 1)) ∉ E ∪ E' :=
        fun hu => ((Set.mem_union _ _ _).mp hu).elim h h'
      rw [if_neg hu, if_neg h, if_neg h']; ring

/-- The Dirac conditional is TWO-VALUED — the display of why it cannot price a
level-1 cylinder (whose `vol_cyl`-pinned mass is p⁻¹ ∉ {0, 1}). -/
lemma diracMass_two_valued (p : ℕ) [Fact p.Prime] (E : Set ↥(Fsub p 1)) :
    diracMass p E = 0 ∨ diracMass p E = 1 := by
  unfold diracMass; split_ifs <;> simp

/-- **THE DIRAC SITE** (the G2 BLOCKED record's junk site, compiled as the
IB-G19a falsifier witness per G14 R-7): δ = δ_j^rel = d_j = 1 (so δ_j = 1,
d_j^rel = 1), continuation points = the F_p-digit atom, FULL powerset event
algebra, `cellMass = 1` (the positive-cell guard fires), Dirac `condMass`.
Content-bearing: p ≥ 2 continuation points, genuine event algebra, genuine
finitely-additive conditional. -/
noncomputable def diracSite (p : ℕ) [Fact p.Prime] : RelSite p where
  δ := 1
  δrel := 1
  d := 1
  Cont := ↥(Fsub p 1)
  contNe := ⟨0⟩
  AmbEvents := Set.univ
  univ_mem := trivial
  compl_mem := fun _ _ => trivial
  union_mem := fun _ _ _ _ => trivial
  cellMass := 1
  cellMass_nonneg := by norm_num
  cellMass_le_one := le_refl 1
  condMass := diracMass p
  condMass_nonneg := diracMass_nonneg p
  condMass_empty := diracMass_empty p
  condMass_univ := fun _ => diracMass_univ p
  condMass_add := fun E _ E' _ hd => diracMass_add p E E' hd
  PTree := Unit
  Tj := ()
  SEvent := fun _ => Set.univ
  SEvent_mem := fun _ => trivial
  StateIdx := Unit
  τ := ()
  FrameC := Unit
  frameCNe := ⟨()⟩
  reframe := fun _ _ f => f

private lemma diracSite_δabs (p : ℕ) [Fact p.Prime] : (diracSite p).δabs = 1 := rfl

private lemma diracSite_dRel (p : ℕ) [Fact p.Prime] : (diracSite p).dRel = 1 := by
  simp [RelSite.dRel, diracSite]

/-- The guard FIRES at the Dirac site: `μ(Σ_c) = 1 > 0` — the rel2b refutation
below is not vacated by the positive-cell guard. -/
theorem diracSite_cellMass_pos (p : ℕ) [Fact p.Prime] : 0 < (diracSite p).cellMass :=
  one_pos

/-- EVERY set is an ambient event at the Dirac site — the rel2b refutation below
is not vacated by the pullback-membership conjunct either: only the priced
EQUALITY fails. -/
theorem diracSite_events_total (p : ℕ) [Fact p.Prime]
    (E : Set (diracSite p).Cont) : E ∈ (diracSite p).AmbEvents := trivial

/-- The verdict reader of the wrong-valued pack: separates the digit 0 from
everything else (the compiled witness that the broken rel2d square is
verdict-VISIBLE, not an invisible relabeling). -/
noncomputable def vread (p : ℕ) [Fact p.Prime] (t : ↥(Fsub p 1)) : List Bool :=
  if t = 0 then [] else [true]

private lemma vread_zero (p : ℕ) [Fact p.Prime] : vread p 0 = [] := by
  unfold vread; exact if_pos rfl

private lemma vread_one (p : ℕ) [Fact p.Prime] : vread p 1 = [true] := by
  unfold vread; exact if_neg one_ne_zero

/-- **THE WRONG-VALUED DATA PACK** over the Dirac site: constant `Θ`, IDENTITY
ambient trees against a CONSTANT target `tgtTcan` (the non-constant-composite
square breaker), `vread` verdicts on both sides, `TgtRealizes ≡ True` (the
realization event = the FULL box event), and the β-table reading the CONSTANT 2.
Every law-free field is genuine data; the three falsifiers below prove the
LAW slots FALSE at it. -/
noncomputable def wrongValuedData (p : ℕ) [Fact p.Prime] (Sp : SpeciesSyntax)
    (AD : AlphabetData p Sp) : SiteData p (diracSite p) Sp AD where
  dom :=
    { freeCoords := {((0 : ℕ), (0 : ℕ))}
      domIdent := (Equiv.funUnique ↥({((0 : ℕ), (0 : ℕ))} : Set (ℕ × ℕ)) ↥(Fsub p 1)).symm
      prodEvents := Set.univ }
  emb :=
    { TowerRes := ↥(Fsub p (diracSite p).δabs)
      embed := RingHom.id _
      teich := fun _ => 0 }
  theta := { Θ := fun _ => 0 }
  frames := { tgtOf := fun _ _ => Equiv.refl _ }
  dict :=
    { AmbRead := Unit
      ambReadNe := ⟨()⟩
      TgtRead := Unit
      readDict := fun r => r
      ambLetter := fun _ => AD.posLetter (diracSite p).δabs AD.posNe.some
      tgtLetter := fun _ => AD.posLetter (diracSite p).δabs AD.posNe.some
      ambShape := fun _ => (0, 0, 0, 0)
      tgtShape := fun _ => (0, 0, 0, 0)
      ambAnchor := fun _ => 0
      tgtAnchor := fun _ => 0
      ambSide := fun _ => ((0, 0), [])
      tgtSide := fun _ => ((0, 0), [])
      AmbResDat := fun _ => Unit
      TgtResDat := fun _ => Unit
      resDict := fun _ x => x }
  trees :=
    { AmbTree := ↥(Fsub p 1)
      ambTreeNe := ⟨0⟩
      ambTcan := fun f => f
      TgtTree := ↥(Fsub p 1)
      tgtTcan := fun _ => 0
      nodeCorr := fun t => t
      ambWord := fun _ => []
      tgtWord := fun _ => []
      ambReads := fun _ => []
      tgtReads := fun _ => []
      ambVerdict := vread p
      tgtVerdict := vread p
      posOf := fun _ => AD.posNe.some
      TgtSub := Unit
      subtreeCorr := fun _ => ()
      TgtRealizes := fun _ _ => True }
  beta :=
    { RelState := Unit
      relStateNe := ⟨()⟩
      stateDict := fun _ => ()
      stateReadsAmb := fun _ => []
      stateReadsRel := fun _ => []
      β := fun _ _ _ => 2
      entryFirst := 0 }

/-! ## (F1) The inverted-Dirac pricing falsifier for `SitedSlot_rel2b` -/

/-- **(F1) VALUE FALSIFIER** (the G2 record's own countermodel INVERTED): the
Dirac site refutes the filled `SitedSlot_rel2b` against EVERY data pack and
EVERY cylinder-pinned `BoxVol` target — the pricing clause demands the
two-valued Dirac conditional equal the level-1 cylinder mass p⁻¹ ∉ {0, 1}.
The guard fires (`diracSite_cellMass_pos`) and the pullback is an ambient event
(`diracSite_events_total`): the priced EQUALITY is the failing leg. -/
theorem sitedSlot_rel2b_refuted_at_diracSite (p : ℕ) [hp : Fact p.Prime]
    {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
    (SD : SiteData p (diracSite p) Sp AD)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    ¬ SitedSlot_rel2b (diracSite p) SD CI := by
  rintro ⟨-, hprice⟩
  obtain ⟨-, heq⟩ := hprice (diracSite_cellMass_pos p)
    (cyl p (diracSite p).δabs 1 0) (CI.C.V.cyl_mem 1 0)
  rw [CI.C.V.vol_cyl 1 0] at heq
  have hval : ((qq p (diracSite p).δabs : ℚ) ^ ((diracSite p).dRel * 1))⁻¹
      = ((p : ℚ))⁻¹ := by
    rw [diracSite_δabs, diracSite_dRel]
    simp [qq]
  rw [hval] at heq
  have heq' : diracMass p
      ((fun f => SD.theta.Θ (SD.dom.domIdent f)) ⁻¹' cyl p (diracSite p).δabs 1 0)
      = ((p : ℚ))⁻¹ := heq
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.out.two_le
  unfold diracMass at heq'
  split_ifs at heq'
  · -- 1 = p⁻¹: taking inverses gives p = 1, against p ≥ 2
    have h1 : ((1 : ℚ))⁻¹ = (((p : ℚ))⁻¹)⁻¹ := by rw [heq']
    rw [inv_one, inv_inv] at h1
    linarith
  · -- 0 = p⁻¹: gives p = 0, against p ≥ 2
    have h0 : (p : ℚ) = 0 := inv_eq_zero.mp heq'.symm
    linarith

/-- (F1) instantiation witness: the quantification domain of the falsifier is
inhabited — the refutation fires at the compiled wrong-valued pack. -/
theorem sitedSlot_rel2b_refuted_at_wrongValued (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    ¬ SitedSlot_rel2b (diracSite p) (wrongValuedData p Sp AD) CI :=
  sitedSlot_rel2b_refuted_at_diracSite p (wrongValuedData p Sp AD) CI

/-! ## (F2) The non-constant-composite square falsifier for `SitedSlot_rel2d` -/

/-- (F2) display: the composite `nodeCorr ∘ ambTcan` is NON-CONSTANT at the
wrong-valued carrier — the failure class the degenerate falsifiers cannot
reach (a constant composite square can be True-satisfied by constants). -/
theorem wrongValued_composite_nonconstant (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) :
    (wrongValuedData p Sp AD).trees.nodeCorr
        ((wrongValuedData p Sp AD).trees.ambTcan (1 : ↥(Fsub p 1)))
      ≠ (wrongValuedData p Sp AD).trees.nodeCorr
        ((wrongValuedData p Sp AD).trees.ambTcan (0 : ↥(Fsub p 1))) := by
  intro h
  exact one_ne_zero (show (1 : ↥(Fsub p 1)) = 0 from h)

/-- (F2) display: the two legs of the acceptance-criterion square are separated
by the VERDICT reader at the continuation point 1 — [true] on the ambient
composite, [] on the target composite: the broken square is a compiled
verdicts mismatch. -/
theorem wrongValued_verdict_mismatch (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) :
    (wrongValuedData p Sp AD).trees.tgtVerdict
        ((wrongValuedData p Sp AD).trees.nodeCorr
          ((wrongValuedData p Sp AD).trees.ambTcan (1 : ↥(Fsub p 1))))
      ≠ (wrongValuedData p Sp AD).trees.tgtVerdict
        ((wrongValuedData p Sp AD).trees.tgtTcan
          ((wrongValuedData p Sp AD).theta.Θ
            ((wrongValuedData p Sp AD).dom.domIdent (1 : ↥(Fsub p 1))))) := by
  intro h
  have h1 : vread p 1 = vread p 0 := h
  rw [vread_one, vread_zero] at h1
  exact List.cons_ne_nil true [] h1

/-- **(F2) VALUE FALSIFIER**: the wrong-valued carrier refutes the filled
`SitedSlot_rel2d` — the lift-policy square fails at the NON-CONSTANT composite
(`wrongValued_composite_nonconstant`), and the failure is the compiled
verdicts mismatch (`wrongValued_verdict_mismatch`); all other legs hold
(`wrongValued_rel2d_nonsquare_legs`), so the square is the unique failing leg. -/
theorem sitedSlot_rel2d_refuted_at_wrongValued (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) :
    ¬ SitedSlot_rel2d (diracSite p) (wrongValuedData p Sp AD) := by
  rintro ⟨hsq, -, -, -, -, -⟩
  exact wrongValued_verdict_mismatch p Sp AD
    (congrArg _ (hsq (1 : ↥(Fsub p 1))))

/-- (F2) value-borne certificate: the word/read/verdict preservation legs, the
(CF12) wiring leg, and the (R-17) identification leg of `SitedSlot_rel2d` all
HOLD at the wrong-valued carrier — the refutation above is borne by the square
alone, not by degeneracy of any other leg. -/
theorem wrongValued_rel2d_nonsquare_legs (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) :
    (∀ t, (wrongValuedData p Sp AD).trees.tgtWord ((wrongValuedData p Sp AD).trees.nodeCorr t)
        = (wrongValuedData p Sp AD).trees.ambWord t) ∧
    (∀ t, (wrongValuedData p Sp AD).trees.tgtReads ((wrongValuedData p Sp AD).trees.nodeCorr t)
        = ((wrongValuedData p Sp AD).trees.ambReads t).map (wrongValuedData p Sp AD).dict.readDict) ∧
    (∀ t, (wrongValuedData p Sp AD).trees.tgtVerdict ((wrongValuedData p Sp AD).trees.nodeCorr t)
        = (wrongValuedData p Sp AD).trees.ambVerdict t) ∧
    (∀ r, AD.posLetter (diracSite p).δabs ((wrongValuedData p Sp AD).trees.posOf r)
        = (wrongValuedData p Sp AD).dict.tgtLetter r) ∧
    (∀ (T : (diracSite p).PTree) (f : (diracSite p).Cont), f ∈ (diracSite p).SEvent T ↔
      (wrongValuedData p Sp AD).trees.TgtRealizes
        ((wrongValuedData p Sp AD).trees.tgtTcan
          ((wrongValuedData p Sp AD).theta.Θ ((wrongValuedData p Sp AD).dom.domIdent f)))
        ((wrongValuedData p Sp AD).trees.subtreeCorr T)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩

/-! ## (F3) The β ≡ 2 value falsifier for `SitedSlot_rel2e` (and the rel3 co-assignee) -/

/-- **(F3) VALUE FALSIFIER**: the β ≡ 2 table refutes the filled
`SitedSlot_rel2e` at EVERY exported convention, EVERY `consumed`, and EVERY
cylinder-pinned target — the (e3) MASS = ENTRY leg reads the constant 2 where
the certified `BoxVol` mass of the (full, realizable) realization event is
pinned at 1 by the target's own `vol_univ` law.  The (e1)/(e4)/(e5) legs hold
at the pinned non-degenerate exports (`wrongValued_rel2e_nonvalue_legs`). -/
theorem sitedSlot_rel2e_refuted_at_betaTwo (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (tableConv : ℕ → Prop) (consumed : Set (diracSite p).PTree)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    ¬ SitedSlot_rel2e (diracSite p) (wrongValuedData p Sp AD) tableConv consumed CI := by
  rintro ⟨-, -, -, -, -, heq⟩
  have h2 : (2 : ℚ) = CI.C.V.vol Set.univ := heq
  rw [CI.C.V.vol_univ] at h2
  norm_num at h2

/-- (F3) value-borne certificate: at the PINNED non-degenerate exports —
`tableConv := (· = 0)` (determining, satisfied by `entryFirst`) and
`consumed := {Tj}` (covering and determined at the site's own prescription) —
the (e1)/(e4)/(e5) legs of `SitedSlot_rel2e` all HOLD at the wrong-valued
carrier: the β-value leg is the unique failing conjunct. -/
theorem wrongValued_rel2e_nonvalue_legs (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) :
    (∀ s, (wrongValuedData p Sp AD).beta.stateReadsRel
          ((wrongValuedData p Sp AD).beta.stateDict s)
        = ((wrongValuedData p Sp AD).beta.stateReadsAmb s).map
            (wrongValuedData p Sp AD).dict.readDict) ∧
    ((wrongValuedData p Sp AD).beta.entryFirst = 0 ∧
      ∀ m : ℕ, m = 0 → m = (wrongValuedData p Sp AD).beta.entryFirst) ∧
    ((diracSite p).Tj ∈ ({(diracSite p).Tj} : Set (diracSite p).PTree) ∧
      ∀ T ∈ ({(diracSite p).Tj} : Set (diracSite p).PTree), T = (diracSite p).Tj) :=
  ⟨fun _ => rfl, ⟨rfl, fun _ hm => hm⟩, rfl, fun _ hT => hT⟩

/-! ## (F3, rel3 co-assignee) The one-leg junk pack against `SitedSlot_rel3` -/

/-- The ONE-SITE realized family `{diracSite p}` — nonempty, root-indexed
(δ = 1), positive-mass, descent-closed (empty descent). -/
noncomputable def oneLegFam (p : ℕ) [Fact p.Prime] : RelSiteFamily p where
  mem := {diracSite p}
  ne := ⟨diracSite p, rfl⟩
  root_mem := ⟨diracSite p, rfl, rfl⟩
  mem_pos := fun S hS => by
    rw [show S = diracSite p from hS]; exact diracSite_cellMass_pos p
  desc := fun _ _ _ => ∅
  desc_sub := fun _ _ _ => Set.empty_subset _
  desc_amb := fun _ _ _ _ hS' => hS'.elim

/-- The one-site assignment carrying the WRONG-VALUED pack (β ≡ 2) with the
pinned non-degenerate exports: `tableConv := (· = 0)`, `consumed := Set.univ`. -/
noncomputable def oneLegAssign (p : ℕ) [Fact p.Prime] (Sp : SpeciesSyntax)
    (AD : AlphabetData p Sp)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    RelAssignment p Sp AD (oneLegFam p) where
  data := fun S hS => by
    rw [show S = diracSite p from hS]; exact wrongValuedData p Sp AD
  tgt := fun S hS => by
    rw [show S = diracSite p from hS]; exact CI
  tableConv := fun _ _ m => m = 0
  consumed := fun _ _ => Set.univ

/-- **THE ONE-LEG JUNK PACK** (G17 header's named IB-G19a falsifier carrier): a
POPULATED single-leg display pack — the leg keyed at the Dirac site, [3]'s own
first index 0, the site's prescription.  Content-bearing: `Nonempty Leg` holds,
coverage holds, keying holds, the consumption tie holds
(`oneLeg_rel3_nonvalue_legs`) — only the leg's derived VALUE is wrong. -/
noncomputable def oneLegPack (p : ℕ) [Fact p.Prime] :
    ConsumedDisplayPack p (oneLegFam p) where
  Leg := Unit
  site := fun _ => diracSite p
  site_mem := fun _ => rfl
  first := fun _ => 0
  presc := fun _ => ()

/-- **(F3, rel3) VALUE FALSIFIER**: the one-leg junk pack refutes the filled
`SitedSlot_rel3` at EVERY cylinder-pinned target assignment — the per-leg
certification demands the β-table read (the constant 2) equal the certified
`BoxVol` mass of the leg's realization event (the full event, `vol_univ`-pinned
at 1).  The G3 record's junk-VALUE arm, resurrected at the derived-not-free
design exactly as D-SC principle P3 predicted: with no value field to junk, the
wrong value must sit in the ASSIGNMENT's β-table, and the slot catches it. -/
theorem sitedSlot_rel3_refuted_at_betaTwo (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    ¬ SitedSlot_rel3 (oneLegFam p) (oneLegAssign p Sp AD CI) (oneLegPack p) := by
  rintro ⟨-, -, hleg⟩
  obtain ⟨⟨-, -, heq⟩, -, -⟩ := hleg ()
  have h2 : (2 : ℚ) = CI.C.V.vol Set.univ := heq
  rw [CI.C.V.vol_univ] at h2
  norm_num at h2

/-- (F3, rel3) value-borne certificate: the POPULATION, COVERAGE, KEYING, and
CONSUMPTION-TIE legs of `SitedSlot_rel3` all HOLD at the one-leg junk pack —
the per-leg certification VALUE is the unique failing conjunct. -/
theorem oneLeg_rel3_nonvalue_legs (p : ℕ) [Fact p.Prime]
    (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (CI : CInterface p Sp AD (diracSite p).δabs (diracSite p).dRel) :
    Nonempty (oneLegPack p).Leg ∧
    (∀ (S : RelSite p) (hS : S ∈ (oneLegFam p).mem),
      ∀ T ∈ (oneLegAssign p Sp AD CI).consumed S hS,
        ∃ l : (oneLegPack p).Leg,
          (⟨(oneLegPack p).site l, (oneLegPack p).presc l⟩ : Σ S' : RelSite p, S'.PTree)
            = ⟨S, T⟩) ∧
    (∀ l : (oneLegPack p).Leg,
      ((oneLegPack p).first l
          = ((oneLegAssign p Sp AD CI).data ((oneLegPack p).site l)
              ((oneLegPack p).site_mem l)).beta.entryFirst ∧
        (oneLegAssign p Sp AD CI).tableConv ((oneLegPack p).site l)
          ((oneLegPack p).site_mem l) ((oneLegPack p).first l)) ∧
      (oneLegPack p).presc l ∈ (oneLegAssign p Sp AD CI).consumed
        ((oneLegPack p).site l) ((oneLegPack p).site_mem l)) := by
  refine ⟨⟨()⟩, ?_, fun l => ⟨⟨rfl, rfl⟩, trivial⟩⟩
  intro S hS T _
  refine ⟨(), ?_⟩
  have hS' : S = diracSite p := hS
  subst hS'
  rfl

end LeanUrat.MovesU

/-!
AXIOM FOOTPRINTS (verified 2026-07-31 via `lake env lean` on a `#print axioms`
scratch over the built module; 0 `sorry` tokens in this file):

* `sitedSlot_rel2b_refuted_at_diracSite`    — [propext, Classical.choice, Quot.sound]
* `sitedSlot_rel2b_refuted_at_wrongValued`  — [propext, Classical.choice, Quot.sound]
* `sitedSlot_rel2d_refuted_at_wrongValued`  — [propext, Classical.choice, Quot.sound]
* `wrongValued_composite_nonconstant`       — [propext, Classical.choice, Quot.sound]
* `wrongValued_verdict_mismatch`            — [propext, Classical.choice, Quot.sound]
* `wrongValued_rel2d_nonsquare_legs`        — [propext, Classical.choice, Quot.sound]
* `sitedSlot_rel2e_refuted_at_betaTwo`      — [propext, Classical.choice, Quot.sound]
* `wrongValued_rel2e_nonvalue_legs`         — [propext, Classical.choice, Quot.sound]
* `sitedSlot_rel3_refuted_at_betaTwo`       — [propext, Classical.choice, Quot.sound]
* `oneLeg_rel3_nonvalue_legs`               — [propext, Classical.choice, Quot.sound]
* `diracMass_two_valued`                    — [propext, Classical.choice, Quot.sound]
* `diracSite_cellMass_pos`                  — [propext, Classical.choice, Quot.sound]
* `diracSite_events_total`                  — [propext, Classical.choice, Quot.sound]

Lean-core only — no declared axiom (GMN / cell recursion) enters any falsifier.
-/
