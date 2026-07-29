/-
Unit V3-3a/3d-NEG-2 — COMPILED NEGATION WITNESSES, round 2 (MovesV wave-4
prover pass B3, 2026-07-29; the `U1_negWitness` durability pattern).  Three
refutations, all Lean-core-only footprints:

(1) `SpWordNeg2.spWord_exists_false'` — V3-3a's `spWord_exists` is STILL
    FALSE **with the adjudicated width hypotheses (hn + hcont) included**:
    THE SPECIES/TAG OFF-BY-ONE.  `SpFitsRead`'s species clause
    (`R.species = if i = 0 then .root else speciesTagOf s`) ties read i's
    OWN move class (forced by `ShapeRead.hspecInc`/`hspecRec` +
    `ShapeWF.species_iff`: increment iff its own e·g ≥ 2) to letter i's
    POSITION class (forced by `StageLaws`' tag law through the `SuccStep`
    chain: postInc iff the PARENT letter's e·g_sel ≥ 2).  `ShapeWF` has no
    cross-read species law, so the two classes can disagree: the witness
    `P4` = [root move e·g = 1 with window μ = 2; increment read e = 2] is
    ShapeWF at n = 3, satisfies 2 ≤ n and every continued read's μ ≥ 2,
    and admits NO fitting species word — letter 1's tag is pinned POST-REC
    by the chain while S1.species = increment demands POST-INC.  A repair
    must either add the missing cross-read species coherence to `ShapeWF`
    (species(r+1) keyed to read r's (e, g)) or re-key `SpFitsRead`'s
    species clause to the PARENT read's move class (sign-off item).

(2) `WHNeg.writeHeights_total_false` — V3-3d's `writeHeights_total` is
    FALSE as stated (∀ h : Hpt εT.entDim): at the ZERO slot point the first
    `readOfLetter?` dite demands `R.h = 0`, contradicting `ShapeRead.hh`
    (1 ≤ h).  Witness: the one-letter root template `T0` at n = 3.
    Note for the repair: restricting to pointwise-positive h is NOT enough —
    `ReadFits`' anchor clause `e·a = s0 − bezT e h · γ` needs
    `bezT·γ ≡ s0 (mod e)`, a per-read CONGRUENCE on the u*-slot at every
    e ≥ 2 letter (this is semilinear — exactly the `entDom` domain's job);
    totality can only hold on the restricted domain.

(3) `SpFaithNeg.spWord_faithful_false` (+ `_with_width`) — V3-3d's
    `spWord_faithful` is FALSE as stated, AND still false with the V3-3a
    width hypotheses added to both shapes: on any prefix with no fitting
    species word `spWord` is the junk [], so the `hw` hypothesis is
    vacuously satisfiable between DISTINCT shapes; the retained (h, zig γ)
    slots do not pin s0.  Witness pair: `P4` and `P4'` (s0 shifted 0 → 1,
    same (h, γ) lists, both width-compliant, both fitting-word-free by (1)).
    On the non-junk class the lemma's informal content stands: SpFitsRead +
    hs pin every field except (a, Dwidth, ustar), and those are determined
    by anchorTie/dchain/gamTie — the refutation lives ONLY on the junk-[]
    class, so a repair = hypotheses strong enough to make spWord ≠ [] (needs
    (1)'s repair first) or re-keying hw to fitting words.

All witnesses' WF certificates are machine-checked (`hWF4`, `hWF4'`);
axioms: Lean core only (checked 2026-07-29).
deps: MovesV Defs, MovesSp SP0_reflSucc (Bool reflection for the catalogue
membership of the template letter).
-/
import LeanUrat.MovesV.Defs
import LeanUrat.MovesSp.SP0_reflSucc

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
namespace SpWordNeg2

/-- root read, RECENTERING-CLASS MOVE (e·g = 1) with a width-2 window μ = 2:
e = 1, h = 1, g = 1, μ = 2, s0 = 0, wSide = 2 (len = 2, so g·μ = 2 ≤ 2). -/
def S0 : MovesD.ShapeRead :=
  { species := .root, e := 1, h := 1, g := 1, μ := 2, a := 0, s0 := 0,
    wSide := 2, Dwidth := 1, ustar := 0, gam := 2, w := 1, monicTop := false,
    he := le_refl 1, hg := le_refl 1, hμ := by norm_num, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := rfl,
    hspecInc := fun h => (nomatch h),
    hspecRec := fun h => (nomatch h),
    hmonicRoot := fun h => (nomatch h) }

/-- the follow-up read: an INCREMENT-CLASS read (own e·g = 2) inside the
width-2 window: e = 2, h = 1, g = 1, μ = 1, s0 = 0, wSide = 2 (len = 1). -/
def S1 : MovesD.ShapeRead :=
  { species := .increment, e := 2, h := 1, g := 1, μ := 1, a := 0, s0 := 0,
    wSide := 2, Dwidth := 1, ustar := -1, gam := 0, w := 1, monicTop := false,
    he := by norm_num, hg := le_refl 1, hμ := le_refl 1, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := rfl,
    hspecInc := fun _ => by norm_num,
    hspecRec := fun h => (nomatch h),
    hmonicRoot := fun h => (nomatch h) }

/-- THE WITNESS PREFIX: a recentering-class root move, then an
increment-class read. -/
def P4 : MovesD.ShapePrefix := ⟨[S0, S1]⟩

theorem P4_len : P4.reads.length = 2 := rfl

/-- machine-checked WF certificate at n = 3. -/
theorem hWF4 : MovesD.ShapeWF 3 P4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide  -- species_iff
  · decide  -- root_box
  · -- window
    intro r hr
    have hr0 : r = 0 := by have := P4_len; omega
    subst hr0
    simp only [P4, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · decide  -- gmu
  · decide  -- edvd
  · decide  -- dchain0
  · -- dchain
    intro r hr
    have hr0 : r = 0 := by have := P4_len; omega
    subst hr0
    simp only [P4, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- monic
    unfold MovesD.ShapePrefix.MonicTie
    decide
  · decide  -- w0
  · -- wchain
    intro r hr
    have hr0 : r = 0 := by have := P4_len; omega
    subst hr0
    simp only [P4, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- gamTie
    intro r hr
    have hr2 : r < 2 := by have := P4_len; omega
    interval_cases r <;>
      norm_num [P4, S0, S1, MovesD.ShapePrefix.strS]
  · -- anchorTie
    intro r hr
    have hr2 : r < 2 := by have := P4_len; omega
    interval_cases r
    · simp only [P4, List.getElem_cons_zero]
      norm_num [S0, MovesD.bezT, Int.emod_one]
    · simp only [P4, List.getElem_cons_zero, List.getElem_cons_succ]
      norm_num [S1]

/-- the width hypotheses HOLD on P4: every continued read has μ ≥ 2. -/
theorem hcont4 : ∀ (r : ℕ) (hr : r + 1 < P4.reads.length),
    2 ≤ (P4.reads[r]'(Nat.lt_of_succ_lt hr)).μ := by
  intro r hr
  have hr0 : r = 0 := by have := P4_len; omega
  subst hr0
  simp only [P4, List.getElem_cons_zero]
  norm_num [S0]

/-- NO species word fits P4: letter 1's tag is pinned POST-REC by the chain
(StageLaws from letter 0's selection (1,2) with e = 1), but S1.species =
increment demands speciesTagOf = increment, i.e. tag = postInc. -/
theorem spWordFits_impossible : ¬ ∃ ws, SpWordFits 3 P4 ws := by
  rintro ⟨ws, hlen, hfit, _hmem, hchain⟩
  have hlen2 : ws.length = 2 := by simpa [P4] using hlen
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen2
  have hfit0 := hfit 0 (by norm_num) (by simp [P4])
  have hfit1 := hfit 1 (by norm_num) (by simp [P4])
  -- letter 0's stage fields off S0
  have he0 : a.e = 1 := by
    have h := hfit0.1
    simpa [P4, S0] using h
  have hsel0 : a.sel = some (1, 2) := by
    have h := hfit0.2.2.2.2.1
    simpa [P4, S0] using h
  -- the chain step pins b.tag
  have hsucc : MovesSp.SuccStep 3 a b := List.rel_of_isChain_cons_cons hchain
  have hstage := hsucc.1
  unfold MovesSp.StageLaws at hstage
  rw [hsel0] at hstage
  have htagNe : b.tag ≠ .postInc := by
    intro h
    have h2 := hstage.2.2.2.1.mp h
    rw [he0] at h2
    norm_num at h2
  -- SpFitsRead at index 1 demands speciesTagOf b = .increment, i.e. tag = postInc
  have hspec : MovesC.ReadSpecies.increment = speciesTagOf b := by
    have h := hfit1.2.2.2.2.2.2.2.2.2.1
    simpa [P4, S1] using h
  have hbtag : b.tag = .postInc := by
    cases htag : b.tag <;> simp [speciesTagOf, htag] at hspec ⊢
  exact htagNe hbtag

/-- THE REFUTATION: the REPAIRED V3-3a sentence (width hypotheses included)
is STILL FALSE. -/
theorem spWord_exists_false' :
    ¬ ∀ (n : ℕ) (P : MovesD.ShapePrefix), MovesD.ShapeWF n P → 2 ≤ n →
        (∀ (r : ℕ) (hr : r + 1 < P.reads.length),
          2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ) →
        ∃ ws, SpWordFits n P ws := by
  intro h
  exact spWordFits_impossible (h 3 P4 hWF4 (by norm_num) hcont4)

end SpWordNeg2

namespace WHNeg

/-! ### Refutation 2: `writeHeights_total` at the zero slot point -/

/-- a catalogue ROOT letter with a designated selection (1, 1) at n = 3. -/
def L0 : MovesSp.Species :=
  { tag := .root, D := 1, w := 1, W := 3, e := 1, s0 := 0, ell := 1, a := 0,
    d := 2, slots := Finset.Icc 0 1, lam := {(1, 1)}, sel := some (1, 1),
    lflank := [], rflank := [2] }

theorem L0_rootAdm : MovesSp.RootAdmissible 3 L0 :=
  (MovesSp.rootAdmissibleB_iff 3 L0).mp (by decide)

/-- the one-letter template at n = 3. -/
def T0 : EntTemplate 3 :=
  { word := [L0], hne := by simp,
    hMem := by
      intro s hs
      have : s = L0 := by simpa using hs
      subst this
      exact MovesSp.InCatalogue.root L0_rootAdm,
    hWalk := List.isChain_singleton _,
    gsel := 1, musel := 1, hsel_g := le_refl 1, hsel_μ := le_refl 1,
    hEntry := by
      intro s hs
      have : L0 = s := by simpa using hs
      subst this
      rfl,
    selRec := [],
    hlen := by decide,
    hmenu := by intro i hi; simp at hi }

/-- the zero slot point. -/
def h0 : Hpt T0.entDim := fun _ => 0

theorem readOfLetter_none : readOfLetter? 3 emptyPrefix L0 0 0 = none := by
  rw [readOfLetter?, dif_neg]
  rintro ⟨R, hR⟩
  have hh := R.hh
  have h7 := hR.2.2.2.2.2.2.1
  omega

/-- THE REFUTATION: `writeHeights?` is NONE at the zero point of T0. -/
theorem writeHeights_total_false : ¬ (writeHeights? T0 h0).isSome := by
  have hsl : SelfLoopLetter 3 L0 = false := by decide
  have hex : expandRuns 3 T0.word (T0.depthSlots h0) = [L0] := by
    change expandRuns 3 [L0] _ = [L0]
    rw [expandRuns, if_neg (by simp [hsl]), expandRuns]
  have hps : T0.pairSlots h0 = [(0, 0)] := by
    simp [EntTemplate.pairSlots, T0, h0, List.ofFn_succ]
  have hnone : shapeOfSlots? 3 [L0] [(0, 0)] = none := by
    simp only [shapeOfSlots?, List.zip_cons_cons, List.zip_nil_left,
      List.foldlM_cons, readOfLetter_none]
    rfl
  rw [writeHeights?, hex, hps, hnone]
  simp

end WHNeg

namespace SpFaithNeg

open SpWordNeg2

/-- S0's height-preserving variant: same (h, γ) = (1, 2), same stage data
(e, g, μ, w, Dwidth), but s0 = 1 (side shifted right; wSide still 2, so
s0 + wSide = 3 = n forces monicTop = true by the monic tie), u* = -1, a = 1. -/
def S0' : MovesD.ShapeRead :=
  { species := .root, e := 1, h := 1, g := 1, μ := 2, a := 1, s0 := 1,
    wSide := 2, Dwidth := 1, ustar := -1, gam := 2, w := 1, monicTop := true,
    he := le_refl 1, hg := le_refl 1, hμ := by norm_num, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := rfl,
    hspecInc := fun h => (nomatch h),
    hspecRec := fun h => (nomatch h),
    hmonicRoot := fun _ => rfl }

/-- the sibling witness prefix: SAME (h, zig γ) slot lists as P4, different s0. -/
def P4' : MovesD.ShapePrefix := ⟨[S0', S1]⟩

theorem P4'_len : P4'.reads.length = 2 := rfl

theorem hWF4' : MovesD.ShapeWF 3 P4' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide  -- species_iff
  · decide  -- root_box
  · -- window
    intro r hr
    have hr0 : r = 0 := by have := P4'_len; omega
    subst hr0
    simp only [P4', List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · decide  -- gmu
  · decide  -- edvd
  · decide  -- dchain0
  · -- dchain
    intro r hr
    have hr0 : r = 0 := by have := P4'_len; omega
    subst hr0
    simp only [P4', List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- monic
    unfold MovesD.ShapePrefix.MonicTie
    decide
  · decide  -- w0
  · -- wchain
    intro r hr
    have hr0 : r = 0 := by have := P4'_len; omega
    subst hr0
    simp only [P4', List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- gamTie
    intro r hr
    have hr2 : r < 2 := by have := P4'_len; omega
    interval_cases r <;>
      norm_num [P4', S0', S1, MovesD.ShapePrefix.strS]
  · -- anchorTie
    intro r hr
    have hr2 : r < 2 := by have := P4'_len; omega
    interval_cases r
    · simp only [P4', List.getElem_cons_zero]
      norm_num [S0', MovesD.bezT, Int.emod_one]
    · simp only [P4', List.getElem_cons_zero, List.getElem_cons_succ]
      norm_num [S1]

/-- P4' has NO fitting species word either (same species/tag clash as P4). -/
theorem spWordFits_impossible' : ¬ ∃ ws, SpWordFits 3 P4' ws := by
  rintro ⟨ws, hlen, hfit, _hmem, hchain⟩
  have hlen2 : ws.length = 2 := by simpa [P4'] using hlen
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen2
  have hfit0 := hfit 0 (by norm_num) (by simp [P4'])
  have hfit1 := hfit 1 (by norm_num) (by simp [P4'])
  have he0 : a.e = 1 := by
    have h := hfit0.1
    simpa [P4', S0'] using h
  have hsel0 : a.sel = some (1, 2) := by
    have h := hfit0.2.2.2.2.1
    simpa [P4', S0'] using h
  have hsucc : MovesSp.SuccStep 3 a b := List.rel_of_isChain_cons_cons hchain
  have hstage := hsucc.1
  unfold MovesSp.StageLaws at hstage
  rw [hsel0] at hstage
  have htagNe : b.tag ≠ .postInc := by
    intro h
    have h2 := hstage.2.2.2.1.mp h
    rw [he0] at h2
    norm_num at h2
  have hspec : MovesC.ReadSpecies.increment = speciesTagOf b := by
    have h := hfit1.2.2.2.2.2.2.2.2.2.1
    simpa [P4', S1] using h
  have hbtag : b.tag = .postInc := by
    cases htag : b.tag <;> simp [speciesTagOf, htag] at hspec ⊢
  exact htagNe hbtag

/-- both spWords collapse to the junk []. -/
theorem spWord_P4 : spWord 3 P4 = [] := by
  unfold spWord
  rw [dif_neg spWordFits_impossible]

theorem spWord_P4' : spWord 3 P4' = [] := by
  unfold spWord
  rw [dif_neg spWordFits_impossible']

/-- the two Shape-level witnesses. -/
def PS4 : MovesD.Shape 3 := ⟨P4, hWF4⟩
def PS4' : MovesD.Shape 3 := ⟨P4', hWF4'⟩

theorem PS4_ne : PS4 ≠ PS4' := by
  intro h
  have h2 : P4 = P4' := congrArg Subtype.val h
  have h3 := congrArg
    (fun P : MovesD.ShapePrefix => P.reads[0]?.map MovesD.ShapeRead.s0) h2
  simp [P4, P4', S0, S0'] at h3

/-- the retained-slot hypothesis HOLDS: equal (h, zig γ) lists. -/
theorem hslots_eq :
    (P4.reads.map (fun R => (R.h, zig R.gam)))
      = (P4'.reads.map (fun R => (R.h, zig R.gam))) := by
  simp [P4, P4', S0, S0', S1]

/-- THE REFUTATION: `spWord_faithful`'s ∀-sentence is FALSE — on the junk-[]
class the spWord hypothesis is vacuous and the retained slots do not pin s0. -/
theorem spWord_faithful_false :
    ¬ ∀ (n : ℕ) (P P' : MovesD.Shape n),
        spWord n (P : MovesD.ShapePrefix) = spWord n (P' : MovesD.ShapePrefix) →
        (P : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
            = (P' : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam)) →
        P = P' := by
  intro h
  refine PS4_ne (h 3 PS4 PS4' ?_ hslots_eq)
  change spWord 3 P4 = spWord 3 P4'
  rw [spWord_P4, spWord_P4']

/-- STRONGER: adding the V3-3a width hypotheses to BOTH shapes does NOT rescue
`spWord_faithful` — the witness pair satisfies them. -/
theorem spWord_faithful_false_with_width :
    ¬ ∀ (n : ℕ) (P P' : MovesD.Shape n), 2 ≤ n →
        (∀ (r : ℕ) (hr : r + 1 < (P : MovesD.ShapePrefix).reads.length),
          2 ≤ ((P : MovesD.ShapePrefix).reads[r]'(Nat.lt_of_succ_lt hr)).μ) →
        (∀ (r : ℕ) (hr : r + 1 < (P' : MovesD.ShapePrefix).reads.length),
          2 ≤ ((P' : MovesD.ShapePrefix).reads[r]'(Nat.lt_of_succ_lt hr)).μ) →
        spWord n (P : MovesD.ShapePrefix) = spWord n (P' : MovesD.ShapePrefix) →
        (P : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
            = (P' : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam)) →
        P = P' := by
  intro h
  refine PS4_ne (h 3 PS4 PS4' (by norm_num) hcont4 ?_
    (by change spWord 3 P4 = spWord 3 P4'; rw [spWord_P4, spWord_P4']) hslots_eq)
  change ∀ (r : ℕ) (hr : r + 1 < P4'.reads.length),
    2 ≤ (P4'.reads[r]'(Nat.lt_of_succ_lt hr)).μ
  intro r hr
  have hr0 : r = 0 := by have := P4'_len; omega
  subst hr0
  simp only [P4', List.getElem_cons_zero]
  norm_num [S0']

end SpFaithNeg

end LeanUrat.MovesV
