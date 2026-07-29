/-  MovesV unit V3-5b `inst_bij_surj` — SURJECTIVITY onto the realizable
    concrete ε with template ε̊, GIVEN the entrance exactness face (XHDdEnt);
    SCOPED SELF-LOOP-FREE (ADJ-3, 2026-07-31).

    STATEMENT REPAIR (adjudicated; Codex-confirmed mechanism — the depth-slot
    zip truncation, quoted in full in `V3_instbijA.lean`'s header): the
    unscoped surjectivity is NOT ONTO on self-loop templates — once any
    self-loop depth ≥ 1, `shapeOfSlots?`'s zip truncates past `word.length`,
    so no slot point can write a shape whose expanded run exceeds the
    pair-slot budget; concrete realizable ε over such templates have no
    preimage.  Ledger warrant (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md,
    wave-A record): "instbij self-loop-free scoping (the depth-slot zip
    truncation, Codex-confirmed)" — "MIRRORS the capstone's order-0
    perimeter."  Scope hypothesis: `εT.word.filter (SelfLoopLetter n) = []`
    (all depth slots vanish; the zip is exact — A's mechanism lemmas).

    ADJ-2 RESIDUE CLOSED (closer pass, this file): the inverse-construction
    fold is PROVED with NO new scoping hypotheses, wired through the landed
    ADJ-2 spword proofs — `readFits_unique` (V3-3d, isSome-scoped) pins the
    fold's per-letter choice to ε's own read; the width/Dwidth chain legs
    (the V3-3a width-law seam) and the gamTie/anchorTie legs come from ε's
    OWN `ShapeWF` certificate (words → reads needs no `SpeciesCoherent`: the
    letters are GIVEN by hT's fitting word, not constructed); the hSLF
    collapse identity rides the SP4 self-loop characterization
    (`SuccStep s s` forces a self-loop letter, which would survive collapse
    into εT.word against hSLF).  M1 SOUNDNESS REPAIR (2026-07-29): the false
    shim is DELETED; the statement gains the threaded domain-scoping
    hypothesis `hdom` (the order-0 perimeter family) and returns the
    perimeter-certified `writeHeights` value — sorry-free. -/
import LeanUrat.MovesV.V3_instbijA
import LeanUrat.MovesV.V3_tfin
import LeanUrat.MovesSp.SP4_selfloopChar

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesV

/-! ### ADJ-2 wiring apparatus (all `private`) -/

/-- SP4's characterization, chain-side: a letter with a self-loop `SuccStep`
edge IS a `SelfLoopLetter` (D-cancellation forces e·g = 1; the postRec tag
law and W′ = μ pin tag/sel). -/
private theorem selfLoop_of_succStep_self {n : ℕ} {s : MovesSp.Species}
    (h : MovesSp.SuccStep n s s) : SelfLoopLetter n s = true := by
  unfold SelfLoopLetter
  exact decide_eq_true ((MovesSp.selfloop_succStep_iff h.2.1 h.2.2).mp h)

/-- `collapseRuns` keeps the head of a run. -/
private theorem collapseRuns_head :
    ∀ (a : MovesSp.Species) (t : List MovesSp.Species),
      ∃ t', MovesSp.collapseRuns (a :: t) = a :: t'
  | _, [] => ⟨[], rfl⟩
  | a, b :: r => by
    rw [MovesSp.collapseRuns]
    by_cases hab : a = b
    · rw [if_pos hab]
      obtain ⟨t', ht'⟩ := collapseRuns_head b r
      exact ⟨t', by rw [ht', hab]⟩
    · rw [if_neg hab]
      exact ⟨MovesSp.collapseRuns (b :: r), rfl⟩

/-- on a `SuccStep` chain whose COLLAPSED word is self-loop-free, the collapse
is the identity: any adjacent duplicate would be a self-loop letter (SP4) and
its run head survives into the collapsed word's filter. -/
private theorem collapse_id_of_filterSLF {n : ℕ} :
    ∀ l : List MovesSp.Species, l.Chain' (MovesSp.SuccStep n) →
      (MovesSp.collapseRuns l).filter (SelfLoopLetter n) = [] →
      MovesSp.collapseRuns l = l
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | s :: s' :: rest, hch, hf => by
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hch
    by_cases heq : s = s'
    · exfalso
      rw [MovesSp.collapseRuns, if_pos heq] at hf
      have hstep' : MovesSp.SuccStep n s' s' := heq ▸ hstep
      obtain ⟨t', ht'⟩ := collapseRuns_head s' rest
      rw [ht', List.filter_cons, selfLoop_of_succStep_self hstep'] at hf
      simp at hf
    · rw [MovesSp.collapseRuns, if_neg heq] at hf ⊢
      rw [List.filter_cons] at hf
      have hf' : (MovesSp.collapseRuns (s' :: rest)).filter (SelfLoopLetter n)
          = [] := by
        rcases hsl : SelfLoopLetter n s with _ | _
        · rw [hsl] at hf
          simpa using hf
        · rw [hsl] at hf
          simp at hf
      rw [collapse_id_of_filterSLF (s' :: rest) htail hf']

/-- the data fields `template?` pins (Option-inj + structure projections). -/
private theorem template?_fields {n : ℕ} {ε : EntShapeV n} {εT : EntTemplate n}
    (hT : ε.template? = some εT) :
    εT.word = MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix))
      ∧ εT.gsel = ε.gsel ∧ εT.musel = ε.musel ∧ εT.selRec = ε.selRec := by
  simp only [EntShapeV.template?] at hT
  split at hT
  case isTrue h =>
    obtain heq := Option.some.inj hT
    subst heq
    exact ⟨rfl, rfl, rfl, rfl⟩
  case isFalse h => exact absurd hT (by simp)

/-- data-field extensionality for `EntShapeV` (proof fields irrelevant). -/
private theorem entShapeV_eq {n : ℕ} {A B : EntShapeV n}
    (hP : A.Phat = B.Phat) (hg : A.gsel = B.gsel)
    (hm : A.musel = B.musel) (hs : A.selRec = B.selRec) : A = B := by
  obtain ⟨P₁, e₁, g₁, m₁, x₁, y₁, z₁, w₁, s₁, u₁, v₁⟩ := A
  obtain ⟨P₂, e₂, g₂, m₂, x₂, y₂, z₂, w₂, s₂, u₂, v₂⟩ := B
  obtain rfl : P₁ = P₂ := hP
  obtain rfl : g₁ = g₂ := hg
  obtain rfl : m₁ = m₂ := hm
  obtain rfl : s₁ = s₂ := hs
  rfl

/-- THE SpFitsRead → ReadFits CLAUSE BRIDGE at one letter of a fitting word:
ε's read k itself satisfies `ReadFits` at the truncated prefix — e/s0 from
SpFitsRead; wSide = wraw via edvd; the w/Dwidth chains (the V3-3a WIDTH-LAW
seam) from `ShapeWF.w0/wchain/dchain0/dchain`; the γ-tie at the truncated
stretch (strS only reads the first k reads); the Bézout anchor from
`anchorTie`; species/monic by the `i = 0 ↔ prefix-empty` translation. -/
private theorem step_reconstruct {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) {ws : List MovesSp.Species}
    (hfits : SpWordFits n P ws) (k : ℕ) (hkw : k < ws.length)
    (hk : k < P.reads.length) :
    ReadFits n ⟨P.reads.take k⟩ (ws[k]'hkw) ((P.reads[k]'hk).h)
      (zig ((P.reads[k]'hk).gam)) (P.reads[k]'hk) := by
  have hsp := hfits.2.1 k hkw hk
  simp only [List.get_eq_getElem] at hsp
  obtain ⟨h1, h2, h3, -, h5, -, -, -, -, h10, h11⟩ := hsp
  have hiff : (P.reads.take k = []) ↔ k = 0 := by
    constructor
    · intro h0
      have hlt := congrArg List.length h0
      rw [List.length_take] at hlt
      simp only [List.length_nil] at hlt
      omega
    · rintro rfl
      exact List.take_zero
  refine ⟨h1.symm, h2.symm, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- wSide = wraw (the e·ℓ identity through edvd)
    rw [show MovesSp.Species.wraw (ws[k]'hkw)
        = (ws[k]'hkw).e * (ws[k]'hkw).ell from rfl, h1, h3]
    exact (Nat.mul_div_cancel' (hWF.edvd k hk)).symm
  · -- the selection pin
    intro gμ hgμ
    rw [h5] at hgμ
    obtain rfl := Option.some.inj hgμ
    exact ⟨rfl, rfl⟩
  · -- the width chain (the V3-3a width-law leg)
    by_cases hk0 : k = 0
    · subst hk0
      rw [show (⟨P.reads.take 0⟩ : MovesD.ShapePrefix).reads
          = P.reads.take 0 from rfl, List.take_zero]
      show (P.reads[0]'hk).w = 1
      exact hWF.w0 hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < P.reads.length := by omega
      have htk : P.reads.take (j + 1)
          = P.reads.take j ++ [P.reads[j]'hj] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      rw [show (⟨P.reads.take (j + 1)⟩ : MovesD.ShapePrefix).reads
          = P.reads.take (j + 1) from rfl, htk, List.getLast?_concat]
      show (P.reads[j + 1]'hk).w = (P.reads[j]'hj).w * (P.reads[j]'hj).g
      exact hWF.wchain j hk
  · -- the Dwidth chain
    by_cases hk0 : k = 0
    · subst hk0
      rw [show (⟨P.reads.take 0⟩ : MovesD.ShapePrefix).reads
          = P.reads.take 0 from rfl, List.take_zero]
      show (P.reads[0]'hk).Dwidth = 1
      exact hWF.dchain0 hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < P.reads.length := by omega
      have htk : P.reads.take (j + 1)
          = P.reads.take j ++ [P.reads[j]'hj] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      rw [show (⟨P.reads.take (j + 1)⟩ : MovesD.ShapePrefix).reads
          = P.reads.take (j + 1) from rfl, htk, List.getLast?_concat]
      show (P.reads[j + 1]'hk).Dwidth = (P.reads[j]'hj).childWidthS
      exact hWF.dchain j hk
  · -- γ slot code (zig is an equiv)
    exact (zig.symm_apply_apply _).symm
  · -- the γ-tie at the truncated stretch
    have hstr : (snocP ⟨P.reads.take k⟩ (P.reads[k]'hk)).strS
        ((⟨P.reads.take k⟩ : MovesD.ShapePrefix).reads.length) = P.strS k := by
      show (((P.reads.take k ++ [P.reads[k]'hk]).take
          (P.reads.take k).length).map MovesD.ShapeRead.e).prod
        = ((P.reads.take k).map MovesD.ShapeRead.e).prod
      rw [List.take_left]
    rw [hstr]
    exact hWF.gamTie k hk
  · -- the Bézout anchor tie
    exact hWF.anchorTie k hk
  · -- species (i = 0 ↔ empty-prefix translation)
    rw [h10]
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have h0 : ¬(P.reads.take k = []) := fun hc => hk0 (hiff.mp hc)
      simp [hk0, h0]
  · -- the monic bit
    rw [h11]
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have h0 : ¬(P.reads.take k = []) := fun hc => hk0 (hiff.mp hc)
      simp [hk0, h0]

/-- THE INVERSE-CONSTRUCTION FOLD: along a fitting word, `shapeOfSlots?`'s
fold over ε's own slot read-off reconstructs ε's prefix exactly (per-letter
existence from `step_reconstruct`, per-letter choice pinned by V3-3d's
`readFits_unique` — sel.isSome from SpFitsRead clause 5). -/
private theorem fold_reconstruct {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) {ws : List MovesSp.Species}
    (hfits : SpWordFits n P ws) :
    ∀ k, k ≤ P.reads.length →
      ((ws.take k).zip
          ((P.reads.map (fun R => (R.h, zig R.gam))).take k)).foldlM
        (fun Q sp => readOfLetter? n Q sp.1 sp.2.1 sp.2.2) emptyPrefix
      = some ⟨P.reads.take k⟩
  | 0, _ => by
    simp only [List.take_zero, List.zip_nil_left, List.foldlM_nil]
    rfl
  | k + 1, hk1 => by
    have hk : k < P.reads.length := hk1
    have hkw : k < ws.length := by rw [hfits.1]; exact hk
    have hkm : k < (P.reads.map (fun R => (R.h, zig R.gam))).length := by
      rw [List.length_map]; exact hk
    have hws : ws.take (k + 1) = ws.take k ++ [ws[k]'hkw] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkw, Option.toList_some]
    have hms : (P.reads.map (fun R => (R.h, zig R.gam))).take (k + 1)
        = (P.reads.map (fun R => (R.h, zig R.gam))).take k
          ++ [((P.reads[k]'hk).h, zig ((P.reads[k]'hk).gam))] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkm, Option.toList_some]
      simp only [List.getElem_map]
    have hlen2 : (ws.take k).length
        = ((P.reads.map (fun R => (R.h, zig R.gam))).take k).length := by
      simp only [List.length_take, List.length_map, hfits.1]
    have htake : P.reads.take k ++ [P.reads[k]'hk] = P.reads.take (k + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    have hex : ∃ R, ReadFits n ⟨P.reads.take k⟩ (ws[k]'hkw)
        ((P.reads[k]'hk).h) (zig ((P.reads[k]'hk).gam)) R :=
      ⟨P.reads[k]'hk, step_reconstruct hWF hfits k hkw hk⟩
    have hsel : (ws[k]'hkw).sel.isSome := by
      have hsp := hfits.2.1 k hkw hk
      simp only [List.get_eq_getElem] at hsp
      rw [hsp.2.2.2.2.1]
      rfl
    have hstep : readOfLetter? n ⟨P.reads.take k⟩ (ws[k]'hkw)
        ((P.reads[k]'hk).h) (zig ((P.reads[k]'hk).gam))
        = some ⟨P.reads.take (k + 1)⟩ := by
      rw [readOfLetter?, dif_pos hex,
        readFits_unique n ⟨P.reads.take k⟩ (ws[k]'hkw) hsel _ _ _ _
          hex.choose_spec (step_reconstruct hWF hfits k hkw hk)]
      show some (⟨P.reads.take k ++ [P.reads[k]'hk]⟩ : MovesD.ShapePrefix)
          = some ⟨P.reads.take (k + 1)⟩
      rw [htake]
    rw [hws, hms, List.zip_append hlen2, List.foldlM_append,
      fold_reconstruct hWF hfits k (Nat.le_of_lt hk)]
    show (([ws[k]'hkw].zip
        [((P.reads[k]'hk).h, zig ((P.reads[k]'hk).gam))]).foldlM
      (fun Q sp => readOfLetter? n Q sp.1 sp.2.1 sp.2.2)
      (⟨P.reads.take k⟩ : MovesD.ShapePrefix)) = some ⟨P.reads.take (k + 1)⟩
    simp only [List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons,
      List.foldlM_nil, hstep]
    rfl

/-- the slot point reading off ε's retained pairs (hSLF: no depth slots, the
chart is exactly the 2·word.length pair coordinates). -/
private theorem exists_slotPoint {n : ℕ} (εT : EntTemplate n)
    (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    (rds : List MovesD.ShapeRead) (hlen : εT.word.length = rds.length) :
    ∃ hp : Hpt εT.entDim,
      εT.pairSlots hp = rds.map (fun R => (R.h, zig R.gam)) := by
  have hdim : εT.entDim = 2 * εT.word.length := by
    unfold EntTemplate.entDim
    rw [hSLF]
    simp
  have hidx : ∀ k : Fin εT.entDim, k.val / 2 < rds.length := by
    intro k
    have h1 := k.isLt
    omega
  refine ⟨fun k => if k.val % 2 = 0 then (rds[k.val / 2]'(hidx k)).h
    else zig ((rds[k.val / 2]'(hidx k)).gam), ?_⟩
  unfold EntTemplate.pairSlots
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map]
  rw [if_pos (by omega : 2 * i % 2 = 0),
    if_neg (by omega : ¬(2 * i + 1) % 2 = 0)]
  have e1 : 2 * i / 2 = i := by omega
  have e3 : (2 * i + 1) / 2 = i := by omega
  simp only [e1, e3]

theorem inst_bij_surj {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    (hdom : ∀ h : Hpt εT.entDim, (V.entDom εT).Mem h → Order0Perimeter εT h)
    (β₀ : S.Cell) (ε : EntShapeV n)
    (hT : ε.template? = some εT) (hR : Realizable V ε β₀) :
    ∃ (h : Hpt εT.entDim) (hm : (V.entDom εT).Mem h),
      writeHeights εT h (hdom h hm) = ε := by
  -- The inverse construction: extract the height/depth slots from ε and show
  -- that writing them back into the template's slots recovers ε (template-
  -- matching through readOfLetter, uniqueness by V3-3d's readFits_unique).
  obtain ⟨h, hsome⟩ : ∃ h : Hpt εT.entDim, writeHeights? εT h = some ε := by
    obtain ⟨hword, hgsel, hmusel, hselRec⟩ := template?_fields hT
    -- (1) hT's non-junk fitting word, pinned to εT.word by hSLF
    have hfitEx : ∃ ws, SpWordFits n (ε.Phat : MovesD.ShapePrefix) ws := by
      by_contra hno
      have hjunk : spWord n (ε.Phat : MovesD.ShapePrefix) = [] := by
        rw [spWord, dif_neg hno]
      exact εT.hne (by rw [hword, hjunk]; rfl)
    have hfitsSp : SpWordFits n (ε.Phat : MovesD.ShapePrefix)
        (spWord n (ε.Phat : MovesD.ShapePrefix)) := by
      rw [spWord, dif_pos hfitEx]
      exact hfitEx.choose_spec
    have hcoll : MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix))
        = spWord n (ε.Phat : MovesD.ShapePrefix) :=
      collapse_id_of_filterSLF _ hfitsSp.2.2.2 (by rw [← hword]; exact hSLF)
    have hwfit : SpWordFits n (ε.Phat : MovesD.ShapePrefix) εT.word := by
      rw [hword, hcoll]
      exact hfitsSp
    have hlen : εT.word.length = (ε.Phat : MovesD.ShapePrefix).reads.length :=
      hwfit.1
    -- (2) the slot point read off ε's heights
    obtain ⟨hp, hps⟩ := exists_slotPoint εT hSLF
      (ε.Phat : MovesD.ShapePrefix).reads hlen
    -- (3) the fold reconstructs P̂ exactly
    have hfold : shapeOfSlots? n (expandRuns n εT.word (εT.depthSlots hp))
        (εT.pairSlots hp) = some (ε.Phat : MovesD.ShapePrefix) := by
      rw [expandRuns_eq_of_selfLoopFree εT.word _ hSLF, shapeOfSlots?, hps]
      have h2 := fold_reconstruct ε.Phat.2 hwfit
        (ε.Phat : MovesD.ShapePrefix).reads.length le_rfl
      rw [List.take_of_length_le (le_of_eq hlen),
        List.take_of_length_le (by simp), List.take_length] at h2
      exact h2
    -- (4) the WF + EntTiesAt dite passes from ε's own fields
    have hties : EntTiesAt ε.Phat εT := by
      refine ⟨ε.hne, ?_, ?_, ?_, ?_⟩
      · intro R hRl
        rw [hgsel, hmusel]
        exact ε.hentry R hRl
      · intro R hRl
        rw [hgsel, hmusel]
        exact ε.helig R hRl
      · rw [hselRec]
        exact ε.hlen
      · rw [hselRec]
        exact ε.hmenu
    -- (5) writeHeights? lands exactly on ε (EntShapeV ext closes)
    have hsome : writeHeights? εT hp = some ε := by
      rw [writeHeights?, hfold, Option.bind_some,
        dif_pos (⟨ε.Phat.2, hties⟩ :
          ∃ hWF : ShapeWFOf n (ε.Phat : MovesD.ShapePrefix),
            EntTiesAt ⟨(ε.Phat : MovesD.ShapePrefix), hWF⟩ εT)]
      exact congrArg some (entShapeV_eq rfl hgsel hmusel hselRec)
    exact ⟨hp, hsome⟩
  -- Membership: ε realizes the template at h (Realizable = hR), so the XHD-d
  -- entrance face's no_orphanE places h in the semilinear domain.
  -- (instRealizable εT h β₀ := ∃ ε' ∈ writeHeights? εT h, Realizable V ε' β₀.)
  have hm : (V.entDom εT).Mem h :=
    DE.no_orphanE εT h β₀ ⟨ε, hsome, hR⟩
  -- the perimeter-certified value collapses onto ε through hsome.
  exact ⟨h, hm, Option.some_injective _
    ((Option.some_get
      (writeHeights_total_of_perimeter εT h (hdom h hm))).trans hsome)⟩

end LeanUrat.MovesV
