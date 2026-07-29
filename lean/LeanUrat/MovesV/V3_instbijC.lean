/-  MovesV unit V3-5c `inst_bij_eq` — THE ASSEMBLED EQUIV + computation law
    (incl. the zig/gamTie roundtrip check); SCOPED SELF-LOOP-FREE (ADJ-3,
    2026-07-31) + SPWORD-CHOICE-PINNED (ADJ-2 family, closer pass).

    STATEMENT REPAIR (adjudicated; Codex-confirmed mechanism — the depth-slot
    zip truncation, quoted in full in `V3_instbijA.lean`'s header): the
    assembled equiv consumes A (injectivity) and B (surjectivity), both FALSE/
    not-onto unscoped on self-loop templates, so the equiv inherits the
    SELF-LOOP-FREE scope `εT.word.filter (SelfLoopLetter n) = []`.  Ledger
    warrant (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md, wave-A record):
    "instbij self-loop-free scoping (the depth-slot zip truncation,
    Codex-confirmed)" — "MIRRORS the capstone's order-0 perimeter."

    ADJ-2-FAMILY SCOPING (closer pass; the (b)-leg of the pre-closure residue
    note below the fold): the roundtrip `(writeHeights εT h).template? = some
    εT` recomputes the word as `collapseRuns (spWord …)`, and `spWord` is a
    CLASSICAL CHOICE over `SpWordFits` — fitting words are NOT unique (lam
    fillers, stage fields D/W, flanks, the i = 0 tag are all free), so the
    choice cannot be pinned from `EntTemplate`'s laws; the unscoped pinning
    is exactly V3-3d `spWord_faithful`'s re-keyed content, REFUTED AS STATED
    (junk-[] collision witness `SpFaithNeg.spWord_faithful_false`).  Following
    the ADJ-2 named-typed-hypothesis pattern (`SpeciesCoherent` in V3-3a,
    `AnchorAdmissible` in V3-3d — "the exact law the negWitness exploits the
    absence of"), the equiv gains the NAMED hypothesis `SpWordPinned εT`
    below; Phase B discharges it from the engine's D.7/D.8 output laws on the
    species-coherent stratum (where the fitting word is pinned).  SIGN-OFF
    ITEM: statement-surface addition, recorded per the adjudication family. -/
import LeanUrat.MovesV.V3_instbijB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- ADJ-2-FAMILY SCOPE (V3-5c): the spWord CHOICE-PINNING law at εT's
instantiation points — every successful instantiation's classically chosen
species word collapses back to the template word.  This is the (a)+(b)
residue of V3-5c in one named law (fitting-word existence is subsumed: junk
[] cannot collapse to the nonempty `εT.word`).  Unscoped ∀-template form
unavailable: `spWord` is `Classical.choice` over the NON-unique `SpWordFits`
fitters (V3-3d's `spWord_faithful` re-key, refuted as stated —
`SpFaithNeg.spWord_faithful_false`).  Phase B: discharge from the engine's
D.7/D.8 output laws on the species-coherent stratum. -/
def SpWordPinned {n : ℕ} (εT : EntTemplate n) : Prop :=
  ∀ (h : Hpt εT.entDim) (ε : EntShapeV n), writeHeights? εT h = some ε →
    MovesSp.collapseRuns (spWord n (ε.Phat : MovesD.ShapePrefix)) = εT.word

/-- data-field extensionality for `EntTemplate` (proof fields irrelevant). -/
private theorem entTemplate_eq {n : ℕ} {A B : EntTemplate n}
    (hw : A.word = B.word) (hg : A.gsel = B.gsel)
    (hm : A.musel = B.musel) (hs : A.selRec = B.selRec) : A = B := by
  obtain ⟨w₁, a₁, b₁, c₁, g₁, m₁, d₁, e₁, f₁, s₁, i₁, j₁⟩ := A
  obtain ⟨w₂, a₂, b₂, c₂, g₂, m₂, d₂, e₂, f₂, s₂, i₂, j₂⟩ := B
  obtain rfl : w₁ = w₂ := hw
  obtain rfl : g₁ = g₂ := hg
  obtain rfl : m₁ = m₂ := hm
  obtain rfl : s₁ = s₂ := hs
  rfl

/-- the data fields `writeHeights?` writes (Option-inj + projections). -/
private theorem writeHeights?_fields {n : ℕ} {εT : EntTemplate n}
    {h : Hpt εT.entDim} {ε : EntShapeV n}
    (hw : writeHeights? εT h = some ε) :
    ε.gsel = εT.gsel ∧ ε.musel = εT.musel ∧ ε.selRec = εT.selRec := by
  rw [writeHeights?] at hw
  cases hP : shapeOfSlots? n (expandRuns n εT.word (εT.depthSlots h))
      (εT.pairSlots h) with
  | none =>
    rw [hP] at hw
    simp at hw
  | some P =>
    rw [hP] at hw
    simp only [Option.bind_some] at hw
    split at hw
    case isTrue hex =>
      obtain heq := Option.some.inj hw
      subst heq
      exact ⟨rfl, rfl, rfl⟩
    case isFalse hex => exact absurd hw (by simp)

theorem inst_bij_eq {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (DE : XHDdEnt n S V)
    (εT : EntTemplate n) (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    (hdom : ∀ h : Hpt εT.entDim, (V.entDom εT).Mem h → Order0Perimeter εT h)
    (hpin : SpWordPinned εT)
    (β₀ : S.Cell) (hl : V.entLands εT β₀) :
    ∃ e : {h : Hpt εT.entDim // (V.entDom εT).Mem h} ≃
        {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀},
      ∀ h, (e h).1 = writeHeights εT h.1 (hdom h.1 h.2) := by
  classical
  -- THE ROUNDTRIP CHECK (the zig/gamTie leg): the instantiated concrete shape
  -- reads back to its own template — the dite passes from εT's own laws once
  -- `SpWordPinned` pins the recomputed word to εT.word.
  have hround : ∀ (h : Hpt εT.entDim) (hp : Order0Perimeter εT h),
      (writeHeights εT h hp).template? = some εT := by
    intro h hp
    have hs : writeHeights? εT h = some (writeHeights εT h hp) :=
      (Option.some_get (writeHeights_total_of_perimeter εT h hp)).symm
    obtain ⟨hg, hm, hsl⟩ := writeHeights?_fields hs
    have hpin' := hpin h _ hs
    simp only [EntShapeV.template?]
    split
    case isTrue hcnd =>
      exact congrArg some (entTemplate_eq hpin' hg hm hsl)
    case isFalse hcnd =>
      refine absurd ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hcnd
      · rw [hpin']; exact εT.hne
      · rw [hpin']; exact εT.hMem
      · rw [hpin']; exact εT.hWalk
      · rw [hpin', hg, hm]; exact εT.hEntry
      · rw [hpin', hsl]; exact εT.hlen
      · rw [hpin', hsl]; exact εT.hmenu
  -- realizability of every dom point, via the XHD-d no-stray face + the landing
  -- hypothesis.
  have hreal : ∀ (h : Hpt εT.entDim) (hMem : (V.entDom εT).Mem h),
      Realizable V (writeHeights εT h (hdom h hMem)) β₀ := by
    intro h hMem
    obtain ⟨ε, hεmem, hεR⟩ := DE.no_strayE εT h β₀ hl hMem
    have hmem2 : writeHeights εT h (hdom h hMem) ∈ writeHeights? εT h :=
      Option.get_mem (writeHeights_total_of_perimeter εT h (hdom h hMem))
    obtain rfl := Option.mem_unique hεmem hmem2
    exact hεR
  refine ⟨Equiv.ofBijective
      (fun a : {h : Hpt εT.entDim // (V.entDom εT).Mem h} =>
        (⟨writeHeights εT a.1 (hdom a.1 a.2), hround a.1 (hdom a.1 a.2),
          hreal a.1 a.2⟩ :
          {ε : EntShapeV n // ε.template? = some εT ∧ Realizable V ε β₀}))
      ⟨?_, ?_⟩, fun h => rfl⟩
  · -- injectivity, from V3-5a's `inst_bij_inj` (ADJ-3 scoped)
    intro a a' hEq
    have hv : writeHeights εT a.1 (hdom a.1 a.2)
        = writeHeights εT a'.1 (hdom a'.1 a'.2) := congrArg Subtype.val hEq
    exact Subtype.ext (inst_bij_inj εT hSLF (hdom a.1 a.2) (hdom a'.1 a'.2) hv)
  · -- surjectivity, from V3-5b's `inst_bij_surj` (ADJ-3 scoped)
    rintro ⟨ε, hT, hR⟩
    obtain ⟨h, hMem, hwrite⟩ := inst_bij_surj V DE εT hSLF hdom β₀ ε hT hR
    exact ⟨⟨h, hMem⟩, Subtype.ext hwrite⟩

end LeanUrat.MovesV
