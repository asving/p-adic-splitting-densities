/-  MovesV unit V3-5a `inst_bij_inj` · HARD — INJECTIVITY of the instantiation
    map, SCOPED SELF-LOOP-FREE (ADJ-3, 2026-07-31).

    STATEMENT REPAIR (adjudicated; Codex-confirmed mechanism, wave-A refutation
    queue): the depth-slot truncation — `shapeOfSlots?` folds over
    `(expandRuns n εT.word (εT.depthSlots h)).zip (εT.pairSlots h)` and
    `pairSlots` has length `word.length`, so THE ZIP TRUNCATES PAST
    `word.length`: once any self-loop depth ≥ 1 the expanded word is strictly
    longer than the pair-slot list and the depth slots are ignored by the
    read-off — the unscoped A is FALSE (two points differing only in a depth
    slot collide), and the unscoped B is NOT ONTO on self-loop templates.
    Ledger warrant (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md, wave-A record):
    "instbij self-loop-free scoping (the depth-slot zip truncation,
    Codex-confirmed)" — it "MIRRORS the capstone's order-0 perimeter."
    ADJUDICATED SCOPE: the SELF-LOOP-FREE hypothesis
    `εT.word.filter (SelfLoopLetter n) = []` (equivalently, by
    `List.filter_eq_nil_iff`: no self-loop letters in the template word — all
    depth slots vanish, `entDim = 2·word.length`).  At depth 0 the expansion
    is the identity (`expandRuns_eq_of_selfLoopFree`), `pairSlots` length =
    expanded-word length, and the zip is EXACT — the fold then pins read r's
    retained pair `(R.h, zig R.gam)` to `pairSlots[r]` (`ReadFits` clauses 7–8
    + `zig.apply_symm_apply`), so the slot point is recovered from the shape.

    M1 SOUNDNESS REPAIR (ratification verdict, 2026-07-29): the false shim
    `writeHeights_total_unscoped` is DELETED; `writeHeights` is the SCOPED
    map keyed to `Order0Perimeter` (the order-0 perimeter family), so
    injectivity is stated at perimeter-certified points — statements gaining
    hypotheses is the honest cost.  The proof is otherwise unchanged and
    sorry-free. -/
import LeanUrat.MovesV.V3_spwordD

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- SELF-LOOP-FREE ⇒ the run re-expansion is the identity: every letter takes
`expandRuns`' else-branch, so the depth list is never consumed.  (The ADJ-3
mechanism lemma: at all depths 0 the expanded word IS the template word.) -/
theorem expandRuns_eq_of_selfLoopFree {n : ℕ} :
    ∀ (ws : List MovesSp.Species) (ds : List ℕ),
      ws.filter (SelfLoopLetter n) = [] → expandRuns n ws ds = ws
  | [], _, _ => rfl
  | s :: ws, ds, hf => by
    rw [List.filter_cons] at hf
    by_cases hs : SelfLoopLetter n s
    · simp [hs] at hf
    · simp only [hs] at hf
      rw [expandRuns, if_neg (by simp [hs]),
        expandRuns_eq_of_selfLoopFree ws ds (by simpa using hf)]

/-- one fold step appends exactly the offered slot pair: `ReadFits` clauses
7–8 pin `R.h = hslot`, `R.gam = zig.symm uslot`, and `zig` is an equiv. -/
private theorem readOfLetter?_slots {n : ℕ} {P P' : MovesD.ShapePrefix}
    {s : MovesSp.Species} {hs us : ℕ}
    (h : readOfLetter? n P s hs us = some P') :
    P'.reads.map (fun R => (R.h, zig R.gam))
      = P.reads.map (fun R => (R.h, zig R.gam)) ++ [(hs, us)] := by
  rw [readOfLetter?] at h
  split at h
  case isTrue hc =>
    injection h with h
    obtain ⟨-, -, -, -, -, -, hh, hgam, -, -, -, -⟩ := hc.choose_spec
    subst h
    simp [snocP, hh, hgam]
  case isFalse => exact absurd h (by simp)

/-- the fold recovers the offered slot list (prefix-accumulated form). -/
private theorem foldlM_readOfLetter_slots {n : ℕ} :
    ∀ (l : List (MovesSp.Species × ℕ × ℕ)) (P₀ P : MovesD.ShapePrefix),
      l.foldlM (fun P sp => readOfLetter? n P sp.1 sp.2.1 sp.2.2) P₀ = some P →
      P.reads.map (fun R => (R.h, zig R.gam))
        = P₀.reads.map (fun R => (R.h, zig R.gam)) ++ l.map Prod.snd
  | [], P₀, P, h => by
    simp only [List.foldlM_nil] at h
    cases h
    simp
  | sp :: l, P₀, P, h => by
    rw [List.foldlM_cons] at h
    cases hstep : readOfLetter? n P₀ sp.1 sp.2.1 sp.2.2 with
    | none => simp [hstep] at h
    | some P₁ =>
      rw [hstep] at h
      rw [foldlM_readOfLetter_slots l P₁ P h, readOfLetter?_slots hstep]
      simp

/-- the EXACT-ZIP read-off: when the slot list is no longer than the word —
the self-loop-free situation, where both have length `word.length` — a
successful `shapeOfSlots?` returns a prefix whose retained `(h, zig γ)` pairs
are EXACTLY the offered slots.  (The zip truncates the WORD side only.) -/
theorem shapeOfSlots?_slots {n : ℕ} {ws : List MovesSp.Species}
    {ps : List (ℕ × ℕ)} {P : MovesD.ShapePrefix}
    (hlen : ps.length ≤ ws.length)
    (h : shapeOfSlots? n ws ps = some P) :
    P.reads.map (fun R => (R.h, zig R.gam)) = ps := by
  rw [shapeOfSlots?] at h
  rw [foldlM_readOfLetter_slots (n := n) (ws.zip ps) emptyPrefix P h]
  simp [emptyPrefix, List.map_snd_zip hlen]

/-- SELF-LOOP-FREE slot recovery through `writeHeights?`: a successful
instantiation remembers its pair-slot point in the reads. -/
theorem writeHeights?_pairSlots {n : ℕ} {εT : EntTemplate n}
    (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    {h : Hpt εT.entDim} {ε : EntShapeV n}
    (hw : writeHeights? εT h = some ε) :
    (ε.Phat : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
      = εT.pairSlots h := by
  rw [writeHeights?] at hw
  cases hP : shapeOfSlots? n (expandRuns n εT.word (εT.depthSlots h))
      (εT.pairSlots h) with
  | none => simp [hP] at hw
  | some P =>
    rw [hP] at hw
    simp only [Option.bind_some] at hw
    split at hw
    case isFalse => exact absurd hw (by simp)
    case isTrue hwf =>
      injection hw with hw
      subst hw
      refine shapeOfSlots?_slots ?_ hP
      rw [expandRuns_eq_of_selfLoopFree εT.word (εT.depthSlots h) hSLF,
        EntTemplate.pairSlots, List.length_ofFn]

/-- SELF-LOOP-FREE ⇒ the pair-slot projection is injective on `Hpt`: with no
depth slots, `entDim = 2·word.length` and EVERY coordinate of `h` appears in
`pairSlots` (even coordinates as first components, odd as second). -/
theorem pairSlots_inj_of_selfLoopFree {n : ℕ} {εT : EntTemplate n}
    (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    {h₁ h₂ : Hpt εT.entDim}
    (hp : εT.pairSlots h₁ = εT.pairSlots h₂) : h₁ = h₂ := by
  rw [EntTemplate.pairSlots, EntTemplate.pairSlots] at hp
  have hfun := List.ofFn_inj.mp hp
  funext k
  have hdim : εT.entDim = 2 * εT.word.length := by
    unfold EntTemplate.entDim
    rw [hSLF]
    simp
  have hk : k.val < 2 * εT.word.length := lt_of_lt_of_eq k.isLt hdim
  have hilt : k.val / 2 < εT.word.length := by omega
  have hpt := congrFun hfun ⟨k.val / 2, hilt⟩
  rw [Prod.mk.injEq] at hpt
  rcases Nat.even_or_odd k.val with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hik : k = ⟨2 * (k.val / 2), by omega⟩ := by
      apply Fin.ext
      change k.val = 2 * (k.val / 2)
      omega
    rw [hik]
    exact hpt.1
  · have hik : k = ⟨2 * (k.val / 2) + 1, by omega⟩ := by
      apply Fin.ext
      change k.val = 2 * (k.val / 2) + 1
      omega
    rw [hik]
    exact hpt.2

/-- V3-5a, ADJ-3 SCOPED FORM — injectivity of the instantiation map on
SELF-LOOP-FREE templates (see the file header for the adjudication record;
V3-3d's `spWord_faithful` route is NOT used — the exact zip replaces it). -/
theorem inst_bij_inj {n : ℕ} (εT : EntTemplate n)
    (hSLF : εT.word.filter (SelfLoopLetter n) = [])
    {h₁ h₂ : Hpt εT.entDim}
    (hp₁ : Order0Perimeter εT h₁) (hp₂ : Order0Perimeter εT h₂)
    (heq : writeHeights εT h₁ hp₁ = writeHeights εT h₂ hp₂) : h₁ = h₂ := by
  have hs₁ : writeHeights? εT h₁ = some (writeHeights εT h₂ hp₂) := by
    rw [← heq]
    exact (Option.some_get (writeHeights_total_of_perimeter εT h₁ hp₁)).symm
  have hs₂ : writeHeights? εT h₂ = some (writeHeights εT h₂ hp₂) :=
    (Option.some_get (writeHeights_total_of_perimeter εT h₂ hp₂)).symm
  exact pairSlots_inj_of_selfLoopFree hSLF
    ((writeHeights?_pairSlots hSLF hs₁).symm.trans
      (writeHeights?_pairSlots hSLF hs₂))

end LeanUrat.MovesV
