/-  MovesV unit V3-4 `template_finite` (RESTATED C12/A-3) — FINITE, OUTRIGHT
    AND UNCONDITIONALLY (the boundedness is §2.D's intrinsic WF fields). -/
import LeanUrat.MovesV.V3_spwordB
import LeanUrat.MovesSp.SP4_dagWords      -- SP_DAG_words (collapsed-word set finite), SP_DAG_walk
import LeanUrat.MovesSp.SP0_memCoherent   -- InCatalogue.coherent_budget

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- Each branching-letter menu card is bounded by `n`: the letter is a catalogue
member, so its `ell` is ≤ n (Budget B5), and `letterMbar` divides `ell`. -/
private theorem letterMenuCard_le {n : ℕ} {w : List MovesSp.Species}
    (hw : ∀ s ∈ w, MovesSp.InCatalogue n s) (i : ℕ) :
    letterMenuCard n w i ≤ n := by
  unfold letterMenuCard
  rcases h : (w.filter (IsBranchingLetter n))[i]? with _ | s
  · simp
  · have hsw : s ∈ w :=
      List.mem_of_mem_filter (List.mem_of_getElem? h)
    have hbud : MovesSp.Budget n s := ((hw s hsw).coherent_budget).2
    have hell : s.ell ≤ n := hbud.2.2.2.2.2.1
    change letterMbar s ≤ n
    unfold letterMbar
    rcases hsel : s.sel with _ | gμ
    · exact Nat.zero_le n
    · exact le_trans (Nat.div_le_self _ _) hell

/-- Decoding a `Fin`-tagged `pmap` back through `Fin.val` recovers the list. -/
private theorem pmap_val_eq {n : ℕ} (l : List ℕ) (H : ∀ x ∈ l, x < n + 1) :
    (l.pmap (fun x hx => (⟨x, hx⟩ : Fin (n + 1))) H).map Fin.val = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_pmap]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_pmap]

/-- The `Fin (n+1)`-valued `pmap` encoding is injective in the underlying list. -/
private theorem pmap_inj {n : ℕ} {l1 l2 : List ℕ}
    {H1 : ∀ x ∈ l1, x < n + 1} {H2 : ∀ x ∈ l2, x < n + 1}
    (h : l1.pmap (fun x hx => (⟨x, hx⟩ : Fin (n + 1))) H1
       = l2.pmap (fun x hx => (⟨x, hx⟩ : Fin (n + 1))) H2) :
    l1 = l2 := by
  have h2 := congrArg (List.map Fin.val) h
  rwa [pmap_val_eq, pmap_val_eq] at h2

theorem template_finite (n : ℕ) : Finite (EntTemplate n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: the catalogue is empty (Budget forces D ≤ 0 while WellTyped forces 1 ≤ D),
    -- so a nonempty catalogued word cannot exist and `EntTemplate 0` is empty.
    have hempty : IsEmpty (EntTemplate 0) := by
      constructor
      intro εT
      have hs := List.head_mem εT.hne
      have hcb := (εT.hMem _ hs).coherent_budget
      have h1 : 1 ≤ (εT.word.head εT.hne).D := hcb.1.1.1
      have h0 : (εT.word.head εT.hne).D ≤ 0 := hcb.2.1
      omega
    exact Finite.of_injective (fun x => (hempty.false x).elim : EntTemplate 0 → Empty)
      (fun a _ _ => (hempty.false a).elim)
  · -- n ≥ 1: bound the word (finite collapsed-word set) and the selection record
    -- (length ≤ 6n² and entries < n+1), then inject into a finite product.
    haveI hfw : Finite ↥{l : List MovesSp.Species | MovesSp.CollapsedWalk n l} :=
      (MovesSp.SP_DAG_words n hn).1.to_subtype
    haveI hfr : Finite ↥{r : List (Fin (n + 1)) | r.length ≤ 6 * n ^ 2} :=
      (List.finite_length_le (Fin (n + 1)) (6 * n ^ 2)).to_subtype
    have hbound : ∀ (εT : EntTemplate n), ∀ x ∈ εT.selRec, x < n + 1 := by
      intro εT x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hlt : εT.selRec[i] < letterMenuCard n εT.word i := εT.hmenu i hi
      have hle := letterMenuCard_le εT.hMem i
      omega
    have hlenle : ∀ (εT : EntTemplate n),
        (εT.selRec.pmap (fun x hx => (⟨x, hx⟩ : Fin (n + 1))) (hbound εT)).length ≤ 6 * n ^ 2 := by
      intro εT
      rw [List.length_pmap]
      calc εT.selRec.length = (εT.word.filter (IsBranchingLetter n)).length := εT.hlen
        _ ≤ εT.word.length := List.length_filter_le _ _
        _ ≤ 6 * n ^ 2 := MovesSp.SP_DAG_walk hn ⟨εT.hMem, εT.hWalk⟩
    apply Finite.of_injective (β :=
        (↥{l : List MovesSp.Species | MovesSp.CollapsedWalk n l}) ×
        (↥{r : List (Fin (n + 1)) | r.length ≤ 6 * n ^ 2}))
      (fun εT => (⟨εT.word, ⟨εT.hMem, εT.hWalk⟩⟩,
        ⟨εT.selRec.pmap (fun x hx => (⟨x, hx⟩ : Fin (n + 1))) (hbound εT), hlenle εT⟩))
    intro a b hab
    obtain ⟨aw, ahne, aMem, aWalk, ag, am, asg, asm, aEnt, asel, alen, amenu⟩ := a
    obtain ⟨bw, bhne, bMem, bWalk, bg, bm, bsg, bsm, bEnt, bsel, blen, bmenu⟩ := b
    have hword : aw = bw := congrArg (fun p => p.1.1) hab
    have hsel : asel = bsel := pmap_inj (congrArg (fun p => p.2.1) hab)
    obtain ⟨s, hs1⟩ : ∃ s, aw.getLast? = some s := by
      cases hh : aw.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hh) ahne
      | some s => exact ⟨s, rfl⟩
    have hs2 : bw.getLast? = some s := hword ▸ hs1
    have e1 := aEnt s hs1
    have e2 := bEnt s hs2
    have hgm : (ag, am) = (bg, bm) := Option.some.inj (e1.symm.trans e2)
    have hg : ag = bg := congrArg Prod.fst hgm
    have hm : am = bm := congrArg Prod.snd hgm
    subst hword; subst hsel; subst hg; subst hm
    rfl

end LeanUrat.MovesV
