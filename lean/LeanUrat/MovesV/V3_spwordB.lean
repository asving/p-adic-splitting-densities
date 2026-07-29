/-  MovesV unit V3-3b `spword_collapse` (RE-KEYED REV 7, C11; DELETE-AND-
    SCOPED at the final-ratification M1 repair, 2026-07-29) — the TOTALITY
    theorem is now SCOPED: the unscoped `template_total` was SEMANTICALLY
    FALSE (verdict M1: "the countermodel is constructible from the checked
    witness already in the corpus" — `SpWordNeg.P3` extends to an
    `EntShapeV`, `spWord 3 P3 = []`, `template? = none`; the compiled
    negation record is `TTNeg.template_total_false`,
    `V3_spword_negWitness3.lean`).  The scoped-true form is
    `template_total_of_perimeter` under the named `SpWordPerimeter`
    predicate (the `Order0Perimeter`/`EntDomOrder0` family pattern), PROVED
    sorry-free; `EntShapeV.template` now demands the perimeter
    certificate. -/
import LeanUrat.MovesV.V3_spwordA
import LeanUrat.MovesSp.SP3_collapseNeNil
import LeanUrat.MovesSp.SP3_collapseSublist
import LeanUrat.MovesSp.SP3_collapseWalk

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-! ### c456 machinery (prover pass 2026-07-29): collapse preservation +
the branch-slot ↔ branching-letter bridge.  All PRIVATE — proof apparatus
for `template_total`'s entry/count/menu legs, no statement surface. -/

/-- collapsing self-loop runs keeps the LAST letter of the last run. -/
private theorem collapseRuns_getLast? :
    ∀ l : List MovesSp.Species,
      (MovesSp.collapseRuns l).getLast? = l.getLast?
  | [] => rfl
  | [_] => rfl
  | s :: s' :: rest => by
    rw [MovesSp.collapseRuns]
    by_cases heq : s = s'
    · rw [if_pos heq, collapseRuns_getLast? (s' :: rest),
        List.getLast?_cons_cons]
    · rw [if_neg heq]
      have hne : MovesSp.collapseRuns (s' :: rest) ≠ [] :=
        MovesSp.collapseRuns_ne_nil (by simp)
      cases hcl : MovesSp.collapseRuns (s' :: rest) with
      | nil => exact absurd hcl hne
      | cons x xs =>
        rw [List.getLast?_cons_cons, ← hcl,
          collapseRuns_getLast? (s' :: rest), List.getLast?_cons_cons]

/-- a self-loop letter (SuccStep s s) is NEVER branching: the stage law forces
sel = some (1, W) (e·g = 1 by D-cancellation, μ = W), and Budget (B3)'s
`s0 + wraw ≤ W` gives ℓ ≤ W, so m̄ = ℓ/W ≤ 1 < 2. -/
private theorem selfStep_not_branching {n : ℕ} {s : MovesSp.Species}
    (h : MovesSp.SuccStep n s s) : IsBranchingLetter n s = false := by
  obtain ⟨hstage, hcoh, hbud⟩ := h
  unfold MovesSp.StageLaws at hstage
  rcases hsel : s.sel with _ | ⟨g, μ⟩
  · rw [hsel] at hstage; exact hstage.elim
  · rw [hsel] at hstage
    obtain ⟨hD, -, hW, -, -⟩ := hstage
    have hD1 : 0 < s.D := hcoh.1.1
    have hW1 : 0 < s.W := hcoh.1.2.2.1
    have he1 : 0 < s.e := hcoh.1.2.2.2.1
    have heg : s.e * g = 1 :=
      Nat.eq_of_mul_eq_mul_right hD1 (by rw [one_mul]; exact hD.symm)
    have hg1 : g = 1 := by
      have hgle : g ≤ 1 := by
        by_contra hgt
        have h2 : 2 ≤ s.e * g :=
          le_trans (by omega) (Nat.le_mul_of_pos_left g he1)
        omega
      rcases Nat.eq_zero_or_pos g with h0 | hpos
      · rw [h0, Nat.mul_zero] at heg
        exact absurd heg (by norm_num)
      · omega
    have hb3 : s.s0 + s.wraw ≤ s.W := hbud.2.2.1.1
    have hellW : s.ell ≤ s.W :=
      calc s.ell ≤ s.e * s.ell := Nat.le_mul_of_pos_left _ he1
        _ = s.wraw := rfl
        _ ≤ s.s0 + s.wraw := Nat.le_add_left _ _
        _ ≤ s.W := hb3
    have hmb : letterMbar s ≤ 1 := by
      rw [letterMbar, hsel]
      simp only [Option.map_some, Option.getD_some]
      rw [hg1, one_mul, ← hW]
      calc s.ell / s.W ≤ s.W / s.W := Nat.div_le_div_right hellW
        _ = 1 := Nat.div_self hW1
    rw [IsBranchingLetter]
    simp only [decide_eq_false_iff_not]
    omega

/-- collapse strikes only self-loop copies, so any Bool filter that is false
on self-loop letters passes through `collapseRuns` unchanged. -/
private theorem collapseRuns_filter {n : ℕ} (p : MovesSp.Species → Bool)
    (hp : ∀ s, MovesSp.SuccStep n s s → p s = false) :
    ∀ l : List MovesSp.Species, l.Chain' (MovesSp.SuccStep n) →
      (MovesSp.collapseRuns l).filter p = l.filter p
  | [], _ => rfl
  | [_], _ => rfl
  | s :: s' :: rest, hch => by
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hch
    rw [MovesSp.collapseRuns]
    by_cases heq : s = s'
    · rw [if_pos heq, collapseRuns_filter p hp (s' :: rest) htail]
      subst heq
      conv_rhs => rw [List.filter_cons]
      simp [hp s hstep]
    · rw [if_neg heq, List.filter_cons, List.filter_cons,
        collapseRuns_filter p hp (s' :: rest) htail]

/-- two equal-length lists with pointwise-tied filter bits and values have
equal filtered value lists (the index-to-induction bridge). -/
private theorem filter_map_congr {α β γ : Type*} :
    ∀ (l1 : List α) (l2 : List β) (p : α → Bool) (q : β → Bool)
      (f : α → γ) (g : β → γ),
      l1.length = l2.length →
      (∀ (i : ℕ) (h1 : i < l1.length) (h2 : i < l2.length),
        p (l1.get ⟨i, h1⟩) = q (l2.get ⟨i, h2⟩) ∧
        f (l1.get ⟨i, h1⟩) = g (l2.get ⟨i, h2⟩)) →
      (l1.filter p).map f = (l2.filter q).map g
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _ => by simp at hlen
  | a :: t1, b :: t2, p, q, f, g, hlen, hpt => by
    have h0 : p a = q b ∧ f a = g b := hpt 0 (by simp) (by simp)
    have IH := filter_map_congr t1 t2 p q f g (by simpa using hlen)
      (fun i h1 h2 => hpt (i + 1) (by simpa using h1) (by simpa using h2))
    rw [List.filter_cons, List.filter_cons, h0.1]
    cases hq : q b with
    | false => simpa using IH
    | true => simp only [if_true, List.map_cons, h0.2, IH]

/-- THE SPWORD PERIMETER (M1 delete-and-scope, final-ratification verdict
2026-07-29): the entrance shape's prefix HAS a fitting species word.  The
unscoped ∀-form (`template_total`) is REFUTED — `TTNeg.template_total_false`
(`V3_spword_negWitness3.lean`) exhibits `SpWordNeg.P3` extended to an
`EntShapeV 3` with `template? = none`.  This named predicate is the
`Order0Perimeter` family's spWord face: consumers thread it exactly as
`EntDomOrder0` threads the writeHeights perimeter; Phase B discharges it
from the (sign-off) width + cross-read species-coherence laws. -/
def SpWordPerimeter {n : ℕ} (ε : EntShapeV n) : Prop :=
  ∃ ws, SpWordFits n (ε.Phat : MovesD.ShapePrefix) ws

/-- TOTALITY ON THE PERIMETER (the scoped-true form of the DELETED
`template_total`; sorry-free): given the `SpWordPerimeter` certificate the
`template?` dite passes — all six clauses proved via the SP3 collapse
machinery + the private c456 transports above. -/
theorem template_total_of_perimeter {n : ℕ} (ε : EntShapeV n)
    (hp : SpWordPerimeter ε) : (ε.template?).isSome := by
  have hex : ∃ ws, SpWordFits n (ε.Phat : MovesD.ShapePrefix) ws := hp
  have hfits : SpWordFits n (ε.Phat : MovesD.ShapePrefix)
      (spWord n (ε.Phat : MovesD.ShapePrefix)) := by
    unfold spWord
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨hlenW, hfit, hmem, hch⟩ := hfits
  set sw := spWord n (ε.Phat : MovesD.ShapePrefix) with hsw
  -- sw ≠ [] : its length equals P̂.reads.length, which is nonzero by ε.hne.
  have hswne : sw ≠ [] := by
    intro h
    apply ε.hne
    have hz : (ε.Phat : MovesD.ShapePrefix).reads.length = 0 := by
      rw [← hlenW, h]; rfl
    exact List.length_eq_zero_iff.mp hz
  -- Clauses 1–3 : nonempty / catalogue / collapsed-walk chain (SP3 machinery).
  have c1 : MovesSp.collapseRuns sw ≠ [] := MovesSp.collapseRuns_ne_nil hswne
  have cw := MovesSp.collapseRuns_collapsedWalk hmem hch
  have c2 : ∀ s ∈ MovesSp.collapseRuns sw, MovesSp.InCatalogue n s := cw.1
  have c3 : (MovesSp.collapseRuns sw).Chain'
      (fun s s' => MovesSp.SuccStep n s s' ∧ s ≠ s') := cw.2
  -- Clauses 4–6 : entry / branch-count / menu tie transports (PROVED
  -- 2026-07-29 via the private collapse-preservation + branch-slot↔
  -- branching-letter lemmas above; conditional on the hfits leg only).
  have c456 :
      (∀ s, (MovesSp.collapseRuns sw).getLast? = some s →
          s.sel = some (ε.gsel, ε.musel)) ∧
      ε.selRec.length =
          ((MovesSp.collapseRuns sw).filter (IsBranchingLetter n)).length ∧
      (∀ i (hi : i < ε.selRec.length),
          ε.selRec.get ⟨i, hi⟩ <
            letterMenuCard n (MovesSp.collapseRuns sw) i) := by
    -- the pointwise branching/menu tie along the fitted word
    have hQ : ∀ (i : ℕ) (h1 : i < sw.length)
        (h2 : i < (ε.Phat : MovesD.ShapePrefix).reads.length),
        IsBranchingLetter n (sw.get ⟨i, h1⟩)
            = (fun R => decide (IsBranchSlot R))
                ((ε.Phat : MovesD.ShapePrefix).reads.get ⟨i, h2⟩) ∧
        letterMbar (sw.get ⟨i, h1⟩)
            = MovesD.ShapeRead.mbar
                ((ε.Phat : MovesD.ShapePrefix).reads.get ⟨i, h2⟩) := by
      intro i h1 h2
      obtain ⟨-, -, hell, -, hsel, -, -, -, -, -, -⟩ := hfit i h1 h2
      have hmbar : letterMbar (sw.get ⟨i, h1⟩)
          = MovesD.ShapeRead.mbar
              ((ε.Phat : MovesD.ShapePrefix).reads.get ⟨i, h2⟩) := by
        rw [letterMbar, hsel, hell]
        rfl
      refine ⟨?_, hmbar⟩
      rw [IsBranchingLetter]
      rw [decide_eq_decide]
      rw [hmbar]
      exact Iff.rfl
    -- the filtered-menu list tie
    have hmap : (sw.filter (IsBranchingLetter n)).map letterMbar
        = ((ε.Phat : MovesD.ShapePrefix).reads.filter
            (fun R => decide (IsBranchSlot R))).map MovesD.ShapeRead.mbar :=
      filter_map_congr _ _ _ _ _ _ hlenW hQ
    -- collapse preserves the branching filter (self-loops never branch)
    have hfileq : (MovesSp.collapseRuns sw).filter (IsBranchingLetter n)
        = sw.filter (IsBranchingLetter n) :=
      collapseRuns_filter _ (fun s hs => selfStep_not_branching hs) sw hch
    refine ⟨?_, ?_, ?_⟩
    · -- c4: the entry tie at the collapsed last letter
      intro s hlast
      rw [collapseRuns_getLast?] at hlast
      have hlpos : 0 < (ε.Phat : MovesD.ShapePrefix).reads.length :=
        List.length_pos_of_ne_nil ε.hne
      have hsw_idx : sw.length - 1 < sw.length := by rw [hlenW]; omega
      have hr_idx : sw.length - 1
          < (ε.Phat : MovesD.ShapePrefix).reads.length := by
        rw [← hlenW]; exact hsw_idx
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hsw_idx] at hlast
      have hs_eq : sw[sw.length - 1]'hsw_idx = s := Option.some.inj hlast
      obtain ⟨-, -, -, -, hsel, -, -, -, -, -, -⟩ :=
        hfit (sw.length - 1) hsw_idx hr_idx
      have hlastR : (ε.Phat : MovesD.ShapePrefix).reads.getLast? =
          some ((ε.Phat : MovesD.ShapePrefix).reads.get
            ⟨sw.length - 1, hr_idx⟩) := by
        rw [List.getLast?_eq_getElem?]
        have hidx : (ε.Phat : MovesD.ShapePrefix).reads.length - 1
            = sw.length - 1 := by omega
        rw [hidx, List.getElem?_eq_getElem hr_idx]
        rfl
      have hent := ε.hentry _ hlastR
      rw [← hs_eq]
      change (sw.get ⟨sw.length - 1, hsw_idx⟩).sel = some (ε.gsel, ε.musel)
      rw [hsel, hent.1, hent.2]
    · -- c5: the branch-count tie
      rw [hfileq]
      have hlen2 := congrArg List.length hmap
      simp only [List.length_map] at hlen2
      rw [ε.hlen, ← hlen2]
    · -- c6: the menu tie
      intro i hi
      have h2 : ((sw.filter (IsBranchingLetter n))[i]?).map letterMbar
          = (((ε.Phat : MovesD.ShapePrefix).reads.filter
              (fun R => decide (IsBranchSlot R)))[i]?).map
                MovesD.ShapeRead.mbar := by
        rw [← List.getElem?_map, ← List.getElem?_map, hmap]
      rw [letterMenuCard, hfileq, h2]
      exact ε.hmenu i hi
  obtain ⟨c4, c5, c6⟩ := c456
  simp only [EntShapeV.template?, ← hsw]
  rw [dif_pos ⟨c1, c2, c3, c4, c5, c6⟩]
  rfl

/-- the PERIMETER-SCOPED template (M1 repair: the formerly total def demands
its shape's `SpWordPerimeter` certificate — proof-irrelevant, so downstream
equalities are unaffected). -/
noncomputable def EntShapeV.template {n : ℕ} (ε : EntShapeV n)
    (hp : SpWordPerimeter ε) : EntTemplate n :=
  (ε.template?).get (template_total_of_perimeter ε hp)

end LeanUrat.MovesV
