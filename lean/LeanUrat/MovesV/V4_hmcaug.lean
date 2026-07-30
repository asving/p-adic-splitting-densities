/-  MovesV unit V4-13 `hmcaug_of_hmc` (NEW at REV 7, G1) — the vacuous-repair
    implication: HMC ⟹ HMCAug via the identity refinement (unavoidable for
    any faithful encoding; proves nothing about HMC; consumed by no unit). -/
import LeanUrat.MovesV.V4_hmc

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

open Classical

/-- THE IDENTITY REFINEMENT CORE (V4-13): `B α := PUnit`, `S' := S`, `cellEq`
the evident equiv, `histFib x := {⟨(), x⟩}`, all projections identity — the
vacuous-repair carrier's data + identity laws. -/
noncomputable def idRefinementCore {n : ℕ} (S : StepSys n) : RefinementCore n S where
  B := fun _ => PUnit
  finB := fun _ => inferInstance
  S' := S
  cellEq := ⟨fun α => ⟨α, PUnit.unit⟩, Sigma.fst, fun _ => rfl, fun _ => rfl⟩
  histOf := @fun _ _ x => x
  histFib := fun x => {⟨PUnit.unit, x⟩}
  histFib_proj := by
    intro α q₀ x p hp
    rw [Finset.mem_singleton] at hp; subst hp; rfl
  histFib_complete := by
    intro α' q₀ x'
    exact ⟨⟨PUnit.unit, x'⟩, Finset.mem_singleton_self _, rfl, HEq.rfl⟩
  moveProj := fun m' => m'
  dim_eq := fun _ => rfl
  assignOf := @fun _ _ _ _ _ _ a' => a'
  mass_eq := @fun _ _ _ _ _ _ _ => rfl
  moveProjT := fun m' => m'
  dimT_eq := fun _ => rfl
  assignOfT := @fun _ _ _ _ _ _ a' => a'
  massT_eq := @fun _ _ _ _ _ _ _ => rfl

@[simp] lemma idRefCore_histFib {n : ℕ} (S : StepSys n) {α : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ α) : (idRefinementCore S).histFib x = {⟨PUnit.unit, x⟩} := rfl

@[simp] lemma idRefCore_histFib_toList {n : ℕ} (S : StepSys n) {α : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ α) :
    ((idRefinementCore S).histFib x).toList = [⟨PUnit.unit, x⟩] :=
  Finset.toList_singleton _

@[simp] lemma idRefCore_cellEq_symm {n : ℕ} (S : StepSys n) (α : S.Cell) (b : PUnit) :
    (idRefinementCore S).cellEq.symm ⟨α, b⟩ = α := rfl

/-- the identity refinement's assign-cover: the `coverFn` is the evident
singleton-Σ bijection. -/
lemma idRef_assign_cover {n : ℕ} (S : StepSys n) {α β : S.Cell} (m : S.Move α β)
    (α' : S.Cell) (hα : ((idRefinementCore S).cellEq α').1 = α) {q₀ : ℚ}
    (x' : S.Hist q₀ α') (h : Hpt (S.dim m)) :
    Function.Bijective ((idRefinementCore S).coverFn m α' hα x' h) := by
  change α' = α at hα
  subst hα
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun a => ⟨β, rfl, m, rfl, assign_congrHpt m x' (castHpt_self _ h).symm a⟩, ?_, ?_⟩
  · rintro ⟨β', hβ, m', hm, a'⟩
    change β' = β at hβ; subst hβ
    change m' = m at hm; subst hm
    rfl
  · intro a
    rfl

/-- the identity refinement's terminal assign-cover. -/
lemma idRef_assign_coverT {n : ℕ} (S : StepSys n) {α : S.Cell} {v : VLabel n}
    (m : S.MoveT α v) (α' : S.Cell) (hα : ((idRefinementCore S).cellEq α').1 = α)
    {q₀ : ℚ} (x' : S.Hist q₀ α') (h : Hpt (S.dimT m)) :
    Function.Bijective ((idRefinementCore S).coverFnT m α' hα x' h) := by
  change α' = α at hα
  subst hα
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun a => ⟨m, rfl, assignT_congrHpt m x' (castHpt_self _ h).symm a⟩, ?_, ?_⟩
  · rintro ⟨m', hm, a'⟩
    change m' = m at hm; subst hm
    rfl
  · intro a
    rfl

/-- THE IDENTITY REFINEMENT (V4-13): the core plus the two partition covers. -/
noncomputable def idRefinement {n : ℕ} (S : StepSys n) : Refinement n S where
  toRefinementCore := idRefinementCore S
  assign_cover := idRef_assign_cover S
  assign_coverT := idRef_assign_coverT S

/-- a `Nodup` list all of whose elements equal `y` and which contains `y` is `[y]`. -/
private lemma nodup_all_eq_singleton {β : Type*} {l : List β} {y : β} (hnd : l.Nodup)
    (hall : ∀ b ∈ l, b = y) (hmem : y ∈ l) : l = [y] := by
  cases l with
  | nil => simp at hmem
  | cons b t =>
    have hby : b = y := hall b (by simp)
    cases t with
    | nil => rw [hby]
    | cons c t' =>
      have hcy : c = y := hall c (by simp)
      exact absurd ((hby.trans hcy.symm) ▸ (by simp : c ∈ c :: t'))
        (List.nodup_cons.mp hnd).1

/-- `filterMap` of `Finset.univ.toList` with a unique `some`-preimage is a singleton. -/
private lemma filterMap_univ_singleton {ι β : Type*} [Fintype ι] (g : ι → Option β)
    (x₀ : ι) (y : β) (hx₀ : g x₀ = some y)
    (huniq : ∀ x b, g x = some b → x = x₀ ∧ b = y) :
    (Finset.univ.toList).filterMap g = [y] := by
  refine nodup_all_eq_singleton ?_ ?_ ?_
  · refine List.Nodup.filterMap ?_ (Finset.nodup_toList _)
    intro a a' b hb hb'
    exact (huniq a b hb).1.trans (huniq a' b hb').1.symm
  · intro b hb
    obtain ⟨a, _, hab⟩ := List.mem_filterMap.mp hb
    exact (huniq a b hab).2
  · exact List.mem_filterMap.mpr ⟨x₀, Finset.mem_toList.mpr (Finset.mem_univ _), hx₀⟩

/-- singleton-roster reduction: at the identity refinement, the refined-template
roster over a coarse template `γ` is exactly `[⟨γ, rfl⟩]`. -/
lemma idRef_refTmpls {n : ℕ} (S : StepSys n) {α : S.Cell}
    (hα : ((idRefinementCore S).cellEq α).1 = α) (γ : Template n S α) :
    refTmpls (idRefinementCore S) α hα γ = [⟨γ, rfl⟩] := by
  letI iC : Fintype (idRefinementCore S).S'.Cell := (idRefinementCore S).S'.finC
  letI iM : ∀ (a b : (idRefinementCore S).S'.Cell), Fintype ((idRefinementCore S).S'.Move a b) :=
    (idRefinementCore S).S'.finM
  letI iMT : ∀ (a : (idRefinementCore S).S'.Cell) (v : VLabel n),
      Fintype ((idRefinementCore S).S'.MoveT a v) := (idRefinementCore S).S'.finMT
  induction γ with
  | @last a b m =>
    simp only [refTmpls]
    refine filterMap_univ_singleton _ ⟨_, m⟩ _ (dif_pos ⟨rfl, rfl⟩) ?_
    rintro ⟨xf, xs⟩ bb hgx
    split at hgx
    · rename_i hP
      obtain ⟨hβ, hcm⟩ := hP
      change xf = b at hβ; subst hβ
      change xs = m at hcm; subst hcm
      exact ⟨rfl, (Option.some.inj hgx).symm⟩
    · simp at hgx
  | @lastT a v m =>
    simp only [refTmpls]
    refine filterMap_univ_singleton (ι := (idRefinementCore S).S'.MoveT a v) _ m _ (dif_pos rfl) ?_
    intro x bb hgx
    split at hgx
    · rename_i hP
      change x = m at hP; subst hP
      exact ⟨rfl, (Option.some.inj hgx).symm⟩
    · simp at hgx
  | @cons a b m γ' ih =>
    simp only [refTmpls]
    have hfm : List.filterMap
        (fun p : (β' : (idRefinementCore S).S'.Cell) × (idRefinementCore S).S'.Move a β' =>
          if h : ∃ (hβ : ((idRefinementCore S).cellEq p.fst).fst = b),
              castMove hα hβ ((idRefinementCore S).moveProj p.snd) = m then
            some (⟨p, h⟩ : (p' : (β' : (idRefinementCore S).S'.Cell) ×
                (idRefinementCore S).S'.Move a β') ×'
              ∃ (hβ : ((idRefinementCore S).cellEq p'.fst).fst = b),
                castMove hα hβ ((idRefinementCore S).moveProj p'.snd) = m) else none)
        Finset.univ.toList = [⟨⟨b, m⟩, ⟨rfl, rfl⟩⟩] := by
      refine filterMap_univ_singleton _ ⟨b, m⟩ _ (dif_pos ⟨rfl, rfl⟩) ?_
      rintro ⟨xf, xs⟩ bb hgx
      split at hgx
      · rename_i hP
        obtain ⟨hβ, hcm⟩ := hP
        change xf = b at hβ; subst hβ
        change xs = m at hcm; subst hcm
        exact ⟨rfl, (Option.some.inj hgx).symm⟩
      · simp at hgx
    rw [hfm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ih, List.map_cons,
      List.map_nil]
    rfl

/-- the `idRefinement`-level `toRefinementCore` projection (defeq). -/
lemma idRef_toCore {n : ℕ} (S : StepSys n) :
    (idRefinement S).toRefinementCore = idRefinementCore S := rfl

/-- the `idRefinement`-level `histFib` fiber-list (singleton). -/
lemma idRef_histFib_toList {n : ℕ} (S : StepSys n) {α : S.Cell} {q₀ : ℚ}
    (x : S.Hist q₀ α) : ((idRefinement S).histFib x).toList = [⟨PUnit.unit, x⟩] :=
  Finset.toList_singleton _

/-- the `idRefinement`-level `cellEq.symm` projection (defeq). -/
lemma idRef_cellEq_symm {n : ℕ} (S : StepSys n) (α : S.Cell) (b : PUnit) :
    (idRefinement S).cellEq.symm ⟨α, b⟩ = α := rfl

/-- the singleton-roster reduction as it appears over the identity refinement's
`histFib` fiber — the whole `refTmpls` application rewrites to `[⟨γ, rfl⟩]`. -/
lemma idRef_refTmpls_symm {n : ℕ} (S : StepSys n) {α : S.Cell} (b : (idRefinement S).B α)
    (hα : ((idRefinement S).cellEq ((idRefinement S).cellEq.symm ⟨α, b⟩)).fst = α)
    (γ : Template n S α) :
    refTmpls (idRefinement S).toRefinementCore ((idRefinement S).cellEq.symm ⟨α, b⟩) hα γ
      = [⟨γ, rfl⟩] :=
  idRef_refTmpls S hα γ

/-- THE TRANSPORTED EVENTS over the identity refinement: `TE' := TE`,
`boxEq := Equiv.refl`.  The fiber-union covers (`tevt_cover`/`tinst_cover`)
collapse over the singleton fiber to the singleton-roster reduction of
`refTmpls` at the identity — the isolated `refTmpls`-reduction legs. -/
noncomputable def idRefEvents {n : ℕ} (S : StepSys n) (TE : TmplEvents n S) :
    RefEvents (idRefinement S) TE where
  TE' := TE
  boxEq := fun _ _ => Equiv.refl _
  tevt_cover := by
    intro α q₀ x γ h N _
    rw [idRef_histFib_toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      idRef_refTmpls_symm]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Equiv.coe_refl,
      Finset.image_id, Finset.union_empty]
    rfl
  tinst_cover := by
    intro α q₀ x γ h _
    rw [idRef_histFib_toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      idRef_refTmpls_symm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rfl

theorem hmcaug_of_hmc {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) (hHMC : HMC TE D) : HMCAug S TE :=
  ⟨idRefinement S, idRefEvents S TE, D, hHMC⟩

end LeanUrat.MovesV
