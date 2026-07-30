/-
Unit E9.encIdx_inj  (MovesD campaign, E-phase)
moves_ref: "The map enc′: η ⟼ (the side-digit tuples (d_j) of its reads; the selection
indices (s_r)) is an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r})" (L11 — now a
THEOREM at the η-class granularity).  [REV 9: rev-6's hnorm rider REMOVED as unused
(Fable#7/coordinator) — the injection is hypothesis-free.]
[REV 8, Codex#6 c.3 — the ∅ dispatch]: `encTargetP_empty` — L11's encoding at P̂ = ∅ is
the SINGLETON-TO-UNIT map (Pref(∅) = {∅}, target = the empty product, card 1 = C_∅).
deps: E1, E3, E4, E7, E8; Defs (Matches.hmonic, encIdx).
sketch: classes are (digit-tuple, ψ-image) sequences; the d_r counted digits + the scoped
monic tie (§0.5) recover the FULL digit tuple; the digit tuple determines RanchImage
(hRanch, coefficient images); E8 recovers ψImage from the rank. So encIdx equal ⟹
etaData equal ⟹ i = j (subtype ext).  difficulty: medium-hard.
hypothesis_fields: none [REV 9 — hnorm removed as unused].
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.E1_digitPool
import LeanUrat.MovesD.E7_rankLt
import LeanUrat.MovesD.E8_rankInj

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- `RanchImage` read off the side digits: `R_anch = Σ_{k ≤ ℓ} sideDigit(k)·X^k`
(the F-image of `hRanch`, `pat` embedded to `sideDigit`). -/
private lemma ranchImage_eq_sum {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) :
    RanchImage ν = ∑ k ∈ Finset.range (ν.wSide / ν.e + 1),
      Polynomial.C (ν.sideDigit k) * Polynomial.X ^ k := by
  unfold RanchImage
  rw [ν.hRanch, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rfl

/-- L11's injection, at the η-class granularity — hypothesis-free. -/
theorem encIdx_inj :
    Function.Injective (encIdx : PrefIdx n pol P → EncTargetP p F (P : ShapePrefix)) := by
  -- pool-projection is injective on genuine pool members
  have hpp : ∀ (w : ℕ) (x y : F), x ∈ pool p w F → y ∈ pool p w F →
      poolProj p w F x = poolProj p w F y → x = y := by
    intro w x y hx hy h
    simp only [poolProj] at h
    rw [dif_pos hx, dif_pos hy] at h
    exact Subtype.ext_iff.mp h
  intro i j hEq
  apply Subtype.ext
  rw [← i.2.choose_spec.2, ← j.2.choose_spec.2]
  show etaData (P : ShapePrefix) (reprOf i) = etaData (P : ShapePrefix) (reprOf j)
  have hi_mem : reprOf i ∈ PrefSet n pol P := i.2.choose_spec.1
  have hj_mem : reprOf j ∈ PrefSet n pol P := j.2.choose_spec.1
  obtain ⟨hleni, hmi⟩ := hi_mem.1
  obtain ⟨hlenj, hmj⟩ := hj_mem.1
  funext r
  have hri : (r : ℕ) < (reprOf i).nodes.length := by rw [hleni]; exact r.2
  have hrj : (r : ℕ) < (reprOf j).nodes.length := by rw [hlenj]; exact r.2
  set νi := (reprOf i).nodes[(r : ℕ)]'hri with hνi
  set νj := (reprOf j).nodes[(r : ℕ)]'hrj with hνj
  have hsi : (reprOf i).nodes[(r : ℕ)]? = some νi := List.getElem?_eq_getElem hri
  have hsj : (reprOf j).nodes[(r : ℕ)]? = some νj := List.getElem?_eq_getElem hrj
  set R := (P : ShapePrefix).reads.get r with hRDef
  have hMi : R.Matches νi := hmi (r : ℕ) hri
  have hMj : R.Matches νj := hmj (r : ℕ) hrj
  have hMi2 := hMi
  have hMj2 := hMj
  obtain ⟨-, hei, -, hgi, hμi, -, -, hwsi, -, -, -, -, htiei⟩ := hMi2
  obtain ⟨-, hej, -, hgj, hμj, -, -, hwsj, -, -, -, -, htiej⟩ := hMj2
  have hleni' : νi.wSide / νi.e = R.len := by
    simp only [ShapeRead.len]; rw [hwsi, hei]
  have hlenj' : νj.wSide / νj.e = R.len := by
    simp only [ShapeRead.len]; rw [hwsj, hej]
  -- side-digit agreement on positions 0..ℓ
  have hdig : ∀ m : ℕ, m ≤ R.len → νi.sideDigit m = νj.sideDigit m := by
    intro m hm
    by_cases hmd : m < R.d
    · have key : poolProj p R.w F (νi.sideDigit m) = poolProj p R.w F (νj.sideDigit m) := by
        simpa only [encIdx, hsi, hsj, Option.elim_some] using
          congrFun (congrArg Prod.fst (congrFun hEq r)) ⟨m, hmd⟩
      exact hpp R.w _ _ (digit_in_pool hMi m) (digit_in_pool hMj m) key
    · have hmono : R.monicTop = true := by
        cases hb : R.monicTop with
        | true => rfl
        | false =>
            exfalso
            have hd1 : R.d = R.len + 1 := by simp [ShapeRead.d, hb]
            omega
      have hdlen : R.d = R.len := by simp [ShapeRead.d, hmono]
      have hmeq : m = R.len := by omega
      rw [hmeq, htiei hmono, htiej hmono]
  -- selection-rank agreement
  have hsel : selRank R.w νi = selRank R.w νj := by
    have h2 : selRank R.w νi % R.mbar = selRank R.w νj % R.mbar := by
      simpa only [encIdx, hsi, hsj, Option.elim_some] using
        congrArg Fin.val (congrArg Prod.snd (congrFun hEq r))
    rwa [Nat.mod_eq_of_lt (selRank_lt hMi), Nat.mod_eq_of_lt (selRank_lt hMj)] at h2
  -- ψ-image agreement via E8
  have hψ : ψImage νi = ψImage νj := by
    refine rank_inj hMi hMj ?_ ?_ ?_ hsel
    · rw [hgi, hgj]
    · rw [hμi, hμj]
    · rw [ranchImage_eq_sum, ranchImage_eq_sum, hleni', hlenj']
      apply Finset.sum_congr rfl
      intro m hm
      rw [hdig m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
  -- assemble the two η-tuples
  refine Prod.ext ?_ ?_
  · funext k
    simp only [etaData, hsi, hsj, Option.elim_some]
    exact hdig (↑k) (Nat.lt_succ_iff.mp k.2)
  · funext k
    simp only [etaData, hsi, hsj, Option.elim_some]
    have hce : (ψImage νi).coeff (↑k : ℕ) = (ψImage νj).coeff (↑k : ℕ) := by rw [hψ]
    rw [ψImage, ψImage, Polynomial.coeff_map, Polynomial.coeff_map] at hce
    exact hce

/-- The ∅ dispatch: at P̂ = ∅ the encoding target is the empty product — card 1 = C_∅. -/
theorem encTargetP_empty (hP : (P : ShapePrefix).reads = []) :
    Nat.card (EncTargetP p F (P : ShapePrefix)) = 1 := by
  have h0 : (P : ShapePrefix).reads.length = 0 := by rw [hP]; rfl
  haveI hemp : IsEmpty (Fin ((P : ShapePrefix).reads.length)) := by
    rw [h0]; exact Fin.isEmpty'
  haveI : Unique (EncTargetP p F (P : ShapePrefix)) := by
    unfold EncTargetP; exact Pi.uniqueOfIsEmpty _
  exact Nat.card_unique

end LeanUrat.MovesD
