/-  MovesV unit V4-8 `part2_n3_zero` (PREMISE DISPLAYED C18) — at n = 3 the
    surplus vanishes IDENTICALLY, GIVEN DegCons + the displayed ContTwo
    premise.  [Gate-roster decide leg deferred with the omem-roster deviation.] -/
import LeanUrat.MovesV.V2_degcons

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the note's own argument premise: a CONTINUING cluster has size ≥ 2. -/
def ContTwo {n : ℕ} (T : MovesS.TableShape n) : Prop :=
  ∀ e (τ : T.State e) (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem,
    μ.continuing → 2 ≤ μ.size

/-- at n = 3: at most one continuing member per outcome (2 + 2 > 3). -/
theorem surplus_zero (T : MovesS.TableShape 3) (hDC : MovesS.DegCons T)
    (h2 : ContTwo T) (e : ℕ) (he : e ∈ Finset.Icc 1 3) (τ : T.State e)
    (o : T.Out e τ) :
    ((T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).length ≤ 1 := by
  have he3 : e ≤ 3 := (Finset.mem_Icc.mp he).2
  have hsum : ((T.odata e τ o).mem.map MovesS.Member.size).sum ≤ e :=
    hDC.size_sum e he τ o
  -- Every continuing member has size ≥ 2 (ContTwo); non-continuing members have
  -- size ≥ 0, so twice the number of continuing members bounds the total size sum.
  have key : ∀ (l : List (MovesS.Member T.VType T.State)),
      (∀ μ ∈ l, μ.status.isRight = true → 2 ≤ μ.size) →
      2 * (l.filter (fun μ => μ.status.isRight)).length
        ≤ (l.map MovesS.Member.size).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro hall
      have htail : ∀ μ ∈ t, μ.status.isRight = true → 2 ≤ μ.size :=
        fun μ hμ => hall μ (List.mem_cons_of_mem a hμ)
      have iht := ih htail
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hc : a.status.isRight = true
      · rw [if_pos hc, List.length_cons]
        have ha : 2 ≤ a.size := hall a List.mem_cons_self hc
        omega
      · rw [if_neg hc]
        omega
  have hcont : ∀ μ ∈ (T.odata e τ o).mem, μ.status.isRight = true → 2 ≤ μ.size :=
    fun μ hμ hr => h2 e τ o μ hμ hr
  have hkey := key (T.odata e τ o).mem hcont
  omega

end LeanUrat.MovesV
