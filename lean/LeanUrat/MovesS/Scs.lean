/-
Unit U-6 `scs` (medium) — kcol ⟹ all member sizes = e; PRODUCES the `hK` argument
of every Kmat consumer.  moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child
inherits the block size: e₁ = e".  sketch: hk + U-1 ⟹ m = 1; the only member is
selIdx, continuing (sel_continuing); cluster_child + U-5 + cluster_parent:
size = W′D′ = WD = e.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.Dispatch
import LeanUrat.MovesS.ScsStage

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem scs {T : TableShape n} (S : SCSData T) (hdc : DegCons T) {e : ℕ}
    (he : e ∈ Finset.Icc 1 n) {τ : T.State e} {o : T.Out e τ}
    (hk : routeOf (T.odata e τ o) = .kcol) :
    ∀ μ ∈ (T.odata e τ o).mem, μ.size = e := by
  -- hk + U-1: a kcol outcome has exactly one member (m = 1).
  have hm1 : (T.odata e τ o).m = 1 := by
    unfold routeOf at hk
    by_cases h1 : (T.odata e τ o).c = 0
    · rw [if_pos h1] at hk; exact absurd hk (by decide)
    · rw [if_neg h1] at hk
      by_cases h2 : (T.odata e τ o).m = 1
      · exact h2
      · rw [if_neg h2] at hk; exact absurd hk (by decide)
  have hlen : (T.odata e τ o).mem.length = 1 := hm1
  -- the single member is the selected one, which is continuing (SCS `sel_continuing`).
  have hcont : ((T.odata e τ o).mem.get (S.selIdx e τ o)).continuing :=
    S.sel_continuing e τ o hk
  -- its size is W′·D′ = W·D = e  (cluster_child + U-5 scs_stage + cluster_parent).
  have hsel : ((T.odata e τ o).mem.get (S.selIdx e τ o)).size = e := by
    rw [S.cluster_child e τ o (S.selIdx e τ o) hcont rfl, scs_stage S hm1,
      S.cluster_parent e τ o]
  -- every member equals the selected one, since the list has length one.
  intro μ hμ
  obtain ⟨i, hi⟩ := List.get_of_mem hμ
  have hidx : i = S.selIdx e τ o := by
    apply Fin.ext
    have hi' := i.isLt
    have hs' := (S.selIdx e τ o).isLt
    omega
  rw [← hi, hidx]
  exact hsel

end LeanUrat.MovesS
