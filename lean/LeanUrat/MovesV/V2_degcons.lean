/-  MovesV unit V2-9 `deg_cons_gate` — DEG-CONS at the computed rosters.
    [E-PHASE NOTE: the gate omem list literals are deferred with DefsGate's
    roster deviation; the SHAPE lemma producing `MovesS.DegCons` (V7-3b's
    consumer) is landed and PROVED.] -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the shape lemma: a per-member-positive, size-bounded roster produces
`MovesS.DegCons` (Member.size = OMember.size under V7-3a's odata map). -/
theorem degcons_of_roster {n : ℕ} (T : MovesS.TableShape n)
    (hpos : ∀ e (τ : T.State e) (o : T.Out e τ),
      ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size)
    (hsum : ∀ e ∈ Finset.Icc 1 n, ∀ (τ : T.State e) (o : T.Out e τ),
      ((T.odata e τ o).mem.map MovesS.Member.size).sum ≤ e) :
    MovesS.DegCons T :=
  ⟨hpos, hsum⟩

end LeanUrat.MovesV
