/-  MovesV unit V7-3a `tableShape_inst` (odata CONSTRUCTIBLE REV 5, Codex-2)
    — the `MovesS.TableShape n` instance from `CtsFamily`.  [E-PHASE FORM:
    theorem-under-data (Fintype/DecidableEq instance arguments explicit; the
    odata map's omem_size casts + route_eq clause are the ∃-bound content) —
    the full field-by-field construction is the prover's; MANIFEST
    deviations.] -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.V2_cells

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the block-e CTS state carrier. -/
def StateOf (n : ℕ) (e : ℕ) : Type :=
  {p : Σ s : Skeleton n, PUnit // skBlk p.1 = e}

theorem tableShape_inst {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      Nonempty (T.VType ≃ VLabel n) ∧
      ∀ e (τ : T.State e) (o : T.Out e τ), (T.odata e τ o).mem ≠ [] := by
  sorry

end LeanUrat.MovesV
