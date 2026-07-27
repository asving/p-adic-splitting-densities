/-
Unit Sp.entranceDef [REV 2, F4 — EntranceShape (Defs) now carries the block-entry
selection (gsel, μsel) + height/depth parameter slots; the finiteness theorem
quantifies over EntranceShape itself] — moves_ref: "so it has ≤ 6n² letters
(SP-DAG(iii)); with SP-FIN the family of such words is finite and p-independent —
{ε} is finite up to its (height pair, depth) parameters, which is exactly the
finiteness CTS-M(iii) consumes".
deps: Sp.collapseWalk, Sp.collapseNeNil, Sp.dagWalk, Sp.dagWords. sketch: E.word
is a member-wise catalogued SuccStep chain (E.hMem, E.hChain); collapseRuns gives
a CollapsedWalk, so ≤ 6n² (dagWalk) and the image set sits inside the finite
collapsed-word set (dagWords). The parameters (heights, depths) are quantified
AWAY by the image construction — "up to its parameters", exactly.
difficulty: medium.
hypothesis_fields: the size-e-block / landing-cell β₀ IDENTIFICATION of the entry
datum is [1v] CTS-M(iii)'s (owner, cited); per-shape masses ι_{e,ε,β₀} and
entrance counts are [1]/[1v] objects, never assigned here.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem entrance_collapsed_finite (n gsel μsel : ℕ) (hn : 1 ≤ n) :
    {l : List Species | ∃ E : EntranceShape n gsel μsel,
      collapseRuns E.word = l}.Finite := sorry

theorem entrance_collapsed_len {n gsel μsel : ℕ} (hn : 1 ≤ n)
    (E : EntranceShape n gsel μsel) :
    (collapseRuns E.word).length ≤ 6 * n ^ 2 := sorry

end LeanUrat.MovesSp
