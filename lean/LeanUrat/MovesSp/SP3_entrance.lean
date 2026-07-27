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
import LeanUrat.MovesSp.SP3_collapseWalk   -- dep Sp.collapseWalk: collapseRuns_collapsedWalk
import LeanUrat.MovesSp.SP4_dagWalk        -- dep Sp.dagWalk: SP_DAG_walk (length ≤ 6n²)
import LeanUrat.MovesSp.SP4_dagWords       -- dep Sp.dagWords: SP_DAG_words (finite collapsed-word set)

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- The image set of `collapseRuns` over all entrance shapes is finite: every such
collapsed word is a `CollapsedWalk` (E.word is a member-wise catalogued `SuccStep`
chain, so `collapseRuns_collapsedWalk` applies), hence the image sits inside the
finite collapsed-word set `SP_DAG_words`. The height/depth parameters are quantified
away by the image construction — "up to its parameters". -/
theorem entrance_collapsed_finite (n gsel μsel : ℕ) (hn : 1 ≤ n) :
    {l : List Species | ∃ E : EntranceShape n gsel μsel,
      collapseRuns E.word = l}.Finite := by
  apply Set.Finite.subset (SP_DAG_words n hn).1
  rintro l ⟨E, rfl⟩
  exact collapseRuns_collapsedWalk E.hMem E.hChain

/-- Each collapsed entrance word has ≤ 6n² letters: `collapseRuns E.word` is a
`CollapsedWalk` (`collapseRuns_collapsedWalk` on E.hMem/E.hChain), and every
collapsed walk visits pairwise-distinct ranks, so `SP_DAG_walk` bounds its length. -/
theorem entrance_collapsed_len {n gsel μsel : ℕ} (hn : 1 ≤ n)
    (E : EntranceShape n gsel μsel) :
    (collapseRuns E.word).length ≤ 6 * n ^ 2 :=
  SP_DAG_walk hn (collapseRuns_collapsedWalk E.hMem E.hChain)

end LeanUrat.MovesSp
