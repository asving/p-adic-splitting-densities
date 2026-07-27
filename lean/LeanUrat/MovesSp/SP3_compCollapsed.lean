/-
Unit Sp.compCollapsed [REV 4, Codex-1 — Branch/len tied to SP-DAG as a
CONCLUSION: real, non-vacuous content over the interface] — moves_ref: "the
collapsed LETTER length of a walk (the number of letters after collapsing
self-loop runs) IS bounded — Lemma SP-DAG (SP.4): … every collapsed walk has
≤ 6n² letters. SCOPE OF THAT BOUND …: it bounds letter ALTERNATIONS only. The
number of READS stays unbounded".
deps: Sp.compMember, Sp.collapseWalk, Sp.dagWalk. sketch: the length-m read
prefix is a member-wise catalogued SuccStep chain; collapseRuns gives a
CollapsedWalk; dagWalk bounds it. NOTE the fence, kept: m (the READ count) is
NOT bounded — only the collapsed image is. difficulty: medium (easy-medium).
hypothesis_fields: the standing group-F list (see SP3_compMember.lean).
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP3_compMember    -- dep Sp.compMember: SP_COMP (InCatalogue)
import LeanUrat.MovesSp.SP3_collapseWalk  -- dep Sp.collapseWalk: collapseRuns_collapsedWalk
import LeanUrat.MovesSp.SP4_dagWalk       -- dep Sp.dagWalk: SP_DAG_walk (≤ 6n²)

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem SP_COMP_collapsed (n p : ℕ) (hn : 1 ≤ n) [Fact p.Prime]
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (M : CanTreeModel n p f) (η : M.Branch) (m : ℕ) (hm : (m : ℕ∞) ≤ M.len η) :
    (collapseRuns ((List.range m).map (M.datum η))).length ≤ 6 * n ^ 2 := by
  -- The length-`m` read prefix, as a list of retained data.
  -- (1) Every letter of the prefix is a catalogue member (compMember, SP_COMP).
  have hmem : ∀ s ∈ (List.range m).map (M.datum η), InCatalogue n s := by
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    rw [List.mem_range] at hr
    have hlt : (r : ℕ∞) < M.len η := lt_of_lt_of_le (by exact_mod_cast hr) hm
    exact SP_COMP n p f hf hdeg M η r hlt
  -- (2) Consecutive reads are SuccStep-linked: StageLaws (hStage) + Coherent∧Budget
  -- (hCoh) assembled per read pair — the member-wise catalogued SuccStep chain.
  have hch : ((List.range m).map (M.datum η)).IsChain (SuccStep n) := by
    rw [List.isChain_iff_getElem]
    intro i h
    simp only [List.length_map, List.length_range] at h
    simp only [List.getElem_map, List.getElem_range]
    have hlt : ((i + 1 : ℕ) : ℕ∞) < M.len η :=
      lt_of_lt_of_le (by exact_mod_cast h) hm
    have hcohbud := M.hCoh η (i + 1) (by exact_mod_cast hlt)
    exact ⟨M.hStage η i (by exact_mod_cast hlt), hcohbud.1, hcohbud.2⟩
  -- (3) collapseRuns of that chain is a CollapsedWalk; dagWalk bounds it by 6n².
  exact SP_DAG_walk hn (collapseRuns_collapsedWalk hmem hch)

end LeanUrat.MovesSp
