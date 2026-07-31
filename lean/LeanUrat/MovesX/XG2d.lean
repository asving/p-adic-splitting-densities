/-
Unit XG.2d treeFinite — X.3(a) pointwise, DERIVED (replaces the deleted
`stratumLink`/`infBranch` fields)  [PROVED, fleet 2026-07-28]
moves_ref: "Off {disc f = 0} …, EITHER route gives every branch finite pointwise, by
the four-population decomposition … Hence a.e. f has a FINITE tree".
sketch: an infinite path g (¬Finite via XG.2's contrapositive) gives hist (g k) of
length k (parent_hist induction), each a stratum of f (`X.gmnLink`) with HistWF (`wf`);
dTotal ≥ k − 1 (termLast) contradicts XG.1's bound at large k.
deps: XG.1, XG.2. difficulty: HARD (MEDIUM-HARD band).
hyp_fields: X3aRouteP; gmnLink/wf (context inputs).
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XG1
import LeanUrat.MovesX.XG2

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Generic list fact: if every element except possibly the last satisfies a boolean
predicate `P` (the `HistWF.termLast` shape), then at most one element fails `P`, so the
list is no longer than its `P`-filtered sublist plus one. Proof: `H.dropLast`
consists entirely of `P`-nodes, so filtering fixes it, and it is a sublist of the
filter of `H`; length monotonicity of sublists gives `|H| − 1 ≤ |filter P H|`. -/
/- [SYN2-S1 SWEEP-6, 2026-07-31] private len_le_filter_succ + length_le_dTotal_succ
DELETED — survivor = MovesX/Defs.length_le_dTotal_succ (XD2's raw-hypothesis form);
the use below re-pointed through `.termLast`. -/

theorem treeFinite {n : ℕ} (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : MonicBox n p) (hd : f ∉ discZero n p) :
    Finite ((X.ctx p).Branch f) := by
  set C := X.ctx p with hC
  -- König (XG.2): finiteness of the branch type follows from the ABSENCE of an
  -- infinite root-descending path.  Assume such a path `g` and derive a contradiction.
  apply koenigFinite C f
  rintro ⟨g, g0, gstep⟩
  -- Each history `hist (g k)` has length exactly `k` (root is empty; `parent_hist`
  -- appends one node per step).
  have hlen : ∀ k, (C.hist (g k)).length = k := by
    intro k
    induction k with
    | zero => rw [g0, C.hist_root]; rfl
    | succ m ih =>
        obtain ⟨ν, hν⟩ := C.parent_hist (g (m + 1)) (g m) (gstep m)
        rw [hν, List.length_append, ih]; rfl
  -- XG.1's bound is a constant `M` in `k`; but `dTotal (hist (g k)) ≥ k − 1` forces
  -- `2 * k ≤ M + 2` for every `k`, which is impossible.
  set M := (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n with hM
  have key : ∀ k, 2 * k ≤ M + 2 := by
    intro k
    have hb1 : 2 * dTotal (C.hist (g k)) ≤ M :=
      branchLenBound X K R p f (C.hist (g k)) (X.gmnLink p f (g k)) hd (C.wf (g k)) hn
    have hb2 : (C.hist (g k)).length ≤ dTotal (C.hist (g k)) + 1 :=
      length_le_dTotal_succ (C.hist (g k)) (C.wf (g k)).termLast
    have hl := hlen k
    omega
  have := key (M + 2)
  omega

end LeanUrat.MovesX
