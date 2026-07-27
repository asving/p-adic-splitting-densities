/-
Unit XG.2d treeFinite — X.3(a) pointwise, DERIVED (replaces the deleted
`stratumLink`/`infBranch` fields)  [E-phase: stated, body sorry]
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
private lemma len_le_filter_succ {α : Type*} (H : List α) (P : α → Bool)
    (hlast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → P (H.get i) = true) :
    H.length ≤ (H.filter P).length + 1 := by
  have hself : (H.dropLast).filter P = H.dropLast := by
    apply List.filter_eq_self.mpr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, hget⟩ := hx
    have hi' : i < H.length := by rw [List.length_dropLast] at hi; omega
    have hgd : H.dropLast[i] = H[i]'hi' := List.getElem_dropLast hi
    have hbnd : (i : ℕ) + 1 < H.length := by rw [List.length_dropLast] at hi; omega
    have hc : P (H[i]'hi') = true := by
      have := hlast ⟨i, hi'⟩ hbnd
      simpa [List.get_eq_getElem] using this
    rw [← hget, hgd]; exact hc
  have hsub : List.Sublist ((H.dropLast).filter P) (H.filter P) :=
    (List.dropLast_sublist H).filter P
  have hle : ((H.dropLast).filter P).length ≤ (H.filter P).length := hsub.length_le
  rw [hself, List.length_dropLast] at hle
  omega

/-- A well-formed history has at most one non-`continuing` (terminal) node — its last —
so its total length exceeds the count of continuing nodes (`dTotal`) by at most one. -/
private lemma length_le_dTotal_succ {n : ℕ} (H : XHistory n) (W : HistWF n H) :
    H.length ≤ dTotal H + 1 :=
  len_le_filter_succ H (·.continuing) W.termLast

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
      length_le_dTotal_succ (C.hist (g k)) (C.wf (g k))
    have hl := hlen k
    omega
  have := key (M + 2)
  omega

end LeanUrat.MovesX
