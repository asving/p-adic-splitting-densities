/-
H7 FORGE — the first NON-VACUOUS compiled (H7) instance (synthesis-7 queue #8;
pass-7 F4; charter `docs/SYNTHESIS_PASS7_2026-08-08.md` + OL-2 inhabitant spec of
`lean/notes/openmath/H7PROBE_2026-08-08.md` P-4).

# What this file builds

A hand-built, SORRY-FREE `MovesT.TreeModel` + `CellData` + `VTree` + `SiteLedger`
(`forgeModel`/`forgeCA`/`forgeTree`/`forgeLedger`) meeting the OL-2 inhabitant spec,
breaking BOTH P-2 rfl-degeneracies of the G1 toys:

* **non-diagonal `branchCellOf`** — sibling branch nodes at the SAME `.red` entrance
  key genuinely different read maps (branch a reads the box digit x2, branch b reads
  x3, the joint site reads both).  Certified three ways: the read maps differ at a
  point (`forge_read_nondiagonal`), the sibling STATE EVENTS cross-cut — nonempty
  overlap AND unequal (`forge_states_crosscut`) — and NO single-map read of ANY cell
  type can present both sibling states over the shared entrance
  (`forge_no_diagonal_read`, the structural P-2(a) breaker: under a diagonal read,
  sibling state events are fibers of one map, hence equal or disjoint).
* **sides = 2 at a genuine multi-side site** — the joint site `fHj` carries
  `sides = 2` with a REAL `SideSplit` (`forgeSplitGen`): a 2-clause fresh system
  partitioned over disjoint side spans {2}/{3}, strictly monotone hull slopes 1 < 2,
  and `hside_read` tying the roster nodes' RECORDED slopes (toyHead: slope 1,
  fNodeB0: slope 2) to the hull sides.  The split legs `splitAt`/`hsplit_k`/
  `hsplit_exp` are DISCHARGED (not omega-absurd).  The (JC-multi) price is DECIDED:
  `forge_jcmulti` (1 · 2² = 4).

The five realized sites are ONE-NODE chains sharing the `.red` window entrance
(the S6 shape of N-H7-1 at the cheapest compiled scale: p = 2, m(roster) = 2,
side-separated slopes 1 vs 2 mirroring S6's mixed-degree pair (x−3)(x²−3) with
slopes 1 vs 1/2 at p = 3): branch a = {[toyHead], [sibNode2]} (read digit x2),
branch b = {[fNodeB0], [fNodeB1]} (read digit x3), joint = [fNodeJ] (reads both).

# The pin-corrected (H7) faces, DECIDED at the instance (N-H7-1's two measured pins)

* **PIN 1 (ε keys by REALIZED SLOPE — the slope-pooled form is refuted).**
  `forge_kloc_slope_keyed` PROVES the K-LOC §1.1(ii)-shaped transport with the
  normalization keyed by the branch's recorded slope (`slopeEps ν.line.slope`);
  `forge_kloc_pooled_refuted` is the COMPILED COUNTERMODEL to the slope-pooled
  strengthening at this very instance — the compiled twin of N-H7-1's S5 pooled-u
  refutation.
* **PIN 2 (decide-small semantic gates sit INSIDE the D-8 guard).**
  `forgeDatum : SiteDatum 2 2 2` carries the instance integers (m = 2, thr = 1,
  ρ = 0, Σ-count 4, branch counts 2·2); `forge_guard : InGuard forgeDatum`
  (1 + 2·0 ≤ 2) is the compiled guard fact, and the decide-small semantic count
  gates (`forge_klocCounts` — the FIRST contentful `KLocCounts` instantiation:
  Events := the site's realized joint read words, counts := box cardinalities;
  `forge_stratum_count`, `forge_branch_counts`) are stated ONLY at this in-guard
  site ((N, τ, e_max) = (2, 1, 0): N − e_max = 2 ≥ 1 = τ).  Per pin 2 no such gate
  is stated below the guard (the out-of-guard extraction failure is numeric-tier —
  N-H7-1 P-E — displayed, not compiled).

# Honesty displays (what this instance is NOT)

* The model is DEPTH-1: all realized chains are one-node.  The multi-side site's
  roster nodes are realized as SIBLING chains of the same window entrance, but its
  own deeper CONTINUATIONS are not realized — realizing them requires coherent
  2-node histories (`HistoryCoherent`'s transition legs), i.e. the HK23/HK25
  transplant (those gates prove such histories exist over F4); that is the named
  residual, out of this unit's scope.  `NsHalts` therefore holds at every site.
* The node literals are synthetic-but-lawful `Node` instances (the G1/S2 toy
  genre); the box-digit read tables (x2/x3) are the forge's own keying, NOT derived
  from an engine run.  Engine-tied semantics (`ITauSemantic`/`KLocSemantic` at
  `siteCellEvent` over the pinned canonical models) remain the Tier-M obligation
  H7-W3a; within a branch the two read values are center-distinguished node
  literals (the S2 `sibNode2` genre).  Nothing here discharges (H7); this file
  supplies the first non-vacuous compiled DECISION POINT for its statement shapes.
* `ITauShadow forgeDatum` (Tier-S interface fit, H7-D1b genre) is NOT attempted
  here — the blueprint's own warning says the shadow row is never evidence; the
  decided faces above carry the semantic content of this unit.

Unit record: `lean/notes/openmath/H7FORGE_2026-08-08.md`.  New declarations only;
imports reuse S2_sibFalse's sorry-free node/history/laws layer (t1/t2/laws_t1/
laws_t2/canonRoot_toyHead) and G1's node literals — no sorried declaration
(toyModel/toyCA/toyLedgerA/...) is consumed; in-file `#print axioms` census at EOF.
-/
import Mathlib
import LeanUrat.MovesT.S2_sibFalse
import LeanUrat.Scaffold.HDischarge.H7.Rows

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H7

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open Classical

/-! ### §N — the five root-window node literals (branch a: slope 1 ×2 read values;
branch b: slope 2 ×2 read values; joint: slope 3).  Branch-a nodes REUSED from
G1/S2 (`toyHead`, `sibNode2` — both sorry-free); branch-b and joint nodes are
root-species clones of `toyLeafA`/`toyLeafB` (species-law fields re-supplied,
everything else verbatim — all node laws copy). -/

/-- branch b, read value 0: `toyLeafA` (slope-2 line ⟨4,2⟩, h = 2) as a ROOT read. -/
noncomputable def fNodeB0 : Node 2 (ZMod 2) :=
  { toyLeafA with
    species := ReadSpecies.root
    hspecInc := fun h => ReadSpecies.noConfusion h
    hspecRec := fun h => ReadSpecies.noConfusion h
    hspecRecCenter := fun h => ReadSpecies.noConfusion h }

/-- branch b, read value 1: `fNodeB0` at the other center (the S2 `sibNode2`
center-distinction genre — no node law reads `center` at a root read). -/
noncomputable def fNodeB1 : Node 2 (ZMod 2) :=
  { fNodeB0 with
    center := (0 : ↥fNodeB0.σ.K)
    hspecRecCenter := fun h => ReadSpecies.noConfusion h }

/-- the JOINT (multi-side) site's own read node: `toyLeafB` (slope-3 line ⟨6,3⟩,
h = 3) as a ROOT read. -/
noncomputable def fNodeJ : Node 2 (ZMod 2) :=
  { toyLeafB with
    species := ReadSpecies.root
    hspecInc := fun h => ReadSpecies.noConfusion h
    hspecRec := fun h => ReadSpecies.noConfusion h
    hspecRecCenter := fun h => ReadSpecies.noConfusion h }

lemma fNodeB0_root : ChildRoot none fNodeB0 := rfl
lemma fNodeB1_root : ChildRoot none fNodeB1 := rfl
lemma fNodeJ_root : ChildRoot none fNodeJ := rfl

/-! node distinctness (h-field across branches, center within branch b). -/

lemma toyHead_ne_fNodeB0 : toyHead ≠ fNodeB0 := fun h => by
  have h2 : (1 : ℕ) = 2 := congrArg Node.h h
  omega

lemma toyHead_ne_fNodeB1 : toyHead ≠ fNodeB1 := fun h => by
  have h2 : (1 : ℕ) = 2 := congrArg Node.h h
  omega

lemma toyHead_ne_fNodeJ : toyHead ≠ fNodeJ := fun h => by
  have h2 : (1 : ℕ) = 3 := congrArg Node.h h
  omega

lemma sibNode2_ne_fNodeB0 : sibNode2 ≠ fNodeB0 := fun h => by
  have h2 : (1 : ℕ) = 2 := congrArg Node.h h
  omega

lemma sibNode2_ne_fNodeB1 : sibNode2 ≠ fNodeB1 := fun h => by
  have h2 : (1 : ℕ) = 2 := congrArg Node.h h
  omega

lemma sibNode2_ne_fNodeJ : sibNode2 ≠ fNodeJ := fun h => by
  have h2 : (1 : ℕ) = 3 := congrArg Node.h h
  omega

lemma fNodeB0_ne_fNodeB1 : fNodeB0 ≠ fNodeB1 := fun h => by
  have hc := congrArg (fun n : Node 2 (ZMod 2) => n.σ.K.subtype n.center) h
  simp only [show fNodeB1.center = (0 : ↥fNodeB1.σ.K) from rfl,
    show fNodeB0.center = (1 : ↥fNodeB0.σ.K) from rfl, map_zero, map_one] at hc
  exact one_ne_zero hc

lemma fNodeB0_ne_fNodeJ : fNodeB0 ≠ fNodeJ := fun h => by
  have h2 : (2 : ℕ) = 3 := congrArg Node.h h
  omega

lemma fNodeB1_ne_fNodeJ : fNodeB1 ≠ fNodeJ := fun h => by
  have h2 : (2 : ℕ) = 3 := congrArg Node.h h
  omega

/-! read-dispatch negations (for the `fRead` if-chain). -/

lemma fNodeB0_ne_toyHead : fNodeB0 ≠ toyHead := fun h => toyHead_ne_fNodeB0 h.symm

lemma fNodeB0_notA : ¬ (fNodeB0 = toyHead ∨ fNodeB0 = sibNode2) := fun h =>
  h.elim (fun h1 => toyHead_ne_fNodeB0 h1.symm) (fun h1 => sibNode2_ne_fNodeB0 h1.symm)

lemma fNodeB1_notA : ¬ (fNodeB1 = toyHead ∨ fNodeB1 = sibNode2) := fun h =>
  h.elim (fun h1 => toyHead_ne_fNodeB1 h1.symm) (fun h1 => sibNode2_ne_fNodeB1 h1.symm)

lemma fNodeJ_notA : ¬ (fNodeJ = toyHead ∨ fNodeJ = sibNode2) := fun h =>
  h.elim (fun h1 => toyHead_ne_fNodeJ h1.symm) (fun h1 => sibNode2_ne_fNodeJ h1.symm)

lemma fNodeJ_notB : ¬ (fNodeJ = fNodeB0 ∨ fNodeJ = fNodeB1) := fun h =>
  h.elim (fun h1 => fNodeB0_ne_fNodeJ h1.symm) (fun h1 => fNodeB1_ne_fNodeJ h1.symm)

/-! ### §H — the five one-node chains.  `t1`/`t2` (branch a) REUSED from S2. -/

noncomputable def fHb0 : History 2 (ZMod 2) := oneNode fNodeB0 fNodeB0_root
noncomputable def fHb1 : History 2 (ZMod 2) := oneNode fNodeB1 fNodeB1_root
noncomputable def fHj : History 2 (ZMod 2) := oneNode fNodeJ fNodeJ_root

private lemma histext {H H' : History 2 (ZMod 2)} (h : H.nodes = H'.nodes) : H = H' := by
  obtain ⟨n1, _, _⟩ := H; obtain ⟨n2, _, _⟩ := H'; cases h; rfl

lemma fHb0_nodes : fHb0.nodes = [fNodeB0] := rfl
lemma fHb1_nodes : fHb1.nodes = [fNodeB1] := rfl
lemma fHj_nodes : fHj.nodes = [fNodeJ] := rfl

private lemma one_ne_of_node {ν ν' : Node 2 (ZMod 2)} {H H' : History 2 (ZMod 2)}
    (hH : H.nodes = [ν]) (hH' : H'.nodes = [ν']) (hν : ν ≠ ν') : H ≠ H' := fun h => by
  apply hν
  have h2 : ([ν] : List (Node 2 (ZMod 2))) = [ν'] := by rw [← hH, ← hH', h]
  simpa using h2

lemma t1_ne_fHb0 : t1 ≠ fHb0 := one_ne_of_node t1_nodes fHb0_nodes toyHead_ne_fNodeB0
lemma t1_ne_fHb1 : t1 ≠ fHb1 := one_ne_of_node t1_nodes fHb1_nodes toyHead_ne_fNodeB1
lemma t1_ne_fHj : t1 ≠ fHj := one_ne_of_node t1_nodes fHj_nodes toyHead_ne_fNodeJ
lemma t2_ne_fHb0 : t2 ≠ fHb0 := one_ne_of_node t2_nodes fHb0_nodes sibNode2_ne_fNodeB0
lemma t2_ne_fHb1 : t2 ≠ fHb1 := one_ne_of_node t2_nodes fHb1_nodes sibNode2_ne_fNodeB1
lemma t2_ne_fHj : t2 ≠ fHj := one_ne_of_node t2_nodes fHj_nodes sibNode2_ne_fNodeJ
lemma fHb0_ne_fHb1 : fHb0 ≠ fHb1 := one_ne_of_node fHb0_nodes fHb1_nodes fNodeB0_ne_fNodeB1
lemma fHb0_ne_fHj : fHb0 ≠ fHj := one_ne_of_node fHb0_nodes fHj_nodes fNodeB0_ne_fNodeJ
lemma fHb1_ne_fHj : fHb1 ≠ fHj := one_ne_of_node fHb1_nodes fHj_nodes fNodeB1_ne_fNodeJ

/-! ### §Laws — the one-node `mem_realizable` payloads for the three NEW chains
(S2 `laws_t1`/`laws_t2` pattern; `Realizable` and the chain clauses are vacuous at
length 1, so the content is the three per-node coherence clauses + canonicity). -/

lemma canonRoot_fNodeB0 : canonRoot fNodeB0 = ((fNodeB0.zbar : (ZMod 2)ˣ) : ZMod 2) := by
  have e1 : canonRoot fNodeB0 = canonRoot toyHead := by unfold canonRoot ψImage; rfl
  rw [e1]; exact canonRoot_toyHead

lemma canonRoot_fNodeB1 : canonRoot fNodeB1 = ((fNodeB1.zbar : (ZMod 2)ˣ) : ZMod 2) := by
  have e1 : canonRoot fNodeB1 = canonRoot toyHead := by unfold canonRoot ψImage; rfl
  rw [e1]; exact canonRoot_toyHead

lemma canonRoot_fNodeJ : canonRoot fNodeJ = ((fNodeJ.zbar : (ZMod 2)ˣ) : ZMod 2) := by
  have e1 : canonRoot fNodeJ = canonRoot toyHead := by unfold canonRoot ψImage; rfl
  rw [e1]; exact canonRoot_toyHead

private lemma laws_one_node (ν : Node 2 (ZMod 2)) (H : History 2 (ZMod 2))
    (hn : H.nodes = [ν])
    (hΦ : ν.σ.Φ.natDegree = 1)
    (hslope : ν.line.slope * ((ν.e : ℚ) * (1 : ℚ) * (ν.Dwidth : ℚ)) = (ν.h : ℚ))
    (hgam : ((ν.gam : ℤ) : ℚ)
      = (ν.e : ℚ) * ((1 : ℚ) * ν.ustar) + (((ν.s0 + ν.wSide) : ℕ) : ℚ) * (ν.h : ℚ))
    (hlift : ν.lift = polTriv.liftOf ν)
    (hzbar : ((ν.zbar : (ZMod 2)ˣ) : ZMod 2) = canonRoot ν) :
    HistoryCoherent H ∧ Realizable H ∧ polTriv.IsCanonPres H := by
  have hsf : H.strFrame 0 = 1 := by simp [History.strFrame]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hj
    simp only [hn, List.getElem_cons_zero]
    exact hΦ
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    rw [hsf]
    simpa using hslope
  · intro i hi
    obtain rfl : i = 0 := by have h := hi; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    rw [hsf]
    simpa using hgam
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro i hi
    exfalso; rw [hn] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    exact hlift
  · intro r hr
    obtain rfl : r = 0 := by have h := hr; rw [hn] at h; simpa using h
    simp only [hn, List.getElem_cons_zero]
    exact hzbar

lemma laws_fHb0 : HistoryCoherent fHb0 ∧ Realizable fHb0 ∧ polTriv.IsCanonPres fHb0 := by
  refine laws_one_node fNodeB0 fHb0 fHb0_nodes ?_ ?_ ?_ rfl canonRoot_fNodeB0.symm
  · rw [show fNodeB0.σ.Φ = (X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]
  · norm_num [show fNodeB0.line.slope = (2 : ℚ) from rfl, show fNodeB0.e = 1 from rfl,
      show fNodeB0.Dwidth = 1 from rfl, show fNodeB0.h = 2 from rfl]
  · norm_num [show fNodeB0.gam = 4 from rfl, show fNodeB0.e = 1 from rfl,
      show fNodeB0.ustar = (2 : ℚ) from rfl, show fNodeB0.s0 = 0 from rfl,
      show fNodeB0.wSide = 1 from rfl, show fNodeB0.h = 2 from rfl]

lemma laws_fHb1 : HistoryCoherent fHb1 ∧ Realizable fHb1 ∧ polTriv.IsCanonPres fHb1 := by
  refine laws_one_node fNodeB1 fHb1 fHb1_nodes ?_ ?_ ?_ rfl canonRoot_fNodeB1.symm
  · rw [show fNodeB1.σ.Φ = (X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]
  · norm_num [show fNodeB1.line.slope = (2 : ℚ) from rfl, show fNodeB1.e = 1 from rfl,
      show fNodeB1.Dwidth = 1 from rfl, show fNodeB1.h = 2 from rfl]
  · norm_num [show fNodeB1.gam = 4 from rfl, show fNodeB1.e = 1 from rfl,
      show fNodeB1.ustar = (2 : ℚ) from rfl, show fNodeB1.s0 = 0 from rfl,
      show fNodeB1.wSide = 1 from rfl, show fNodeB1.h = 2 from rfl]

lemma laws_fHj : HistoryCoherent fHj ∧ Realizable fHj ∧ polTriv.IsCanonPres fHj := by
  refine laws_one_node fNodeJ fHj fHj_nodes ?_ ?_ ?_ rfl canonRoot_fNodeJ.symm
  · rw [show fNodeJ.σ.Φ = (X : Polynomial ℤ_[2]) from rfl, Polynomial.natDegree_X]
  · norm_num [show fNodeJ.line.slope = (3 : ℚ) from rfl, show fNodeJ.e = 1 from rfl,
      show fNodeJ.Dwidth = 1 from rfl, show fNodeJ.h = 3 from rfl]
  · norm_num [show fNodeJ.gam = 6 from rfl, show fNodeJ.e = 1 from rfl,
      show fNodeJ.ustar = (3 : ℚ) from rfl, show fNodeJ.s0 = 0 from rfl,
      show fNodeJ.wSide = 1 from rfl, show fNodeJ.h = 3 from rfl]

/-! ### §M — the forge tree model (p = 2, F = ZMod 2, n = 2, N = 2, m = 4).
Box coordinates: x0, x1 = the reduction block (chart `fχ4`), x2 = branch a's read
digit, x3 = branch b's read digit.  The window event W = {x0 = 0 ∧ x1 = 0} is the
`.red` entrance event (= `rootCell fχ4 fg0`). -/

/-- the forge chart: the identity embedding Fin 2 → Fin 4. -/
def fχ4 : Fin 2 → Fin 4 := fun b => ⟨(b : ℕ), by omega⟩

/-- the pinned level-0 reduction datum (all-zero: f̄ = x², the repeated track X). -/
def fg0 : Fin 2 → ZMod 2 := fun _ => 0

/-- the shared window entrance of the five sites. -/
noncomputable def esF : EntSt 2 (ZMod 2) 2 := EntSt.red fg0 Polynomial.X

/-- forge membership: five one-node chains, each on its own read event. -/
noncomputable def fMem : Option (History 2 (ZMod 2)) → Box 2 4 → Prop
  | none, _ => True
  | some H, x => (x 0 = 0 ∧ x 1 = 0) ∧
      ((H = t1 ∧ x 2 = 0) ∨ (H = t2 ∧ x 2 = 1) ∨
       (H = fHb0 ∧ x 3 = 0) ∨ (H = fHb1 ∧ x 3 = 1) ∨
       (H = fHj ∧ x 2 = 0 ∧ x 3 = 0))

/-- forge children: the five root reads on their events; no deeper children
(the model is depth-1 — the honesty display in the header). -/
noncomputable def fChild : Option (History 2 (ZMod 2)) → Node 2 (ZMod 2) → Box 2 4 → Prop
  | none, ν, x => (x 0 = 0 ∧ x 1 = 0) ∧
      ((ν = toyHead ∧ x 2 = 0) ∨ (ν = sibNode2 ∧ x 2 = 1) ∨
       (ν = fNodeB0 ∧ x 3 = 0) ∨ (ν = fNodeB1 ∧ x 3 = 1) ∨
       (ν = fNodeJ ∧ x 2 = 0 ∧ x 3 = 0))
  | some _, _, _ => False

private lemma t1_len : t1.nodes.length = 1 := rfl
private lemma t2_len : t2.nodes.length = 1 := rfl
private lemma fHb0_len : fHb0.nodes.length = 1 := rfl
private lemma fHb1_len : fHb1.nodes.length = 1 := rfl
private lemma fHj_len : fHj.nodes.length = 1 := rfl

private lemma snoc_ne_len1 {H K : History 2 (ZMod 2)} {ν : Node 2 (ZMod 2)}
    {hν : ν.species ≠ ReadSpecies.root} (hK : K.nodes.length = 1) :
    H.snoc ν hν ≠ K := by
  intro h
  have hl := congrArg (fun L : History 2 (ZMod 2) => L.nodes.length) h
  have hlen : (H.snoc ν hν).nodes.length = H.nodes.length + 1 := by simp [History.snoc]
  have hpos : 0 < H.nodes.length := List.length_pos_of_ne_nil H.nonempty
  simp only [hlen, hK] at hl
  omega

private lemma single_key {ν ν' : Node 2 (ZMod 2)} {K : History 2 (ZMod 2)}
    (hK : K.nodes = [ν'])
    (h1 : ([ν] : List (Node 2 (ZMod 2))) ≠ [] ∧
      ∀ (j : ℕ) (hj : j < ([ν] : List (Node 2 (ZMod 2))).length),
        ((([ν] : List (Node 2 (ZMod 2)))[j]'hj).species = ReadSpecies.root ↔ j = 0)) :
    (⟨[ν], h1.1, h1.2⟩ : History 2 (ZMod 2)) = K ↔ ν = ν' := by
  constructor
  · intro h
    have h2 := congrArg History.nodes h
    rw [hK] at h2
    simpa using h2
  · intro h
    subst h
    exact histext (by rw [hK])

/-- THE FORGE TREE MODEL — sorry-free: every realized chain is one-node, so
`mem_realizable` closes by the per-node laws (no transition legs demanded —
exactly how the G1 wall is avoided; the 2-node continuation layer is the displayed
residual, HK23/HK25 genre). -/
noncomputable def forgeModel : TreeModel 2 (ZMod 2) 2 2 4 polTriv where
  mem := fMem
  child := fChild
  root_mem := fun _ => trivial
  mem_single := by
    intro ν h1 x
    show fMem (some _) x ↔ fChild none ν x
    simp only [fMem, fChild, single_key t1_nodes h1, single_key t2_nodes h1,
      single_key fHb0_nodes h1, single_key fHb1_nodes h1, single_key fHj_nodes h1]
  mem_snoc := by
    intro H ν hν x
    show fMem (some (H.snoc ν hν)) x ↔ (fMem (some H) x ∧ fChild (some H) ν x)
    constructor
    · rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩
      · exact absurd h (snoc_ne_len1 t1_len)
      · exact absurd h (snoc_ne_len1 t2_len)
      · exact absurd h (snoc_ne_len1 fHb0_len)
      · exact absurd h (snoc_ne_len1 fHb1_len)
      · exact absurd h (snoc_ne_len1 fHj_len)
    · rintro ⟨-, h⟩
      exact h.elim
  mem_realizable := by
    intro H x hmem
    rcases hmem with ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;> subst h
    · exact laws_t1
    · exact laws_t2
    · exact laws_fHb0
    · exact laws_fHb1
    · exact laws_fHj

/-! ### §C — the cell layer.  The read tables are Classical-free in the box
argument (decidable throughout — the decide-small gates below evaluate). -/

/-- the forge cell alphabet: root cell, joint window cells (both side digits),
per-branch read cells (one side digit each), state cell (empty roster), junk. -/
inductive FCell
  | cRoot | cJunk | cSt
  | cRed (a b : Bool)
  | cA (a : Bool)
  | cB (b : Bool)
  deriving DecidableEq

instance : Fintype FCell :=
  ⟨⟨{.cRoot, .cJunk, .cSt, .cRed false false, .cRed false true, .cRed true false,
     .cRed true true, .cA false, .cA true, .cB false, .cB true}, by decide⟩,
    fun c => by
      cases c with
      | cRoot => decide
      | cJunk => decide
      | cSt => decide
      | cRed a b => cases a <;> cases b <;> decide
      | cA a => cases a <;> decide
      | cB b => cases b <;> decide⟩

/-- the JOINT window read (the multi-side site's own read map): both side digits. -/
def jointRead (x : Box 2 4) : FCell :=
  if x 0 = 0 ∧ x 1 = 0 then FCell.cRed (decide (x 2 = 0)) (decide (x 3 = 0))
  else FCell.cJunk

/-- branch a's read map: the x2 digit only. -/
def aRead (x : Box 2 4) : FCell :=
  if x 0 = 0 ∧ x 1 = 0 then FCell.cA (decide (x 2 = 0)) else FCell.cJunk

/-- branch b's read map: the x3 digit only. -/
def bRead (x : Box 2 4) : FCell :=
  if x 0 = 0 ∧ x 1 = 0 then FCell.cB (decide (x 3 = 0)) else FCell.cJunk

/-- the ambient read. -/
def ambRead (x : Box 2 4) : FCell :=
  if x 0 = 0 ∧ x 1 = 0 then FCell.cRoot else FCell.cJunk

/-- the joint cell assignment: `.red` entrances read the joint table (the joint
cell is FINER than any single branch's read — MOVES 7447–7448); `.st` states have
the empty-roster cell (depth-1 model). -/
noncomputable def fCellOf : EntSt 2 (ZMod 2) 2 → Box 2 4 → FCell
  | .amb => ambRead
  | .red _ _ => jointRead
  | .st _ => fun _ => FCell.cSt

/-- rosters: the root carries all five reads; a joint cell carries ONE node per
side (side a's read value picks the a-node, side b's the b-node); the read-value
cells `cA`/`cB` and the state/junk cells carry none. -/
noncomputable def fBranch : FCell → Finset (Node 2 (ZMod 2))
  | .cRoot => {toyHead, sibNode2, fNodeB0, fNodeB1, fNodeJ}
  | .cRed a b => {(if a then toyHead else sibNode2), (if b then fNodeB0 else fNodeB1)}
  | _ => ∅

/-- THE NON-DIAGONAL MEMBER-KEYED SITE READ: at the `.red` window entrance,
branch-a nodes key the x2 projection, branch-b nodes the x3 projection, every
other node (incl. the joint site's own `fNodeJ`) the joint read.  Sibling sites
key genuinely different read maps — the P-2(a) degeneracy broken. -/
noncomputable def fRead : EntSt 2 (ZMod 2) 2 → Node 2 (ZMod 2) → Box 2 4 → FCell :=
  fun es ν => match es with
  | .red _ _ =>
      if ν = toyHead ∨ ν = sibNode2 then aRead
      else if ν = fNodeB0 ∨ ν = fNodeB1 then bRead
      else jointRead
  | es => fCellOf es

lemma fRead_a0 : fRead esF toyHead = aRead := by
  show (if toyHead = toyHead ∨ toyHead = sibNode2 then aRead
    else if toyHead = fNodeB0 ∨ toyHead = fNodeB1 then bRead else jointRead) = aRead
  rw [if_pos (Or.inl rfl)]

lemma fRead_a1 : fRead esF sibNode2 = aRead := by
  show (if sibNode2 = toyHead ∨ sibNode2 = sibNode2 then aRead
    else if sibNode2 = fNodeB0 ∨ sibNode2 = fNodeB1 then bRead else jointRead) = aRead
  rw [if_pos (Or.inr rfl)]

lemma fRead_b0 : fRead esF fNodeB0 = bRead := by
  show (if fNodeB0 = toyHead ∨ fNodeB0 = sibNode2 then aRead
    else if fNodeB0 = fNodeB0 ∨ fNodeB0 = fNodeB1 then bRead else jointRead) = bRead
  rw [if_neg fNodeB0_notA, if_pos (Or.inl rfl)]

lemma fRead_b1 : fRead esF fNodeB1 = bRead := by
  show (if fNodeB1 = toyHead ∨ fNodeB1 = sibNode2 then aRead
    else if fNodeB1 = fNodeB0 ∨ fNodeB1 = fNodeB1 then bRead else jointRead) = bRead
  rw [if_neg fNodeB1_notA, if_pos (Or.inr rfl)]

lemma fRead_j : fRead esF fNodeJ = jointRead := by
  show (if fNodeJ = toyHead ∨ fNodeJ = sibNode2 then aRead
    else if fNodeJ = fNodeB0 ∨ fNodeJ = fNodeB1 then bRead else jointRead) = jointRead
  rw [if_neg fNodeJ_notA, if_neg fNodeJ_notB]

/-! joint-read case helpers. -/

private lemma jointRead_in {x : Box 2 4} (hW : x 0 = 0 ∧ x 1 = 0) :
    jointRead x = FCell.cRed (decide (x 2 = 0)) (decide (x 3 = 0)) := if_pos hW

private lemma jointRead_out {x : Box 2 4} (hW : ¬ (x 0 = 0 ∧ x 1 = 0)) :
    jointRead x = FCell.cJunk := if_neg hW

private lemma jointRead_congr {x y : Box 2 4} (h : jointRead x = jointRead y) :
    ((x 0 = 0 ∧ x 1 = 0) ↔ (y 0 = 0 ∧ y 1 = 0)) ∧
    ((x 0 = 0 ∧ x 1 = 0) → ((x 2 = 0 ↔ y 2 = 0) ∧ (x 3 = 0 ↔ y 3 = 0))) := by
  by_cases hx : x 0 = 0 ∧ x 1 = 0 <;> by_cases hy : y 0 = 0 ∧ y 1 = 0
  · rw [jointRead_in hx, jointRead_in hy] at h
    obtain ⟨h2, h3⟩ := FCell.cRed.inj h
    exact ⟨iff_of_true hx hy, fun _ =>
      ⟨decide_eq_decide.mp h2, decide_eq_decide.mp h3⟩⟩
  · rw [jointRead_in hx, jointRead_out hy] at h
    exact absurd h (by simp)
  · rw [jointRead_out hx, jointRead_in hy] at h
    exact absurd h (by simp)
  · exact ⟨iff_of_false hx hy, fun hx' => absurd hx' hx⟩

private lemma aRead_congr {x y : Box 2 4} (h : jointRead x = jointRead y) :
    aRead x = aRead y := by
  obtain ⟨hW, hd⟩ := jointRead_congr h
  by_cases hx : x 0 = 0 ∧ x 1 = 0
  · have hy := hW.mp hx
    rw [aRead, aRead, if_pos hx, if_pos hy]
    have h2 := (hd hx).1
    congr 1
    exact decide_eq_decide.mpr h2
  · have hy := (not_iff_not.mpr hW).mp hx
    rw [aRead, aRead, if_neg hx, if_neg hy]

private lemma zmod2_iff_one {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = 1 ↔ b = 1 := by
  have ha := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a
  have hb := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at h ⊢
  -- the (0,0) and (1,1) cases close by `rw`'s terminal `rfl`; two mixed cases remain
  · exact absurd (h.mp rfl) (by decide)
  · exact absurd (h.mpr rfl) (by decide)

private lemma bRead_congr {x y : Box 2 4} (h : jointRead x = jointRead y) :
    bRead x = bRead y := by
  obtain ⟨hW, hd⟩ := jointRead_congr h
  by_cases hx : x 0 = 0 ∧ x 1 = 0
  · have hy := hW.mp hx
    rw [bRead, bRead, if_pos hx, if_pos hy]
    have h3 := (hd hx).2
    congr 1
    exact decide_eq_decide.mpr h3
  · have hy := (not_iff_not.mpr hW).mp hx
    rw [bRead, bRead, if_neg hx, if_neg hy]

/-- THE FORGE CELL DATA — the non-diagonal `branchCellOf := fRead`. -/
noncomputable def forgeCA : CellData 2 (ZMod 2) 2 2 4 polTriv forgeModel where
  Cell := FCell
  hCellFin := inferInstance
  cellOf := fCellOf
  cellLevel := fun _ => 4
  levelOf := fun c => (c : ℕ)
  cell_local := by
    intro es x x' h
    have hx : x = x' := funext fun c => h c (by omega)
    rw [hx]
  branchSetOf := fBranch
  child_cell := by
    intro H ν x hmem
    show fChild (some H) ν x ↔ ν ∈ fBranch (fCellOf (.st H) x)
    simp only [fChild, fCellOf, fBranch, Finset.notMem_empty]
  child_root_sub := by
    rintro ν x ⟨hW, hν⟩
    show ν ∈ fBranch (ambRead x)
    rw [show ambRead x = FCell.cRoot from if_pos hW]
    simp only [fBranch, Finset.mem_insert, Finset.mem_singleton]
    rcases hν with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> tauto
  child_cell_red := by
    intro χ g ψ ν x hx hν
    show (x 0 = 0 ∧ x 1 = 0) ∧ _
    by_cases hW : x 0 = 0 ∧ x 1 = 0
    · rw [show fCellOf (.red g ψ) x = FCell.cRed (decide (x 2 = 0)) (decide (x 3 = 0))
        from jointRead_in hW] at hν
      simp only [fBranch, Finset.mem_insert, Finset.mem_singleton] at hν
      refine ⟨hW, ?_⟩
      rcases hν with h | h
      · by_cases h2 : x 2 = 0
        · rw [show decide (x 2 = 0) = true from decide_eq_true h2] at h
          exact Or.inl ⟨by simpa using h, h2⟩
        · rw [show decide (x 2 = 0) = false from decide_eq_false h2] at h
          have h2' : x 2 = 1 := by
            rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x 2) with h' | h'
            · exact absurd h' h2
            · exact h'
          exact Or.inr (Or.inl ⟨by simpa using h, h2'⟩)
      · by_cases h3 : x 3 = 0
        · rw [show decide (x 3 = 0) = true from decide_eq_true h3] at h
          exact Or.inr (Or.inr (Or.inl ⟨by simpa using h, h3⟩))
        · rw [show decide (x 3 = 0) = false from decide_eq_false h3] at h
          have h3' : x 3 = 1 := by
            rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (x 3) with h' | h'
            · exact absurd h' h3
            · exact h'
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simpa using h, h3'⟩)))
    · rw [show fCellOf (.red g ψ) x = FCell.cJunk from jointRead_out hW] at hν
      simp [fBranch] at hν
  child_red_uniform := by
    intro g ψ x y hcell ν
    have h := jointRead_congr (show jointRead x = jointRead y from hcell)
    obtain ⟨hW, hd⟩ := h
    show (x 0 = 0 ∧ x 1 = 0) ∧ _ ↔ (y 0 = 0 ∧ y 1 = 0) ∧ _
    by_cases hx : x 0 = 0 ∧ x 1 = 0
    · have hy := hW.mp hx
      obtain ⟨h2, h3⟩ := hd hx
      have h2' : x 2 = 1 ↔ y 2 = 1 := zmod2_iff_one h2
      have h3' : x 3 = 1 ↔ y 3 = 1 := zmod2_iff_one h3
      rw [iff_true_intro hx, iff_true_intro hy, true_and, true_and, h2, h3, h2', h3']
    · have hy := (not_iff_not.mpr hW).mp hx
      exact iff_of_false (fun h => hx h.1) (fun h => hy h.1)
  branchCellOf := fRead
  branch_cell_joint := by
    intro es ν x y h
    match es with
    | .amb => exact h
    | .st H => exact h
    | .red g ψ =>
      show (if ν = toyHead ∨ ν = sibNode2 then aRead
        else if ν = fNodeB0 ∨ ν = fNodeB1 then bRead else jointRead) x
        = (if ν = toyHead ∨ ν = sibNode2 then aRead
        else if ν = fNodeB0 ∨ ν = fNodeB1 then bRead else jointRead) y
      have hj : jointRead x = jointRead y := h
      split_ifs
      · exact aRead_congr hj
      · exact bRead_congr hj
      · exact hj

/-! ### §Cert — the non-diagonality certificates (P-2(a) broken three ways). -/

/-- the all-zero window point (in every site event). -/
def x00 : Box 2 4 := fun _ => 0

/-- the window point with x3 = 1 (in branch-a's 0-event, NOT in branch-b's). -/
def x01 : Box 2 4 := fun c => if c = 3 then 1 else 0

/-- CERTIFICATE 1: sibling branch nodes at the SAME entrance key DIFFERENT read
maps (the literal non-diagonality of `branchCellOf` in the member index). -/
theorem forge_read_nondiagonal :
    forgeCA.branchCellOf esF toyHead ≠ forgeCA.branchCellOf esF fNodeB0 := by
  intro h
  have h1 : aRead = bRead := by
    have h0 : fRead esF toyHead = fRead esF fNodeB0 := h
    rwa [fRead_a0, fRead_b0] at h0
  have h2 : FCell.cA true = FCell.cB false := by
    have h3 := congrFun h1 x01
    rwa [show aRead x01 = FCell.cA true from by decide,
      show bRead x01 = FCell.cB false from by decide] at h3
  exact FCell.noConfusion h2

/-- CERTIFICATE 2: the sibling STATE EVENTS cross-cut — nonempty overlap AND
unequal.  Under any diagonal read the sibling states are fibers of ONE map over
the shared entrance, hence equal or disjoint: this configuration is exactly what
the T re-ratification found unrepresentable pre-re-key. -/
theorem forge_states_crosscut :
    stateEvent forgeModel (some t1) ≠ stateEvent forgeModel (some fHb0) ∧
    (stateEvent forgeModel (some t1) ∩ stateEvent forgeModel (some fHb0)).Nonempty := by
  constructor
  · intro h
    have hx : x01 ∈ stateEvent forgeModel (some t1) := by
      show fMem (some t1) x01
      exact ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    rw [h] at hx
    obtain ⟨-, h5⟩ := (show fMem (some fHb0) x01 from hx)
    rcases h5 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact t1_ne_fHb0 (h.symm)
    · exact absurd h.symm (fun h' => t2_ne_fHb0 h')
    · exact absurd (show (1 : ZMod 2) = 0 from h) (by decide)
    · exact fHb0_ne_fHb1 h
    · exact fHb0_ne_fHj h
  · exact ⟨x00, ⟨⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, ⟨⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩⟩

/-- CERTIFICATE 3 (the STRUCTURAL P-2(a) breaker): NO single-map read — over ANY
cell type — presents both sibling state events as its fibers over the shared
entrance.  So no diagonal (`ν`-independent) `branchCellOf` can carry this
ledger's `state_cell` rows: the forge's non-diagonality is forced, not tabular. -/
theorem forge_no_diagonal_read :
    ¬ ∃ (γ : Type) (Ψ : Box 2 4 → γ) (c₁ c₂ : γ),
      stateEvent forgeModel (some t1)
        = {x | x ∈ entEvent forgeModel fχ4 esF ∧ Ψ x = c₁} ∧
      stateEvent forgeModel (some fHb0)
        = {x | x ∈ entEvent forgeModel fχ4 esF ∧ Ψ x = c₂} := by
  rintro ⟨γ, Ψ, c₁, c₂, h₁, h₂⟩
  obtain ⟨hne, x, hx₁, hx₂⟩ := forge_states_crosscut
  have hc₁ : Ψ x = c₁ := ((Set.ext_iff.mp h₁ x).mp hx₁).2
  have hc₂ : Ψ x = c₂ := ((Set.ext_iff.mp h₂ x).mp hx₂).2
  exact hne (h₁.trans (by rw [← hc₁.symm.trans hc₂] at h₂; exact h₂.symm))

/-! ### §L — the presented systems (locus + fresh clauses). -/

/-- the window locus: coordinates 0, 1 pinned to 0 (solution set = the window
event = the `.red` entrance event). -/
noncomputable def forgeLocus : Locus 2 4 :=
  ⟨fun c => decide ((c : ℕ) < 2), fun _ _ => 0⟩

lemma forgeLocus_iff (x : Box 2 4) :
    forgeLocus.IsSolution x ↔ (x 0 = 0 ∧ x 1 = 0) := by
  constructor
  · intro h
    exact ⟨h 0 rfl, h 1 rfl⟩
  · rintro ⟨h0, h1⟩ i hi
    fin_cases i
    · exact h0
    · exact h1
    all_goals exact absurd hi (by decide)

/-- the codim-1 value clause at coordinate `i`: pins `x i = v`. -/
noncomputable def valClause (i : Fin 4) (v : ZMod 2) : LevelClause 2 4 where
  support := {i}
  codim := 1
  sat := fun x => x i = v
  dep := fun x y h => by rw [h i (Finset.mem_singleton_self i)]
  count := by
    have h1 : Nat.card {y : Fin 4 → ZMod 2 //
        y i = v ∧ ∀ c ∉ ({i} : Finset (Fin 4)), y c = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · constructor
        intro a b
        apply Subtype.ext; funext c
        by_cases hc : c = i
        · subst hc; rw [a.2.1, b.2.1]
        · rw [a.2.2 c (by simp [hc]), b.2.2 c (by simp [hc])]
      · refine ⟨⟨fun c => if c = i then v else 0, by simp, fun c hc => ?_⟩⟩
        show (if c = i then v else 0) = 0
        rw [if_neg (by simpa using hc)]
    rw [h1, one_mul, Finset.card_singleton]

private lemma valClause_ne {i j : Fin 4} {v w : ZMod 2} (hij : i ≠ j) :
    valClause i v ≠ valClause j w := fun h => by
  have h2 : ({i} : Finset (Fin 4)) = {j} := congrArg LevelClause.support h
  exact hij (by simpa using h2)

/-- per-branch single-clause fresh systems + the joint 2-clause system. -/
noncomputable def fdA0 : FreshData 2 4 := ⟨[valClause 2 0], List.pairwise_singleton _ _⟩
noncomputable def fdA1 : FreshData 2 4 := ⟨[valClause 2 1], List.pairwise_singleton _ _⟩
noncomputable def fdB0 : FreshData 2 4 := ⟨[valClause 3 0], List.pairwise_singleton _ _⟩
noncomputable def fdB1 : FreshData 2 4 := ⟨[valClause 3 1], List.pairwise_singleton _ _⟩

/-- the joint site's fresh system: one clause per side, disjoint spans {2}/{3}. -/
noncomputable def fdJ : FreshData 2 4 :=
  ⟨[valClause 2 0, valClause 3 0], by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro cl hcl
    rw [List.mem_singleton] at hcl
    subst hcl
    show Disjoint ({(2 : Fin 4)} : Finset (Fin 4)) {3}
    decide⟩

noncomputable def fdNone : FreshData 2 4 := ⟨[], List.Pairwise.nil⟩

private lemma fdA0_sat (x : Box 2 4) : fdA0.sat x ↔ x 2 = 0 := by
  constructor
  · intro hs
    exact hs (valClause 2 0) List.mem_cons_self
  · intro hs cl hcl
    rw [List.mem_singleton.mp hcl]
    exact hs

private lemma fdA1_sat (x : Box 2 4) : fdA1.sat x ↔ x 2 = 1 := by
  constructor
  · intro hs
    exact hs (valClause 2 1) List.mem_cons_self
  · intro hs cl hcl
    rw [List.mem_singleton.mp hcl]
    exact hs

private lemma fdB0_sat (x : Box 2 4) : fdB0.sat x ↔ x 3 = 0 := by
  constructor
  · intro hs
    exact hs (valClause 3 0) List.mem_cons_self
  · intro hs cl hcl
    rw [List.mem_singleton.mp hcl]
    exact hs

private lemma fdB1_sat (x : Box 2 4) : fdB1.sat x ↔ x 3 = 1 := by
  constructor
  · intro hs
    exact hs (valClause 3 1) List.mem_cons_self
  · intro hs cl hcl
    rw [List.mem_singleton.mp hcl]
    exact hs

private lemma fdJ_sat (x : Box 2 4) : fdJ.sat x ↔ (x 2 = 0 ∧ x 3 = 0) := by
  constructor
  · intro hs
    exact ⟨hs (valClause 2 0) List.mem_cons_self,
      hs (valClause 3 0) (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rintro ⟨h2, h3⟩ cl hcl
    rcases List.mem_cons.mp hcl with h | h
    · subst h; exact h2
    · rw [List.mem_singleton.mp h]; exact h3

/-! ### §T — the forge tree (five maximal one-node chains). -/

private lemma prefix_len1 {H K : History 2 (ZMod 2)} (h : H.IsPrefixOf K)
    (hK : K.nodes.length = 1) : H = K := by
  refine histext (List.IsPrefix.eq_of_length h ?_)
  have h1 := h.length_le
  have h0 : 0 < H.nodes.length := List.length_pos_of_ne_nil H.nonempty
  omega

private lemma chains_len1 {H : History 2 (ZMod 2)}
    (hH : H ∈ ({t1, t2, fHb0, fHb1, fHj} : Set (History 2 (ZMod 2)))) :
    H.nodes.length = 1 := by
  rcases hH with h | h | h | h | h <;> subst h
  · exact t1_len
  · exact t2_len
  · exact fHb0_len
  · exact fHb1_len
  · exact fHj_len

open Classical in
/-- THE FORGE TREE: five sibling one-node chains at the shared window entrance. -/
noncomputable def forgeTree : VTree 2 (ZMod 2) where
  chains := {t1, t2, fHb0, fHb1, fHj}
  hfin := ((((Set.finite_singleton fHj).insert fHb1).insert fHb0).insert t2).insert t1
  hne_nodes := fun H _ => H.nonempty
  hclosed := by
    intro H hH H' hpre hne
    have h1 : H' = H := prefix_len1 hpre (chains_len1 hH)
    rw [h1]
    exact hH
  henV := ∅
  hhen := by simp
  leafV := fun H =>
    if H ∈ ({t1, t2, fHb0, fHb1, fHj} : Set (History 2 (ZMod 2)))
    then some (irrVerdictOf H) else none
  hleaf := by
    intro H
    constructor
    · intro hsome
      by_cases hmem : H ∈ ({t1, t2, fHb0, fHb1, fHj} : Set (History 2 (ZMod 2)))
      · refine ⟨hmem, ?_⟩
        intro H' hH' hpre
        exact (prefix_len1 hpre (chains_len1 hH')).symm ▸ rfl
      · rw [if_neg hmem] at hsome
        exact absurd hsome (by simp)
    · rintro ⟨hmem, -⟩
      rw [if_pos hmem]
      rfl
  nsLeaf := fun _ => False
  hns_leaf := by simp

/-! ### §S — the genuine SideSplit at the joint site (the sides = 2 legs,
DISCHARGED).  Data fields are index-independent; the Prop fields consume the
cell/fd pins by subst — so the ledger's `hsplit_k` reads the literal `k = 2`. -/

/-- the sides-2 split, generic in its (cell, fd) indexes so the ledger's
if-chain dispatch never casts data: k = 2, side 0 = the slope-1 side (roster node
`toyHead`, clause x2, span {2}), side 1 = the slope-2 side (roster node `fNodeB0`,
clause x3, span {3}); hull slopes 1 < 2 = the roster nodes' RECORDED line slopes. -/
noncomputable def forgeSplitGen (c : FCell) (fd : FreshData 2 4)
    (hc : c = FCell.cRed true true) (hfd : fd = fdJ) :
    SideSplit forgeModel forgeCA c fd where
  k := 2
  sideOf := fun ν => if ν = toyHead then (0 : Fin 2) else 1
  side_ne := by
    subst hc
    intro j
    fin_cases j
    · exact ⟨toyHead,
        (Finset.mem_insert_self toyHead {fNodeB0} :
          toyHead ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2)))),
        if_pos rfl⟩
    · exact ⟨fNodeB0,
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self fNodeB0) :
          fNodeB0 ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2)))),
        if_neg fNodeB0_ne_toyHead⟩
  clausesOf := fun j => if j = 0 then {valClause 2 0} else {valClause 3 0}
  hpartition := by
    subst hfd
    constructor
    · ext cl
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj⟩
        by_cases h0 : j = 0
        · rw [h0, if_pos rfl] at hj
          rw [Finset.coe_singleton, Set.mem_singleton_iff] at hj
          subst hj
          exact List.mem_cons_self
        · rw [if_neg h0] at hj
          rw [Finset.coe_singleton, Set.mem_singleton_iff] at hj
          subst hj
          exact List.mem_cons_of_mem _ List.mem_cons_self
      · intro hcl
        rcases List.mem_cons.mp hcl with h | h
        · exact ⟨0, by rw [if_pos rfl, Finset.coe_singleton]; exact h⟩
        · rw [List.mem_singleton] at h
          exact ⟨1, by rw [if_neg (by decide), Finset.coe_singleton]; exact h⟩
    · intro i j hij
      have hd : ∀ a b : Fin 2, a ≠ b →
          Disjoint (if a = 0 then ({valClause 2 0} : Finset (FreshClause 2 4))
              else {valClause 3 0})
            (if b = 0 then ({valClause 2 0} : Finset (FreshClause 2 4))
              else {valClause 3 0}) := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> first
          | exact absurd rfl hab
          | (simp only [reduceIte]
             first
               | exact Finset.disjoint_singleton.mpr (valClause_ne (by decide))
               | exact Finset.disjoint_singleton.mpr (valClause_ne (by decide)))
      exact hd i j hij
  sideSpan := fun j => if j = 0 then ({2} : Finset (Fin 4)) else {3}
  hspan_disj := by
    have h : ∀ i j : Fin 2, i ≠ j →
        Disjoint (if i = 0 then ({2} : Finset (Fin 4)) else {3})
          (if j = 0 then ({2} : Finset (Fin 4)) else {3}) := by decide
    exact fun i j hij => h i j hij
  hsupport := by
    intro j cl hcl cIdx hsup
    by_cases h0 : j = 0
    · rw [h0, if_pos rfl] at hcl
      rw [Finset.mem_singleton] at hcl
      subst hcl
      rw [Finset.mem_singleton.mp hsup, h0, if_pos rfl]
      exact Finset.mem_singleton_self _
    · rw [if_neg h0] at hcl
      rw [Finset.mem_singleton] at hcl
      subst hcl
      rw [Finset.mem_singleton.mp hsup, if_neg h0]
      exact Finset.mem_singleton_self _
  hullSlope := fun j => if j = 0 then (1 : ℚ) else 2
  hslope := by
    have h : ∀ i j : Fin 2, i < j →
        (if i = 0 then (1 : ℚ) else 2) < (if j = 0 then (1 : ℚ) else 2) := by
      decide
    exact fun i j hij => h i j hij
  hside_read := by
    subst hc
    intro ν hν
    have hν' : ν ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2))) := hν
    rcases Finset.mem_insert.mp hν' with h | h
    · subst h
      rw [if_pos rfl]
      rfl
    · rw [Finset.mem_singleton] at h
      subst h
      rw [if_neg fNodeB0_ne_toyHead]
      rfl

/-! ### §Ledger — the forge site ledger (sides = 2 at the joint site; all split
legs discharged). -/

private lemma esF_lemma : entEvent forgeModel fχ4 esF = rootCell fχ4 fg0 := rfl

private lemma rootCell_fχ4 (x : Box 2 4) :
    x ∈ rootCell fχ4 fg0 ↔ (x 0 = 0 ∧ x 1 = 0) := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ b
    fin_cases b
    · exact h0
    · exact h1

/- the five read-fiber event computations. -/

private lemma aRead_cA_iff (x : Box 2 4) (v : Bool) :
    aRead x = FCell.cA v ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ decide (x 2 = 0) = v) := by
  by_cases hW : x 0 = 0 ∧ x 1 = 0
  · rw [aRead, if_pos hW]
    constructor
    · intro h
      exact ⟨hW, (FCell.cA.inj h)⟩
    · rintro ⟨-, h⟩
      rw [h]
  · rw [aRead, if_neg hW]
    exact iff_of_false (by simp) (fun h => hW h.1)

private lemma bRead_cB_iff (x : Box 2 4) (v : Bool) :
    bRead x = FCell.cB v ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ decide (x 3 = 0) = v) := by
  by_cases hW : x 0 = 0 ∧ x 1 = 0
  · rw [bRead, if_pos hW]
    constructor
    · intro h
      exact ⟨hW, (FCell.cB.inj h)⟩
    · rintro ⟨-, h⟩
      rw [h]
  · rw [bRead, if_neg hW]
    exact iff_of_false (by simp) (fun h => hW h.1)

private lemma jointRead_cRed_iff (x : Box 2 4) (v w : Bool) :
    jointRead x = FCell.cRed v w
      ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ decide (x 2 = 0) = v ∧ decide (x 3 = 0) = w) := by
  by_cases hW : x 0 = 0 ∧ x 1 = 0
  · rw [jointRead_in hW]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := FCell.cRed.inj h
      exact ⟨hW, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      rw [h1, h2]
  · rw [jointRead_out hW]
    exact iff_of_false (by simp) (fun h => hW h.1)

private lemma dec0_true {a : ZMod 2} : decide (a = 0) = true ↔ a = 0 := by
  simp

private lemma dec0_false {a : ZMod 2} : decide (a = 0) = false ↔ a = 1 := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with h | h <;> subst h <;> simp

/-! the five per-site read-fiber characterizations (the state events as compiled
fibers of the member-keyed reads). -/

private lemma readfib_a0 (x : Box 2 4) :
    fRead esF toyHead x = FCell.cA true ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ x 2 = 0) := by
  rw [fRead_a0, aRead_cA_iff]
  exact and_congr_right fun _ => dec0_true

private lemma readfib_a1 (x : Box 2 4) :
    fRead esF sibNode2 x = FCell.cA false ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ x 2 = 1) := by
  rw [fRead_a1, aRead_cA_iff]
  exact and_congr_right fun _ => dec0_false

private lemma readfib_b0 (x : Box 2 4) :
    fRead esF fNodeB0 x = FCell.cB true ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ x 3 = 0) := by
  rw [fRead_b0, bRead_cB_iff]
  exact and_congr_right fun _ => dec0_true

private lemma readfib_b1 (x : Box 2 4) :
    fRead esF fNodeB1 x = FCell.cB false ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ x 3 = 1) := by
  rw [fRead_b1, bRead_cB_iff]
  exact and_congr_right fun _ => dec0_false

private lemma readfib_j (x : Box 2 4) :
    fRead esF fNodeJ x = FCell.cRed true true
      ↔ ((x 0 = 0 ∧ x 1 = 0) ∧ x 2 = 0 ∧ x 3 = 0) := by
  rw [fRead_j, jointRead_cRed_iff]
  exact and_congr_right fun _ => and_congr dec0_true dec0_true

open Classical in
/-- THE FORGE SITE LEDGER — the OL-2 inhabitant: non-diagonal member-keyed reads
(`forgeCA.branchCellOf = fRead`), `sides fHj = 2` with the genuine `SideSplit`,
every law field discharged, over the sorry-free `forgeModel`/`forgeTree`. -/
noncomputable def forgeLedger : SiteLedger forgeTree forgeModel forgeCA fχ4 := by
  classical
  exact
    { sys := fun H =>
        if H = t1 then (forgeLocus, fdA0)
        else if H = t2 then (forgeLocus, fdA1)
        else if H = fHb0 then (forgeLocus, fdB0)
        else if H = fHb1 then (forgeLocus, fdB1)
        else if H = fHj then (forgeLocus, fdJ)
        else (forgeLocus, fdNone)
      cellAt := fun H =>
        if H = t1 then FCell.cA true
        else if H = t2 then FCell.cA false
        else if H = fHb0 then FCell.cB true
        else if H = fHb1 then FCell.cB false
        else if H = fHj then FCell.cRed true true
        else FCell.cJunk
      parentSt := fun _ => esF
      hparent := by
        intro H hH
        show match esF with
          | .amb => False
          | .red _ _ => H.nodes.length = 1
          | .st H' => H'.IsPrefixOf H ∧ H'.nodes.length + 1 = H.nodes.length ∧ H' ∈ forgeTree.chains
        exact chains_len1 hH
      presents := by
        intro H hH
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl]
          constructor
          · ext x
            change (x ∈ rootCell fχ4 fg0 ∧ fRead esF toyHead x = FCell.cA true)
              ↔ (forgeLocus.IsSolution x ∧ fdA0.sat x)
            rw [rootCell_fχ4, readfib_a0, forgeLocus_iff, fdA0_sat]
            tauto
          · ext x
            change x ∈ rootCell fχ4 fg0 ↔ forgeLocus.IsSolution x
            rw [rootCell_fχ4, forgeLocus_iff]
        · rw [if_neg t1_ne_t2.symm, if_pos rfl, if_neg t1_ne_t2.symm, if_pos rfl]
          constructor
          · ext x
            change (x ∈ rootCell fχ4 fg0 ∧ fRead esF sibNode2 x = FCell.cA false)
              ↔ (forgeLocus.IsSolution x ∧ fdA1.sat x)
            rw [rootCell_fχ4, readfib_a1, forgeLocus_iff, fdA1_sat]
            tauto
          · ext x
            change x ∈ rootCell fχ4 fg0 ↔ forgeLocus.IsSolution x
            rw [rootCell_fχ4, forgeLocus_iff]
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl,
            if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl]
          constructor
          · ext x
            change (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeB0 x = FCell.cB true)
              ↔ (forgeLocus.IsSolution x ∧ fdB0.sat x)
            rw [rootCell_fχ4, readfib_b0, forgeLocus_iff, fdB0_sat]
            tauto
          · ext x
            change x ∈ rootCell fχ4 fg0 ↔ forgeLocus.IsSolution x
            rw [rootCell_fχ4, forgeLocus_iff]
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl, if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm,
            if_neg fHb0_ne_fHb1.symm, if_pos rfl]
          constructor
          · ext x
            change (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeB1 x = FCell.cB false)
              ↔ (forgeLocus.IsSolution x ∧ fdB1.sat x)
            rw [rootCell_fχ4, readfib_b1, forgeLocus_iff, fdB1_sat]
            tauto
          · ext x
            change x ∈ rootCell fχ4 fg0 ↔ forgeLocus.IsSolution x
            rw [rootCell_fχ4, forgeLocus_iff]
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl, if_neg t1_ne_fHj.symm,
            if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm, if_neg fHb1_ne_fHj.symm,
            if_pos rfl]
          constructor
          · ext x
            change (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeJ x = FCell.cRed true true)
              ↔ (forgeLocus.IsSolution x ∧ fdJ.sat x)
            rw [rootCell_fχ4, readfib_j, forgeLocus_iff, fdJ_sat]
            tauto
          · ext x
            change x ∈ rootCell fχ4 fg0 ↔ forgeLocus.IsSolution x
            rw [rootCell_fχ4, forgeLocus_iff]
      sides := fun H => if H = fHj then 2 else 1
      hsides := by
        intro H hH
        by_cases h : H = fHj
        · rw [if_pos h]; omega
        · rw [if_neg h]
      state_cell := by
        intro H hH
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl]
          ext x
          change fMem (some t1) x
            ↔ (x ∈ rootCell fχ4 fg0 ∧ fRead esF toyHead x = FCell.cA true)
          rw [rootCell_fχ4, readfib_a0]
          simp only [fMem]
          constructor
          · rintro ⟨hW, h5⟩
            refine ⟨hW, hW, ?_⟩
            rcases h5 with ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
            · exact h
            · exact absurd ht t1_ne_t2
            · exact absurd ht t1_ne_fHb0
            · exact absurd ht t1_ne_fHb1
            · exact absurd ht t1_ne_fHj
          · rintro ⟨hW, -, hd⟩
            exact ⟨hW, Or.inl ⟨by trivial, hd⟩⟩
        · rw [if_neg t1_ne_t2.symm, if_pos rfl]
          ext x
          change fMem (some t2) x
            ↔ (x ∈ rootCell fχ4 fg0 ∧ fRead esF sibNode2 x = FCell.cA false)
          rw [rootCell_fχ4, readfib_a1]
          simp only [fMem]
          constructor
          · rintro ⟨hW, h5⟩
            refine ⟨hW, hW, ?_⟩
            rcases h5 with ⟨ht, -⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
            · exact absurd ht.symm t1_ne_t2
            · exact h
            · exact absurd ht t2_ne_fHb0
            · exact absurd ht t2_ne_fHb1
            · exact absurd ht t2_ne_fHj
          · rintro ⟨hW, -, hd⟩
            exact ⟨hW, Or.inr (Or.inl ⟨by trivial, hd⟩)⟩
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl]
          ext x
          change fMem (some fHb0) x
            ↔ (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeB0 x = FCell.cB true)
          rw [rootCell_fχ4, readfib_b0]
          simp only [fMem]
          constructor
          · rintro ⟨hW, h5⟩
            refine ⟨hW, hW, ?_⟩
            rcases h5 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
            · exact absurd ht.symm t1_ne_fHb0
            · exact absurd ht.symm t2_ne_fHb0
            · exact h
            · exact absurd ht fHb0_ne_fHb1
            · exact absurd ht fHb0_ne_fHj
          · rintro ⟨hW, -, hd⟩
            exact ⟨hW, Or.inr (Or.inr (Or.inl ⟨by trivial, hd⟩))⟩
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl]
          ext x
          change fMem (some fHb1) x
            ↔ (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeB1 x = FCell.cB false)
          rw [rootCell_fχ4, readfib_b1]
          simp only [fMem]
          constructor
          · rintro ⟨hW, h5⟩
            refine ⟨hW, hW, ?_⟩
            rcases h5 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h⟩ | ⟨ht, -⟩
            · exact absurd ht.symm t1_ne_fHb1
            · exact absurd ht.symm t2_ne_fHb1
            · exact absurd ht.symm fHb0_ne_fHb1
            · exact h
            · exact absurd ht fHb1_ne_fHj
          · rintro ⟨hW, -, hd⟩
            exact ⟨hW, Or.inr (Or.inr (Or.inr (Or.inl ⟨by trivial, hd⟩)))⟩
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl]
          ext x
          change fMem (some fHj) x
            ↔ (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeJ x = FCell.cRed true true)
          rw [rootCell_fχ4, readfib_j]
          simp only [fMem]
          constructor
          · rintro ⟨hW, h5⟩
            refine ⟨hW, hW, ?_⟩
            rcases h5 with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, h2, h3⟩
            · exact absurd ht.symm t1_ne_fHj
            · exact absurd ht.symm t2_ne_fHj
            · exact absurd ht.symm fHb0_ne_fHj
            · exact absurd ht.symm fHb1_ne_fHj
            · exact ⟨h2, h3⟩
          · rintro ⟨hW, -, hd2, hd3⟩
            exact ⟨hW, Or.inr (Or.inr (Or.inr (Or.inr ⟨by trivial, hd2, hd3⟩)))⟩
      splitAt := fun H hH h2 => by
        have hj : H = fHj := by
          by_contra hne
          rw [if_neg hne] at h2
          omega
        exact forgeSplitGen _ _
          (by rw [hj, if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm,
            if_neg fHb0_ne_fHj.symm, if_neg fHb1_ne_fHj.symm, if_pos rfl])
          (by rw [hj, if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm,
            if_neg fHb0_ne_fHj.symm, if_neg fHb1_ne_fHj.symm, if_pos rfl])
      hsplit_k := by
        intro H hH h2
        have hj : H = fHj := by
          by_contra hne
          rw [if_neg hne] at h2
          omega
        show (2 : ℕ) = _
        rw [hj, if_pos rfl]
      hsplit_exp := by
        intro H hH h2
        have hj : H = fHj := by
          by_contra hne
          rw [if_neg hne] at h2
          omega
        subst hj
        have hR : (if fHj = t1 then (forgeLocus, fdA0)
            else if fHj = t2 then (forgeLocus, fdA1)
            else if fHj = fHb0 then (forgeLocus, fdB0)
            else if fHj = fHb1 then (forgeLocus, fdB1)
            else if fHj = fHj then (forgeLocus, fdJ)
            else (forgeLocus, fdNone)) = (forgeLocus, fdJ) := by
          rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl]
        conv_rhs => rw [hR]
        show (∑ j : Fin 2,
          ((if j = (0 : Fin 2) then ({valClause 2 0} : Finset (FreshClause 2 4))
            else {valClause 3 0}).card)) = fdJ.mstar
        rw [Fin.sum_univ_two, if_pos rfl,
          if_neg (show ¬((1 : Fin 2) = 0) by decide),
          Finset.card_singleton, Finset.card_singleton]
        rfl
      free := by
        intro H hH cl hcl cIdx hsup
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_pos rfl, Finset.mem_singleton.mp hsup]
          rfl
        · rw [if_neg t1_ne_t2.symm, if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_t2.symm, if_pos rfl, Finset.mem_singleton.mp hsup]
          rfl
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl,
            Finset.mem_singleton.mp hsup]
          rfl
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl, Finset.mem_singleton.mp hsup]
          rfl
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl] at hcl
          rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl]
          rcases List.mem_cons.mp hcl with h | h
          · rw [h] at hsup
            rw [Finset.mem_singleton.mp hsup]
            rfl
          · rw [List.mem_singleton.mp h] at hsup
            rw [Finset.mem_singleton.mp hsup]
            rfl
      freshCoords := fun H =>
        if H = t1 then ({2} : Finset (Fin 4))
        else if H = t2 then {2}
        else if H = fHb0 then {3}
        else if H = fHb1 then {3}
        else if H = fHj then {2, 3}
        else ∅
      spectator_sol := by
        intro H hH
        have key : ∀ (S : Finset (Fin 4)), (0 : Fin 4) ∉ S → (1 : Fin 4) ∉ S →
            SpectatorFor S {x : Box 2 4 | forgeLocus.IsSolution x} := by
          intro S h0 h1 x x' hagree
          simp only [Set.mem_setOf_eq, forgeLocus_iff]
          rw [hagree 0 h0, hagree 1 h1]
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl]
          exact key _ (by decide) (by decide)
        · rw [if_neg t1_ne_t2.symm, if_pos rfl, if_neg t1_ne_t2.symm, if_pos rfl]
          exact key _ (by decide) (by decide)
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl,
            if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl]
          exact key _ (by decide) (by decide)
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl, if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm,
            if_neg fHb0_ne_fHb1.symm, if_pos rfl]
          exact key _ (by decide) (by decide)
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl, if_neg t1_ne_fHj.symm,
            if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm, if_neg fHb1_ne_fHj.symm,
            if_pos rfl]
          exact key _ (by decide) (by decide)
      hfresh := by
        intro H hH cl hcl cIdx hsup
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_pos rfl]
          exact hsup
        · rw [if_neg t1_ne_t2.symm, if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_t2.symm, if_pos rfl]
          exact hsup
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl]
          exact hsup
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl] at hcl
          rw [List.mem_singleton.mp hcl] at hsup
          rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl]
          exact hsup
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl] at hcl
          rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl]
          rcases List.mem_cons.mp hcl with h | h
          · rw [h] at hsup
            rw [Finset.mem_singleton.mp hsup]
            decide
          · rw [List.mem_singleton.mp h] at hsup
            rw [Finset.mem_singleton.mp hsup]
            decide
      hcard := by
        intro H hH
        rcases hH with h | h | h | h | h <;> subst h
        · rw [if_pos rfl, if_pos rfl]
          rfl
        · rw [if_neg t1_ne_t2.symm, if_pos rfl, if_neg t1_ne_t2.symm, if_pos rfl]
          rfl
        · rw [if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl,
            if_neg t1_ne_fHb0.symm, if_neg t2_ne_fHb0.symm, if_pos rfl]
          rfl
        · rw [if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm, if_neg fHb0_ne_fHb1.symm,
            if_pos rfl, if_neg t1_ne_fHb1.symm, if_neg t2_ne_fHb1.symm,
            if_neg fHb0_ne_fHb1.symm, if_pos rfl]
          rfl
        · rw [if_neg t1_ne_fHj.symm, if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm,
            if_neg fHb1_ne_fHj.symm, if_pos rfl, if_neg t1_ne_fHj.symm,
            if_neg t2_ne_fHj.symm, if_neg fHb0_ne_fHj.symm, if_neg fHb1_ne_fHj.symm,
            if_pos rfl]
          rfl }

/-! ### §JC — the (JC-multi) price DECIDED at the sides-2 site: the site's exact
cell event (1 point) times p^(side-exponent sum 2) = the entrance event (4 points). -/

/-- the concrete split at the joint site's literal indexes. -/
noncomputable def forgeSplitJ : SideSplit forgeModel forgeCA (FCell.cRed true true) fdJ :=
  forgeSplitGen _ _ rfl rfl

theorem forge_jcmulti : JCmultiAt forgeModel forgeCA fχ4 esF fNodeJ forgeSplitJ := by
  have hev : siteCellEvent forgeModel forgeCA fχ4 esF fNodeJ (FCell.cRed true true)
      = {x : Box 2 4 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0} := by
    ext x
    change (x ∈ rootCell fχ4 fg0 ∧ fRead esF fNodeJ x = FCell.cRed true true)
      ↔ (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0)
    rw [rootCell_fχ4, readfib_j]
    constructor
    · rintro ⟨hW, -, h2, h3⟩
      exact ⟨hW.1, hW.2, h2, h3⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1⟩, ⟨h0, h1⟩, h2, h3⟩
  have hent : entEvent forgeModel fχ4 esF = {x : Box 2 4 | x 0 = 0 ∧ x 1 = 0} := by
    ext x
    change x ∈ rootCell fχ4 fg0 ↔ (x 0 = 0 ∧ x 1 = 0)
    exact rootCell_fχ4 x
  have hsum : (∑ j : Fin 2, (forgeSplitJ.clausesOf j).card) = 2 := by
    show (∑ j : Fin 2,
      ((if j = (0 : Fin 2) then ({valClause 2 0} : Finset (FreshClause 2 4))
        else {valClause 3 0}).card)) = 2
    rw [Fin.sum_univ_two, if_pos rfl,
      if_neg (show ¬((1 : Fin 2) = 0) by decide),
      Finset.card_singleton, Finset.card_singleton]
  show Nat.card ↥(siteCellEvent forgeModel forgeCA fχ4 esF fNodeJ (FCell.cRed true true))
      * 2 ^ (∑ j : Fin 2, (forgeSplitJ.clausesOf j).card)
    = Nat.card ↥(entEvent forgeModel fχ4 esF)
  rw [hev, hent, hsum]
  rw [show Nat.card ↥({x : Box 2 4 | x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0}) = 1 from by
    rw [Nat.card_eq_fintype_card]; decide]
  rw [show Nat.card ↥({x : Box 2 4 | x 0 = 0 ∧ x 1 = 0}) = 4 from by
    rw [Nat.card_eq_fintype_card]; decide]
  norm_num

/-! ### §P1 — PIN 1 (N-H7-1): the K-LOC normalization keys by REALIZED SLOPE;
the slope-pooled form is REFUTED at this instance. -/

/-- the slope-1 (branch-a) projection of a joint cell. -/
def aProj : FCell → FCell
  | .cRed i _ => .cA i
  | c => c

/-- the slope-2 (branch-b) projection of a joint cell. -/
def bProj : FCell → FCell
  | .cRed _ j => .cB j
  | c => c

/-- the slope-keyed cell normalization ε: at slope 1 (branch a's recorded slope)
project the joint cell to its a-component; at slope 2 (branch b's) to its
b-component; identity elsewhere. -/
def slopeEps : ℚ → FCell → FCell := fun s c =>
  if s = 1 then aProj c else if s = 2 then bProj c else c

/-- PIN 1, POSITIVE FACE (proved): on the sides-2 site's roster, every branch's
read map IS the slope-keyed normalization of the JOINT read — ε keyed by
`ν.line.slope`, the branch's recorded realized slope, uniformly in the box point
(the §1.1(ii)-shaped per-slope transport at this instance). -/
theorem forge_kloc_slope_keyed :
    ∀ ν ∈ forgeCA.branchSetOf (FCell.cRed true true), ∀ x : Box 2 4,
      forgeCA.branchCellOf esF ν x = slopeEps ν.line.slope (forgeCA.cellOf esF x) := by
  intro ν hν x
  have hν' : ν ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2))) := hν
  rcases Finset.mem_insert.mp hν' with h | h
  · subst h
    show fRead esF toyHead x = slopeEps toyHead.line.slope (jointRead x)
    rw [fRead_a0, show toyHead.line.slope = (1 : ℚ) from rfl]
    show aRead x = if (1 : ℚ) = 1 then aProj (jointRead x)
      else if (1 : ℚ) = 2 then bProj (jointRead x) else jointRead x
    rw [if_pos rfl]
    by_cases hW : x 0 = 0 ∧ x 1 = 0
    · rw [aRead, if_pos hW, jointRead_in hW]
      rfl
    · rw [aRead, if_neg hW, jointRead_out hW]
      rfl
  · rw [Finset.mem_singleton] at h
    subst h
    show fRead esF fNodeB0 x = slopeEps fNodeB0.line.slope (jointRead x)
    rw [fRead_b0, show fNodeB0.line.slope = (2 : ℚ) from rfl]
    show bRead x = if (2 : ℚ) = 1 then aProj (jointRead x)
      else if (2 : ℚ) = 2 then bProj (jointRead x) else jointRead x
    rw [if_neg (by norm_num), if_pos rfl]
    by_cases hW : x 0 = 0 ∧ x 1 = 0
    · rw [bRead, if_pos hW, jointRead_in hW]
      rfl
    · rw [bRead, if_neg hW, jointRead_out hW]
      rfl

/-- PIN 1, NEGATIVE FACE (compiled countermodel): the slope-POOLED strengthening
— ONE normalization ε₀ serving every roster branch — is FALSE at this instance
(evaluate both branch reads at the window point with x2 = 0, x3 = 1: the same
joint cell must map to both `cA true` and `cB false`).  The compiled twin of
N-H7-1's S5 pooled-u refutation: any Lean `KLocSemantic` row must key ε per
realized slope, never pool. -/
theorem forge_kloc_pooled_refuted :
    ¬ ∃ ε₀ : FCell → FCell,
      ∀ ν ∈ forgeCA.branchSetOf (FCell.cRed true true), ∀ x : Box 2 4,
        forgeCA.branchCellOf esF ν x = ε₀ (forgeCA.cellOf esF x) := by
  rintro ⟨ε₀, hε⟩
  have hmemA : toyHead ∈ forgeCA.branchSetOf (FCell.cRed true true) :=
    (Finset.mem_insert_self toyHead {fNodeB0} :
      toyHead ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2))))
  have hmemB : fNodeB0 ∈ forgeCA.branchSetOf (FCell.cRed true true) :=
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self fNodeB0) :
      fNodeB0 ∈ ({toyHead, fNodeB0} : Finset (Node 2 (ZMod 2))))
  have hA : fRead esF toyHead x01 = ε₀ (jointRead x01) := hε toyHead hmemA x01
  have hB : fRead esF fNodeB0 x01 = ε₀ (jointRead x01) := hε fNodeB0 hmemB x01
  rw [fRead_a0] at hA
  rw [fRead_b0] at hB
  have hAB : aRead x01 = bRead x01 := hA.trans hB.symm
  rw [show aRead x01 = FCell.cA true from by decide,
    show bRead x01 = FCell.cB false from by decide] at hAB
  exact FCell.noConfusion hAB

/-! ### §P2 — PIN 2 (N-H7-1): the decide-small semantic count gates, stated
INSIDE the D-8 guard.  Site integers: (N, τ, e_max) = (2, 1, 0), so
N − e_max = 2 ≥ 1 = τ; `forge_guard` is the compiled guard fact.  Per pin 2, no
count gate is stated below the guard. -/

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- the forge site's H7 datum: m = 2 roster, thr = 1 (the level-0 reduction read),
ρ = 0 (order-0 separation), Σ-count 4 = #(entrance event), per-branch read-class
counts 2·2. -/
noncomputable def forgeDatum : SiteDatum 2 2 2 where
  m := 2
  two_le_m := le_refl 2
  thr := 1
  one_le_thr := le_refl 1
  rho := 0
  stratumCount := 4
  branchCount := ![2, 2]

/-- PIN 2, guard fact: the forge site sits in the D-8 guard (thr + 2ρ = 1 ≤ N = 2). -/
theorem forge_guard : InGuard forgeDatum := by
  show (1 : ℕ) + 2 * 0 ≤ 2
  norm_num

/-- the datum's Σ-count is the ACTUAL entrance-event cardinality (not a free pin). -/
theorem forge_stratum_count :
    Nat.card ↥(entEvent forgeModel fχ4 esF) = forgeDatum.stratumCount := by
  have hent : entEvent forgeModel fχ4 esF = {x : Box 2 4 | x 0 = 0 ∧ x 1 = 0} := by
    ext x
    rw [esF_lemma]
    exact rootCell_fχ4 x
  rw [hent, Nat.card_eq_fintype_card]
  decide

/-- the datum's branch counts are the ACTUAL per-branch read-class counts. -/
theorem forge_branch_counts :
    Nat.card {x : Box 2 4 // aRead x = FCell.cA true} = 2 ∧
    Nat.card {x : Box 2 4 // bRead x = FCell.cB true} = 2 ∧
    ∀ j : Fin 2, forgeDatum.branchCount j = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    decide
  · rw [Nat.card_eq_fintype_card]
    decide
  · intro j
    show (![2, 2] : Fin 2 → ℕ) j = 2
    fin_cases j <;> rfl

/-- PIN 2, THE DECIDE-SMALL SEMANTIC GATE (in-guard): the FIRST contentful
`KLocCounts` instantiation — `Events` := the site's four realized joint read
words (Bool × Bool), joint/single counts := ACTUAL box cardinalities of the read
fibers.  The (SIB)-shaped identity #joint · #Σ^{m−1} = ∏ #single holds EXACTLY
at every word (1·4 = 2·2) — decided by kernel evaluation over the 16-point box.
This is the `gate_order0_semantic` genre (H7-W3a) at the forge surrogate site;
the engine-tied instantiation (at `siteCellEvent` over the pinned canonical
models) remains the Tier-M obligation. -/
theorem forge_klocCounts :
    KLocCounts forgeDatum (Bool × Bool)
      (fun w => Nat.card {x : Box 2 4 // jointRead x = FCell.cRed w.1 w.2})
      (fun w j => if j = (0 : Fin 2)
        then Nat.card {x : Box 2 4 // aRead x = FCell.cA w.1}
        else Nat.card {x : Box 2 4 // bRead x = FCell.cB w.2}) := by
  intro w
  show Nat.card {x : Box 2 4 // jointRead x = FCell.cRed w.1 w.2} * 4 ^ (2 - 1)
    = ∏ j : Fin 2, (if j = (0 : Fin 2)
        then Nat.card {x : Box 2 4 // aRead x = FCell.cA w.1}
        else Nat.card {x : Box 2 4 // bRead x = FCell.cB w.2})
  rw [Fin.prod_univ_two, if_pos rfl, if_neg (show ¬((1 : Fin 2) = 0) by decide)]
  obtain ⟨i, j⟩ := w
  cases i <;> cases j <;>
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      decide

/-! ### §E — census (in-file `#print axioms`; expected: Lean core only —
`propext`, `Classical.choice`, `Quot.sound`; ZERO `sorryAx`). -/

#print axioms forgeModel
#print axioms forgeCA
#print axioms forgeTree
#print axioms forgeLedger
#print axioms forgeSplitJ
#print axioms forge_read_nondiagonal
#print axioms forge_states_crosscut
#print axioms forge_no_diagonal_read
#print axioms forge_jcmulti
#print axioms forge_kloc_slope_keyed
#print axioms forge_kloc_pooled_refuted
#print axioms forge_guard
#print axioms forge_stratum_count
#print axioms forge_branch_counts
#print axioms forge_klocCounts

end LeanUrat.Scaffold.HDischarge.H7
