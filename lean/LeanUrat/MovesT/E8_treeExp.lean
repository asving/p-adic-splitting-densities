/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.E5_rootSplit
import LeanUrat.MovesT.E6_segStep
import LeanUrat.MovesT.F0_preHalt

/-! # T-E8 `treeExp` [hard — THE CORPUS CENTERPIECE] — (TREE-EXP) (MOVES 7449–7461):
strong induction on the chain cones via the first-split decomposition; every site
charged exactly once. The ∀-closure `TreeExpFin` (Defs §2.10) carries the FULL W4-1
interface.

EXECUTION RECORD 2026-08-01 (THE T RE-RATIFICATION REPAIRS APPLIED — REJECT-M
verdict, `/tmp/finalratify_t/verdict.txt`; supersedes the 2026-07-29 [date corrected
2026-07-30; original record mis-dated 2026-07-31] exact-cell
round): the verdict's central finding — "`siteCellEvent` is keyed only by `es` and
`c` … For two co-realized sibling sites with the same `parentSt`, `state_cell`
forces their exact cells—and hence state events—to coincide whenever they share a
fiber witness … the carrier still lacks the site/branch/frame index needed to
represent distinct sibling reads" — is repaired by THE SITE-ENTRANCE KEYING
(adjudicated fix: the branch taken is part of the child site's entrance datum —
the note's recursion has each child recurse FROM the joint cell WITH its member
index, MOVES 7503–7515): `CellData` gains the member-keyed site read
`branchCellOf es ν` (with the joint-factoring law `branch_cell_joint`), and
`siteCellEvent es ν c` is Ψ_s^{−1}(c) over the entrance with Ψ_s the SITE's own
read map (MOVES 7448–7449) — sibling sites key different maps, so distinct pins
no longer collide (`f1_two_leaf_discharge` below, the displayed check). The
verdict's second material finding — the `SibCountAt` c/cSplit two-keying ("an
arbitrary split-cell roster can be attached to an unrelated exact conditioning
cell") — is repaired by the ONE-CELL form: conditioning and roster both key the
site's own `L.cellAt H`, tied to the scaffold frame by the new
`TreeScaffold.hframe_cell`. `hjcm` stays CONSUMED at multi-side sites in
`cone_charge` (T-E6's `presents_imply_jcMultiAt` records that the ledger's
presented faces already imply it). The global `SibCount` serves the root step
through T-E5 unchanged.

THE F1 ALL-SITES SATISFIABILITY COMPUTATION, RE-RUN UNDER THE SITE-ENTRANCE
KEYING. Censused integers VERBATIM (CASE_SIB P2/P3, MOVES 7516–7528; B22 slice of
5²² boxes, n = 4):
* head site H₀ (10-pin window read): stateEvent(H₀) = the 14-pin Σ_c, N = 5⁸;
  entrance = the 4-pin reduction cell, N = 5¹⁸. Per-site row: 5⁸ · 5¹⁰ = 5¹⁸ ✓.
* leaf site b₁ (RAM read, ONE fresh digit): stateEvent(b₁) = Σ_c ∩ S₁, N = 5⁷ =
  78,125; entrance = stateEvent(H₀) = 5⁸. Row: 5⁷ · 5¹ = 5⁸ ✓.
* leaf site b₂: N(Σ_c ∩ S₂) = 5⁷; row: 5⁷ · 5¹ = 5⁸ ✓ — S₁ ≠ S₂ (distinct pins,
  neither contains the other) is CONSISTENT under the re-key: S₁ is the exact
  fiber of Ψ_{b₁} = `branchCellOf (.st H₀) b₁` (b₁'s own RAM-digit read) at
  cellAt(b₁), S₂ the exact fiber of the DIFFERENT map Ψ_{b₂} at cellAt(b₂) — two
  fibers of two reads, not two values of one cell function; both factor through
  the parent's joint (d₁, d₂) read (`branch_cell_joint`). The forcing is
  structurally dead — the displayed check is `f1_two_leaf_discharge` below.
* site-level (SIB) at H₀ (the hsibT row): N(S₁∩S₂∩Σ_c)·N(Σ_c) = 5⁶·5⁸ = 5⁷·5⁷ =
  N(S₁∩Σ_c)·N(S₂∩Σ_c) ✓ (P3's censused identity, EXACT).
* the whole tree: fiber = Σ_c ∩ S₁ ∩ S₂, N = 5⁶; exponent n + Σ siteExp =
  4 + (10 + 1 + 1) = 16; 5⁶ · 5¹⁶ = 5²² ✓ — every site charged exactly once.

STATEMENT RE-KEY RECORD (adjudication-warranted): `CA` is the FULL `CellAssign`
(T-E5's interface — the root step fires E5, which consumes it); `hjcm` keys the
per-site `JCmultiAt` at the site's own node `H.lastNode`; `hsibT` carries the
ONE-CELL `SibCountAt` at `(parentSt H, H.lastNode, cellAt H)`; `hdet` kept (the
(NS) exclusion, 7457–7461). PROOF STATUS: assembled below — root = T-E5 (inherits
the fenced `hnostray` sorryAx, disclosed in E5's header), unbranched/leaf/split
steps = T-E6 + the frame clauses (incl. the new `hframe_cell` one-cell tie) +
`hsibT` via the cone recursion (`cone_charge`). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-! ## The bracketed shared-split forcing (HISTORICAL RECORD)

The two lemmas below were PROVED Lean-core on 2026-07-29 against the E-PHASE keying
of `state_cell` (`stateEvent T (some H) = cellEventE T CA χ (parentSt H) (cellAt H)`,
guarded `sides H = 1`): under that keying, two sibling one-side sites are forced to
share `cellAt`, have EQUAL state events, and carry EQUAL `siteExp` — contradicting
F1's distinct censused leaf pins. Codex verdict 2026-07-29 (fresh context): CLAIM A
CONFIRMED, CLAIM C CONFIRMED conditional on the census reading — full charge +
verdict archived at `lean/notes/E8_BLOCK_CHARGE_2026-07-29.md`. STATUS AFTER THE T
RE-RATIFICATION (2026-08-01, the site-entrance keying): the forcing is
STRUCTURALLY DEAD — the 2026-07-29 [date corrected 2026-07-30; original record
mis-dated 2026-07-31] exact-cell keying (Ψ shared across siblings)
that made it a machine-checked instance-level obstruction is superseded: sibling
sites now key DIFFERENT read maps (`branchCellOf es ν₁` vs `branchCellOf es ν₂`),
so the forcing proofs below no longer typecheck (their pivot — "cellOf es is a
function" applied to BOTH siblings' cells — has no analogue), and the F1 two-leaf
configuration is exhibited SATISFIABLE at the event level by
`f1_two_leaf_discharge` below. Bracketed verbatim for the record (statement forms
of the RETIRED keyings; not restatable in the current vocabulary):

```
theorem shared_split_state_forced (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (hreal : Realizes T χ Tr)
    (H₁ H₂ : History p F) (h1 : H₁ ∈ Tr.chains) (h2 : H₂ ∈ Tr.chains)
    (hp : L.parentSt H₁ = L.parentSt H₂)
    (hs1 : L.sides H₁ = 1) (hs2 : L.sides H₂ = 1) :
    L.cellAt H₁ = L.cellAt H₂ ∧ stateEvent T (some H₁) = stateEvent T (some H₂)
-- proof: hreal's fiber witness lies in both state events; the OLD state_cell
-- rewrote both into cell events at the SAME entrance; cellOf es is a function.

theorem shared_split_siteExp_forced (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (hreal : Realizes T χ Tr)
    (H₁ H₂ : History p F) (h1 : H₁ ∈ Tr.chains) (h2 : H₂ ∈ Tr.chains)
    (hp : L.parentSt H₁ = L.parentSt H₂)
    (hs1 : L.sides H₁ = 1) (hs2 : L.sides H₂ = 1) :
    L.siteExp H₁ = L.siteExp H₂
-- proof: T-E6 at both siblings with E = univ, cancellation, pow-injectivity.
```
-/

section F1TwoLeafDischarge

/-! ## The F1 two-leaf discharge — THE DISPLAYED CHECK (2026-08-01 re-ratification
repair): under the site-entrance keying, the F1 configuration (two co-realized
sibling leaf sites with DISTINCT pins v₁ = 1, v₂ = 2 — CASE_SIB P2/P3, MOVES
7516–7528) is satisfiable at the event level. The two leaf digits (the census's
d₁/d₂) are modeled as the two coordinates of a `ZMod 5` pair-slice; each site's
read map is ITS OWN coordinate projection — the `branchCellOf es νⱼ` genre —
and both factor through the parent's joint (d₁, d₂) read (`branch_cell_joint`'s
shape). Distinct pins now give DISTINCT, OVERLAPPING exact-fiber events — exactly
what the retired shared-map keying refuted (`shared_read_forces` below is the
retired forcing's abstract content, confined to the shared-map hypothesis the
re-key removed). -/

private def f1rd₁ (x : Fin 2 → ZMod 5) : ZMod 5 := x 0
private def f1rd₂ (x : Fin 2 → ZMod 5) : ZMod 5 := x 1
private def f1joint (x : Fin 2 → ZMod 5) : ZMod 5 × ZMod 5 := (x 0, x 1)

/-- **distinct pins ⟹ distinct entrance events, coherently co-realized** — the F1
check: (i) the two sites' exact-fiber events at the censused pins v₁ = 1, v₂ = 2
are DISTINCT; (ii) they SHARE a fiber witness (co-realization — the point with
d₁ = 1, d₂ = 2, the censused 5⁶-slice's genre); (iii) each site read factors
through the parent's joint read (the `branch_cell_joint` law's shape). Under the
retired keying (one read map for both siblings), (i) ∧ (ii) was REFUTABLE
(`shared_read_forces`); under the site-entrance keying all three hold at once. -/
theorem f1_two_leaf_discharge :
    ({x | f1rd₁ x = 1} ≠ {x : Fin 2 → ZMod 5 | f1rd₂ x = 2}) ∧
    (∃ x : Fin 2 → ZMod 5, f1rd₁ x = 1 ∧ f1rd₂ x = 2) ∧
    (∀ x y, f1joint x = f1joint y → f1rd₁ x = f1rd₁ y ∧ f1rd₂ x = f1rd₂ y) := by
  refine ⟨?_, ⟨![1, 2], rfl, rfl⟩, ?_⟩
  · intro h
    have h1 : (![1, 0] : Fin 2 → ZMod 5) ∈ {x | f1rd₁ x = 1} := rfl
    rw [h] at h1
    have h0 : (0 : ZMod 5) = 2 := h1
    exact absurd h0 (by decide)
  · intro x y h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- the retired forcing's abstract content, quarantined to its real hypothesis:
ONE shared read map's exact fibers sharing a witness are forced equal (this is
the whole engine of `shared_split_state_forced`). The site-entrance keying denies
the hypothesis at sibling sites — Ψ_{b₁} ≠ Ψ_{b₂} — so nothing forces
`stateEvent(b₁) = stateEvent(b₂)`. -/
theorem shared_read_forces {α β : Type*} (rd : α → β) (c₁ c₂ : β) (x : α)
    (h₁ : rd x = c₁) (h₂ : rd x = c₂) :
    c₁ = c₂ ∧ {y | rd y = c₁} = {y | rd y = c₂} :=
  ⟨h₁.symm.trans h₂, by rw [h₁.symm.trans h₂]⟩

end F1TwoLeafDischarge

section AssemblyKit

/-- nodes determine a `History` (proof-irrelevant remaining fields). -/
private theorem hist_ext' {A B : History p F} (h : A.nodes = B.nodes) : A = B := by
  cases A; cases B; simp only at h; subst h; rfl

/-- a chain of length ≥ 2 has ledger entrance `.st` of its (unique) immediate prefix —
`hparent`'s `.red` leg forces length 1, and equal-length list prefixes coincide. -/
theorem parentSt_of_deep (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) (H₀ H : History p F) (hH : H ∈ Tr.chains)
    (hpre : H₀.IsPrefixOf H) (hlen : H₀.nodes.length + 1 = H.nodes.length) :
    L.parentSt H = .st H₀ := by
  have hp := L.hparent H hH
  cases hps : L.parentSt H with
  | amb => rw [hps] at hp; exact hp.elim
  | red g ψ =>
    rw [hps] at hp
    have := H₀.nonempty
    have h0 : 0 < H₀.nodes.length := List.length_pos_iff.mpr this
    omega
  | st H' =>
    rw [hps] at hp
    obtain ⟨hpre', hlen', -⟩ := hp
    congr 1
    apply hist_ext'
    have e1 : H'.nodes = H.nodes.take H'.nodes.length := List.prefix_iff_eq_take.mp hpre'
    have e2 : H₀.nodes = H.nodes.take H₀.nodes.length := List.prefix_iff_eq_take.mp hpre
    have hl : H'.nodes.length = H₀.nodes.length := by omega
    rw [e1, e2, hl]

/-- `[ν]` is a list prefix iff the head is `ν`. -/
private lemma singleton_prefix_iff' {α : Type*} (ν : α) (l : List α) :
    [ν] <+: l ↔ l.head? = some ν := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    rfl
  · intro h
    cases l with
    | nil => exact absurd h (by simp)
    | cons a t =>
      obtain rfl : a = ν := by simpa using h
      exact ⟨t, rfl⟩

/-- the (CLOSED) CONE of a chain — the tree's chains extending it; the recursion's
exponent carrier ("the fiber mass of the strictly smaller tree T_j", MOVES 7513). -/
private noncomputable def coneF (Tr : VTree p F) (H : History p F) :
    Finset (History p F) :=
  (Tr.hfin.subset
    (show {H' | H' ∈ Tr.chains ∧ H.IsPrefixOf H'} ⊆ Tr.chains from
      fun _ h => h.1)).toFinset

private lemma coneF_mem {Tr : VTree p F} {H H' : History p F} :
    H' ∈ coneF Tr H ↔ H' ∈ Tr.chains ∧ H.IsPrefixOf H' :=
  Set.Finite.mem_toFinset _

/-- the SUBTREE-FIBER event strictly below a site (the frame's `scope` value). -/
private def SFset (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (trackOf : Node p F → Polynomial (ZMod p)) (H : History p F) : Set (Box p m) :=
  {x | SubtreeFiber T trackOf (EntSt.st H : EntSt p F n)
      {H' | H' ∈ Tr.chains ∧ belowEnt trackOf (EntSt.st H : EntSt p F n) H'}
      Tr.leafV Tr.nsLeaf x}

private lemma childHist_nodes (H : History p F) (ν : Node p F)
    (hν : ChildRoot (some H) ν) :
    (childHist (some H) ν hν).nodes = H.nodes ++ [ν] := rfl

private lemma prefix_childHist (H : History p F) (ν : Node p F)
    (hν : ChildRoot (some H) ν) : H.IsPrefixOf (childHist (some H) ν hν) :=
  ⟨[ν], rfl⟩

private lemma childHist_length (H : History p F) (ν : Node p F)
    (hν : ChildRoot (some H) ν) :
    (childHist (some H) ν hν).nodes.length = H.nodes.length + 1 := by
  rw [childHist_nodes]; simp

private lemma not_child_prefix_parent (H : History p F) (ν : Node p F)
    (hν : ChildRoot (some H) ν) : ¬ (childHist (some H) ν hν).IsPrefixOf H := by
  intro h
  have h1 := List.IsPrefix.length_le h
  rw [childHist_nodes] at h1
  simp at h1

/-- two roster children heading the SAME extension coincide (equal-length prefixes). -/
private lemma childHist_prefix_unique {H H' : History p F} {ν ν' : Node p F}
    (hν : ChildRoot (some H) ν) (hν' : ChildRoot (some H) ν')
    (h1 : (childHist (some H) ν hν).IsPrefixOf H')
    (h2 : (childHist (some H) ν' hν').IsPrefixOf H') : ν = ν' := by
  have e1 : (childHist (some H) ν hν).nodes
      = H'.nodes.take (childHist (some H) ν hν).nodes.length :=
    List.prefix_iff_eq_take.mp h1
  have e2 : (childHist (some H) ν' hν').nodes
      = H'.nodes.take (childHist (some H) ν' hν').nodes.length :=
    List.prefix_iff_eq_take.mp h2
  rw [childHist_nodes] at e1 e2
  have hlen : (H.nodes ++ [ν]).length = (H.nodes ++ [ν']).length := by simp
  have : H.nodes ++ [ν] = H.nodes ++ [ν'] := by rw [e1, e2, hlen]
  simpa using this

/-- children's cones sit strictly inside the parent's cone. -/
private lemma coneF_card_lt (Tr : VTree p F) (H : History p F) (hH : H ∈ Tr.chains)
    (ν : Node p F) (hν : ChildRoot (some H) ν) :
    (coneF Tr (childHist (some H) ν hν)).card < (coneF Tr H).card := by
  apply Finset.card_lt_card
  constructor
  · intro H' hmem
    obtain ⟨h1, h2⟩ := coneF_mem.mp hmem
    exact coneF_mem.mpr ⟨h1, List.IsPrefix.trans (prefix_childHist H ν hν) h2⟩
  · intro hsub
    have hHH : H ∈ coneF Tr H := coneF_mem.mpr ⟨hH, List.prefix_refl _⟩
    exact not_child_prefix_parent H ν hν (coneF_mem.mp (hsub hHH)).2

end AssemblyKit

open Classical in
/-- **THE CONE CHARGE** — the per-site recursion of the ratified assembly: for
every chain H, the count of (H's state ∩ the subtree fiber strictly below H) prices
`p^{Σ_{H' ∈ cone(H)} siteExp H'}` against H's ENTRANCE event — every site of the cone
charged exactly once (MOVES 7454–7456). Strong induction on the cone's card: the
frame's `hdecomp`/`hscope` decompose the subtree fiber over the frame's own roster;
`hsibT` (site-level (SIB) at the exact Σ_c, converted to the state event by the
`state_cell` scaffold law, guarded k ≥ 2) factorizes the children; `hglue` (REL.2's
identification, 7511–7513) hands each realized child's factor to its own strictly
smaller cone; `hcover` accounts the cone partition; the site's own read is charged
by the `hjcm` row at MULTI-SIDE sites ((JC-multi), the note's declared OPEN
conditionality, MOVES 7473–7483 — CONSUMED, per the T-ratification verdict §4) and
by T-E6 at one-side sites ((JC-single) genre, 7469–7472; "unbranched segments never
consume (JC-multi)", 7482–7483). -/
private theorem cone_charge (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p))
    (L : SiteLedger Tr T CA χ) (sc : TreeScaffold Tr T CA χ L trackOf)
    (hreal : Realizes T χ Tr)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S) :
    ∀ (k : ℕ) (H : History p F) (hH : H ∈ Tr.chains), (coneF Tr H).card ≤ k →
      Nat.card ↥(stateEvent T (some H) ∩ SFset Tr T trackOf H)
          * p ^ (∑ H' ∈ coneF Tr H, L.siteExp H')
        = Nat.card ↥(entEvent T χ (L.parentSt H)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro H hH hcard
  classical
  obtain ⟨x₀, hx₀⟩ := hreal
  have hx₀st : ∀ K ∈ Tr.chains, x₀ ∈ stateEvent T (some K) :=
    fun K hK => ((hx₀.1 K).mp hK).2.1
  obtain ⟨hes, hje⟩ := sc.hframe H hH
  -- ==== the frame decomposition: state ∩ SF = state ∩ ⋂_{roster} S ν ====
  have hdec : stateEvent T (some H) ∩ SFset Tr T trackOf H
      = stateEvent T (some H)
        ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν := by
    have h0 := (sc.splitFrame H hH).hdecomp
    rw [hes, sc.hscope H hH] at h0
    have hent : entEvent T χ (EntSt.st H : EntSt p F n) = stateEvent T (some H) := rfl
    rw [hent] at h0
    calc stateEvent T (some H) ∩ SFset Tr T trackOf H
        = SFset Tr T trackOf H ∩ stateEvent T (some H) := Set.inter_comm _ _
      _ = _ := h0
  -- ==== the realized-children roster J + the per-child choice data ====
  set J := (CA.branchSetOf (sc.splitFrame H hH).c).filter
    (fun ν => (sc.splitFrame H hH).S ν ≠ Set.univ) with hJdef
  have hpc : ∀ ν : {ν // ν ∈ J}, ∃ hν : ChildRoot (some H) ν.1,
      childHist (some H) ν.1 hν ∈ Tr.chains ∧
      (sc.splitFrame H hH).S ν.1
        = {x | ContFiber T (some H) ν.1 hν
            {H' | H' ∈ Tr.chains ∧ (childHist (some H) ν.1 hν).IsPrefixOf H'}
            Tr.leafV Tr.nsLeaf x} := by
    rintro ⟨ν, hνJ⟩
    have hνR : ν ∈ CA.branchSetOf (sc.splitFrame H hH).c := (Finset.mem_filter.mp hνJ).1
    have hne : (sc.splitFrame H hH).S ν ≠ Set.univ := (Finset.mem_filter.mp hνJ).2
    rcases sc.subtree_part H hH ν hνR with h | h
    · exact absurd h hne
    · exact h
  choose hcrJ hmemJ hSJ using hpc
  set child : {ν // ν ∈ J} → History p F :=
    fun ν => childHist (some H) ν.1 (hcrJ ν) with hchilddef
  -- ==== per realized child: the IH factor ====
  have hstep : ∀ ν : {ν // ν ∈ J},
      Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν.1)
          * p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H')
        = Nat.card ↥(stateEvent T (some H)) := by
    intro ν
    have hglue := sc.hglue H hH ν.1 (hcrJ ν) (hmemJ ν)
    have hSν : stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν.1
        = stateEvent T (some (child ν)) ∩ SFset Tr T trackOf (child ν) := by
      rw [hSJ ν, hglue]
      apply Set.inter_eq_right.mpr
      intro x hx
      exact mem_of_prefix T x (child ν).nodes (child ν) rfl hx.1 H
        (prefix_childHist H ν.1 (hcrJ ν))
    have hlt : (coneF Tr (child ν)).card < k :=
      lt_of_lt_of_le (coneF_card_lt Tr H hH ν.1 (hcrJ ν)) hcard
    have hIH := IH (coneF Tr (child ν)).card hlt (child ν) (hmemJ ν) le_rfl
    have hps : L.parentSt (child ν) = .st H :=
      parentSt_of_deep Tr T CA χ L H (child ν) (hmemJ ν)
        (prefix_childHist H ν.1 (hcrJ ν)) (childHist_length H ν.1 (hcrJ ν)).symm
    rw [hps] at hIH
    have hent : entEvent T χ (EntSt.st H : EntSt p F n) = stateEvent T (some H) := rfl
    rw [hent] at hIH
    rw [hSν]
    exact hIH
  -- ==== the cone partition: cone(H) = {H} ⊔ ⨆_{ν ∈ J} cone(child ν) ====
  have hconeq : coneF Tr H
      = insert H (J.attach.biUnion (fun ν => coneF Tr (child ν))) := by
    ext H'
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists]
    constructor
    · intro hmem
      obtain ⟨h1, h2⟩ := coneF_mem.mp hmem
      rcases eq_or_ne H' H with rfl | hne
      · exact Or.inl rfl
      · right
        obtain ⟨ν, hνR, hν, hpre, hSne⟩ := sc.hcover H hH H' h1 h2 (Ne.symm hne)
        have hνJ : ν ∈ J := Finset.mem_filter.mpr ⟨hνR, hSne⟩
        refine ⟨ν, hνJ, coneF_mem.mpr ⟨h1, ?_⟩⟩
        have hce : child ⟨ν, hνJ⟩ = childHist (some H) ν hν := hist_ext' rfl
        rw [hce]
        exact hpre
    · intro h
      rcases h with rfl | ⟨ν, hνJ, hmem⟩
      · exact coneF_mem.mpr ⟨hH, List.prefix_refl _⟩
      · obtain ⟨h1, h2⟩ := coneF_mem.mp hmem
        exact coneF_mem.mpr
          ⟨h1, List.IsPrefix.trans (prefix_childHist H ν (hcrJ ⟨ν, hνJ⟩)) h2⟩
  have hHnot : H ∉ J.attach.biUnion (fun ν => coneF Tr (child ν)) := by
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
      not_exists]
    intro ν hνJ hmem
    exact not_child_prefix_parent H ν (hcrJ ⟨ν, hνJ⟩) (coneF_mem.mp hmem).2
  have hdisj : ∀ ν₁ ∈ J.attach, ∀ ν₂ ∈ J.attach, ν₁ ≠ ν₂ →
      Disjoint (coneF Tr (child ν₁)) (coneF Tr (child ν₂)) := by
    intro ν₁ _ ν₂ _ hne
    rw [Finset.disjoint_left]
    intro H' h1 h2
    apply hne
    apply Subtype.ext
    exact childHist_prefix_unique (hcrJ ν₁) (hcrJ ν₂)
      (coneF_mem.mp h1).2 (coneF_mem.mp h2).2
  have hsum : ∑ H' ∈ coneF Tr H, L.siteExp H'
      = L.siteExp H
        + ∑ ν ∈ J.attach, ∑ H' ∈ coneF Tr (child ν), L.siteExp H' := by
    rw [hconeq, Finset.sum_insert hHnot, Finset.sum_biUnion hdisj]
  -- ==== positivity ====
  haveI : Finite ↥(stateEvent T (some H)) := (Set.toFinite _).to_subtype
  have hBpos : 0 < Nat.card ↥(stateEvent T (some H)) :=
    Nat.card_pos_iff.mpr ⟨⟨x₀, hx₀st H hH⟩, inferInstance⟩
  -- ==== (★): the roster factorization prices the strict cone ====
  have hstar : Nat.card ↥(stateEvent T (some H)
        ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
      * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H')
      = Nat.card ↥(stateEvent T (some H)) := by
    rcases Nat.lt_or_ge (CA.branchSetOf (sc.splitFrame H hH).c).card 2 with hk | hk
    · -- k ≤ 1: no (SIB) consumed
      by_cases hk0 : (CA.branchSetOf (sc.splitFrame H hH).c).card = 0
      · -- k = 0: empty roster, empty J, trivial intersection
        have hR : CA.branchSetOf (sc.splitFrame H hH).c = ∅ := Finset.card_eq_zero.mp hk0
        have hJ0 : J = ∅ := by rw [hJdef, hR]; rfl
        have hattach : J.attach = ∅ := by rw [hJ0]; rfl
        rw [hR, hattach]
        simp
      · -- k = 1: singleton roster
        obtain ⟨ν₀, hR⟩ : ∃ a, CA.branchSetOf (sc.splitFrame H hH).c = {a} :=
          Finset.card_eq_one.mp (by omega)
        by_cases hν₀J : ν₀ ∈ J
        · have hJ1 : J = {ν₀} := by
            apply Finset.Subset.antisymm
            · intro ν hν
              have := (Finset.mem_filter.mp hν).1
              rw [hR] at this
              exact this
            · intro ν hν
              rw [Finset.mem_singleton] at hν
              subst hν
              exact hν₀J
          have hIcap : (⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
              = (sc.splitFrame H hH).S ν₀ := by
            rw [hR]; simp
          rw [hIcap]
          have hsingle : ∀ ν : {ν // ν ∈ J}, ν = ⟨ν₀, hν₀J⟩ := by
            rintro ⟨ν, hν⟩
            apply Subtype.ext
            have hm := hν
            rw [hJ1, Finset.mem_singleton] at hm
            exact hm
          have hattach : J.attach = {(⟨ν₀, hν₀J⟩ : {ν // ν ∈ J})} :=
            Finset.eq_singleton_iff_unique_mem.mpr
              ⟨Finset.mem_attach _ _, fun x _ => hsingle x⟩
          rw [hattach, Finset.prod_singleton]
          exact hstep ⟨ν₀, hν₀J⟩
        · -- the single branch is a univ prescription
          have hSuniv : (sc.splitFrame H hH).S ν₀ = Set.univ := by
            by_contra hne
            exact hν₀J (Finset.mem_filter.mpr ⟨by rw [hR]; simp, hne⟩)
          have hJ0 : J = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro ν hν
            have h1 := (Finset.mem_filter.mp hν).1
            rw [hR, Finset.mem_singleton] at h1
            subst h1
            exact (Finset.mem_filter.mp hν).2 hSuniv
          have hattach : J.attach = ∅ := by rw [hJ0]; rfl
          have hIcap : (⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
              = Set.univ := by
            rw [hR]; simp [hSuniv]
          rw [hIcap, hattach]
          simp
    · -- k ≥ 2: the ONE-CELL site-level (SIB) row at the exact Σ_c under the site's
      -- own read map, converted to the state event by the `state_cell` scaffold law;
      -- the roster cell is the SAME cell via the scaffold's `hframe_cell` tie
      -- (the 2026-08-01 c/cSplit unification)
      have hSIB : Nat.card ↥(stateEvent T (some H)
            ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
          * (Nat.card ↥(stateEvent T (some H)))
              ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1)
          = ∏ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c,
              Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν) := by
        have hfc := sc.hframe_cell H hH
        have hk' : 2 ≤ (CA.branchSetOf (L.cellAt H)).card := hfc ▸ hk
        have h := hsibT H hH hk'
        unfold SibCountAt at h
        rwa [← L.state_cell H hH, ← hfc] at h
      -- split the roster product over J and its complement
      have hJsub : J ⊆ CA.branchSetOf (sc.splitFrame H hH).c := Finset.filter_subset _ _
      have hprod : ∏ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c,
          Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν)
          = (∏ ν ∈ J,
              Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν))
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - J.card) := by
        rw [← Finset.prod_sdiff hJsub]
        have hrest : ∏ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c \ J,
            Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν)
            = (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - J.card) := by
          have hstepu : ∀ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c \ J,
              Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν)
                = Nat.card ↥(stateEvent T (some H)) := by
            intro ν hν
            obtain ⟨hνR, hνnJ⟩ := Finset.mem_sdiff.mp hν
            have hSuniv : (sc.splitFrame H hH).S ν = Set.univ := by
              by_contra hne
              exact hνnJ (Finset.mem_filter.mpr ⟨hνR, hne⟩)
            rw [hSuniv, Set.inter_univ]
          rw [Finset.prod_congr rfl hstepu, Finset.prod_const, Finset.card_sdiff,
            Finset.inter_eq_left.mpr hJsub]
        rw [hrest, mul_comm]
      -- the J-product with the cone prices = B^{|J|}
      have hJprod : (∏ ν ∈ J,
            Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν))
          * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H')
          = (Nat.card ↥(stateEvent T (some H))) ^ J.card := by
        rw [← Finset.prod_attach J (fun ν =>
          Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν))]
        rw [← Finset.prod_mul_distrib]
        rw [Finset.prod_congr rfl (fun ν _ => hstep ν), Finset.prod_const,
          Finset.card_attach]
      -- assemble and cancel B^{k-1}
      refine Nat.eq_of_mul_eq_mul_right
        (pow_pos hBpos ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1)) ?_
      have hcard1 : (CA.branchSetOf (sc.splitFrame H hH).c).card - J.card + J.card
          = (CA.branchSetOf (sc.splitFrame H hH).c).card :=
        Nat.sub_add_cancel (Finset.card_le_card hJsub)
      calc Nat.card ↥(stateEvent T (some H)
              ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
            * (∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H'))
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1)
          = (Nat.card ↥(stateEvent T (some H)
              ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1))
            * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H') := by
              ring
        _ = (∏ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c,
              Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν))
            * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H') := by
              rw [hSIB]
        _ = ((∏ ν ∈ J,
              Nat.card ↥(stateEvent T (some H) ∩ (sc.splitFrame H hH).S ν))
            * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H'))
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - J.card) := by
              rw [hprod]; ring
        _ = (Nat.card ↥(stateEvent T (some H))) ^ J.card
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - J.card) := by
              rw [hJprod]
        _ = (Nat.card ↥(stateEvent T (some H)))
              ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card) := by
              rw [← pow_add]
              congr 1
              omega
        _ = Nat.card ↥(stateEvent T (some H))
            * (Nat.card ↥(stateEvent T (some H)))
                ^ ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1) := by
              conv_lhs => rw [show (CA.branchSetOf (sc.splitFrame H hH).c).card
                = 1 + ((CA.branchSetOf (sc.splitFrame H hH).c).card - 1) by omega]
              rw [pow_add, pow_one]
  -- ==== the site's own charge: `hjcm` CONSUMED at multi-side sites ((JC-multi),
  -- the note's declared OPEN conditionality, MOVES 7473–7483 — converted by the
  -- `state_cell` tie + the side-union exponent tie `hsplit_exp`); T-E6 at one-side
  -- sites ((JC-single) genre; "unbranched segments never consume (JC-multi)") ====
  have hE6 : Nat.card ↥(stateEvent T (some H)) * p ^ L.siteExp H
      = Nat.card ↥(entEvent T χ (L.parentSt H)) := by
    by_cases h2 : 2 ≤ L.sides H
    · have hj : Nat.card ↥(siteCellEvent T CA χ (L.parentSt H) H.lastNode (L.cellAt H))
          * p ^ (∑ j : Fin (L.splitAt H hH h2).k, (L.splitAt H hH h2).sideExp j)
          = Nat.card ↥(entEvent T χ (L.parentSt H)) := hjcm H ⟨hH, h2⟩ h2
      rwa [L.hsplit_exp H hH h2, ← L.state_cell H hH] at hj
    · have hspec : SpectatorFor (L.freshCoords H) (Set.univ : Set (Box p m)) := by
        intro x x' _; simp
      have h := fiber_seg_step T CA Tr χ L H hH Set.univ hspec
      rwa [Set.inter_univ, Set.inter_univ] at h
  -- ==== compose ====
  calc Nat.card ↥(stateEvent T (some H) ∩ SFset Tr T trackOf H)
        * p ^ (∑ H' ∈ coneF Tr H, L.siteExp H')
      = Nat.card ↥(stateEvent T (some H)
          ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
        * (p ^ L.siteExp H
          * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H')) := by
        rw [hdec, hsum, pow_add]
        congr 1
        rw [Finset.prod_pow_eq_pow_sum]
    _ = (Nat.card ↥(stateEvent T (some H)
          ∩ ⋂ ν ∈ CA.branchSetOf (sc.splitFrame H hH).c, (sc.splitFrame H hH).S ν)
        * ∏ ν ∈ J.attach, p ^ (∑ H' ∈ coneF Tr (child ν), L.siteExp H'))
        * p ^ L.siteExp H := by ring
    _ = Nat.card ↥(stateEvent T (some H)) * p ^ L.siteExp H := by rw [hstar]
    _ = Nat.card ↥(entEvent T χ (L.parentSt H)) := hE6

/-- **T-E8, TREE-EXP** (MOVES 7449–7456): μ{f : T_can^τ(f) = T} = ∏_{sites} jvol —
every site charged exactly once, the ROOT INCLUDED — assembled from T-E5 (the root
clause) and the cone recursion
(`cone_charge`) over the adjudicated per-site row. Statement re-key record in the
file header. [QUEUE ITEM 5 (E5 hoist ripple 1, TV-A3 shape) 2026-07-31: gains the
∀-g (U)∧(R) row `hUR` (appended last), consumed at the internal `fiber_root_split`
call at the scaffold's root datum `sc.g`; the former inherited E5 sorryAx is GONE —
Lean-core footprint.] -/
theorem treeExp (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf)
    (hχ : Function.Injective χ) (hrc : RootCellsOf T CA.toCellData χ)
    (hred : RedCellPartition T CA.toCellData χ trackOf)
    (hsib : SibCount T CA.toCellData χ) (hreal : Realizes T χ Tr)
    (L : SiteLedger Tr T CA.toCellData χ)
    (sc : TreeScaffold Tr T CA.toCellData χ L trackOf)
    (hjcm : ∀ H (hH : H ∈ multiSites Tr T CA.toCellData χ L) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.splitAt H hH.1 h2))
    (hsibT : ∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S)
    (hdet : ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H)
    (hUR : ∀ g : Fin n → ZMod p,
      TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) :
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
      = p ^ m := by
  classical
  obtain ⟨x₀, hx₀⟩ := hreal
  -- ==== the root clause (T-E5 at the scaffold's own root data; the (U)∧(R)
  -- row fired at sc.g — the item-5 hoist threading, TV-A3) ====
  have hE5 := fiber_root_split Tr T χ trackOf CA hχ hrc hred hsib
    ⟨x₀, hx₀⟩ sc.g sc.root sc.hcr sc.hg (hUR sc.g).1 (hUR sc.g).2
  -- ==== the track groups are the head cones ====
  have hheadmem : ∀ i, oneNode (sc.root.headOf i) (sc.hcr i) ∈ Tr.chains := by
    intro i
    obtain ⟨h, hm⟩ := sc.root.hcov i
    exact hm
  have htc : ∀ i, sc.root.trackChains i
      = {H' | H' ∈ Tr.chains
          ∧ (oneNode (sc.root.headOf i) (sc.hcr i)).IsPrefixOf H'} := by
    intro i
    ext H'
    constructor
    · intro hmem
      have h1 : H' ∈ Tr.chains := by
        rw [← sc.root.hpart.1]
        exact Set.mem_iUnion.mpr ⟨i, hmem⟩
      exact ⟨h1, (singleton_prefix_iff' _ _).mpr (sc.root.hhead i H' hmem)⟩
    · rintro ⟨h1, h2⟩
      have hhd : H'.nodes.head? = some (sc.root.headOf i) :=
        (singleton_prefix_iff' _ _).mp h2
      have h1' : H' ∈ ⋃ j, sc.root.trackChains j := by
        rw [sc.root.hpart.1]; exact h1
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h1'
      have hh := sc.root.hhead j H' hj
      rw [hhd] at hh
      have hij : i = j := sc.root.hinj (Option.some.inj hh)
      rw [hij]
      exact hj
  -- ==== each track factor prices its head cone (glue + cone_charge) ====
  have htrack : ∀ i,
      Nat.card ↥(rootCell χ sc.g ∩ trackEvent Tr T sc.root i (sc.hcr i))
        * p ^ (∑ H' ∈ coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)),
            L.siteExp H')
      = Nat.card ↥(rootCell χ sc.g) := by
    intro i
    have hone_len : (oneNode (sc.root.headOf i) (sc.hcr i)).nodes.length = 1 := rfl
    have htev : rootCell χ sc.g ∩ trackEvent Tr T sc.root i (sc.hcr i)
        = stateEvent T (some (oneNode (sc.root.headOf i) (sc.hcr i)))
          ∩ SFset Tr T trackOf (oneNode (sc.root.headOf i) (sc.hcr i)) := by
      have h1 : trackEvent Tr T sc.root i (sc.hcr i)
          = stateEvent T (some (oneNode (sc.root.headOf i) (sc.hcr i)))
            ∩ SFset Tr T trackOf (oneNode (sc.root.headOf i) (sc.hcr i)) := by
        show {x | SubFiber T (sc.root.trackChains i) (sc.root.headOf i) (sc.hcr i)
            Tr.leafV Tr.nsLeaf x} = _
        rw [htc i]
        exact sc.hglue_root (sc.root.headOf i) (sc.hcr i) (hheadmem i)
      rw [h1]
      apply Set.inter_eq_right.mpr
      intro x hx
      have hxs := hx.1
      rw [L.state_cell _ (hheadmem i), sc.hent_root _ (hheadmem i) hone_len] at hxs
      exact hxs.1
    rw [htev]
    have hcc := cone_charge Tr T CA.toCellData χ trackOf L sc ⟨x₀, hx₀⟩ hjcm hsibT
      (coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i))).card
      (oneNode (sc.root.headOf i) (sc.hcr i)) (hheadmem i) le_rfl
    rwa [sc.hent_root _ (hheadmem i) hone_len] at hcc
  -- ==== the chain sum splits over the head cones ====
  have hdisjT : ∀ i ∈ (Finset.univ : Finset (Fin sc.root.t)), ∀ j ∈ Finset.univ,
      i ≠ j →
      Disjoint (coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)))
        (coneF Tr (oneNode (sc.root.headOf j) (sc.hcr j))) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro H' h1 h2
    have hm1 : H' ∈ sc.root.trackChains i := by
      rw [htc i]; exact coneF_mem.mp h1
    have hm2 : H' ∈ sc.root.trackChains j := by
      rw [htc j]; exact coneF_mem.mp h2
    exact Set.disjoint_left.mp (sc.root.hpart.2 hij) hm1 hm2
  have hchainsum : ∑ H' ∈ Tr.hfin.toFinset, L.siteExp H'
      = ∑ i : Fin sc.root.t,
          ∑ H' ∈ coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)),
            L.siteExp H' := by
    have hset : Tr.hfin.toFinset
        = Finset.biUnion Finset.univ
            (fun i : Fin sc.root.t =>
              coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i))) := by
      ext H'
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_univ,
        true_and]
      constructor
      · intro hH'
        have h1' : H' ∈ ⋃ j, sc.root.trackChains j := by
          rw [sc.root.hpart.1]; exact hH'
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1'
        rw [htc i] at hi
        exact ⟨i, coneF_mem.mpr hi⟩
      · rintro ⟨i, hi⟩
        exact (coneF_mem.mp hi).1
    rw [hset, Finset.sum_biUnion hdisjT]
  -- ==== positivity of the root cell ====
  haveI : Finite ↥(rootCell χ sc.g) := (Set.toFinite _).to_subtype
  have hRpos : 0 < Nat.card ↥(rootCell χ sc.g) :=
    Nat.card_pos_iff.mpr ⟨⟨x₀, sc.hg x₀ hx₀⟩, inferInstance⟩
  -- ==== assemble: multiply E5 by the track prices, cancel |R|^t ====
  refine Nat.eq_of_mul_eq_mul_right (pow_pos hRpos sc.root.t) ?_
  calc Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H)
        * (Nat.card ↥(rootCell χ sc.g)) ^ sc.root.t
      = (Nat.card ↥{x | Tr.fiberAt T χ x}
          * (Nat.card ↥(rootCell χ sc.g)) ^ sc.root.t * p ^ n)
        * ∏ i : Fin sc.root.t,
            p ^ (∑ H' ∈ coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)),
              L.siteExp H') := by
        rw [pow_add, hchainsum, Finset.prod_pow_eq_pow_sum]
        ring
    _ = (p ^ m * ∏ i : Fin sc.root.t,
          Nat.card ↥(rootCell χ sc.g ∩ trackEvent Tr T sc.root i (sc.hcr i)))
        * ∏ i : Fin sc.root.t,
            p ^ (∑ H' ∈ coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)),
              L.siteExp H') := by
        rw [hE5]
    _ = p ^ m * ∏ i : Fin sc.root.t,
          (Nat.card ↥(rootCell χ sc.g ∩ trackEvent Tr T sc.root i (sc.hcr i))
            * p ^ (∑ H' ∈ coneF Tr (oneNode (sc.root.headOf i) (sc.hcr i)),
                L.siteExp H')) := by
        rw [Finset.prod_mul_distrib]
        ring
    _ = p ^ m * ∏ i : Fin sc.root.t, Nat.card ↥(rootCell χ sc.g) := by
        rw [Finset.prod_congr rfl (fun i _ => htrack i)]
    _ = p ^ m * (Nat.card ↥(rootCell χ sc.g)) ^ sc.root.t := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end LeanUrat.MovesT
