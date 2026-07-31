# M11-cl19-rep — problem brief (neutral, self-contained)

## One-line statement

Settle the *history face* of the CL-19 joint-cell invariance row: the named
Prop `Slot_jcInvHist n` (Lean text below) — for two realized classifier
histories whose last reads agree in a designated "retained state" roster, the
joint digit-cell conditional law given the entrance event is the same,
division-free — prove it for the degrees the capstone targets (n ≥ 2), refute
it, or deliver what its resolution requires.

## Background: where this sits

The corpus formalizes a uniformity theorem: for each degree n and each
splitting type σ (multiset of (e, f) pairs, Σ e·f = n), the density of monic
degree-n polynomials over ℤ_p factoring over ℚ_p with type σ is one rational
function R_σ(q) evaluated at q = p, uniformly in p. The engine is an
Okutsu–Montes / MacLane-style classifier: a polynomial is processed by a
sequence of *reads* (Newton-polygon side selection + residual-polynomial
factor selection); the sequence of reads made so far is a *history*; the
classifier's run on all inputs is organized as a tree.

The capstone theorem (`theoremU`, `lean/LeanUrat/MovesU/U10_theoremU.lean`)
carries thirteen named bare-`Prop` hypotheses ("slots") for ledger rows whose
carrier vocabulary was not yet built at its ratification. One of them is
`jcInvHist`, documented there as:

> `jcInvHist` — CL-19's h_ent/history-invariance residue beyond the typed
> `cl19_rep` face (owner [2b]).

The source proof note's ledger row (CL-19 "(JC-INV)",
`lean/notes/MOVES_2026-07-24.md` 13345–13361) reads:

> per read, the JOINT digit-cell conditional law given the entrance (all
> cells of the read jointly, branching cells INCLUDED — hence the
> branching-cell selection law) is ONE function of the retained state —
> invariant across representatives and admissible histories, h_ent included.

("h_ent" = the height at which the state was entered — a valuation-axis
datum. "Retained state" is made precise below.)

CL-19 is split in the formalization into two disjoint faces:

1. **Representative face** (`cl19_rep`) — a typed field carried by two
   hypothesis-ledger structures (`CapstoneLedger`,
   `lean/LeanUrat/MovesU/DefsLedger.lean:802`, and `BridgeKernels`,
   `lean/LeanUrat/MovesU/BridgeKernels.lean:272`), stated over an *abstract*
   measured carrier:

   ```lean
   cl19_rep : ∀ e (τ : C.T.State e) (x x' : C.MS.Rep e τ) (c : C.MS.Cell e τ)
     (q₀ : ℚ), q₀ ∈ C.MS.Pools → C.MS.activeState q₀ e τ →
     C.MS.μcell e τ x c q₀ = C.MS.μcell e τ x' c q₀
   ```

   Here `C.MS : MeasuredSide C.T` is an abstract structure (a field of the
   carrier pack `C : UCarriers n`); `Rep e τ` is a type of "representatives"
   of the state τ, `Cell e τ` a finite cell type, `μcell e τ x c q₀ : ℝ` the
   per-cell conditional mass at pool value q₀ (intended: q₀ = p^δ), and
   `activeState` an activity predicate. The row asserts μcell is independent
   of the representative x. It is a hypothesis row over the abstract carrier:
   nothing in the corpus proves or instantiates it non-trivially; discharging
   it is a wave-D (instance-building) duty.

2. **History face** — THE SUBJECT OF THIS BRIEF: the named Prop
   `Slot_jcInvHist` (`lean/LeanUrat/MovesU/SlotsG10_jcInvHist.lean`), over
   the built tree-model vocabulary, quantifying the history/h_ent leg that
   `cl19_rep` does not mention. The two faces deliberately share no
   vocabulary; the file header records that reading their conjunction as the
   full CL-19 display goes through a separately-carried identification of
   the two cell vocabularies (the `UInstance.Tpin`/`sibjc` seam), which is
   not this slot's content.

## The precise obligation (Lean text, normative)

From `lean/LeanUrat/MovesU/SlotsG10_jcInvHist.lean` (compiled, statement-only
unit; no proof exists in the corpus):

```lean
def NodeRetainedKeyEq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν ν' : MovesC.Node p F) : Prop :=
  ν.species = ν'.species ∧ ν.e = ν'.e ∧ ν.g = ν'.g ∧ ν.μ = ν'.μ ∧
    ν.a = ν'.a ∧ ν.s0 = ν'.s0 ∧ ν.wSide = ν'.wSide ∧ ν.Dwidth = ν'.Dwidth ∧
    Nat.card ↥ν.σ.K = Nat.card ↥ν'.σ.K

def Slot_jcInvHist (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (N m : ℕ) (pol : MovesD.CanonPolicy p (ZMod p))
    (T : MovesD.TreeModel p (ZMod p) n N m pol)
    (CA : MovesT.CellData p (ZMod p) n N m pol T)
    (χ : Fin n → Fin m) (H H' : MovesC.History p (ZMod p)),
    (MovesT.entEvent T χ (MovesT.EntSt.st H)).Nonempty →
    (MovesT.entEvent T χ (MovesT.EntSt.st H')).Nonempty →
    NodeRetainedKeyEq H.lastNode H'.lastNode →
    ∀ c : CA.Cell,
      Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H) c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H'))
        = Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H') c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H))
```

In standard language. Fix n. For EVERY prime p, every pair (N, m) ∈ ℕ², every
canonicity policy `pol`, every tree model T over the box 𝔽_p^m, every
joint-cell datum CA over T (both defined below), every chart
χ : {0,…,n−1} → {0,…,m−1}, and every pair of histories H, H′ (finite read
sequences, defined below): writing

- Σ_H := {x ∈ 𝔽_p^m : T realizes the chain H at x} (the *entrance event*;
  for state entrances the chart χ plays no role in its definition),
- Ψ_H := CA.cellOf(.st H) : 𝔽_p^m → Cell (the *entrance-keyed joint read*),

if Σ_H ≠ ∅, Σ_{H′} ≠ ∅, and the last nodes of H and H′ agree in the retained
roster (species, e, g, μ, a, s0, wSide, Dwidth, #K), then for every cell c:

  #(Ψ_H⁻¹(c) ∩ Σ_H) · #Σ_{H′}  =  #(Ψ_{H′}⁻¹(c) ∩ Σ_{H′}) · #Σ_H.

(Equivalently: the conditional laws P(Ψ_H = c │ Σ_H) and P(Ψ_{H′} = c │ Σ_{H′})
coincide — stated division-free by cross-multiplication. All sets are finite
since the box is; `Nat.card` of the subtype is the count.)

Recorded formulation resolutions (from the unit's header, binding for
faithfulness): (r1) the conditional law is rendered division-free by
cross-multiplied cardinalities against the entrance events; branching cells
are included because `cellOf` is the FULL joint read (its fibers refine every
branch stratum — the `branch_cell_joint` law); (r2) "retained state" = the
roster above, with the HEIGHT-AXIS data erased — h, ustar, gam are excluded
(that is exactly "h_ent included"), the Bézout pair (s, t) is a function of
(e, h) and is excluded with h, and the recorded frame data enter only through
the residue-weight source #K; this roster is FLAGGED as the load-bearing
resolution of an ambiguous sketch; (r3) "admissible histories" = realizedness
in the pinned model (nonempty entrance events) — the weaker guard, hence the
stronger statement.

## Definitions unfolded (standard mathematics)

**Box.** `Box p m := Fin m → ZMod p` — vectors of m coordinates in 𝔽_p. In
the intended semantics each coordinate is one p-ary digit of one coefficient
of a monic degree-n polynomial truncated at level N (so m ≈ n·N), reached
through the chart χ; but the statement quantifies over all (N, m, χ).

**Node** (`MovesC.Node p F`, `lean/LeanUrat/MovesC/Defs.lean:361`): one read
of the classifier, recording — species ∈ {root, increment, recentering}; a
frame ("stage") σ carrying the current key polynomial Φ (Dwidth = deg Φ) and
its residue field K ⊆ F; the selected Newton-polygon side of slope −h/e
(e, h ≥ 1 coprime) spanning slots [s0, s0 + wSide] (e ∣ wSide); the canonical
Bézout pair (s, t) for (e, h) with t ∈ [0, e); the side's residual polynomial
data: a monic irreducible ψ over K of degree g with multiplicity μ (= ord_ψ
of the anchored residual R_anch), the anchor a pinned by e·a = s0 − t·γ; the
height data u* (side right-endpoint height), γ = e·u* + j*·h ∈ ℤ (total side
weight), the side line (slope −h/e through (s0+wSide)·Dwidth ↦ u*); the
selected residue root z̄ of ψ; recentering center/lift; the side digit
pattern pat and R_anch = Σ_k pat(k)·z^k. Numerous Prop fields enforce these
meanings (coprimality, ψ monic irreducible of degree g, ord_ψ R_anch = μ
exactly, endpoint digits nonzero, anchor equation, line-through-(j*, u*),
species laws). The retained key keeps (species, e, g, μ, a, s0, wSide,
Dwidth, #K) and erases everything else — in particular ALL height-axis data
(h, u*, γ, (s,t)) and the frame identity beyond #K (Φ, z̄, ψ, center, lift,
pattern, line).

**History** (`MovesC.History p F`): a nonempty finite list of nodes in which
the species-root read appears exactly at index 0. `H.lastNode` is the final
node. (Two auxiliary predicates appear through the tree model below:
`HistoryCoherent` — the Newton-polygon bookkeeping coherence of consecutive
reads: slope ties, γ-ties, frame-width chain Dwidth_{i+1} = e·g·Dwidth_i,
strictly increasing slopes, residue-field growth #K_{i+1} = #K_i^g, etc.;
and `Realizable` plus a canonical-presentation predicate `pol.IsCanonPres`.
They constrain a history's NODE DATA internally; they do not tie the tree
model's membership relation to any polynomial semantics.)

**TreeModel** (`MovesD.TreeModel p F n N m pol`,
`lean/LeanUrat/MovesD/Defs.lean:630`): a pair of relations
`mem : Option (History) → Box → Prop` (none = the empty chain/root state) and
`child : Option (History) → Node → Box → Prop`, subject to four laws:
(i) `root_mem`: every x realizes the root state; (ii) `mem_single`: a
one-node history is realized at x iff its node is a `child none` at x;
(iii) `mem_snoc`: H.snoc(ν) is realized at x iff H is realized and ν is a
`child (some H)` at x; (iv) `mem_realizable`: any realized history satisfies
HistoryCoherent ∧ Realizable ∧ pol.IsCanonPres. Nothing else is imposed —
`mem`/`child` are otherwise free relations.

**Entrance carrier and events** (`lean/LeanUrat/MovesT/Defs.lean`):
`EntSt p F n` has three constructors — `.amb` (ambient box), `.red g ψ`
(level-0 reduction cell keyed by the reduction datum g and a track factor ψ),
`.st H` (a realized chain state). `entEvent T χ es` is: the whole box for
`.amb`; the level-0 cell {x : ∀ b, x(χ b) = g b} for `.red g ψ`; and the
*state event* {x : T.mem (some H) x} for `.st H`. The obligation only
involves `.st` entrances.

**CellData** (`MovesT.CellData p F n N m pol T`,
`lean/LeanUrat/MovesT/Defs.lean:335`): the joint-cell assignment layer —
- `Cell` : a finite type (the joint digit-cell alphabet, shared by all
  entrances);
- `cellOf : EntSt → Box → Cell` — the entrance-keyed joint read;
- `cellLevel : EntSt → ℕ`, `levelOf : Fin m → ℕ`, and the locality law
  `cell_local`: cellOf es x depends only on the coordinates i with
  levelOf i < cellLevel es (a constraint in the BOX argument only);
- `branchSetOf : Cell → Finset Node` and the branch laws: `child_cell` (at a
  realized state, ν is a child at x iff ν ∈ branchSetOf(cellOf (.st H) x)),
  `child_root_sub`, `child_cell_red`, `child_red_uniform` (root-side laws
  tying `child none` to the `.amb`/`.red` reads);
- `branchCellOf : EntSt → Node → Box → Cell` (per-site read) with
  `branch_cell_joint`: branchCellOf es ν factors through cellOf es.

`cellEventE T CA χ es c := {x ∈ entEvent T χ es : CA.cellOf es x = c}` is the
joint-cell event over the entrance.

**CanonPolicy**: a structure supplying the canonical-presentation predicate
`IsCanonPres` consumed by `mem_realizable`; the statement quantifies over all
policies.

## What is already proved / recorded around this obligation

- The statement unit `SlotsG10_jcInvHist.lean` compiles (statement-only, no
  proof; zero sorries). The identifier-closure manifest is
  `SlotsG12_closureManifest.lean`.
- **A compiled falsifier exists.** `SlotsG11c_seamAudit.lean` proves,
  kernel-checked with Lean-core axioms only (propext, Classical.choice,
  Quot.sound; verified 2026-07-31):

  ```lean
  theorem slot_jcInvHist_falsifiable : ∃ n : ℕ, ¬ Slot_jcInvHist n
  ```

  witnessed at n = 2. The witness (built on the 0-sorry toy
  `MovesT/S2_sibFalse.lean`, at p = 2, F = 𝔽₂, N = 1, m = 2): two one-node
  histories t1, t2 whose nodes differ only in the recorded recentering-center
  datum (a field the retained key erases, so `NodeRetainedKeyEq` holds),
  both realized exactly on the slice {x : x₀ = 0}; a degenerate `CellData`
  whose state-entrance read is `cellOf (.st H) := if H = t1 then 2 else 3`
  (constant in the box argument, so every CellData law checks — the state
  branch sets are empty and the toy tree has no children at state sites);
  at c = 2 the law reads 2·2 = 4 ≠ 0 = 0·2. This falsifier was BUILT ON
  PURPOSE, per the campaign's standing non-vacuity doctrine ("every
  formulated slot Prop must be FALSE for a degenerate instance the note
  would reject"); the per-slot design table records it as the slot's
  non-vacuity audit, discharged.
- Consumption status: `theoremU` consumes `jcInvHist` as a bare Prop
  parameter with hypothesis `hjc : jcInvHist`; the boundary record states
  the thirteen slots are UNPINNED (True-instantiable) pending wave-D. The
  planned consumption theorem (`theoremU_bridged`, unit IB-G13/G13′)
  instantiating the thirteen parameters at the Slot props is NOT YET
  WRITTEN (gated on adjudication Q13). The governing adjudication (BP1 Q5,
  `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`) is: statement-only now,
  Codex formulation audit + the falsifier before any consumer lands.
- Signature pattern of the sibling slots (fact, relevant to any repair):
  the other twelve slots all take their carriers as PARAMETERS — e.g.
  `Slot_rs0Lump (n) (C : UCarriers n)`,
  `Slot_m4bConst (n) {Cv} {Sv} (V : CtsMeasured n Cv Sv)`,
  `Slot_trackRule (n) {C} (KC : KernelCarriers n C) …` — while
  `Slot_jcInvHist (n)` closes over its carriers (∀ p N m pol T CA inside).
- The representative face `cl19_rep` (quoted above) is carried as a
  hypothesis field; no instance discharges it (wave-D duty). No real
  (classifier-semantic) instance of `MeasuredSide`, and no real `TreeModel`
  + `CellData` instance tied to polynomial factorization, exists in the
  corpus at HEAD; the compiled instances are finite toys.

## What a resolution must deliver

The capstone needs, at each degree n ≥ 2 it is fired at, a supply for the
`jcInvHist` hypothesis that faithfully transcribes CL-19's history/h_ent
face. Concretely, a resolution is one of:

1. A proof of `Slot_jcInvHist n` (for the target degrees), from the stated
   hypotheses alone; or
2. A refutation — in which case the deliverable is (a) the precise failure
   analysis, and (b) a repaired normative statement that still faithfully
   transcribes the CL-19 display (statement changes require explicit
   sign-off under the project's fence rules; this slot currently gates
   nothing, and its Q5 adjudication anticipates a formulation audit before
   consumers), together with a proof of the repaired statement or a precise
   reduction of it to named open lemmas, and a re-satisfied non-vacuity
   falsifier for the repaired form; any repair must remain consistent with
   the slot family's consumption architecture and with the recorded
   conjunction duty (repaired history face ∧ `cl19_rep` ≡ CL-19's display,
   through the Tpin/sibjc cell-vocabulary identification).

Either way the mathematical heart to be settled is: in what generality is
the joint digit-cell conditional law given a state entrance a function of
the retained roster (species, e, g, μ, a, s0, wSide, Dwidth, #K) alone —
independent of the entrance height and of everything else in the history —
and from which structural hypotheses on (T, CA) does it actually follow?
