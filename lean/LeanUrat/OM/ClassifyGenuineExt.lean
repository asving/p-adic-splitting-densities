/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.OMType
import LeanUrat.OM.UnramifiedBase
import LeanUrat.OM.ChildResidualExt
import LeanUrat.OM.LiftKeyExt
import LeanUrat.OM.OrderTwoContext
import LeanUrat.OM.OrderTwoContextR

/-!
# `ClassifyGenuineExt` — the residue-field-EXTENSION descent recursion `classifyGenuineExtAux`
(P9, WAVE 4)

**The SEPARATE extension recursion.** This file builds `classifyGenuineExtAux`, the
`Nat.strongRecOn`-on-budget recursion that emits the ext OM-tree shape by descending through the
GENUINE-`Rr` extension context `OrderTwoContextR.fChildCtxExtR` at every level. It is the extension
analogue of `Classifier.classifyGenuineAux` (which is FIXED at `Fr = ZMod p` DEFINITIONALLY, and is
deliberately NOT repointed here — its closure relies on that defeq, `Classifier.lean` is never
edited).

## The crux (blueprint §3): the residue field TRAVELS AS DATA

Unlike `classifyGenuineAux`, whose recursion argument is a `ψ : (ZMod p)[X]` over a fixed field, the
residue field here is a genuine extension `k_S = resField p N g hN = F_{p^{deg g}}`, and it is carried
**as the defining DATA of the recursion, not as a type in the motive** — precisely to avoid the
`eqRec`-on-motive pathology of putting a varying field type inside `Nat.strongRecOn`'s `motive`.

Concretely:

* **The field is fixed AMBIENT data** for one invocation, threaded as the explicit parameters
  `p N g hgm hN hgirr` — exactly the tuple that `fChildCtxExtR` consumes to build a context whose
  `Fr = resField p N g hN`. These parameters are captured in the recursion's closure; they are NOT in
  the `Nat.strongRecOn` motive.
* **The `Nat.strongRecOn` motive is field-agnostic**:
  `motive := fun _ : ℕ => (r : ℕ) → (Ψ : (resField p N g hN)[X]) → (μ : ℕ) → ClusterShape`.
  The residue-field TYPE `(resField p N g hN)[X]` appears only as a closure constant inside this
  motive, never as a bound/transported type. So there is NO dependent transport across the strong
  recursion: every recursive call reads the SAME fixed field type.
* **The per-node residual factor threads without transport.** At a node the recursion lifts the
  incoming factor `Ψ : (resField p N g hN)[X]` to a monic key `Φ := liftKeyExt … Ψ` over
  `O″ = Oring p N g`, forms the context `T := fChildCtxExtR … Φ μ h`, and for each descent child
  `ch : M5.OMCell.Child T` recurses on the child's own factor `ch.P : T.Fr[X] = (resField p N g hN)[X]`
  — the SAME type as the incoming `Ψ`, so it threads with no `▸` (this is the extension analogue of
  `classifyGenuineAux` feeding `ch.P : (ZMod p)[X]` back in). Strict descent is
  `ch.hChildSizeLt : ch.childSize < clusterSize T = budget` via `clusterSize_fChildCtxExtR`.

## What this file lands (core-only, no `sorry`/`axiom`/`native_decide`)

1. `classifyGenuineExtAux` — the strong-recursion emitting the ext OM-tree shape, threading
   `resField p N g hN` as fixed defining data (§3).
2. `classifyGenuineExtAux_unfold` — its one-step unfold (`Nat.strongRecOn_eq` + beta).
3. Well-formedness:
   * `classifyGenuineExtAux_head` — the emitted tree's head tuple is `(r, budget, (fChildCtxExtR …).dr)`
     (a head-tuple / tree-shape lemma);
   * `classifyGenuineExtAux_head_dr_pos` — the NON-VACUITY analogue of
     `Classifier.classifyGenuineAux_head_dr_pos`: when the extension residual `childResidualExt` has
     positive degree within budget, the emitted head's `dr`-slot is NONZERO, so the tree is NOT the
     degenerate `(r, budget, 0)` leaf that the `Rr := 0` stub `OrderTwoContext.fChildCtxExt` produces.
     This is what distinguishes the genuine extension reader from the interface stub AT THE ROOT TUPLE,
     via the extension residual degree.

## Scope, stated honestly — this is the RECURSION, NOT yet the full faithful reader

* This is the extension descent recursion + unfold + well-formedness ONLY. It does NOT build the
  reduce-stability / CERTLEVEL cylinder, and it does NOT state the order-≥2 CITE (owned elsewhere).
* **`Φ`, `h` are wired through `Ψ` and an ambient box element** — but this file does NOT tie `h` to a
  genuinely base-changed `f` (`O″Box`, blueprint §1a), so it inherits the `childResidualExt`
  scaffolding caveat (`Φ`/`h`/`Ψ` are honest data, not yet certified to be `f`'s order-`r` residual).
* **The GENUINE changing-field crux (per-level LARGER residue field) is honestly OPEN.** In a true
  Montes order-≥2 descent each child's residue field is a FURTHER extension of the parent's, i.e. the
  child would carry its OWN `g' : (ZMod (p^N))[X]` with `resField p N g' hN ⊋ resField p N g hN`, and
  `ch.P : (resField p N g hN)[X]` would need reinterpreting over `resField p N g'`. THIS file threads
  a SINGLE fixed `g` (one extension level) — the child factor `ch.P` is fed back over the SAME
  `resField p N g hN`. That is exactly the design that keeps the field out of the motive and makes the
  recursion build; promoting each level to its own `g'` (the dependent-type-across-varying-`k_S` step)
  is the OPEN wave-5 target. See the recursion's docstring for the precise boundary.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.ClassifyGenuineExt

open Polynomial LeanUrat LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The residue-field-EXTENSION descent recursion -/

/-- **The genuine residue-field-EXTENSION descent recursion** (P9 wave 4). Emits the ext OM-tree
shape by strong recursion on the cluster budget, descending through the GENUINE-`Rr` context
`OrderTwoContextR.fChildCtxExtR` at every level.

**How `resField` travels as data (the crux, blueprint §3).** The residue field
`k_S = resField p N g hN = F_{p^{deg g}}` is threaded as the FIXED defining DATA
`p N g hgm hN hgirr h` (all captured in the closure), NOT as a type in the strong-recursion motive:

* `motive := fun _ : ℕ => (r : ℕ) → (Ψ : (resField p N g hN)[X]) → (μ : ℕ) → ClusterShape` —
  the field type is a closure constant, never bound/transported, so there is NO `eqRec`-on-motive.
* At a node with budget `b`, incoming factor `Ψ : (resField p N g hN)[X]` and multiplicity `μ`:
  lift `Ψ` to a monic key `Φ := LiftKeyExt.liftKeyExt p N g hgm hN Ψ` over `O″ = Oring p N g`, form
  the context `T := OrderTwoContextR.fChildCtxExtR p N g r b hgm hN hgirr Φ μ h` (whose
  `Rr := childResidualExt … Φ μ h` guarded to budget, `Fr := resField p N g hN`), emit the root tuple
  `(T.order, clusterSize T, T.dr) = (r, b, T.dr)`, and for each descent child
  `ch : M5.OMCell.Child T` recurse on `ch.childSize < b` (via `clusterSize_fChildCtxExtR`) with the
  child's OWN residual factor `ch.P : T.Fr[X] = (resField p N g hN)[X]` — the SAME field type as `Ψ`,
  fed back with NO transport (extension analogue of `classifyGenuineAux` threading `ch.P : (ZMod p)[X]`).

**Boundary (honest).** A single fixed `g` (one extension level) is threaded: `ch.P` is fed back over
the SAME `resField p N g hN`. The genuine Montes crux — each child's residue field a FURTHER extension
`resField p N g' hN` — would require each level to carry its own `g'` and reinterpret `ch.P`; that
changing-field step is the OPEN wave-5 target and is NOT done here. This recursion builds the ext tree
SHAPE with a genuine per-node residual reader over a fixed extension level; it is NOT yet the full
faithful order-≥2 reader (reduce-stability + CITE + dispatcher are later). -/
def classifyGenuineExtAux (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (h : (UnramifiedBase.Oring p N g)[X]) :
    (budget : ℕ) → (r : ℕ) → (Ψ : (UnramifiedBase.resField p N g hN)[X]) → (μ : ℕ) → ClusterShape :=
  fun budget => Nat.strongRecOn budget
    (motive := fun _ => (r : ℕ) → (Ψ : (UnramifiedBase.resField p N g hN)[X]) → (μ : ℕ) → ClusterShape)
    (fun b ih => fun r Ψ μ =>
      let Φ := LiftKeyExt.liftKeyExt p N g hgm hN Ψ
      let T := OrderTwoContextR.fChildCtxExtR p N g r b hgm hN hgirr Φ μ h
      ⟨(T.order, M5.clusterSize T, T.dr) ::
          (M5.cells T).flatMap (fun c =>
            c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
              have hlt : ch.childSize < b :=
                (OrderTwoContextR.clusterSize_fChildCtxExtR p N g r b hgm hN hgirr Φ μ h) ▸
                  ch.hChildSizeLt
              (ih ch.childSize hlt (T.order + 1) ch.P ch.μ).tree)),
        M5.encodeCells T⟩)

/-- **One-step unfold of `classifyGenuineExtAux`** (`Nat.strongRecOn_eq` + beta). Exposes the emitted
shape at a level `budget = b`: the root tuple of `fChildCtxExtR … (liftKeyExt … Ψ) μ h` followed by
the genuine recursive descent over that context's cells' children. Mirrors
`Classifier.classifyGenuineAux_unfold`. No axiom. -/
theorem classifyGenuineExtAux_unfold (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (h : (UnramifiedBase.Oring p N g)[X])
    (budget r : ℕ) (Ψ : (UnramifiedBase.resField p N g hN)[X]) (μ : ℕ) :
    classifyGenuineExtAux p N g hgm hN hgirr h budget r Ψ μ
      = (let Φ := LiftKeyExt.liftKeyExt p N g hgm hN Ψ
        let T := OrderTwoContextR.fChildCtxExtR p N g r budget hgm hN hgirr Φ μ h
        ⟨(T.order, M5.clusterSize T, T.dr) ::
            (M5.cells T).flatMap (fun c =>
              c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
                (classifyGenuineExtAux p N g hgm hN hgirr h ch.childSize (T.order + 1) ch.P ch.μ).tree)),
          M5.encodeCells T⟩) := by
  have heq := Nat.strongRecOn_eq
    (motive := fun _ => (r : ℕ) → (Ψ : (UnramifiedBase.resField p N g hN)[X]) → (μ : ℕ) → ClusterShape)
    (fun b ih => fun r Ψ μ =>
      (let Φ := LiftKeyExt.liftKeyExt p N g hgm hN Ψ
      let T := OrderTwoContextR.fChildCtxExtR p N g r b hgm hN hgirr Φ μ h
      (⟨(T.order, M5.clusterSize T, T.dr) ::
          (M5.cells T).flatMap (fun c =>
            c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
              have hlt : ch.childSize < b :=
                (OrderTwoContextR.clusterSize_fChildCtxExtR p N g r b hgm hN hgirr Φ μ h) ▸
                  ch.hChildSizeLt
              (ih ch.childSize hlt (T.order + 1) ch.P ch.μ).tree)),
        M5.encodeCells T⟩ : ClusterShape)))
    budget
  exact congrFun (congrFun (congrFun heq r) Ψ) μ

/-! ## Well-formedness -/

/-- **Head-tuple / tree-shape** of `classifyGenuineExtAux` (well-formedness). The emitted tree is a
CONS whose head is the root tuple `(r, budget, (fChildCtxExtR … (liftKeyExt … Ψ) μ h).dr)`: the order
slot is the input order `r` (`order := r`), the size slot is the input budget (`cs := budget`, via
`clusterSize`), and the `dr` slot is the extension context's residual degree. So every emitted ext
node reads back its `(order, clusterSize, dr)` triple exactly as the extension context specifies.
No axiom. -/
theorem classifyGenuineExtAux_head (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (h : (UnramifiedBase.Oring p N g)[X])
    (budget r : ℕ) (Ψ : (UnramifiedBase.resField p N g hN)[X]) (μ : ℕ) :
    (classifyGenuineExtAux p N g hgm hN hgirr h budget r Ψ μ).tree.head?
      = some (r, budget,
          (OrderTwoContextR.fChildCtxExtR p N g r budget hgm hN hgirr
            (LiftKeyExt.liftKeyExt p N g hgm hN Ψ) μ h).dr) := by
  rw [classifyGenuineExtAux_unfold]
  -- After unfold the tree is a `cons`; `head?` reads the root tuple.
  -- `T.order = r` (`order := r`), `clusterSize T = budget` (`cs := budget`), both definitionally.
  rfl

/-- **Genuine extension reader's root tuple is `dr`-nondegenerate** (P9 wave-4 NON-VACUITY, the
extension analogue of `Classifier.classifyGenuineAux_head_dr_pos`). When the extension residual
`childResidualExt p N g hgm hN (liftKeyExt … Ψ) μ h` has positive degree within the cluster budget,
the emitted `classifyGenuineExtAux` tree's ROOT TUPLE carries a NONZERO `dr`-slot
(`= (childResidualExt …).natDegree > 0`). So the emitted tree is NOT the degenerate `(r, budget, 0)`
leaf that the `Rr := 0` interface stub `OrderTwoContext.fChildCtxExt` produces (whose `dr = 0`) — the
genuine extension reader is DISTINGUISHED FROM THE STUB at the root tuple, via the genuine extension
residual degree over `resField = F_{p^{deg g}}`.

Mirrors the honest scope of the ℤ/p `classifyGenuineAux_head_dr_pos`: it does NOT assert the descent
flatMap is non-empty (a positive-degree but separable residual gives cells with no descent child); a
length-≥2 witness needs an extra repeated-factor hypothesis and is future work. No axiom. -/
theorem classifyGenuineExtAux_head_dr_pos (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (h : (UnramifiedBase.Oring p N g)[X])
    (budget r : ℕ) (Ψ : (UnramifiedBase.resField p N g hN)[X]) (μ : ℕ)
    (h0 : 0 < (ChildResidualExt.childResidualExt p N g hgm hN
      (LiftKeyExt.liftKeyExt p N g hgm hN Ψ) μ h).natDegree)
    (hle : (ChildResidualExt.childResidualExt p N g hgm hN
      (LiftKeyExt.liftKeyExt p N g hgm hN Ψ) μ h).natDegree ≤ budget) :
    (classifyGenuineExtAux p N g hgm hN hgirr h budget r Ψ μ).tree
      ≠ [(r, budget, (0 : ℕ))] := by
  intro hleaf
  -- The head tuple of the emitted tree is `(r, budget, (fChildCtxExtR …).dr)`.
  have hhead := classifyGenuineExtAux_head p N g hgm hN hgirr h budget r Ψ μ
  rw [hleaf] at hhead
  -- `hhead : some (r, budget, 0) = some (r, budget, (fChildCtxExtR …).dr)`, so the `dr`-slot is `0`.
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
  -- `hhead.2.2 : 0 = (fChildCtxExtR …).dr`. But that `dr` is the guarded extension residual degree.
  set Φ := LiftKeyExt.liftKeyExt p N g hgm hN Ψ with hΦ
  have hdr : (OrderTwoContextR.fChildCtxExtR p N g r budget hgm hN hgirr Φ μ h).dr
      = (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree := by
    show (if (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ budget
            then ChildResidualExt.childResidualExt p N g hgm hN Φ μ h else 0).natDegree
        = (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree
    rw [if_pos hle]
  have hdr0 : (OrderTwoContextR.fChildCtxExtR p N g r budget hgm hN hgirr Φ μ h).dr = 0 :=
    hhead.2.2.symm
  rw [hdr] at hdr0
  omega

-- Footprint checks: each built decl must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms classifyGenuineExtAux_unfold
#print axioms classifyGenuineExtAux_head
#print axioms classifyGenuineExtAux_head_dr_pos

end

end LeanUrat.OM.ClassifyGenuineExt
