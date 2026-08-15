/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B22
import Uniformity.ChapB.B34
import Uniformity.Density.ScaleExtraction

/-!
# Uniformity.ChapB.B44 — the integral-slope shortcut (the chapter's cross-check on the engine)

**Chapter B, NODE B.44** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §6, the two dissections),
ENV-C. One signed declaration.

*The integral-slope shortcut, as an independent check.* At the key `φ = X` (so `m = 1`) and
slope denominator `ℓ = 1` — the case where the slope `−u/1` is an integer — the whole
dissection collapses to a rescaling of the variable: a monic `f` of positive degree `n` that is
`(u,1)`-pure with `suppVal X f u 1 = u*n` is `f = G.scaleRoots (π^u)` for a monic `G` of the
same degree `n`, with `typeOf f = typeOf G`, and `G`'s coefficients are read off `f`'s by the
digit map: `residue O (G.coeff i) = digAt π (u*(n−i)) (f.coeff i)`.

**⚠ WHY THIS NODE EXISTS.** It is the chapter's **independent cross-check on the graded
engine**: at `m = ℓ = 1` the entire dissection is *landed* API (`Density/ScaleExtraction.lean`,
CN-12/CN-13), reached without any of §§3–5's polygon representation, so B.41/B.42 restricted to
that case must agree with what is proved here. If they disagree, the graded engine is wrong;
that disagreement test is B.83's gate. The corpus runs the same internal decorrelation at
`EFF.HE3.34` ("at `μ ≤ 3`, HE6.A agrees with HE3-4").

## The signed statement keeps only the `digAt` clause — the declared signature risk fired

The blueprint's prose also asks for `G.map (residue O) = resPoly π X f u 1 _ H₀` "up to the
identification `resField X ≅ ResidueField O`", and books the **SPLIT MANDATE → 3 only if that
identification is not `rfl`**. It is not `rfl`: `resField X = AdjoinRoot (X.map (residue O))`,
and `AdjoinRoot X ≃ₐ ResidueField O` needs an explicit equivalence. Per the node's own
instruction the frozen SIGNATURE therefore **drops the `resPoly` clause and keeps only the
`digAt` clause**, which is representation-free — and with the `resPoly` clause gone the split
mandate does not fire: this is one file. The residual-to-reduction bridge is B.59's job, and
B.60 is the consumer that needs it.

DEPENDS: B.15 (`suppVal_X_iff`, the `φ = X` compatibility certificate) · B.22 (`digAt_eq`) ·
B.34 (`IsPure`, in the signature) · landed `Uniformity.Density.exists_monic_scaleRoots_typeOf`
(`Uniformity/Density/ScaleExtraction.lean:136`, itself CN-12's `exists_monic_scaleRoots`
composed with `typeOf_scaleRoots`) · mathlib `Polynomial.coeff_scaleRoots`, `pow_mul`.
The node's DEPENDS line also names B.21 (`digAt`, imported through B.22), B.24 and B.28.

**PROOF.**

1. `hsupp` is an equality, so in particular `((u * n : ℕ) : ℕ∞) ≤ suppVal X f u 1`; B.15's
   `suppVal_X_iff hπ hf hn u` converts that half into the coefficient divisibility
   `∀ i < n, π^(u*(n−i)) ∣ f.coeff i`. This is the *only* place the polygon hypothesis is used,
   and it is exactly the hypothesis of the landed extraction — which is B.15's whole point as
   DECISION D-1's criterion-C8 certificate.
2. Landed `exists_monic_scaleRoots_typeOf hπ hf u` applied to step 1 gives the monic `G` with
   `G.natDegree = f.natDegree`, `f = G.scaleRoots (π^u)` and `typeOf f = typeOf G` — the first
   four conjuncts verbatim.
3. The digit clause: rewriting the *left* side only (the right side names `f.natDegree`, which
   must not be rewritten to `(G.scaleRoots (π^u)).natDegree`),
   `Polynomial.coeff_scaleRoots` and `pow_mul` give
   `f.coeff i = π^(u*(n−i)) * G.coeff i`, and B.22's `digAt_eq hπ` reads the digit of any such
   product as `residue O (G.coeff i)`.

`hpure : IsPure X f u 1` is a **signed but unconsumed** hypothesis: purity's numerical content
at `φ = X` is precisely `suppVal X f u 1 = u * f.natDegree` (B.13 puts the right endpoint at
height `0`), which the signature already carries as the separate hypothesis `hsupp`, and only
the `≥` half of that is needed. The statement is **not** weakened — `hpure` stays in the frozen
binder list, and `linter.unusedVariables` is silenced for the declaration, the precedent being
B.15's own `hf`/`hn` (`B15.lean`).

## ENV-C, and the one `omit` that the type diff forces

`[IsAdicComplete (maximalIdeal O) O]` and `[Finite (ResidueField O)]` are the ENV-C section
variables; neither is consumed here (`typeOf` is defined over the bare DVR arena). The binder
list is nevertheless pinned to the frozen stub — the axiom signed inside
`leanspec/Leanspec/ChapB.lean`'s ENV-C section (`ENVC3`) — and **`axiom` and `theorem` do not
auto-include section instances by the same rule**: an `axiom` keeps only the instances that
elaborating its *statement* needs (the stub therefore carries `[IsAdicComplete …]` but **not**
`[Finite (ResidueField O)]`), while a `theorem` auto-includes every instance variable whose type
mentions an included variable. Transcribed naively, the twin would acquire a `Finite` binder the
contract does not have. So `[Finite (ResidueField O)]` is `omit`ted on this declaration, and the
elaborated type then matches the stub binder-for-binder (checked by `#check`-diffing the two
constants inside the `leanspec` project, which requires `leanfinal`). `[IsAdicComplete …]` is
kept, matching the stub, with `linter.unusedSectionVars` silenced alongside
`linter.unusedVariables`.

SOURCE: `spec/CERTAIN_NODES_2026-08-14.md` CN-12/CN-13; `EFF.HE3.34` (the decorrelation
pattern); landed `ScaleExtraction.lean`.

**TEETH.** `W12-L1X` (`EFF.W12.55`, 0/1,594,090, "FRESH direct cubic read vs SEALED W-11
classifier, pointwise") → **executable regression** retained; this node is the Lean analogue of
that cross-implementation discipline.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open IsLocalRing Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena, with `π` explicit.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC
-- ENV-C.  Neither instance is consumed below; both are kept to match the frozen stub.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
omit [Finite (ResidueField O)] in
/-- **B.44 — the integral-slope shortcut.** At `φ = X` and `ℓ = 1` a `(u,1)`-pure monic `f` of
positive degree with `suppVal X f u 1 = u * f.natDegree` is the `π^u`-rescaling of a monic `G`
of the same degree, with the same splitting type, whose coefficients are `f`'s digits at the
side's heights.  The chapter's independent cross-check on the graded engine: this route uses
only the landed `ScaleExtraction.lean` API, no polygon representation. -/
theorem exists_scaleRoots_of_pure_integral (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) {u : ℕ} (hpure : IsPure X f u 1)
    (hsupp : suppVal X f u 1 = ((u * f.natDegree : ℕ) : ℕ∞)) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧
      f = G.scaleRoots (π ^ u) ∧ typeOf f = typeOf G ∧
      (∀ i, IsLocalRing.residue O (G.coeff i) = digAt π (u * (f.natDegree - i)) (f.coeff i)) := by
  -- Step 1: the polygon hypothesis, cleared into the landed extraction's divisibility.
  have hdvd : ∀ i < f.natDegree, π ^ (u * (f.natDegree - i)) ∣ f.coeff i :=
    (suppVal_X_iff hπ hf hn u).1 hsupp.ge
  -- Step 2: the landed extraction, `typeOf`-preserving.
  obtain ⟨G, hG, hGdeg, hGeq, hGtype⟩ :=
    Uniformity.Density.exists_monic_scaleRoots_typeOf hπ hf u hdvd
  refine ⟨G, hG, hGdeg, hGeq, hGtype, fun i => ?_⟩
  -- Step 3: the digit clause, read off the rescaling coefficientwise.
  have hcoeff : f.coeff i = π ^ (u * (f.natDegree - i)) * G.coeff i := by
    conv_lhs => rw [hGeq]
    rw [coeff_scaleRoots, hGdeg, ← pow_mul]
    ring
  exact (digAt_eq hπ hcoeff).symm

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_scaleRoots_of_pure_integral
end AxCheck
