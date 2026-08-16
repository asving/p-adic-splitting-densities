/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D13

/-!
# Uniformity.ChapD.D24 — `liftC6`, the `(C6-lift)` exact lift, point-free

**Chapter D, NODE D.24** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §4, the level-1 gauge
layer; amendments A-1 and A-D.1 govern — **A-D.1/D-D4 RE-SIGNS this SIGNATURE**, see below).
ENV-D4 — the concrete level-1 arena over the bundle (CHAP-B's ENV-A′: a complete-DVR bundle `O`),
with `π` bound by the definition itself. One signed declaration.

*`(C6-lift)`: the exact lift, point-free.* For `e₁ h f₁ : ℕ`, a residue section
`σ : ResidueField O → O`, a height `M : ℕ` and a coordinate vector `λ : Fin f₁ → ResidueField O`,

`liftC6 π e₁ h σ M λ = Σ_{r : Fin f₁} C (σ (λ r) · π ^ (a(M) − r·h).toNat) · X ^ (i(M) + e₁·r)`

— the corpus's `L_M(λ) = Σ_r λ̃_r x^{i(M)+e₁r} π^{a−rh}` on coordinates in the basis
`1, η, …, η^{f₁−1}` (`EFF.T1.20`).

## What is NOT here (the point-free discipline, §4's design note)

Three things a reader may expect and must not look for in this file:

1. **No properties.** This node is a `def`. Integrality of the π-exponents, the degree bound
   `natDegree < e₁·f₁`, the exact height `suppVal X (liftC6 …) h e₁ = M`, the x-support formula
   and the x-free criterion are all NODE D.25, under the live-domain hypothesis
   `hM : e₁·f₁·h < M` and the section hypotheses `hσ : residue ∘ σ = id`, `hσ0 : σ 0 = 0`.
   **Those hypotheses are deliberately absent from the definition** — the blueprint signs them as
   hypotheses of the property lemmas, not of the def, so `liftC6` is total in `σ`.
2. **No `ξ`-evaluation.** The clause `(C6-residue)` at a tower point `ξ` with its embedding `ι_ξ`
   needs a valued-extension carrier that `leanfinal` does not have; chapter C owns it (GC-7).
   What this chapter transcribes is the point-free shadow: `γ_M(L_M(λ)) = λ` on coordinates, at
   NODE D.26.
3. **No sub-live-domain lemma.** Below the live domain the `.toNat` truncates and the definition
   is junk. That is faithful, not sloppy: `EFF.T1.01` asserts a full integral `K₁`-digit slot
   ONLY on the proved live domain `k > D′h` ("No full `K₁`-slot is asserted at `k ≤ D′h`"), and
   the transcription of that sentence is precisely the ABSENCE of any lemma reading `liftC6`
   there. D.25 clause 1 proves `0 ≤ aexp M − r·h` on the live domain, which is what makes the
   `.toNat` exact where anything is claimed.

## DEFECT D-D4 (A-D.1) — why `π` is EXPLICIT and FIRST

ENV-D4's section variable is `{π : O}`, implicit. **It cannot be the binder here.** `π` occurs
only in this definition's BODY, never in its type, so under an implicit binder every call site
(`liftC6 … e₁ h σ M l` at D.25 clauses 2–4, D.26, D.28) would leave an unsolvable
implicit-argument metavariable — Lean cannot invent the uniformizer. `π` is therefore an EXPLICIT
FIRST argument, matching the landed convention `Uniformity.Density.Leaf.digAt (π : O)` (B.21).
The rule generalises: *a binder that only the body mentions must be in the binder list* — the
definition-level form of the B.42 inline-binder rule this chapter runs for truth-bearing
hypotheses. ENV-D4's block is left byte-unchanged (it is CHAP-B's ENV-A′ verbatim by contract);
its `{π : O}` is simply not the binder for this chapter's def-class nodes, and this file
accordingly declares the ENV-D4 variables WITHOUT it.

`f₁` stays IMPLICIT (it is determined by `l`) and is EXPLICIT in D.26's `gammaCoord` (nothing
determines it there) — as the original text writes them.

## Faithfulness

**⚠ Mandatory, trust-boundary definition.** Flagged for the chapter cross-read and for human
review (parent CLAUDE.md trust boundary). The three coordinates of the transcription:

* the π-exponent is `(aexp e₁ h M − r·h).toNat`, i.e. the corpus's `a − rh` with `a = a(M)` from
  D.13's exact-height identity — `.toNat` because `Polynomial.C`'s argument is a power of `π` in
  `O` and `O` has no negative powers. Exactness of the `.toNat` is D.25 clause 1, not a fact this
  file may assume;
* the x-exponent is `iexp e₁ h M + e₁·r`, i.e. `i(M) + e₁r`, so the `f₁` terms sit in DISTINCT
  residues mod `e₁` — no collision, which is what makes the support formula of D.25 clause 3 a
  bijection onto `{i(M) + e₁r : l r ≠ 0}`;
* the coefficient is `σ (l r)`, the fixed residue section applied to the `r`-th coordinate — the
  corpus's `λ̃_r`. Nothing forces `σ` to be a section at definition time.

DEPENDS: D.13 (`iexp`, `aexp`) · mathlib `IsLocalRing.ResidueField`, `Polynomial.C`,
`Polynomial.X`, `Int.toNat`, `Finset.sum` — all name-verified at the v4.31.0 pin.

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
verbatim (stage 0e, the D-D4-repaired form).

SOURCE: `EFF.T1.20` (the boxed `(C6-lift)` with the fixed residue section `σ : F_Q → Ô`,
`res(σ(a)) = a`, `σ(0) = 0`); `EFF.T1.30` (the A6/GENTOW6 lift pin is this display together with
D.25's support clause).

**TEETH.** T1 §4.2 checks 1 (live-domain boundary), 7 and 10 → D.25 + the §10 gates; nothing is
scored inside this file, which is a definition over an abstract bundle and admits no `decide`.

ENVIRONMENT: ENV-D4 (+ `f₁` as an implicit binder; no `Finite` instance — nothing counts).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

open IsLocalRing Polynomial

-- ENV-D4 (blueprint §0.1) = CHAP-B's ENV-A′, MINUS its `{π : O}`: per defect D-D4 this node
-- binds `π` itself, explicitly and first.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **D.24 — `(C6-lift)`, point-free.**
`L_M(λ) = Σ_r λ̃_r x^{i(M)+e₁r} π^{a(M)−rh}` (`EFF.T1.20`), written on coordinates
`λ : Fin f₁ → ResidueField O` in the basis `1, η, …, η^{f₁−1}` and lifted by the residue section
`σ`.  `π` is EXPLICIT and FIRST (defect D-D4: it occurs only in the body); `f₁` is implicit,
inferred from `l`.  Total: the section hypotheses `residue ∘ σ = id`, `σ 0 = 0` and the
live-domain hypothesis `e₁·f₁·h < M` belong to D.25's property lemmas, and below the live domain
the `.toNat` truncates and no lemma of this chapter reads the result. -/
noncomputable def liftC6 (π : O) {f₁ : ℕ} (e₁ h : ℕ) (σ : ResidueField O → O) (M : ℕ)
    (l : Fin f₁ → ResidueField O) : Polynomial O :=
  ∑ r : Fin f₁,
    Polynomial.C (σ (l r) * π ^ (aexp e₁ h M - (r : ℕ) * h).toNat)
      * Polynomial.X ^ (iexp e₁ h M + e₁ * (r : ℕ))

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.liftC6

end AxCheck
