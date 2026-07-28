/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine

/-!
# HC1/DefsChild — the D.7(vi)-normalized child residual (blueprint §9.5, S9r's Defs
home; ADDITIVE — no accepted statement touched)

**Provenance.** Blueprint §9.5 (the S9 decomposition, pre-approved split): `childR`
is "the D.7(vi)-NORMALIZED child residual on all of A (the new object; MOVES
2395–2418: normalize the minimal-slot development data by the transported unit
T′^{−w′(f)})". §9.5 does not display a Lean body, so the definition follows the
corpus's E-phase precedent for underdetermined Defs (`childW`, `Tower.side`):
CHOICE against a spec structure, with junk fallback. The spec `ChildResData`
transcribes §9.5's own law lists verbatim:
* the S5′ PINNED shape (S9r's lemma: positions `−t′·σ.w B`, scalars = the parent
  ψ-digit — `digPrime`·(the pinned alignment), i.e. the K1 `VertexPin`
  normalization `mfun ≡ 0`) + the D.3(b) key pin `Rc Φ̂ = z^{s′}`;
* the residual apparatus laws hR0/hRne/hRadd/hRlt/hRmul w.r.t. `childW` (§9.5
  S9w's list, in `Stage`'s own field shapes at the pair `(childW, Rc)`);
* the two D.1(b) tie laws that mention `Rc` (w_jump, R_neg — StageCore's shapes).
The S9r/S9w seam is the STRUCTURE BOUNDARY: S9r = inhabitation (the hard
construction block, §9.8: "S9r + S9w"); S9w = the law pack of the DEFINED `childR`
(projections through the choice) + the childW-only tie law w_strict. `Tower`-level
consumers never see `childR` directly — S9a records it through `VertexPin` + the
childW tie (the ↥K/↥K′ cast wall stays inside S9a's proof, where the blueprint put
it). Definitions only — no theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The D.7(vi)-normalized child residual DATA** (blueprint §9.5): a residual
function on all of A for the read `(Φ̂, e′, h′, z̄)` over the child field
`K′ = K⟮z̄⟯ = σ.nextField z̄`, at the child Bézout pair `(s′, t′)`, carrying
exactly the §9.5 law lists (see the file header). S9r proves inhabitation for
every legal read; `childR` below is the choice against it. -/
structure ChildResData (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) : Type u where
  /-- the residual function on all of A -/
  Rc : Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar)
  /-- D.1(e) apparatus: zero -/
  hR0 : Rc 0 = 0
  /-- D.1(e) apparatus: nonvanishing -/
  hRne : ∀ f, f ≠ 0 → Rc f ≠ 0
  /-- D.1(e) apparatus: multiplicativity (the carry-exact product — D7's cmul law
  through `L3_DIV`, §9.5 S9w) -/
  hRmul : ∀ f g, f ≠ 0 → g ≠ 0 → Rc (f * g) = Rc f * Rc g
  /-- D.1(e) apparatus: additivity at equal weight without jump -/
  hRadd : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' (f + g) = childW σ Φhat e' h' f →
      Rc (f + g) = Rc f + Rc g
  /-- D.1(e) apparatus: lower-weight domination -/
  hRlt : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g → Rc (f + g) = Rc f
  /-- D.3(b) at the child: the pinned key residual `R′(Φ̂) = z^{s′}` -/
  hRPhi : Rc Φhat = LaurentPolynomial.T s'
  /-- **the S5′ PINNED shape** (S9r's lemma; the D.7(vi) normalization — the K1
  `VertexPin` clause of the assembled stage): position `−t′·σ.w B`, scalar's
  F-image = the parent ψ-digit exactly (`mfun ≡ 0`, no frame twist) -/
  hS5' : ∀ B, B ≠ 0 → inC Φhat B →
      ∃ c' : (↥(σ.nextField zbar))ˣ,
        Rc B = LaurentPolynomial.C ((c' : ↥(σ.nextField zbar))) *
            LaurentPolynomial.T (- t' * σ.w B) ∧
        ((c' : ↥(σ.nextField zbar)) : F) = σ.digPrime zbar B
  /-- StageCore tie law (D.1(b)): residual cancellation at a weight jump -/
  hWjump : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g) →
      Rc f + Rc g = 0
  /-- StageCore tie law (D.1(b)): `R(−f) = −R(f)` -/
  hRneg : ∀ f, Rc (-f) = - Rc f

open scoped Classical in
/-- **The D.7(vi)-normalized child residual** `childR`, by choice against
`ChildResData` (the `childW`/`Tower.side` precedent); junk `0` when the spec is
uninhabited (never fires on legal reads once S9r lands). -/
noncomputable def childR (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) :
    Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar) :=
  if h : Nonempty (ChildResData σ Φhat e' h' zbar s' t') then h.some.Rc
  else fun _ => 0

/-- **The child parent-scale weight set 𝒜′** (§9.5 S9b: "weightSet := 𝒜′"): the
parent stage weights realized by nonzero Φ̂-coefficients — the set the assembled
child's `weightSet` field is pinned to (its `hWS` reads against
`σ'.wPrev = σ.w`, the `child_wPrev` record). -/
def childWeightSet (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) : Set ℤ :=
  {ν | ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν}

end LeanUrat.HC1
