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
CHOICE against a spec, with junk fallback.

**UNBUNDLED (2026-07-28 remediation round — the Codex batch-confirmation S9
rejection repair).** The E-phase draft of this file bundled the residual apparatus
+ tie laws as `ChildResData` FIELDS, which relocated §9.5's S9w hardness into
S9r's inhabitation sorry and reduced S9w to projections — exactly the confirmed
billing mismatch. Restored shape:
* `ChildResData` = ONLY the CHOICE-SPEC CARRIER — the residual function plus the
  two NORMALIZATION PINS that §9.5 assigns to S9r ("`childR` definition + the S5′
  shape lemma"): the S5′ PINNED shape (positions `−t′·σ.w B`, scalars = the parent
  ψ-digit — `digPrime`·(the pinned alignment), i.e. the K1 `VertexPin`
  normalization `mfun ≡ 0`) and the D.3(b) key pin `Rc Φ̂ = z^{s′}`.
* `ChildResLaws` = the LAW PACK as a `Prop` ON a carrier (§9.5's S9w list: the
  apparatus laws hR0/hRne/hRadd/hRlt/hRmul w.r.t. `childW`, in `Stage`'s own field
  shapes, + the two D.1(b) tie laws mentioning `Rc`: w_jump, R_neg). These are NO
  LONGER structure fields — proving a lawful carrier EXISTS is S9w's OWN theorem
  (`S9w_residualLaws`, the draft's "one genuinely new algebra block"), and the
  laws of the defined `childR` are its clearly-labeled projection corollary
  (`childR_laws`).
* `childR` = choice against carrier + laws (`∃ D, ChildResLaws D`) — the SAME
  witness class as the pre-unbundle bundled structure, so `childR`'s denotation
  is unchanged; only the unit boundaries moved.
S9r keeps its `Nonempty ChildResData` statement (now carrier-only: the
construction SEED; once S9w lands, S9r follows from its first conjunct).
`Tower`-level consumers never see `childR` directly — S9a records it through
`VertexPin` + the childW tie (the ↥K/↥K′ cast wall stays inside S9a's proof,
where the blueprint put it). Definitions only — no theorems, no `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **The D.7(vi)-normalized child residual CARRIER** (blueprint §9.5; UNBUNDLED at
the 2026-07-28 remediation round — see the file header): a residual function on all
of A for the read `(Φ̂, e′, h′, z̄)` over the child field `K′ = K⟮z̄⟯ =
σ.nextField z̄`, at the child Bézout pair `(s′, t′)`, carrying ONLY the two
D.7(vi) NORMALIZATION PINS — the choice-spec carrier (§9.5 S9r: "`childR`
definition + the S5′ shape lemma"). The apparatus/tie LAWS live in
`ChildResLaws` below (S9w's own content, no longer fields). S9r proves carrier
inhabitation (the seed); S9w constructs a LAWFUL carrier. -/
structure ChildResData (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) : Type u where
  /-- the residual function on all of A -/
  Rc : Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar)
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

/-- **The child-residual LAW PACK** (blueprint §9.5's S9w list, as a `Prop` ON a
carrier — the 2026-07-28 unbundle; conjuncts in order: hR0, hRne, hRmul (the
carry-exact product — D7's cmul law through `L3_DIV`), hRadd, hRlt, hWjump,
hRneg): the D.1(e) residual apparatus w.r.t. `childW` in `Stage`'s own field
shapes, plus the two D.1(b) StageCore tie laws that mention `Rc`. Proving a
lawful carrier exists is `S9w_residualLaws`' OWN theorem content — the §9.5
"one genuinely new algebra block". -/
def ChildResLaws {σ : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ}
    {zbar : Fˣ} {s' t' : ℤ} (D : ChildResData σ Φhat e' h' zbar s' t') : Prop :=
  (D.Rc 0 = 0) ∧
  (∀ f, f ≠ 0 → D.Rc f ≠ 0) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → D.Rc (f * g) = D.Rc f * D.Rc g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' (f + g) = childW σ Φhat e' h' f →
      D.Rc (f + g) = D.Rc f + D.Rc g) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f < childW σ Φhat e' h' g → D.Rc (f + g) = D.Rc f) ∧
  (∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      childW σ Φhat e' h' f = childW σ Φhat e' h' g →
      childW σ Φhat e' h' f < childW σ Φhat e' h' (f + g) →
      D.Rc f + D.Rc g = 0) ∧
  (∀ f, D.Rc (-f) = - D.Rc f)

open scoped Classical in
/-- **The D.7(vi)-normalized child residual** `childR`, by choice against a LAWFUL
carrier — carrier + `ChildResLaws`, the SAME witness class as the pre-unbundle
bundled structure, so the denotation is unchanged (the `childW`/`Tower.side`
precedent); junk `0` when the spec is uninhabited (never fires on legal reads
once S9w lands). -/
noncomputable def childR (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ)
    (zbar : Fˣ) (s' t' : ℤ) :
    Polynomial ℤ_[p] → LaurentPolynomial ↥(σ.nextField zbar) :=
  if h : ∃ D : ChildResData σ Φhat e' h' zbar s' t', ChildResLaws D then h.choose.Rc
  else fun _ => 0

/-- **The child parent-scale weight set 𝒜′** (§9.5 S9b: "weightSet := 𝒜′"): the
parent stage weights realized by nonzero Φ̂-coefficients — the set the assembled
child's `weightSet` field is pinned to (its `hWS` reads against
`σ'.wPrev = σ.w`, the `child_wPrev` record). -/
def childWeightSet (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) : Set ℤ :=
  {ν | ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν}

end LeanUrat.HC1
