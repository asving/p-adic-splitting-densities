/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C107 — the residual censuses `S_λ(K)` and `C₀(q)`

**Chapter C, NODE C.107** [def] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT count layer),
**ENV-C4** — pure residue-side algebra over a finite field, no local base `O`.  Three
definitions, the counting vocabulary of `(HT-rec)` / `(HT-branch)` / `(HT-global)`:

* `residualTypeOf p` — the factorization type of `p`, i.e. the multiset of pairs
  `(deg Pᵢ, multiplicity of Pᵢ)` over the DISTINCT irreducible factors of `p`.  This is
  GC-4's landed `FactorizationType` carrier used as the value of `λ`; it is *not* a new type.
* `sideCensus K lam` — the corpus's `S_λ(K)`: how many monic `p ∈ K[y]` with `p(0) ≠ 0` have
  factorization type `λ`.  This is the per-side residual count that `(HT-rec)` sums over.
* `configCensus K d` — the corpus's `C₀(q)`: how many configurations of DISTINCT monic
  irreducibles realize the prescribed degree multiset `d`.  This is the level-0 count.

## The A-C.1 determinations transcribed here (signed; divergences from the prose STATEMENT)

1. **`CommRing` + `IsDomain` + `UniqueFactorizationMonoid` binders, not `Field`.**  The
   consumers apply these at `resField φ`'s OWN ring structure; demanding `[Field K]` would
   force a `Field`-instance diamond at every use site.  Every binder is derivable from
   `IsKey φ`, so nothing is lost.  `[Finite K]` is bound on `sideCensus` only — the one
   definition that counts (GC-6.4, minimal binding).
2. **`Nat.card`, not `Finset.card`.**  The blueprint's prose says "both as `Finset.card`
   definitions"; the signed SIGNATURE says `Nat.card` on a subtype, and the signature governs.
   The two agree wherever the subtype is finite, which is exactly where §13's gates read spot
   values; `Nat.card` additionally makes the definitions total (junk value `0` on an infinite
   `K` for `configCensus`, which carries no `[Finite K]`).
3. **`configCensus` is keyed on the DEGREE multiset `d` alone.**  The STATEMENT's datum is
   `{(dᵢ, mᵢ)}`; the multiplicities `mᵢ` are NOT part of the level-0 configuration count — they
   enter through the side-tagged orbit factor `κ₀` of C.108, which is a separate data field.
   `P.Nodup` is what "distinct monic irreducibles `P̄ᵢ`" means.

## What this node does NOT ship

The "standard generating identities as companions where §13's gates need spot values" of the
STATEMENT are **not** declared here: they are §13's business (the `htSpot` rows, C.115/C.123),
and the TEETH of this node are exactly those spot values, not a law proved at this node.

**DEPENDS.** Landed `Uniformity.FactorizationType` (GC-4's carrier for `λ`, from
`Uniformity/Density/LocalData.lean`); B.26/B.27's ENV-D census toolkit shapes, by shape only.

## Status

Definitional (no proof obligation).  Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

/-- The factorization type of a polynomial (the `(deg, mult)` multiset) — stated over
`CommRing` + UFD binders so it applies at `resField φ`'s OWN ring structure (no `Field`
diamond; the instances are derivable from `IsKey φ` at every consumer). -/
noncomputable def residualTypeOf {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] (p : Polynomial K) : FactorizationType :=
  open Classical in
  ⟨(UniqueFactorizationMonoid.factors p).toFinset.val.map
    (fun q => (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))⟩

-- The `overlappingInstances` linter flags `[IsDomain K]` and `[UniqueFactorizationMonoid K]` as
-- both implying the cancel-mul-zero instances and suggests dropping the latter.  It is a false
-- positive here: `residualTypeOf` needs `UniqueFactorizationMonoid K` to get
-- `UniqueFactorizationMonoid (Polynomial K)`, so the binder is load-bearing — and the binder
-- list is the A-C.1 signed signature, which is frozen.
set_option linter.overlappingInstances false in
/-- `S_λ(K)` — the side census: monic, nonzero constant term, prescribed type. -/
noncomputable def sideCensus (K : Type*) [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (lam : FactorizationType) : ℕ :=
  Nat.card {p : Polynomial K // p.Monic ∧ p.coeff 0 ≠ 0 ∧ residualTypeOf p = lam}

/-- `C₀(q)` — the level-0 configuration census: distinct monic irreducibles of the
prescribed degrees. -/
noncomputable def configCensus (K : Type*) [CommRing K] [IsDomain K] (d : Multiset ℕ) : ℕ :=
  Nat.card {P : Multiset (Polynomial K) //
    P.map Polynomial.natDegree = d ∧ (∀ q ∈ P, q.Monic ∧ Irreducible q) ∧ P.Nodup}

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.residualTypeOf
#print axioms Uniformity.Density.Tower.sideCensus
#print axioms Uniformity.Density.Tower.configCensus

end AxCheck
