# UNIT CUR — VERDICT: THE CURRENCY LEMMA PROVED — `inertiaDegOf` = the classical
residue degree through any closure realization, Lean-core, NO completeness — 2026-08-31

**Re-grounding.** The corpus's `(e, f)` currency (`Density/TypeOf.lean`) reads the residue
degree of a monic irreducible `g` over a DVR `O` as the GCD of `addVal ∘ Algebra.norm` over
the monogenic order `A = O[x]/(g)`; the FGMN cite package's caveat A (I10CitePkg docstring,
item 1) records that tying this gcd read to the source's field invariant was a TRUSTED
READING, not a theorem.  The landed `TypeOfFaithful.inertiaDegOf_eq_inertiaDeg'` covered only
the maximal locus (`A` itself a DVR).  This unit proves the identification OFF the maximal
locus and stages the source-side statement carrier the owner-confirmed addendum asked for.

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG76.lean` — 26 declarations, ZERO sorries,
zero errors/warnings; **26/26 `#print axioms` lines exactly Lean core
{propext, Classical.choice, Quot.sound}**.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG76.lean` (5 increments, each GREEN before
the next); targeted `lake build Uniformity.ChapI.IFCG76` GREEN (8958 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the sanctioned one-line import
(IFCG75 → IFCG76 → IFCG72).  IFCG75.lean untouched; no git ops; C130s18 never entered my
import closure.

## ★★★ THE MAIN THEOREM (all in namespace `Uniformity.Density.IFCG76`)

    theorem inertiaDegOf_eq_inertiaDeg'_of_closure
        {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        {B} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B]
        {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
        (bB : Basis (Fin g.natDegree) O B)
        (ι : AdjoinRoot g →ₐ[O] B) (hι : Function.Injective ι) :
        inertiaDegOf g = (IsLocalRing.maximalIdeal B).inertiaDeg' O

The order's gcd read equals the CLASSICAL residue degree of any rank-`deg g` free DVR `B`
receiving an injective `O`-algebra map from the order — mathematically `B = O_L` (any such
`B` is forced: it is integrally closed with fraction field `L`, hence IS the integral
closure; the file docstring records this uniqueness argument).  Companions:
`inertiaDegOf_eq_of_closure` (valuation form: `inertiaDegOf g = v(N_{B/O}(ϖ))`),
`ramIndexOf_eq_ramificationIdx'_of_closure`, `typeOf_eq_classical_of_closure` (the
`TypeOfFaithful` triple with the maximal-locus hypothesis replaced by the realization).
**No completeness hypothesis anywhere in the file** — like TypeOfFaithful, completeness is
what makes the realization CHECKABLE, not what makes the identity true.

## The mechanism (the new mathematics, §1 of the file)

No localization, no torsion modules, no integral-closure theory:

1. **Norm transport** (`norm_algHom_of_injective`): an injective `O`-algebra map between
   free `O`-algebras of the same finite rank preserves `Algebra.norm` EXACTLY — conjugate
   the multiplication matrices through the matrix `M` of `ι` (`M·X = Y·M` from
   `ι ∘ lmul x = lmul (ι x) ∘ ι`) and cancel `det M ≠ 0` in the domain `O`
   (`det_toMatrix_ne_zero`, via `Matrix.exists_mulVec_eq_zero_iff`).
2. **The adjugate conductor** (`exists_preimage_det_smul`): `det(ι) • B ⊆ range ι` —
   Cramer's identity `M * adjugate M = det M • 1` read through the bases.  This replaces the
   classical finite-index conductor argument outright.
3. **The squeeze** (§4): `f₀ := v(N ϖ_B)` divides every order norm-valuation (transport +
   the DVR normal form); conversely the conductor elements `ι⁻¹(det(ι) • ϖ^k)`, `k = 1, 2`,
   have norm-valuations `n·v(det) + k·f₀`, and the gcd divides their difference `f₀`.
   Then the landed TypeOfFaithful endgame (ramification data + the quarried fundamental
   identity `e·f = finrank`) pins `f₀ = inertiaDeg'`.

## The anchors (unconditional, both currencies — consistency teeth for the package's keys)

| theorem | statement |
|---|---|
| `inertiaDegOf_eisenstein` | Eisenstein `f` (coeffs in `𝔪`, `a₀ ∉ 𝔪²`): `inertiaDegOf f = 1`, EVERY degree, no DVR/completeness (standalone extraction of CN-20's inline step) |
| `ramIndexOf_eisenstein` / `efPair_eisenstein` | `ramIndexOf f = deg f`; `efPair f = (deg f, 1)` |
| `eisenstein_classical` | the mirror recon found missing: on the DVR locus `(ramificationIdx', inertiaDeg') = (deg f, 1)` |
| `inertiaDegOf_eisKey` / `efPair_eisKey` | at leg E's key: `inertiaDegOf (eisKey π c e') = 1`, `efPair = (e', 1)` (`c` unit via `residue c ≠ 0`) |
| `inertiaDegOf_of_irreducible_map` | unramified (`ḡ` irreducible): `inertiaDegOf g = deg g` (from InertLeaf's Nakayama divisibility) |
| `hasResidueDegree_eisenstein` / `hasResidueDegree_of_irreducible_map` | both anchors in SOURCE currency (unramified DVR instance from the quarried `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`) |

## The source-side carrier (the addendum's restatement vehicle, §5)

    structure DVRClosure (g : Polynomial O) : Type (u+1)   -- carrier + [CommRing/IsDomain/IsDVR/Algebra O] + Basis (Fin deg g) + emb : AdjoinRoot g →ₐ[O] carrier + emb_injective
    def HasResidueDegree (g : Polynomial O) (f : ℕ) : Prop :=
      ∃ D : DVRClosure g, (maximalIdeal D.carrier).inertiaDeg' O = f

* ★ `inertiaDegOf_eq_of_hasResidueDegree : HasResidueDegree g f → inertiaDegOf g = f` —
  **THE BRIDGE**, unconditional: the one theorem a source-side restatement of the cite legs
  consumes to recover the landed gcd-currency legs.
* `hasResidueDegree_unique` — the carrier is a genuine invariant (single-valued).
* `hasResidueDegree_iff_of_closure` — the full ⟺ given ANY realization (the ← direction is
  where realization existence enters; the restated legs assert `HasResidueDegree`
  conclusions, so existence rides along and consumers only ever fire →).
* `hasResidueDegree_of_isDVR` — non-vacuity: on the maximal locus the identity embedding
  realizes the closure.
* `inertiaDegOf_scale_of_hasResidueDegree` — leg U's genre across two base rings:
  `HasResidueDegree h (d·f') ∧ HasResidueDegree H f' ⟹ inertiaDegOf h = d·inertiaDegOf H`
  (leg R's genre is the bridge at `f := deg ψ`; leg E's is `d = 1`).

## FORMULATION FINDING (charge item 1, resolved with a refutation)

The charge's candidate `∃ P, addVal (norm P) = inertiaDegOf h` (attained gcd) is **FALSE**:
the corpus's own recorded UNIFORMITY-P2 example (`X² − π³` over `ℤ₃`, TypeOf.lean docstring)
has norm-valuation set `{2, 3, 4, …}` with gcd `1` never attained.  Stronger: ANY
corpus-internal ∃-witness form built from norm-valuation clauses alone is EXTENSIONALLY the
gcd read (`w := v∘N/gcd` is always a tautological witness), so no re-wording can eliminate
caveat A — the elimination had to be a theorem against a mathlib-native field invariant,
which is what landed.  The right "witness" is the closure realization itself.

## NOTE FOR THE ORCHESTRATOR — caveat A amendment (I10CitePkg.lean docstring, item 1)

Suggested replacement text for the caveat-A block (do not enact here; orchestrator amends):

> 1. *Caveat A (order vs. field / gcd read) — DISCHARGED TO A SINGLE REALIZATION FACT
>    (IFCG76, 2026-08-31).*  The `(e, f)` currencies are the orders' gcd reads
>    (`inertiaDegOf`); the identification with the classical field invariants is now the
>    Lean-core THEOREM `IFCG76.inertiaDegOf_eq_inertiaDeg'_of_closure` (with
>    `ramIndexOf`/`typeOf` mirrors and the `HasResidueDegree` bridge), conditional only on
>    a closure realization (`IFCG76.DVRClosure`: the integral closure as a rank-`deg` free
>    DVR extension — Serre, *Corps Locaux* II §2 Prop. 3, valid over a complete base
>    WITHOUT separability).  At the package's own keys the realization is landed
>    (`eis_isDVR`, `adjoinRoot_isDVR`) and the reads are machine-checked
>    (`efPair_eisKey = (e', 1)`, `inertiaDegOf_of_irreducible_map = deg`).  Remaining
>    trusted content: EITHER restate the legs source-side with `HasResidueDegree`
>    conclusions (existence rides along inside the cite; the gcd legs then follow by the
>    unconditional bridge), OR sign the one realization fact for the factors `h ∣ g`
>    arising in the legs.  Either way the per-equality currency reading is gone.

## Honest remainder (this unit's fence)

1. **Realization existence off the maximal locus is NOT proved** (`∃ D : DVRClosure g` for
   general monic irreducible `g` over complete `O`).  It is the classical Serre II §2
   Prop. 3; a future unit can either prove it (hard: unique-extension package; possible
   mathlib route via `spectralNorm`/Henselian theory) or fold it into the restated cite
   (recommended — it is the source's own standing assumption).  All anchors and all
   maximal-locus cases are unconditional.
2. The legs are NOT restated here (statement-shape work at the signing surface — the
   follow-up unit per the addendum); this unit supplies the carrier + bridge they consume.
3. `typeOf_eq_classical_of_closure` takes `Irreducible g` as an explicit hypothesis
   (mirroring the landed TypeOfFaithful convention), although the realization forces it.

## File map (`leanfinal/Uniformity/ChapI/IFCG76.lean`, 26 declarations)

§1 `det_toMatrix_ne_zero`, ★ `norm_algHom_of_injective`, ★ `exists_preimage_det_smul` ·
§2 anchors (7 gcd/classical-currency theorems) · §3 closure-side ports of TypeOfFaithful's
helpers to abstract `B` (4) · §4 `injective_algebraMap_of_embedding`,
★ `inertiaDegOf_eq_of_closure`, ★★★ `inertiaDegOf_eq_inertiaDeg'_of_closure`,
`ramIndexOf_eq_ramificationIdx'_of_closure`, `typeOf_eq_classical_of_closure` ·
§5 `DVRClosure`, `HasResidueDegree`, ★★ `inertiaDegOf_eq_of_hasResidueDegree`,
`hasResidueDegree_unique`, `hasResidueDegree_of_isDVR`, `hasResidueDegree_eisenstein`,
`hasResidueDegree_of_irreducible_map`, `hasResidueDegree_iff_of_closure`,
`inertiaDegOf_scale_of_hasResidueDegree` · AxCheck footer (26 lines).
Imports: Density.{TypeOfFaithful, NormLeaves, InertLeaf} + Quarry.AdjoinRootDVR + IFCG39.
Aggregator: one line in `Uniformity/ChapI.lean` (IFCG75 → IFCG76 → IFCG72).

## New definitions (trust boundary — flag for review)

`DVRClosure`, `HasResidueDegree` (the source-side carriers — the point of the unit; their
faithfulness argument is in the structure docstring: any realization IS `O_L`).  No landed
statement changed; TypeOf/TypeOfFaithful/I10CitePkg all byte-untouched.

## Repair log (4 error rounds total, all first-increment-local)

1. Inc 1: `Basis` → `Module.Basis` at this pin (`open Module (Basis)`); `Algebra.lmul` is
   already a linear map (dropped `.toLinearMap`); closed the det-conjugation with
   `Algebra.leftMulMatrix_apply`.
2. Inc 1: `*ᵥ` notation not in scope (explicit `Matrix.mulVec`); `ι` vs `ι.toLinearMap`
   syntactic mismatch (one `AlgHom.toLinearMap_apply` rewrite); `Matrix.smul_mulVec_assoc` →
   `Matrix.smul_mulVec`.
3. Inc 2: `Irreducible.not_unit` → `.not_isUnit`; eisKey coefficient `simp` discharges
   (`he'.ne`, `Nat.ne_of_lt hi`, `hipos.ne'`); one `calc` for the `π ∣ c` cancellation.
4. Inc 4: helpers' implicit base ring underdetermined at two `obtain` sites (`(O := O)`);
   `Nat.dvd_sub'` → `Nat.dvd_sub`; rewrote `injective_algebraMap_of_embedding` via
   `ι.commutes`.  Incs 3 and 5 first-try.
