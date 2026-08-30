# UNIT UBB — VERDICT: LEGS (a)+(b) PROVED, THE VANISHING HALF OF THE HEART PROVED OUTRIGHT, THE BRIDGE REDUCED TO ONE NAMED COUNT LAW (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG27.lean` (555 lines, ZERO sorries; all
17 AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`;
zero warnings; the C.33 cite does not occur; no landed file touched except the
sanctioned one-line aggregator import in `Uniformity/ChapI.lean`; IFCG26 untouched;
no git push).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG27.lean` (final: zero output, exit 0),
targeted `lake build Uniformity.ChapI.IFCG27` green (8934 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE RESULT — `UnramifiedBlockBridge δ e` reduced to ONE named count equality

    theorem unramifiedBlockBridge_of_blockCount (hδ : 1 ≤ δ) :
        UnramifiedBlockCount δ e → UnramifiedBlockBridge δ e
    theorem decidedSliceAt_all_of_remainder_blockCount (hR) (hBC) :
        ∀ n, DecidedSliceAt n            -- ★★★ composed with IFCG25's capstone

The census front now rests on `ConeRemainderLaw e σ` (e ≥ 3) + `UnramifiedBlockCount
δ e` (δ, e ≥ 2) — the bridge's ∃-telescope (extension, instances, q^δ count, linear
point, vanishing clause) is GONE from the open surface.  `UnramifiedBlockCount δ e` is
the count equality ALONE, at the CONCRETE extension (no existentials left for the
successor unit):

    def UnramifiedBlockCount (δ e : ℕ) : Prop :=
      ∀ O [complete DVR, finite residue] (φ : Polynomial O) (hφ : IsKey φ),
        φ.natDegree = δ → ∀ s' N, 1 ≤ N →
        letI := keyIsDomain hφ; letI := adjoinRoot_isDVR hφ;
        letI := adjoinRoot_finite_residueField hφ
        stratDecCount O (δ*e) ⟨fScale δ s'⟩ N ((φ.map (residue O))^e)
          = stratDecCount (AdjoinRoot φ) e ⟨s'⟩ N
              ((X - C (residue _ (AdjoinRoot.root φ)))^e)

## ★★ LEGS (a) AND (b) — CLOSED (charge item 1)

    theorem adjoinRoot_isAdicComplete (hφ : IsKey φ) :     -- leg (a)
      IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ)
    theorem residueCard_adjoinRoot (hφ : IsKey φ) :        -- leg (b)
      residueCard (AdjoinRoot φ) = residueCard O ^ φ.natDegree

Mechanism (a): Quarry's `𝔪' = 𝔪·O'` (`adjoinRoot_maximalIdeal_eq`) turns the goal into
`𝔪`-adic completeness of `O'` as an `O`-MODULE via mathlib's
`IsAdicComplete.map_algebraMap_iff` (Basic.lean:699 at this pin); Hausdorffness is the
mathlib Krull instance for finite modules over Noetherian local rings; precompleteness
is NEW and GENERAL: `isPrecomplete_of_basis` (any finite free module over an
`I`-precomplete ring is `I`-precomplete, limits taken coordinatewise through
`mem_smul_top_iff_repr`).  NOTE: the pinned mathlib has NO finite-module completeness
lemma — `isPrecomplete_of_basis` fills that hole and is reusable.
Mechanism (b): Quarry's `residueFieldEquiv` + `natCard_adjoinRoot` (power-basis count
`#(K[x]/(g)) = q^{deg g}`).

## ★★ THE VANISHING HALF OF THE HEART — PROVED OUTRIGHT (no Hensel blocks needed!)

    theorem stratDecCount_pow_eq_zero_of_not_fScale (hφ : IsKey φ)
        (hs : ∀ s', s ≠ fScale φ.natDegree s') (N) :
      stratDecCount O (φ.natDegree * e) ⟨s⟩ N ((φ.map (residue O))^e) = 0

Mechanism: any decided class in the `p^e` stratum has a lift `F`; every monic
irreducible factor of `F` has residual a POSITIVE power of `p` (unique factorization,
`factor_residual_pow`), so B.52's `key_natDegree_dvd_inertiaDegOf` forces `δ ∣ f` on
every `efPair` — the label IS `fScale δ` of its f-divided multiset
(`typeOf_mem_fScale_range`).  The bridge's vanishing clause carries NO open content.

## ★ THE SCALAR-EXTENSION CLAUSE — CLOSED, plus a general finite-field asset

    theorem exists_monic_irreducible_natDegree (K) [Field K] [Finite K] (hδ : 1 ≤ δ) :
      ∃ p, p.Monic ∧ p.natDegree = δ ∧ Irreducible p
    theorem exists_scalarExtension (O) (hδ : 1 ≤ δ) : ∃ O' [...], q' = q^δ

Existence via POSITIVITY of IFCG19's Möbius necklace identity (the `(1,δ)` term `q^δ`
dominates the geometric tail `≤ q^δ − 1`; the divisor-pair second coordinates inject
into `range δ`).  Not in mathlib at this pin.

## ★ NONVACUITY — the `e = 1` member at EVERY `δ ≥ 1`

    theorem unramifiedBlockCount_one (hδ : 1 ≤ δ) : UnramifiedBlockCount δ 1

Both sides are IFCG19's inert monomial census (`q^{δ(N−1)}` at the inert label, `0`
elsewhere); `fScale δ {(1,1)} = {(1,δ)}` matches exactly, and
`(q^δ)^{1·(N−1)} = q^{δ(N−1)}` closes the value.  This certifies the count law's shape
(labels, level normalization, the concrete `O'`/`p'` choices) against a landed
instance.  The `(2,2)` instrument the charge suggested IS the open heart at its
smallest — see the fence.

## What UBB did NOT close (the exact fence) + the mechanism map for the successor

`UnramifiedBlockCount δ e` for `δ, e ≥ 2` — the level-exact Hensel block
correspondence.  Scoping (from this unit's design work, recorded for the heart unit):

1. **Frobenius** `σ : AdjoinRoot φ →ₐ[O] AdjoinRoot φ`: Hensel-lift `θ̄^q` from the
   seed `(root φ)^q` (`henselianLocalRing_of_adicComplete` is landed in LocalData;
   `p` separable since finite fields are perfect); `σ^δ = id` by uniqueness of the
   lift; **σ-invariants = O** needs the 𝔪-adic induction + Krull intersection.
2. **Blocks**: over `O'` the residual `p` splits into `δ` distinct linear factors
   (conjugates `θ̄^{q^k}`); the landed `exists_monic_factorization_finset` +
   `monic_factorization_unique` give the block decomposition of any lift; IFCG16's
   `factor_sub_mem_of_mul_sub_mem` gives LEVEL-EXACTNESS of the `θ̄`-block map;
   block conjugacy `B_k = σ^k(B_0)` for `F ∈ O[x]` from uniqueness; injectivity of
   the class map from conjugacy; SURJECTIVITY by counting — H124b's
   `card_levelZeroStratum` gives `q^{δe(N−1)}` on both sides.
3. **THE DEEPEST LEG — typeOf descent**: `typeOf_O F = fScale δ (typeOf_{O'} B_0)`.
   Reduces (via landed `typeOf_prod`, no coprimality needed) to: for `C` irreducible
   over `O'`, `G := ∏_k σ^k(C) ∈ O[x]` is irreducible with
   `inertiaDegOf_O G = δ · inertiaDegOf_{O'} C`.  This is `inertiaDegOf`-definition
   work (norm valuations across the extension) of Chapter-B scale — B.52/B.54/B.61
   are the model; it is the real content of the heart and needs its own unit.

## File map (`leanfinal/Uniformity/ChapI/IFCG27.lean`, 555 lines)

§1 `finite_adjoinRoot_of_monic`, `natCard_adjoinRoot` · §2 `mem_smul_top_iff_repr`,
★ `isPrecomplete_of_basis` · §3 `adjoinRoot_isDVR`, `adjoinRoot_maximalIdeal_eq`,
★★ `adjoinRoot_isAdicComplete`, `adjoinRoot_finite_residueField`,
★★ `residueCard_adjoinRoot` · §4 ★ `exists_monic_irreducible_natDegree`,
★ `exists_scalarExtension` · §5 `factor_residual_pow`, `typeOf_mem_fScale_range`,
★★ `stratDecCount_pow_eq_zero_of_not_fScale` · §6 ★★ `UnramifiedBlockCount`,
★★ `unramifiedBlockBridge_of_blockCount` · §7 ★ `unramifiedBlockCount_one` ·
§8 ★★★ `decidedSliceAt_all_of_remainder_blockCount` · AxCheck footer (17 lines, all
Lean core).  Consumed: IFCG25 (fScale, bridge, capstone), IFCG19 (Möbius census,
inert monomials), Quarry AdjoinRootDVR (DVR/maximal/residueFieldEquiv), B53b
(keyIsDomain), B52 (`key_natDegree_dvd_inertiaDegOf`), B01 (IsKey), Hensel
(`exists_monic_lift`), mathlib `IsAdicComplete.map_algebraMap_iff` +
`AdjoinRoot.powerBasis'`.

## Repair log (5 error rounds, all mechanical)

1. `Basis` is `Module.Basis` at this pin (post-namespace-move mathlib).
2. `IsAdicComplete`'s anonymous constructor takes no explicit fields — provide parents
   as local instances, `exact IsAdicComplete.mk`.
3. `Monic.natDegree_map` needs the BASE monicity (`hφ.monic`, not the mapped one) —
   dot-notation on the wrong Monic produced a double-map pattern.
4. `rw [← h] `with a hypothesis whose RHS occurs on both sides of the goal loops —
   rewrite AT the hypothesis first (`rw [h2] at hxprod`), or `conv_rhs`.
5. Inline `(by omega)` against a named-argument metavariable (`m := δ`) elaborates
   early and fails — hoist positivity to a `have` (CN5's telescope trap, omega flavor).
   Also: `push_neg` deprecated at this pin → `push Not`.
