# UNIT UBC — VERDICT: THE BLOCK CORRESPONDENCE CLOSED; THE COUNT LAW REDUCED FROM A TWO-PARAMETER FAMILY TO ONE ONE-PARAMETER INERTIA LEG (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG29.lean` (1973 lines, ZERO sorries; all
41 AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`;
zero warnings; the C.33 cite does not occur — the two textual mentions are the docstring
fence itself; no landed file touched except the sanctioned one-line aggregator import in
`Uniformity/ChapI.lean`; IFCG28 untouched — `git diff` empty; no git operations).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG29.lean`
(final: axiom lines only, exit 0), targeted `lake build Uniformity.ChapI.IFCG29` green
(8937 jobs), aggregator `lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE RESULT — `UnramifiedBlockCount δ e` for ALL e, from ONE leg per δ

    theorem unramifiedBlockCount_of_inertiaScaling (h : InertiaScaling δ) (e : ℕ) :
        UnramifiedBlockCount δ e
    theorem unramifiedBlockBridge_of_inertiaScaling (hδ : 1 ≤ δ) (h : InertiaScaling δ)
        (e : ℕ) : UnramifiedBlockBridge δ e
    theorem decidedSliceAt_all_of_remainder_inertiaScaling (hR) (hIS) :
        ∀ n, DecidedSliceAt n            -- ★★★ composed with IFCG27's capstone

UBB left the count law as a `(δ, e)`-indexed FAMILY. The remainder is now the
ONE-PARAMETER, `e`-INDEPENDENT leg

    def InertiaScaling (δ : ℕ) : Prop :=
      ∀ O [complete DVR, finite residue] (φ) (hφ : IsKey φ), φ.natDegree = δ →
        ∀ (C : Polynomial (AdjoinRoot φ)) (G : Polynomial O), C.Monic → Irreducible C →
          C.map (residue _) = (X - C (residue _ (AdjoinRoot.root φ))) ^ C.natDegree →
          G.Monic → G.map (algebraMap O (AdjoinRoot φ)) = tauProd hφ C →
          inertiaDegOf G = δ * inertiaDegOf C

— a statement about ONE irreducible factor and its conjugate product: no census, no
counting, no classes, no levels. The census front is now
`ConeRemainderLaw e σ` (e ≥ 3) + `InertiaScaling δ` (δ ≥ 2).

## What was CLOSED (everything else in UBB's successor plan)

**§1 the roots package.** `keyRoots` = residual roots of φ̄ over k′; `card_keyRoots` (δ
of them: φ̄ ∣ X^{q^δ}−X whose roots are all of k′), `nodup_keyRoots` (distinct),
`keyRes_eq_prod`, `exists_isRoot_of_mem_keyRoots` (Hensel root lift, separability from
`PerfectField`), `isRoot_unique`.

**§2 the conjugation family — UBB's Frobenius leg, RESHAPED.** One O-algebra
endomorphism `tau hφ ᾱ` per residual root (`AdjoinRoot.liftAlgHom` at the lifted root),
with `tau_comp` (composition closure `τ_β ∘ τ_ᾱ = τ_{resTau β ᾱ}`), `resTau` (residual
action), `tau_bijective`, `exists_resTau_eq`. **This replaces the single Frobenius σ of
UBB's plan: no σ^δ = id obligation, no Frobenius identification, no Witt machinery.**
Also `irreducible_algebraMap_adjoinRoot` (the base uniformizer stays irreducible).

**§3 THE INVARIANTS THEOREM** (`exists_algebraMap_eq_of_forall_tau`): x ∈ O′ fixed by
every τ lies in O. Residue level by a DEGREE COUNT — a polynomial of degree < δ taking
one value at δ distinct roots is constant (`exists_resEmb_eq_of_forall_resTau`), no
Galois theory — then the coordinate Krull induction on `AdjoinRoot.powerBasis'`.

**§4 the Hensel blocks and conjugacy.** `exists_block_family` (multi-Hensel: one monic
block per residual root, reducing to (X−ᾱ)^e), `block_family_eq_at`,
`block_family_conj`, ★ `map_algebraMap_eq_prod_tau` (F = ∏_β τ_β(B)), `exists_block`.

**§5 level exactness and THE CLASS CORRESPONDENCE.** `block_level_exact` (congruent base
lifts have congruent θ̄-blocks — IFCG16's finite-precision Hensel uniqueness applied over
O′ at the base uniformizer), `mem_pow_maximalIdeal_of_algebraMap` (congruence descent via
the zeroth power-basis coordinate), `fScale_injective`, `tauProd_map_tau` (τ-invariance),
★ `exists_descent_tauProd` (the conjugate product DESCENDS to O — invariants theorem
coefficientwise through `Polynomial.lifts`), ★ `exists_baseLift_of_block`, and
`IsBlockClass` with all four structural theorems: `exists_isBlockClass`,
`isBlockClass_unique` (well-definedness), `isBlockClass_injective`,
`exists_isBlockClass_of_stratum`. **SURJECTIVITY IS BY CONSTRUCTION — UBB's planned
H124b counting argument (`card_levelZeroStratum`) is NOT needed at all.**

**§6 the count equality.** `decidedAt_block_of_base` / `decidedAt_base_of_block`
(decidedness transfer both ways), ★★ `stratDecCount_eq_of_blockDescent` (the count
equality from the type-descent law: injectivity = level exactness, surjectivity = the
conjugate-product construction, label transport = the descent law), and the uniform
`BlockTypeDescent δ e` with `unramifiedBlockCount_of_blockTypeDescent`.

**§7 the factorization skeleton and ★ THE IRREDUCIBILITY LEG, PROVED.**
`factor_residual_shape` (every monic irreducible factor of the block has residual
exactly (X−θ̄)^deg — IFCG27's `factor_residual_pow` at the LINEAR key over O′),
`tauProd_mul`/`tauProd_multiset_prod`, `irreducible_map_tau`, `monicFactors_map_tau`,
`nodup_conjugates`, and
★ **`irreducible_descent_tauProd`**: the descent of the conjugate product of a monic
irreducible block factor is IRREDUCIBLE over O. Mechanism (no group theory): the factor
multiset of any proper monic factor is τ-invariant and contains C (the θ̄-conjugation is
the identity), hence contains the whole duplicate-free conjugate family, forcing the
cofactor to be 1. Then ★★ `blockDescentAt_of_legs` derives the type-descent law from the
inertia leg ALONE, with `typeOf`'s multiset algebra doing the bookkeeping and the
ramification index falling out of `(δd)/(δf) = d/f`.

## Why the remaining leg is genuinely Chapter-B-scale (design note for its unit)

`InertiaScaling δ` asks `f_O(G) = δ · f_{O'}(C)` for `G` the descent of `∏_β τ_β(C)`.
The intended mechanism: base-change the norm, `A ⊗_O O' ≅ ∏_β O'[X]/(τ_β C)` by CRT
(the factors are coprime — distinct residuals), so
`addVal_O(N_{A/O} x) = Σ_β addVal_{O'}(N(x_β)) = δ · addVal_{O'}(N(x_θ̄))`
(conjugates have equal valuation). **The subtlety a successor must face:**
`inertiaDegOf` is a gcd over norm-values, and this identity only exhibits the values
attained by elements of the SUBRING `O[x] ⊆ O'[x]`, so the containment gives
`δ·f_C ∣ f_G` (via B.52's lcm trick) but NOT equality without a witness. Consistency
check performed: classically `f(L'/K') = lcm(f,δ)/δ`, so the identity is equivalent to
`δ ∣ f_G` — which IS available as B.52 (`key_natDegree_dvd_inertiaDegOf`), so the leg is
TRUE, and B.51's length-multiplies-by-residue-degree is the model tool.

## Fence (honest)

Not attempted: `InertiaScaling δ` for any δ ≥ 2 (the norm/CRT leg above); consequently
no unconditional `UnramifiedBlockCount δ e` at δ, e ≥ 2, and the (2,2) instance remains
open — it is now exactly the (2,2) instance of the inertia leg, with all block, class,
counting and irreducibility content discharged. Nonvacuity of the shape is carried by
UBB's landed `unramifiedBlockCount_one` (e = 1, every δ).

## Consumed

IFCG27 (package, `UnramifiedBlockCount`, `factor_residual_pow`, the bridge reduction and
census capstone), IFCG25 (`fScale`, `UnramifiedBlockBridge`), IFCG17 (`stratDecCount`),
IFCG16 (`factor_sub_mem_of_mul_sub_mem`, `mem_coeffIdeal_pow_iff`), H100/H102
(`levelZeroStratum`, `proj_surjective'`), MultiHensel
(`exists_monic_factorization_finset`), HenselFactorization
(`monic_factorization_unique`, `natDegree_eq_of_map_eq`, `coeffIdeal` dictionary),
TypeOfAlgebra (`monicFactors_mul`, `typeOf_mul`), B01/B53b (`IsKey`, `keyIsDomain`),
mathlib (`FiniteField.roots_X_pow_card_sub_X`, `AdjoinRoot.liftAlgHom`,
`Polynomial.lifts_and_natDegree_eq_and_monic`, `Ideal.iInf_pow_eq_bot_of_isLocalRing`,
`MulEquiv.irreducible_iff`).

## Repair log (11 error rounds, all mechanical)

1. `congr 1` after `Polynomial.map_map` overshoots — supply the composite `RingHom.ext`.
2. `Splits` at this pin is the ONE-ARGUMENT predicate; `splits_of_splits_of_dvd` is
   deprecated → `Splits.of_dvd`.
3. **Combining-macron identifiers (`β̄`, `γ̄`, `δ̄`) are INVALID Lean tokens** ("expected
   token" at the character) — plain `β`, `γ`, `δ` only. (`ᾱ` with the precomposed
   character is fine.)
4. `AlgHom.comp_algebraMap` does not fire through `toRingHom` coercions — hoist
   `RingHom.ext fun r => (tau ..).commutes r`.
5. `Basis.repr_self` is `Module.Basis.repr_self` at this pin.
6. `rw [← he] at *` shadows section variables — rewrite in named `have`s instead.
7. `AdjoinRoot.mk_surjective` takes no `(f := ·)` named argument at this pin.
8. `Monic.pow` needs the exponent explicitly (`(monic_X_sub_C a).pow e`).
9. `Finset.prod_image` names the image map `g` and the summand `f` — both needed.
10. `Multiset.prod_congr` does not exist → `congrArg Multiset.prod (Multiset.map_congr …)`;
    `Multiset.eq_zero_of_le_zero` → `Multiset.le_zero.mp`.
11. `Multiset.Nodup.map` needs GLOBAL injectivity (false here — `tau` is junk off the
    root set) → `Multiset.Nodup.map_on`. Also `Multiset.prod_hom` direction is
    `(s.map f).prod = f s.prod`.
