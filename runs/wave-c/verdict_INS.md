# UNIT INS — VERDICT: ★★★ `InertiaScaling δ` PROVED FOR EVERY δ; THE BRIDGE FAMILY IS GONE FROM THE CENSUS FRONT (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG32.lean` (1049 lines, ZERO sorries, zero
warnings; all 14 AxCheck footer lines exactly Lean core `{propext, Classical.choice,
Quot.sound}` EXCEPT the final IFCG31-composed census-front theorem, which inherits
exactly IFCG31's one signed cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42) — as documented in the file's axiom fence; the C.33 cite does not occur;
no B.52/B.42 cites consumed by the leg itself).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG32.lean`
(final: axiom lines only, exit 0); targeted `lake build Uniformity.ChapI.IFCG32` green
(8946 jobs); the sanctioned one-line aggregator import added to `Uniformity/ChapI.lean`
and `lake env lean Uniformity/ChapI.lean` green.  IFCG33 untouched.  No git operations.

## ★★★ THE RESULTS

    theorem inertiaScaling_all (δ : ℕ) : InertiaScaling δ                     -- Lean core
    theorem blockTypeDescent_all (δ e : ℕ) : BlockTypeDescent δ e             -- Lean core
    theorem unramifiedBlockCount_all (δ e : ℕ) : UnramifiedBlockCount δ e     -- Lean core
    theorem unramifiedBlockBridge_all (hδ : 1 ≤ δ) (e) : UnramifiedBlockBridge δ e
    theorem decidedSliceAt_all_of_remainder (hR) : ∀ n, DecidedSliceAt n      -- Lean core
    theorem decidedSliceAt_all_of_remainder5_even4 (hR) (hR4) : ∀ n, DecidedSliceAt n

UBC's one-parameter leg is CLOSED, uniformly in `q` and `δ` (no statement weakened; the
(2,2) instance is subsumed — no per-instance fallback needed).  The entire block-bridge
family `UnramifiedBlockCount δ e` / `UnramifiedBlockBridge δ e` is now UNCONDITIONAL for
all `δ, e`.  **What remains on the census front** (via the last theorem, = IFCG31's
`decidedSliceAt_all_of_remainder5_even4_bridge` with its `hBr` discharged): exactly the
remainder laws — `ConeRemainderLaw e σ` for `e ≥ 5` (with the strong induction
hypothesis) and the `e = 4` even-ramification types `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`,
`{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}`.  No bridge, no count law, no inertia leg.

## Mechanism (all elementary linear algebra — no field theory, no B.52 cite)

The theorem `inertiaDegOf_descent : inertiaDegOf G = δ * inertiaDegOf C` comes from the
set identity `normValues G = δ • normValues C` plus sSup-gcd arithmetic:

* **§0 norm transport along a ring map** (`mapAdjoin`, `repr_mapAdjoin`,
  `norm_mapAdjoin`, `norm_mk_map'`): for any `f : R →+* S` and monic `G`,
  `N_{S[X]/G^f}(P^f) = f (N_{R[X]/G}(P))` — the multiplication matrices in the two power
  bases correspond entrywise under `f` (`RingHom.map_det`).  The `hM : G.map f = M`
  call-site form avoids dependent rewrites.  (Technique cribbed from landed
  `TypeOfInvariance.norm_scaleHom`.)
* **§1 ★ norm multiplicativity in the MODULUS** (`norm_mk_mul`, `norm_mk_prod`):
  `N_{S[X]/(FH)}(P) = N_{S[X]/F}(P)·N_{S[X]/H}(P)` for monic `F, H` over ANY nontrivial
  commutative ring — NO coprimality: the adapted basis `{X^i·H} ⊔ {X^j}` of
  `S[X]/(F·H)` (`adaptedBasis`, built by `Module.Basis.mk` from a degree-bookkeeping
  LI/span pair) makes the multiplication matrix block-triangular
  (`Matrix.det_fromBlocks_zero₂₁`), with the two factor matrices as diagonal blocks.
  This replaces UBC's planned CRT norm peel — cleaner and hypothesis-free.
* **§2 valuation transport** (`addVal_map_of_irreducible`): `addVal` is preserved by any
  ring map carrying one irreducible to an irreducible (`u·π^n ↦ u'·(ψπ)^n`); applied to
  `algebraMap O O'` (unramifiedness = IFCG29's `irreducible_algebraMap_adjoinRoot`) and
  to every conjugation `τ_β` (which fixes the base uniformizer, junk values included).
* **(E1) the master identity** (`algebraMap_norm_mk_eq`, `addVal_norm_mk_eq`): for `P`
  over the base, `f(N_{O[X]/G}(P)) = ∏_β τ_β(N_{O'[X]/C}(P^f))`, so
  `addVal_O N_{O[X]/G}(P) = δ • addVal_{O'} N_{O'[X]/C}(P^f)`.
* **LEG A** (`normValues_descent`): (E1) at any `mk`-preimage; `⊤`-bookkeeping in `ℕ∞`
  (ENat lemmas, NOT WithTop — the coercions differ).
* **LEG B, the witness** (`normValues_ascent`): the gcd-witness subtlety UBC flagged.
  CRT solution `P' ≡ τ_β(Q) (mod τ_β C)` over the conjugate family
  (`exists_forall_dvd_sub`, hand-rolled Bézout induction); pairwise comaximality of the
  conjugate factors from residually-coprime `(X−β)^d` at distinct roots via **Nakayama**
  (`isCoprime_of_isCoprime_map_residue`: `S[X]/(F,H)` is module-finite via monic `F` and
  `𝔪`-divisible via the lifted Bézout relation `1 − E`, `E` with coefficients in `𝔪`;
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`).  The reduced representative mod
  `tauProd C` is τ-invariant AS A POLYNOMIAL (uniqueness of reduced representatives +
  `tauProd_map_tau` + `tau_comp` reindexing), hence descends to `O[X]` by IFCG29's
  invariants theorem, coefficientwise through `Polynomial.lifts`; it recovers `y` at the
  identity conjugation (`tau_residue_root`), so (E1) evaluates the witness's norm
  valuation to EXACTLY `δ·v`.
* **(E4) gcd arithmetic** (`dvd_inertiaDegOf_of_mem_normDivisors` = B.52's lcm trick
  packaged, + `inertiaDegOf_descent`): `δ·f_C ∈ normDivisors G ⟹ δ f_C ∣ f_G`;
  conversely `f_G ∣ δ·v ∀v ⟹ (f_G/gcd(f_G,δ)) ∈ normDivisors C ⟹ f_G ∣ δ·f_C`
  (coprime cancellation with explicit `/ d0` divisions); `Nat.dvd_antisymm`.

Classical sanity: `f(L'/K') = lcm(f_G,δ)/δ`, so the leg ⟺ `δ ∣ f_G` = B.52's content —
but this proof is independent of B.52 and fully Lean-core.

## Consumed

IFCG29 (`InertiaScaling`, `tauProd` + `tauProd_monic`/`_natDegree`/`_map_tau`, `tau`/
`tau_comp`/`tau_residue_root`, `resTau_apply_of_mem`, `exists_resTau_eq`, `keyRoots`/
`card_keyRoots`/`nodup_keyRoots`/`residue_root_mem_keyRoots`,
`exists_algebraMap_eq_of_forall_tau`, `irreducible_algebraMap_adjoinRoot`,
`map_resTau_map_residue`, `map_tau_map_algebraMap`, and the §6/§8 wrappers
`blockTypeDescent_of_inertiaScaling`, `unramifiedBlockCount_of_inertiaScaling`,
`unramifiedBlockBridge_of_inertiaScaling`,
`decidedSliceAt_all_of_remainder_inertiaScaling`), IFCG31
(`decidedSliceAt_all_of_remainder5_even4_bridge`), IFCG27 (`adjoinRoot_isDVR`/
`_isAdicComplete`/`_finite_residueField`, `UnramifiedBlockCount`, `BlockTypeDescent`),
Density/TypeOf (`normValues`, `normDivisors`, `inertiaDegOf` + gcd API),
Density/TypeOfInvariance (`rootBasis`, `rootBasis_apply`), mathlib
(`Algebra.norm_eq_matrix_det`, `Algebra.leftMulMatrix_eq_repr_mul`, `RingHom.map_det`,
`Matrix.det_fromBlocks_zero₂₁`, `Module.Basis.mk`, `Fintype.linearIndependent_iff`,
`Finset.prod_dvd_of_coprime`, `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`,
`IsLocalRing.jacobson_eq_maximalIdeal`, `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`,
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`/`addVal_uniformizer`/
`addVal_eq_zero_iff`, `Polynomial.lifts`, `AdjoinRoot.powerBasis'`).

## Repair log (7 error rounds, all mechanical)

1. Bare `map_mul` in a rw matches `Basis.repr` first (LinearEquiv is not MulHomClass —
   synth error cascade) → pin with explicit arguments.
2. Two consecutive docstrings from an insertion → "unexpected token '/--'".
3. `Polynomial.natDegree_le_of_dvd` needs `NoZeroDivisors` → for MONIC divisors use
   `natDegree_mul'` on the factorization instead (works over any nontrivial ring).
4. `Sum.elim`-applications after `Module.Basis.mk_apply` and `repr_basis_sum` need a
   trailing `rfl` (iota reduction not closed by `rw`).
5. Quotient-module smul: `Algebra.smul_def` does not match the canonical
   `Ideal.Quotient` smul instance → route through `map_smul (Ideal.Quotient.mkₐ S J)` +
   `mkₐ_eq_mk` (and a first attempt via `simpa` collapsed the hypothesis to `True` —
   use directed `rw`).  `Polynomial.modByMonic_add_div` takes the POLYNOMIAL, not the
   monic proof (mathlib's junk values make it unconditional).
6. `ℕ∞` is `ENat`, not raw `WithTop ℕ`: `WithTop.mul_top`/`ne_top_iff_exists` produce
   coercion mismatches → `ENat.mul_top`, `ENat.ne_top_iff_exists`, `ENat.coe_ne_top`.
7. Destructuring `gcd ∣ ·` witnesses then rewriting re-enters the gcd subterms → keep
   explicit `m / gcd` forms with `Nat.mul_div_cancel'`.

## Fence (honest)

* The two `decidedSliceAt_*` wiring theorems are conditional on the REMAINDER laws
  (their `hR`/`hR4` hypotheses) — those are the census front's remaining obligations,
  owned by the remainder-law campaign, not this unit.
* `decidedSliceAt_all_of_remainder5_even4` inherits IFCG31's signed B.42 cite
  (`exists_slope_factorization`); everything else in the file is Lean core.
* `normValues_ascent` carries `hd : 0 < C.natDegree` (harmless: derived from
  irreducibility at the one consumer, `inertiaDegOf_descent`).
