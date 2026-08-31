# UNIT KDW — VERDICT: KRASNER CLOSED — `KrasnerIrredAt n` PROVED AT EVERY `n` (stronger than charged); the capstone's a2 field (`∀ n, DrainageAt n`) is UNCONDITIONAL (2026-08-31)

**Status: DONE, ABOVE CHARGE.  The charged Prop `KrasnerDeepAt m` is proved for ALL m —
and so is the strictly stronger `KrasnerIrredAt m` (the deep-wild restriction is never
needed) and hence `KrasnerAt m`.  All of IFCG50's fires fire: the capstone's ENTIRE a2
field (`CapstoneHypotheses.a2 : DrainageAt n`, I10_I15_I18) is now supplied
unconditionally at every degree, Lean-core only.  No fallback was needed.**

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG52.lean` (663 lines, ZERO sorries,
zero warnings beyond the 14 expected AxCheck prints; imports Mathlib + IFCG50 only).
All FOURTEEN AxCheck footer lines print pure Lean core
`{propext, Classical.choice, Quot.sound}` — no cite consumed, no axiom added.
One-line aggregator import added to `Uniformity/ChapI.lean` (after IFCG50; IFCG51
untouched).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG52.lean` (final: zero diagnostics
beyond the expected prints); targeted `lake build Uniformity.ChapI.IFCG52` GREEN
(8961 jobs); aggregator `lake env lean Uniformity/ChapI.lean` GREEN.  NO git ops.

## ★★★ THE HEADLINES

    theorem krasnerIrredAt (n : ℕ) : KrasnerIrredAt n      -- ★★★ UNCONDITIONAL, EVERY n
    theorem krasnerDeepAt (n : ℕ) : KrasnerDeepAt n        -- ★★★ the charged Prop
    theorem krasnerAt (n : ℕ) : KrasnerAt n                -- ★★★
    theorem deepTailDrainAt (n : ℕ) : IFCG46.DeepTailDrainAt n
    theorem drainageAt_all : ∀ n, DrainageAt n             -- ★★★ THE a2 FIELD CLOSES

`drainageAt_all` is byte-identical to the a2 consumer shape: `CapstoneHypotheses.a2`
takes `DrainageAt n` per degree (I10_I15_I18:211), and `∀ n, DrainageAt n` is exactly
what `drainage_of_capstoneHypotheses` extracts.  After KDW the a2 field can be
DISCHARGED in the capstone hypothesis block — no Krasner-genre, drainage-genre, or
disc-genre hypothesis remains anywhere in the a2 supply chain (IFCG45→46→49→50→52 all
Lean-core).

## THE MECHANISM — the ISO ROUTE (fully algebraic Krasner; no normed fields, no
`IsKrasner`, no resultant product formulas, no maximal orders)

For `f = monicPoly a` irreducible with `Res(f, f') = u₀·π^{v₀}` exactly (finite `v₀` by
the separability hypothesis), take `N := 2v₀ + 1`, `σ := typeOf f`.  For EVERY monic
lift `g ≡ f mod π^N` of the level-`N` class:

1. **Resultant congruence** (§5): `Res(g, f') ≡ Res(f, f') mod π^N` at pinned degrees
   (`resultant_map_map` through `O/π^N`; the reductions of `f`, `g` coincide), so
   `π^{v₀+1} ∤ Res(g, f')` and IFCG41's landed Bezout gives
   `g·p + f'·q = C(π^{v₀})`.  Evaluated at `x₀ := AdjoinRoot.root g`:
   `c·q(x₀) = π̄^{v₀}` with `c := f'(x₀)` — the derivative divides `π̄^{v₀}` INSIDE the
   order `A_g`.
2. **Newton in the order** (§2, `exists_aeval_eq_zero_of_close`): `A_g` is π-adically
   complete and Hausdorff via coordinates in `AdjoinRoot.powerBasis'` (§0 — the same
   coordinatewise `IsPrecomplete.prec` trick as IFCG49's König limit).  Since
   `f(x₀) = (f−g)(x₀) ∈ π̄^N·A_g` and `π̄^{2v₀} = (c·q(x₀))²`, we get `f(x₀) = π̄·c²·u`
   EXACTLY; the quadratic Taylor identity (§1, mathlib `Polynomial.taylor` + divX²
   tail) turns `f(x₀ + π̄c·z) = π̄c²·(u + z + π̄·H(z))`; the fixed-point iteration
   `z_{m+1} := −(u + π̄·H(z_m))` contracts (`Polynomial.sub_dvd_eval_sub` gains one π̄
   per step) to `z*` with `u + z* + π̄H(z*) = 0`.  So `ξ := x₀ + π̄c·z*` has
   `f(ξ) = 0`, `ξ ≡ x₀ mod π̄`.
3. **The unit-determinant isomorphism** (§3, `krasnerHom_bijective`):
   `Φ := AdjoinRoot.liftAlgHom f (Algebra.ofId) ξ : A_f →ₐ[O] A_g` sends the power
   basis to `ξ^j ≡ x₀^j mod π̄`, so its matrix `M ≡ 1 mod 𝔪` entrywise (coordinates of
   π̄-multiples are π-multiples, §0); `det M ≡ 1 mod 𝔪` (determinant commutes with the
   residue map) is a unit of the local ring; `Matrix.isUnit_iff_isUnit_det` +
   `nonsing_inv` make `Φ` BIJECTIVE — an O-algebra isomorphism `A_f ≃ₐ[O] A_g`.
4. **Transport** (§4): (a) `A_f` is a domain (`f` prime in the UFD `O[X]`) ⟹ `A_g` is
   a domain ⟹ `g` is IRREDUCIBLE (a nontrivial monic factorization gives zero
   divisors `mk u, mk w ≠ 0` by degree, `natDegree_le_of_dvd`); (b) `Algebra.norm` is
   iso-invariant (mathlib `Algebra.norm_eq_of_algEquiv`) ⟹ `normValues f = normValues g`
   ⟹ `inertiaDegOf`/`efPair` equal (the gcd definition is a function of the
   norm-valuation SET plus the degree — no maximal order enters); (c) both irreducible
   monic ⟹ `typeOf g = ⟨{efPair g}⟩ = ⟨{efPair f}⟩ = typeOf f = σ`.  DecidedAt.  ∎

Note what made this cheap: the classical Krasner route (matched roots in a splitting
field) and the disc-multiplicativity route (Res(g₁,g₂)² ∣ Res(g,g')) were both
DODGED — the Bezout witness evaluated at the root replaces the norm/valuation theory of
the extension entirely, and irreducibility of the lift is FREE through the iso instead
of needing its own factor-lifting contradiction.

## File map (`leanfinal/Uniformity/ChapI/IFCG52.lean`, 663 lines)

§0 coordinate calculus on `AdjoinRoot g` (monic): `pow_dvd_repr_of_pow_dvd`,
`pow_dvd_of_pow_dvd_repr`, `eq_zero_of_forall_pow_dvd` (Hausdorff),
★ `exists_limit_of_cauchy` (completeness; coordinatewise `IsPrecomplete.prec`) ·
§1 `eval_add_eq_taylor_quadratic` (any CommRing; `taylor_eval` + double `divX`) ·
§2 ★★ `exists_aeval_eq_zero_of_close` (THE NEWTON ROOT) ·
§3 `krasnerHom` (+`krasnerHom_root`), ★★ `krasnerHom_bijective` (THE ISO) ·
§4 `norm_algEquiv`, `normValues_eq_of_algEquiv`, `efPair_eq_of_normValues`,
`isDomain_adjoinRoot_of_irreducible`, `irreducible_of_isDomain_adjoinRoot`,
`typeOf_of_irreducible` ·
§5 ★★★ `krasnerIrredAt`, ★★★ `krasnerDeepAt`, ★★★ `krasnerAt`, `deepTailDrainAt`,
★★★ `drainageAt_all` · AxCheck footer (14 lines, ALL Lean core).
Imports: Mathlib + IFCG50 only.

## Honesty ledger

* `KrasnerIrredAt`, `KrasnerDeepAt`, `KrasnerAt`, `DrainageAt`, `DecidedAt`,
  `DeepTailDrainAt`, `typeOf`, `efPair`, `normValues`, `inertiaDegOf` consumed
  byte-unchanged from IFCG50/IFCG49/IFCG46/Density-core; NOTHING weakened; the fires
  are implications into the landed Props, typechecked against them.
* Uniform in `q` and `n` (∀-`O : Type`, the corpus universe convention); the decision
  level `N = 2·v(Res(f,f')) + 1` is pointwise in `f` exactly as the ∃-form permits.
* `krasnerDeepAt` is `krasnerIrredAt` with the deep hypothesis DROPPED (the residue
  shape is never used) — a hypothesis-weakening in the sound direction.
* Degenerate cases: `n = 0` discharged by IFCG50's `krasnerIrredAt_zero`; `v₀ = 0`
  (residue-separable) and `n = 1` flow through the same mechanism with no special case.
* The one definitional trust point is inherited, not new: `typeOf`'s faithfulness to
  the classical (e,f)-type (TypeOf.lean's documented trust boundary).  KDW only ever
  proves EQUALITIES of `typeOf` values, via `Algebra.norm`-set equality of isomorphic
  orders — faithful regardless of that boundary's resolution.
* Axioms: Lean core only, machine-printed for all 14 public declarations; no cite
  (B.42/C.33/FGMN/GMN never occur); no new axiom.
* Adversarial verification: codex fresh-context referee charged on the mechanism +
  statement faithfulness (quote-and-classify) — verdict + disposition in the appendix
  below.  Headline: "The core iso route is mathematically sound.  I find no critical
  error in the Newton exponent budget, determinant argument, or transport of the
  norm-defined invariant."

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. `AdjoinRoot.liftHom` does not exist in the pinned mathlib → `AdjoinRoot.liftAlgHom`
   along `Algebra.ofId` (wrapper `krasnerHom`).
2. `Basis` is namespaced `Module.Basis` here; no Fintype `Basis.sum_repr` → replaced
   all sum manipulations by `repr.symm ∘ Finsupp.equivFunOnFinite.symm` (cleaner too).
3. Section-variable inclusion: lemmas using `hg` only in proofs need `include hg in`
   (placed BEFORE the docstring).
4. KDN trap #3 redux (dependent motive): `rw [hpbg]` under `j : Fin pbg.dim` = motive
   failure — the power-basis `gen = root` equalities are DEFEQ, so `rfl` after
   `basis_eq_pow` replaces the rewrite.  Also `rw [← X_mul_divX_add]` rewrites both
   sides (use the `.symm` equation); `RingHom.map_det` produces `mapMatrix`, needs
   `RingHom.mapMatrix_apply`; `IsLocalRing.mem_maximalIdeal` needs its explicit arg
   before `.mpr`.
5. The `derivative_map` rewrite in the resultant congruence was unnecessary (both
   sides already carry the mapped derivative) — deleted.

## Downstream folding suggestions (for the orchestrator; NOT executed by KDW)

* PROJECT_STATE / frontier: the a2 line should read "CLOSED — `IFCG52.drainageAt_all :
  ∀ n, DrainageAt n`, unconditional, Lean core (KDW 2026-08-31)".
* The capstone hypothesis block (I10_I15_I18 `CapstoneHypotheses`) can now have its
  `a2` field discharged/defaulted at construction sites; that edit belongs to the
  chapter-I owner unit, not KDW.
* IFCG46's `DeepTailDrainAt`, IFCG49's `KrasnerAt`/`DiscNullAt`, IFCG50's fences: all
  now have unconditional suppliers; their honest-remainder docstrings could be
  annotated CLOSED in a docs pass.

## APPENDIX — codex adversarial referee (fresh context, minimal brief, 2026-08-31)

Charge: hostile quote-and-classify on the mechanism + the key Lean statements
(brief: `/tmp/kdw_verify_brief.md`; full report: `/tmp/kdw_codex_verdict.txt`).

**Referee headline: "The core iso route is mathematically sound.  I find no critical
error in the Newton exponent budget, determinant argument, or transport of the
norm-defined invariant."**  Its answers to the four load-bearing questions: (i) the
Newton arithmetic is EXACT (no division by `c` occurs; `u = q(x₀)²h₀(x₀) ∈ A`);
(ii) the determinant/mod-π coordinate argument is sound for the monic power basis;
(iii) an O-algebra isomorphism preserves the ORDER-level norm-valuation set, so the
order-sensitive `inertiaDegOf` transports — "the order-sensitive definition causes no
problem here"; (iv) degeneracies: `n = 0` needs a vacuity branch, `n = 1` and `v₀ = 0`
flow through, `c = 0` cannot occur, and NO separability of `g` is needed (the iso
forces irreducibility).

Findings + disposition:

1. "CRITICAL — `∀ (O : Type)` is universe-0, not `Type*`."  DISPOSITION: TRUE and
   INHERITED — this is the corpus-wide, documented universe convention
   (`KrasnerIrredAt`/`KrasnerDeepAt`/`KrasnerAt`/`DrainageAt` are ALL `O : Type`
   byte-unchanged from IFCG49/IFCG50/Statement.lean — the "ZcURLim universe
   convention" recorded in DTD's and KDN's honesty ledgers), and the capstone consumer
   (`CapstoneHypotheses.a2`) quantifies identically.  KDW's statement fence FORBADE
   changing it.  All KDW-internal lemmas (§0–§4) are `Type*`-polymorphic; only the
   consumed Props pin `Type`.  Recorded, not repaired; a corpus-wide universe lift is
   an owner-level decision.
2. "GAP — `n = 0` needs a separate ex-falso branch."  CLOSED IN THE ARTIFACT: the
   Lean proof opens with `rcases Nat.eq_zero_or_pos n` and discharges `n = 0` by
   IFCG50's landed `krasnerIrredAt_zero` (vacuous: `monicPoly a = 1` is a unit).
3. "GAP — Newton convergence needs completeness/continuity/separatedness, not just
   'Hausdorffness'."  CLOSED IN THE ARTIFACT: §0 supplies exactly these, machine-
   checked (`exists_limit_of_cauchy` = completeness via coordinatewise
   `IsPrecomplete.prec`; `eq_zero_of_forall_pow_dvd` = separatedness; continuity is
   replaced by the algebraic identity `sub_dvd_eval_sub` — no topology used).
4. "GAP — norm invariance not shown."  CLOSED: mathlib's `Algebra.norm_eq_of_algEquiv`
   (Norm/Basic.lean), consumed at §4 `norm_algEquiv`; machine-checked.
5. "GAP — `typeOf`/`Coeff`/`proj` definitions not auditable from the brief."  CLOSED
   BY PROVENANCE: all consumed byte-unchanged from Density-core (LocalData/TypeOf/
   GenuineDensity), the same trust boundary the whole corpus rests on (TypeOf.lean's
   documented faithfulness flag; KDW adds no new definition on that boundary).
6. "GAP — 'they compile' is weaker than an axiom audit."  CLOSED: the file ends in a
   14-line `#print axioms` footer; ALL print pure Lean core
   `{propext, Classical.choice, Quot.sound}`; zero sorries (grep-verified).
7. "GAP — the drainage consequence not refereeable from the brief."  CLOSED BY
   PROVENANCE: `drainageAt_all` is one `exact` into IFCG50's machine-checked
   `drainageAt_all_of_krasnerIrred` (KDN's audited fire), itself Lean-core.

ACCEPTANCE: the referee found no mathematical error; the single CRITICAL is an
inherited, consumer-matched statement convention outside this unit's authority; every
justification gap is discharged by the compiled artifact or by byte-unchanged
provenance.  KDW stands.
