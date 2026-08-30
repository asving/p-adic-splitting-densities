# UNIT ECONE — VERDICT: INTERFACE + BOTH REDUCTIONS LANDED (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG21.lean` (766 lines, ZERO sorries; all
12 AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`; the
C.33 cite does not occur; no landed file touched except the sanctioned one-line
aggregator import in `Uniformity/ChapI.lean`).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG21.lean` (final run green), targeted
`lake build Uniformity.ChapI.IFCG21` green (8918 jobs), `lake env lean
Uniformity/ChapI.lean` (aggregator) green.  No git ops (per charge).

## ★★★ THE RESULT — the census front now rests on TWO named cone laws, reductions PROVED

    def PointConeLaw : Prop :=      -- the e ≥ 2 atom, stratPoly-level, POINT-UNIFORM
      ∀ m ≥ 4, (smaller value laws < m) →
      ∀ δ e, 1 ≤ δ → 2 ≤ e → δ*e ≤ m → ¬(δ = 1 ∧ e = m) →
      ∀ s, PtURLim δ (pointStratFamily δ e s)
      -- pointStratFamily δ e s O p N = (stratPoly O (δe) N (p^e)) s / q^(δeN);
      -- PtURLim δ F = ONE Polynomial ℚ pair with the limit at EVERY complete DVR and
      -- EVERY monic irreducible residual point p of degree δ (point-uniformity = the
      -- interface-level unramified base change)

    def CenteredConeLaw : Prop :=   -- the fractional-cell atom, per-centre, CENTRE-UNIFORM
      ∀ m ≥ 4, (smaller value laws < m) → ∀ σ, σ.degree = m → Witnessed m σ →
      ∃ n d, d ≠ 0 ∧ ∀ O [complete DVR, finite residue], d(q) ≠ 0 ∧
        ∀ π irr, ∀ γ : ResidueField O,
          Tendsto (fun M => coneCellCount O π m σ M γ / q^(m(M+m))) atTop (nhds (n(q)/d(q)))
      -- coneCellCount O π m σ M γ = #((decidedSet(M+m) ∩ stratum((X+Cγ)^m))
      --                                \ range (d ↦ fullLoopClassN π (γ, d)))

    theorem singlePointAggregateLaw_of_pointCone : PointConeLaw → SinglePointAggregateLaw
    theorem deepFractionalCellLaw_of_centeredCone : CenteredConeLaw → DeepFractionalCellLaw
    theorem decidedSliceAt_all_of_cones :
      PointConeLaw → CenteredConeLaw → ∀ n, DecidedSliceAt n        -- ★★★ the wiring

Honesty fences: both laws carry the kernels' exact conditionality (smaller value laws,
mass window) so neither is stronger than the remainder it refines; `PointConeLaw`
excludes `(δ, e) = (1, m)` — the same self-call fence as the kernel's `(1, [m])` — and
the reduction PROVES the excluded factor shape is unreachable from any legal block
(`list_eq_singleton_of_mem_sum_le`).  The uniformity quantifiers (one pair over all
points p of degree δ; one pair over all centres γ) are commitments the discharge unit
must meet; both are mathematically forced (translation symmetry; base-change symmetry),
and stage CN0 below can weaken the centre obligation to a single centre.

### How the reductions work (what was actually proved)

* §1 `PtURLim` — the URLim calculus with one extra monic-irreducible-point parameter;
  closure under const/congr/add/mul/Finset-sum (mirrors IFCG18 §2 verbatim).
* §2 `pointStratFamily`, `PointConeLaw`, and `ptURLim_unit_factor`: the e = 1 factor is
  the constant `q^(−δ)` monomial at `{(1,δ)}` (IFCG19's `stratPoly_irreducible` read
  per point) — so mixed exponent lists consume BOTH IFCG19 and the law.
* §3 the SPAL reduction: `blockPoly` (the per-point product over the exponent list) is
  handled by list induction through the `TypeAlg` convolution `mul_apply_powerset`
  (`ptURLim_blockPoly` — NO coprimality needed, the factors share the point), and the
  point sum collapses by point-uniformity: finitely many summands with the SAME limit,
  count = `N_δ(q)` = IFCG19's `necklacePoly` (`uRLim_spFamily_of_ptURLim`; final pair
  `(necklacePoly δ · n, d)`).
* §4 the DFCL reduction: `fracCellCount = Σ_γ coneCellCount γ` EXACTLY at every finite
  level (`fracCellCount_eq_sum_coneCellCount`) — the loop subtraction is absorbed
  (constrained loop range ⊆ full range, IFCG20), the deep pattern cell is classified by
  the NEW `eq_addC_pow_of_patternOf` (monic + pattern `{(1,m)}` ⇒ `(X+Cγ)^m`; multiset
  singleton inversion + `Monic.eq_X_add_C`), centres are separated by
  `addC_pow_centre_inj` (evaluate at `−γ`, characteristic-free) via the extractor
  `centreOf` (+ `centreOf_eq`), and each centre's full-range piece is exactly its own
  recentering range (`fullLoopClassN_mem_stratum`, IFCG20 §1's inline fact exported).
  Then the γ-sum collapses centre-uniformly with the factor `q` = `Polynomial.X`
  (`deepFractionalCellLaw_of_centeredCone`; pair `(X·n, d)`).  NO translation bijection
  was needed — centre-uniformity replaces it at the interface level.

## SCOPE ANSWERS (charge item 1)

**(a) Does the C.33 dissection / IFCG12 strong cover pin the CLASS COUNT per skeleton?
NO.**  The genre cover (IFCG9–12) is polynomial-level EXISTENCE over a `KeyFrame`: it
realizes skeletons for exact polynomials, not for finite-precision coefficient classes
(`Coeff`), and exports no counting or measure statement for the set of classes realizing
a fixed skeleton.  `skeletonExp`'s counting meaning is pinned in exactly ONE landed
instance (the loop skeleton).  FP1's audit rows stand: GC0 (the class-level classifier)
and RW0 (the `q^(−skeletonExp)` cell measure) are the missing legs; no ChapI ↔ ChapC
bridge exists in either import direction (verified by import grep).  The C.33 cite
(`exists_dvDissection` / `fgmn_dvDissection_factor_eq`) dissects POLYNOMIALS at a frame —
reading a CLASS through it needs the classifier first.

**(b) Does H124's stratum bridge extend to ramified blocks (what breaks in
`stratPoly_irreducible` at residual `p^e`)?**  The CARDINALITY leg survives verbatim:
`card_levelZeroStratum` holds for ANY monic residual, so the stratum of `p^e` has
exactly `q^(δe(N−1))` classes — the total is priced, uniformly.  The DECIDEDNESS leg
breaks completely: `decidedAt_of_mem_levelZeroStratum_irreducible` needs irreducibility;
the stratum of a power contains classes of MANY types (split/inert/ramified mixtures)
plus an undecided-at-every-level deep boundary, so `stratPoly O (δe) N (p^e)` is not a
monomial — it is the OM cone's type-indexed dissection.  Per-class type uniqueness
(`decidedAt_unique`) survives.  The missing object is therefore exactly the per-type
dissection = the two cone laws.

**(c) The e = 2 pattern instrument (drove the whole architecture).**  Stratum of `X²` at
level `N`: classes `(a, b)` with `v(a) ≥ 1, v(b) ≥ 1`; `q^(2(N−1))` total.  Newton
dichotomy: (1) `v(b) = 2j+1` odd and `2v(a) > v(b)` — single NP face of slope
`(2j+1)/2`, ramified quadratic, type `{(2,1)}`, decided once the slope is visible; exact
level-`N` count `(q−1)·q^(2N−3(j+1))`, normalized `(q−1)q^(−3(j+1))`: a geometric series
of ratio `q^(−3)` = `q^(−T₂)` (IFCG14's fixed-point ratio!), summing to
`(q−1)/(q³−1) = 1/(q²+q+1)` — the depth-j term IS the depth-0 term recentred j times.
(2) `2v(a) < v(b)` — two integer slopes, splits, decided.  (3) `v(b) = 2j` even with
`v(a) ≥ j` — unit frame after `x = π^j y`: split/inert/double-root by the residual,
double root recurses.  STRUCTURAL READING: cases 2–3 = exactly the image of IFCG3's
recentering (IFCG20's `fullLoopClassN`) run at exponent 2 — the stratum census =
(cone-proper: immediate fractional faces) + (recentred mixed-box copy of the FULL
degree-2 census), and for blocks of mass < m the recentred part is rationalized by the
SMALLER VALUE LAWS through IFCG20's own machinery (mixedTruncN fibre count + lift
correspondence + boundary annihilation) re-run at exponent e.  This is why the atoms
are: stratPoly-level for SPAL's factors, cone-proper-level (recentred part removed by
construction) for the fractional cell.

## BLUEPRINT for the follow-up fleet (discharging the two cone laws)

The one heart: count, per type, the decided classes of the stratum of `X^e` (linear
centre; base-changed for δ ≥ 2).  Stages, each ≈ one unit:

* **CN0 (translation symmetry; cheap, optional).**  The class-level shift bijection
  `Coeff O m N ≃ Coeff O m N` induced by `X ↦ X + C γ̃` (candidate ready-made pieces:
  H123a's `recentreClass` + `decidedAt_recentreClass`; missing: stratum translation —
  short proof via `monicPoly_shiftVecN` — and commutation with `fullLoopClassN` ranges —
  the triangular unit-diagonal action on mixed boxes; shifts by 𝔪-elements factor
  through the box bijection `d ↦ mkBoxN (shiftVecN (resOut∘d) v)`).  Payoff: weakens
  `CenteredConeLaw`'s obligation to the single centre γ = 0, and derives
  centre-uniformity instead of assuming it.
  Signature: `theorem coneCellCount_translation (γ γ') : coneCellCount … γ = coneCellCount … γ'`.
* **CN1 (class-level Newton data).**  For classes in the stratum of `X^e` at level `N`:
  the visible coefficient valuations `v(a_i) ∈ {1, …, N−1} ∪ {≥N}` are class
  invariants; define the class NP (lower hull of `(i, v(a_i))`, `(e, 0)`) and its
  visibility precision.  Pure `Coeff`/`Res` bookkeeping, no new math.
  Signatures: `def classCoeffVal`, `def classNP`, `lemma classNP_lift_eq` (every lift's
  NP = the class NP when visible).
* **CN2 (the fractional-face decidedness criterion — THE HEART).**  A visible NP face of
  slope `h/e'` in lowest terms with `e' ≥ 2` forces every lift to carry a degree-`e'·f'`
  irreducible factor with ramification divisible by `e'` — in ChapC vocabulary this is
  C61's OPEN ℓ-half (`tier1_typeOf_of_ramLeg`'s `hram` premise; landed only at ℓ = 1 as
  `tier1_typeOf_of_ell_one`).  Two routes: (i) prove it in ChapI vocabulary directly
  (valuation argument on `typeOf`'s factorization — for e' = e prime the Eisenstein
  case, first blood: `stratDecCount O 2 ⟨{(2,1)}⟩ N (X²)` exactly); (ii) bridge ChapC's
  dv-graded Hensel machine (C133mh*) to `Coeff` classes once and consume its dissection
  (heavier, more reusable — this is FP1's GC0 by another name).  The residual polynomial
  of a face (the C.33 frame data) then splits the face's contribution by the residual's
  factorization pattern — the recursion that makes the census self-similar.
  Signatures: `theorem typeOf_ram_of_fracFace : classNP face slope h/e', gcd(h,e')=1 →
  decided-parts constraints on typeOf`, plus per-face `stratDecCount` monomials.
* **CN3 (the recentred-remainder squeeze at exponent e; conversion C).**  Per-centre
  IFCG20 §2–§5 re-run at exponent `e < m`: `stratPoly(X^e)` σ-coefficient = cone-proper
  + recentred part; the recentred part's limit = (fibre `q^(T_e)` count) ×
  (degree-`e` decided density, GIVEN by the smaller value laws) with the boundary
  annihilated by the same squeeze (`decidedSeq_tendsto` only).  Result:
  `theorem pointConeLaw_linear_of_centeredCone : (CenteredConeLaw at all e ∈ [2,m]) →
  (smaller laws) → PointConeLaw restricted to δ = 1` — after which the ONLY open
  content at δ = 1 is the cone-proper count.
* **CN4 (the cone geometric sums).**  Assemble CN2's per-face exact counts over
  recentring depth: depth-`j` faces contribute `q^(−T_e·j)` times the depth-0 monomials
  (the e = 2 instrument's ratio, general `T_e = e(e+1)/2`); closed rational forms via
  the URLim calculus.  The RW1-row formulas are landed as algebra; this stage gives them
  their counting meaning and closes `CenteredConeLaw` at the given e.
* **CN5 (the unramified base change; CL1 — the genuinely new infrastructure).**  δ ≥ 2:
  relate `stratPoly O (δe) N (p^e)` to the exponent-`e` cone over the degree-δ
  unramified extension, whose value laws come FREE from the ∀-O quantifier of
  `DecidedValueLaw`.  Routes: construct the unramified extension of a complete DVR in
  mathlib vocabulary and transport `Coeff` strata along it (pair becomes `ñ(X^δ)`,
  still one `Polynomial ℚ`), or run the OM/φ-adic expansion (ChapC frames) at the
  degree-δ point directly.  No landed theorem touches this; hardest single stage.
  Target: `PointConeLaw` unrestricted — with CN3/CN4 this closes the front through
  `decidedSliceAt_all_of_cones`.

Instruments (directive-compliant): e = 2 (all cases; first blood target
`stratDecCount O 2 ⟨{(2,1)}⟩ N (X²) = Σ_{j : 3(j+1) ≤ ...} (q−1)q^(2N−3(j+1))`-form),
e = 3 (first composite-face residual splits), (δ, e) = (2, 2) (first base-change case).
Every stage statement must remain uniform in q, e, δ; the instruments are pattern
batteries and nonvacuity witnesses only.

## What this unit did NOT do (honest fence)

No cone COUNT was proved — `PointConeLaw` and `CenteredConeLaw` are open (they are the
named heart, deliberately localized).  First blood on the smallest cone (e = 2 ramified
face) was scoped and blueprinted (CN2 route (i)) but not attempted: it needs the
class-level NP decidedness criterion, which is genuinely new math in ChapI vocabulary
(the corpus check confirmed nothing exports "fractional slope ⇒ ramification" over
`Coeff` classes — C61's ℓ-half is open in ChapC too).  Landing the interface + both
reductions was chosen as the maximal honest core; the charge sanctioned this shape.

## File map

`leanfinal/Uniformity/ChapI/IFCG21.lean`: §1 `PtURLim` calculus · §2 `pointStratFamily`
+ `PointConeLaw` + `ptURLim_unit_factor` · §3 `pointBlockFamily` + `ptURLim_blockPoly` +
`uRLim_spFamily_of_ptURLim` + ★★ `singlePointAggregateLaw_of_pointCone` +
`decidedSliceAt_all_of_pointCone_fractional` · §4 `coneCellCount` + `CenteredConeLaw` +
`eq_addC_pow_of_patternOf` + `addC_pow_centre_inj` + `centreOf`/`centreOf_eq` +
`fullLoopClassN_mem_stratum` + ★ `fracCellCount_eq_sum_coneCellCount` + ★★
`deepFractionalCellLaw_of_centeredCone` + ★★★ `decidedSliceAt_all_of_cones` · AxCheck
footer (12 lines, all Lean core).  Aggregator: one import line in
`Uniformity/ChapI.lean`.  No other landed-file edits; no git mutation.

## Repair log (3 error rounds total, all trivial)

1. `div_eq_div_iff` argument order (goal sides swapped) + missing
   `linter.overlappingInstances` set_option.
2. `List.mem_cons_self` is implicit-argument at this pin; a `simp only` closed the nil
   case early (dead `split_ifs` removed).
3. Structure-projection atoms blind `omega` after `obtain ⟨δ, E⟩ := b` — `replace` the
   kernel hypotheses into clean forms first (IFCG19's pattern).  Also
   `Polynomial.Monic.eq_X_add_C` returns `p = X + C (p.coeff 0)`, not an existential;
   `tendsto_finset_sum` → `tendsto_finsetSum` deprecation.
   The §4 partition theorem and the DFCL reduction landed FIRST TRY.
