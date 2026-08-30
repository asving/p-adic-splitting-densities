# UNIT WFR — VERDICT: THE PIGEONHOLE DECISIONS LANDED (full + off-one), THE STAIRCASE SECTOR CLOSED AND SCOPED (it is DEEP), THE RESIDUAL POLYNOMIAL PROVED CLASS DATA (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG28.lean` (1024 lines, ZERO sorries, zero
warnings; 16 AxCheck footer lines — Lean core `{propext, Classical.choice, Quot.sound}`
on §0/§2-counting/§2-scoping and ALL of §3, and Lean core PLUS EXACTLY the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42) on the three
decision theorems; the C.33 (r = 1) cites do NOT occur — no ChapC import; no landed file
touched except the sanctioned one-line aggregator import in `Uniformity/ChapI.lean`;
IFCG27 untouched; no git ops).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG28.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG28` green (8935 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE HEADLINE — CRL's design finding at FULL strength, beyond the charge

    theorem decidedAt_of_two_point_sides :          -- ★★ THE PIGEONHOLE DECISION
      (r slopes (uᵢ,ℓᵢ), pairwise distinct as rationals, coprime, each VISIBLE and
       attained at ≥ 2 abscissae, Σℓᵢ = m; stratum heights ≥ 1; corner visible v₀ < K)
      → DecidedAt O m ⟨{(ℓᵢ,1)}ᵢ⟩ K c
    theorem decidedAt_of_two_point_sides_off_one :  -- ★★ THE OFF-ONE PIGEONHOLE
      (same, all ℓᵢ ≥ 2, Σℓᵢ = m − 1)
      → DecidedAt O m ⟨{(ℓᵢ,1)}ᵢ + {(1,1)}⟩ K c

The charge asked for the all-integer staircase (`m` distinct two-point slopes ⇒ totally
split).  The landed engine is the general form: ANY mixed-denominator system of visible
two-point slopes whose widths total `m` (or `m − 1` with no unit-denominator slack
sink).  Mechanism exactly as CRL predicted: B.42 dissects every lift into one pure block
per two-point slope with `ℓ ∣ deg`, `deg > 0`; the total `m` pins every width with NO
width lemma and NO simultaneous face bookkeeping — the off-one variant additionally
forces the one leftover degree OUT of every fractional block (`ℓ ∣ deg`, `ℓ ≥ 2`
forbids excess 1), so B.42's set must carry exactly one extra block, monic linear, split
`(1,1)`.  IFCG26 §4 decides every pinned block.  Uniform in `q, m, K` and the slope
data; every complete DVR.  CRL's `decidedAt_cubic_mixed` (visible-corner case) is the
off-one instance `T = {(1,2)}` at `m = 3`.

## ★★ THE SECOND ENGINE — CN1-FOR-RESIDUALS, all Lean-core (§3)

    theorem onSide_monicPoly_iff   : below the floor, lift-OnSide ↔ class-NPAttains
    theorem sideSet_monicPoly_eq   : every lift's sideSet = classSideSet (a Finset def)
    theorem sideMin/Max_monicPoly_eq : the endpoints are class data
    theorem resPoly_monicPoly_eq   : ★★ H₀ = H₀' ∧ resPoly(lift a) = resPoly(lift a')

The side residual polynomial at the x-frame is a CLASS INVARIANT below the frame floor:
any two lifts of `c` have the same side set, the same `sideMin`/`sideMax`/`sideDeg`, the
same left height, and byte-identical `resPoly`.  Engine: the new two-sided bridge (the
`→` of `onSide_monicPoly_iff`: a lift's on-side height is finite below the floor, hence
exact, hence the class height — IFCG26 §1 was only `←`) + the digit lemma
(`digAt_congr`/`digPoly_congr`/`resMk_congr`, B77b's private trio re-proved) + the
all-abscissa coefficient congruence `monicPoly_sub_coeff_dvd` (covers the monic top
`1 − 1` and beyond `m`, so NO case split at the side's right end).  This is the exact
input the wide-face (`sideDeg ≥ 2`) refinement consumes: **the residual's factorization
type is class data** — B.63's separability hypothesis and any future coprime-splitting
hypothesis can now be READ OFF THE CLASS.

## ★ THE HONEST SCOPING THEOREM — the literal staircase sector is DEEP (§2)

    theorem decidedAt_staircase      : strictly convex integer heights ⇒ TOTALLY SPLIT
    theorem mem_deepBox_of_staircase : the same hypotheses FORCE vᵢ ≥ m − i
    theorem staircase_not_shallow    : no staircase class is shallow
    theorem card_exactBox            : #(exact-height box) = (q−1)^m · q^(Σ(K−vᵢ−1))

The charge's literal target (`decidedAt_staircase`, the `ℓ ≡ 1` corollary of the
pigeonhole) is landed — WITH the finding that it contributes NOTHING to the cone
remainder carrier: strict convexity of integer slopes forces the Eisenstein-deep heights
(`uᵢ ≥ m − i` by downward induction, so `vᵢ ≥ m − i`), i.e. every all-integer staircase
class lies in the deep box = the zero-centre recentring range = the RECURSION's
territory, disjoint from `shallowSet`.  Contrapositive worth recording: every SHALLOW
class all of whose sides are two-point carries at least one FRACTIONAL side.  The cell
count `card_exactBox` is the CN4 monomial genre, uniform in the height vector — it (with
IFCG24's `card_setOf_le_resOrd`/`card_pi_set`) supplies the per-cell counting for the
whole partition campaign.

## THE EXACT SURVIVING SET (charge item 4 — the fence)

`ConeRemainderLaw e σ` at `e ≥ 4` (hence `DecidedSliceAt` via IFCG26 §8 + the block
bridges) now rests on exactly:

1. **The carrier partition/count** (no new decision engine needed for this sector):
   enumerate the shallow stratum classes off the pure faces by polygon shape; the
   visible all-two-point shapes (with or without one leftover degree) are DECIDED by
   the two pigeonhole theorems with their types explicit; each cell is a box counted by
   `card_exactBox` + IFCG24's toolkit; the sector sum over staircase-style height
   vectors is a geometric-series campaign (rational in `q` by construction).
2. **The invisible-corner cells** (`v₀ ≥ K`, `a₀ = 0` included): both pigeonhole
   theorems consume B.42 directly, which gates on `dev X f 0 ≠ 0` — supplied by corner
   visibility.  The named missing mechanism is the CLASS-LEVEL X-STRIP (IFCG26 §2's
   lift-level induction raised to classes: an invisible-corner mass-`m` class strips to
   a mass-`m−1` class with shifted heights); CRL §5 dodged it at `m = 3` by pure degree
   bookkeeping, which does not scale.
3. **The wide-face cells** (`sideDeg ≥ 2`): §3 delivers the class-stable residual; the
   surviving Hensel input is the x-frame BLOCK SPLIT ALONG A COPRIME RESIDUAL
   FACTORIZATION (C133mh's `theoremA` is the KeyFrame (`h ≥ 1`) sibling; the x-frame
   instance is in neither the corpus nor mathlib) — equivalently B.63's
   `typeOf_of_separable_residuals` fires on B.42 alone but carries the open PERIMETER
   supply (`ψ.natDegree = 1 ∨ φ.natDegree·ψ.natDegree ∣ inertiaDegOf` at every pure
   divisor) at residual degree ≥ 2.  Plus the recursion of refined blocks to
   smaller-mass cones.  §3 was built so that either discharge consumes it verbatim.
4. Unchanged from CRL: `UnramifiedBlockBridge δ e` (CN5's family, another unit's), and
   `FracFaceForcesRamStatement` OFF the stratum (not census-blocking).

## Design decisions (recorded)

* The pigeonhole needs NO "these are all the sides" completeness hypothesis: B.42's
  clause 5 (two-point ⇒ membership) plus the degree total excludes phantom blocks for
  free.  Slope positivity `hu` is likewise re-supplied by B.42's clause 1 for members —
  kept in the signature as the honesty guard (IFCG26's `he'` precedent).
* §3 is stated as LIFT-INDEPENDENCE (two arbitrary lifts agree), not as a new
  choice-based class-residual object — no new definition crosses the trust boundary;
  `classSideSet` (a `Finset.filter` of `NPAttains`) is the only new def and is
  membership-transparent.
* No dead named Prop for the wide-face residue: the fence above is the reduction record
  (CRL precedent).

## File map (`leanfinal/Uniformity/ChapI/IFCG28.lean`, 1024 lines)

§0 supply (`isKey_X` private, `sum_singleton_eq_map`/`map_sum_singleton` private,
`monicFactors_one`, `monicFactors_prod`, `min'_congr`/`max'_congr` private) · §1
★★ `decidedAt_of_two_point_sides`, ★★ `decidedAt_of_two_point_sides_off_one` · §2
`totallySplitType`, `npHeight_strict_anti_of_staircase`, ★ `decidedAt_staircase`,
`exactBox`/`mem_exactBox_iff`, ★ `card_exactBox`, ★ `mem_deepBox_of_staircase`,
`staircase_not_shallow` · §3 ★ `onSide_monicPoly_iff`, `classSideSet`,
★ `sideSet_monicPoly_eq`, `sideMin/Max_monicPoly_eq`, digit trio private,
`monicPoly_sub_coeff_dvd`, ★★ `resPoly_monicPoly_eq` · AxCheck footer (16 lines).
Aggregator: one import line in `Uniformity/ChapI.lean`.

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. `simpa using map_sum ...` self-collapsed to `True` (simp proves the hom equation both
   ways) → replaced by the `map_sum_singleton` helper via `Multiset.map_map`.
2. `Nat.le_or_lt` and `le_or_lt` both absent at the pin → `Nat.lt_or_ge` with swapped
   branches (left one dangling-line cleanup).
3. ℕ∞ casts: `exact_mod_cast` does NOT collapse `↑ℓ * ↑n` here, and
   `WithTop.ne_top_iff_exists` returns the `WithTop.some` coercion, not `Nat.cast` —
   fixed by a defeq-coerced `have hn' : ((n : ℕ) : ℕ∞) = ...` plus IFCG26's explicit
   `nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj` chain.
4. Final `omega` on `ℓ·n = ℓ·classCoeffVal` is NONLINEAR (variable product) → rewrite
   `← hneq` then `exact`.
5. `Finset.sum_eq_sum_diff_singleton_add` and `Finset.eq_empty_iff_forall_not_mem`
   absent at the pin → `Finset.sum_erase_add` (erase-form bookkeeping throughout) and
   `Finset.eq_empty_or_nonempty`; `push_neg` (deprecated) eliminated.

Traps AVOIDED by design (CN2/CN4/CRL logs consulted): `set_option … in` lines precede
docstrings; no `set`-fvars near omega; index-shift atoms (`i+1+1` vs `i+2`) normalized
by defeq-typed `have` bindings before every omega; distance-`d` downward inductions
(`∀ d i, i + d + 1 = m → …`) instead of ℕ-subtraction recursions; `Finset.mem_filter`
unfolds for the Classical filters, never `decide`.
