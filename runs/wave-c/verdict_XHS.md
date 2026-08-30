# UNIT XHS — VERDICT: THE X-FRAME COPRIME-RESIDUAL BLOCK SPLIT LANDED AT BOTH LEVELS, THE UNIT-PART SPLIT LANDED, AND — BEYOND THE CHARGE — IFCG23 §7's `FracFaceForcesRamStatement` IS **CLOSED** (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG30.lean` (777 lines, ZERO sorries, zero
warnings; 9 AxCheck footer lines — Lean core `{propext, Classical.choice, Quot.sound}`
on §0/§1/§2/§3/§5, and Lean core PLUS EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) on §4 and §6; the C.33
(r = 1) cites do NOT occur — no ChapC import; no landed file touched except the
sanctioned one-line aggregator import in `Uniformity/ChapI.lean`; IFCG29 untouched; no
git ops).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG30.lean` (final: zero diagnostics
beyond the 9 expected axiom prints), targeted `lake build Uniformity.ChapI.IFCG30`
green (8938 jobs), aggregator `lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE FINDING THAT REFRAMED THE UNIT — the "absent from corpus" claim was FALSE

Both convergent fences (CRL and WFR) named the x-frame coprime-residual split as
"absent from corpus and mathlib" and pointed at C133mh's `theoremA` (KeyFrame, `h ≥ 1`)
as the sibling to mirror.  **The graded Hensel engine already exists at order 1**:
`Uniformity.Density.Leaf.exists_graded_factorization` (**B.41**,
`ChapB/B41b.lean:184`, landed, sorry-free, LEAN-CORE) is the one-slope
coprime-residual split at EVERY `IsKey φ` — and `X` is an `IsKey` (both consumers
proved `isKey_X` themselves).  C133mh14's own docstring calls Theorem A's conclusion
"B.41-shaped".  The shared blind spot: B41b sits off both consumers' import paths
(they import `ChapB.B42`, which imports only B29/B34/B42a).  Consequence: no new
Hensel engine was needed — the unit's content is the x-frame instantiation, the
class-level packaging, the unit-part split, and the consumer firings, of which the
LAST closes a named open Prop.  **Record correction: CRL's fence item 3 and WFR's
fence items 3–4 should henceforth cite B.41 for the graded split and THIS file for
its x-frame/class forms.**

## ★★★ THE HEADLINE BEYOND THE CHARGE — `FracFaceForcesRamStatement` CLOSED (§6)

    theorem fracFaceForcesRamStatement_holds :
      Uniformity.Density.IFCG23.FracFaceForcesRamStatement

IFCG23 §7's LITERAL open Prop (byte-as-is, arbitrary classes, general face position,
`∀ O`): a visible class NP face of fractional slope `h/e'` (`e' ≥ 2`, coprime)
ANYWHERE on the polygon of ANY class forces a monic irreducible factor with
`e' ∣ ramIndexOf` in every lift.  This was "the exact named residue" of IFCG26 §3
("NOT census-blocking", but a standing named open of the campaign since CN2).
Mechanism (all landed this unit): the unit-part split (§3) produces the strand `g`
with `ḡ = X̄^μ` — ON-stratum by construction; the polygon transfer (§5) moves the two
class-face points from the lift to the strand; IFCG26 §2's Hensel heart splits off the
pure factor; IFCG23's `dvd_ramIndexOf_of_isPure` reads off the ramification.
Footprint: Lean core + exactly the B.42 cite (inherited through IFCG26 §2).

## ★★ THE CHARGE's STATEMENTS (all landed, level-exact, uniform in `q`)

**§1 `exists_xframe_block_split`** (Lean-core) — the pinned statement, byte-shape as in
the stub: monic `(u,ℓ)`-pure `f` at the x-frame, side residual `= unit · (G·H)`, `G, H`
monic coprime ⟹ `f = g · h` with `deg g = ℓ·deg G`, `deg h = ℓ·deg H`, both `(u,ℓ)`-pure,
`GradedCoprime`, left heights `u·deg G / u·deg H`, and residuals EXACTLY `G` and `H`
(∀-pin form).  Proof: B.41 at `φ := X` (degree pins simplified through `deg X = 1`).
This is `C133mh14.TheoremAStatement`'s x-frame sibling, as the charge demanded.

**§2 `exists_class_block_split`** (Lean-core) — THE CLASS-LEVEL SPLIT below the frame
floor: class `c` with visible `(u,ℓ)` side attained at `0` and `m` (class-pure), class
residual — read off ONE reference lift, class data by WFR §3 — factoring as `G · H`
coprime ⟹ EVERY lift of `c` splits with the same `G, H` and all §1 pins.  Consumes
WFR's `resPoly_monicPoly_eq` verbatim (as IFCG28 §3 was designed for) + IFCG26 §1's
bridge + §1.  Note the grading: the class-level coprime-residual split is
**Lean-core** — B.42 is NOT needed for pure-side classes.

**§3 `exists_unitPart_factorization`** (Lean-core) — CRL's fence statement verbatim:
`f̄ = X̄^μ · ū`, `ū` monic, `ū(0) ≠ 0` ⟹ `f = g · h`, `ḡ = X̄^μ`, `h̄ = ū`, degrees
pinned.  Proof: `IsCoprime (X^μ) ū` (explicit Bézout from `divX`, §0) + the landed
exact Hensel `Uniformity.Hensel.exists_monic_factorization`.  PLUS
`unitPart_factorization_level_exact` (IFCG16 §6 at the pair `(X̄^μ, ū)`): strand/unit
splits of mod-`𝔪^N`-congruent products are factorwise congruent mod `𝔪^N` — the
strand's level-`N` class is a function of `f`'s level-`N` class (the class-level
strand map CRL's successor can now define).

**§4 `wideFace_refinement_of_stratum`** (Lean core + exactly B.42) — WFR's wide-face
refinement law, fired at visible-corner stratum classes: stratum class, visible corner
(`v₀ < K`), visible class face `(u,ℓ)`, class residual `G · H` coprime ⟹ EVERY lift
refines as `monicPoly a = g · h · R` with `g, h` pure of degrees `ℓ·deg G / ℓ·deg H`
carrying residuals EXACTLY `G, H`, `R` monic (the other slopes' blocks).  Mechanism:
B.42 clause 5 locates the block from the class face, clause 6 ties its residual up to
a unit, WFR §3 transports the class factorization, §1 splits the block.

**§5 the polygon transfer** (Lean-core) — the engine that closed §6, of standing
independent value: `suppVal_mul_unitCorner` and `onSide_mul_unitCorner_iff` — for
`u > 0` and cofactor `h` with `h(0)` a UNIT, `suppVal X (g·h) u ℓ = suppVal X g u ℓ`
and `OnSide X (g·h) u ℓ j ↔ OnSide X g u ℓ j` for every `j`.  The weighted-Gauss
multiplicativity at a flat cofactor: B.33 (`suppVal_add_le_suppVal_mul`) is the `≥`
half; the `≤` half and the side identity are the first-minimal-index argument — `u > 0`
prices every positive `h`-abscissa one level deeper, so the corner pair `(j, 0)` alone
carries the minimal valuation, and `addVal_eq_of_pow_dvd_not_dvd` reads the exact
height.  (The general polygon-of-product additivity remains open; this unit landed
exactly the unit-cofactor case, which is what every consumer named.)

## Fence-conformance record (the charge's item 1 check)

* CRL fence item 3 ("the x-frame unit-part Hensel split, `f̄ = X̄^μ·ū`, `ū(0) ≠ 0` ⇒
  compatible factorization") — §3 verbatim, THEN §6 fires the whole off-stratum
  forcing, so the item is not merely supplied but RETIRED.
* WFR fence item 3 ("the x-frame block split along a coprime factorization of the
  residual … C133mh's theoremA … x-frame instance") — §1 (polynomial), §2 (class);
  `resPoly_monicPoly_eq` consumed verbatim.  The wide-face refinement law fires at
  visible-corner stratum cells as §4.
* WFR design intent "§3 was built so that either discharge consumes it verbatim" —
  confirmed: §2 and §4 both consume it with no adapter.

## THE EXACT SURVIVING OPEN SET (after this unit)

1. **Invisible-corner wide-face cells** (`v₀ ≥ K`, `a₀ = 0` included): §4 gates on
   corner visibility (B.42's `dev ≠ 0`).  The named mechanism is WFR fence item 2's
   class-level X-strip — another unit's, untouched here.
2. **The leaf decision of refined blocks** (pure block with IRREDUCIBLE residual of
   degree `≥ 2`): B.63's perimeter supply (`ψ.natDegree = 1 ∨ φ.natDegree·ψ.natDegree ∣
   inertiaDegOf` at every pure divisor).  §§1–4 split blocks; they do not decide the
   irreducible-residual leaves.  Unchanged, as scoped.
3. The recursion of refined blocks to smaller-mass cones (the census campaign's own
   structure) — unchanged.
4. `UnramifiedBlockBridge δ e` — CN5's family, another unit's, unchanged.

## File map (`leanfinal/Uniformity/ChapI/IFCG30.lean`, 777 lines)

§0 supply (`isKey_X` private, `isCoprime_X_pow_of_coeff_zero_ne_zero`) · §1
★ `exists_xframe_block_split` · §2 ★★ `exists_class_block_split` · §3
★ `exists_unitPart_factorization`, `unitPart_factorization_level_exact` · §4
★★ `wideFace_refinement_of_stratum` · §5 `succ_le_of_cast_le_nsmul` /
`suppVal_le_weighted` / `suppVal_ne_top_of_monic` / `npHgt_mul_of_onSide` (private),
★ `suppVal_mul_unitCorner`, ★ `onSide_mul_unitCorner_iff` · §6
★★★ `fracFaceForcesRamStatement_holds` · AxCheck footer (9 lines).  Imports beyond the
consumers' baseline: `ChapB.B33` (the `≥` half of the product law), `ChapB.B41b` (the
graded engine), `ChapI.IFCG16` (finite-precision uniqueness), `HenselFactorization`
(exact Hensel).  Aggregator: one import line in `Uniformity/ChapI.lean`.

## Repair log (2 error rounds; every theorem landed as designed)

1. §0 Bézout: `rw [← h1]` (h1 : `divX·X + C c = U`) rewrote `U` inside its own
   subterms (`U.coeff 0`, `U.divX`) — replaced by `linear_combination
   (-(C c⁻¹)) * h1 + hc`.
2. §5: `WithTop.ne_top_iff_exists` returns the `WithTop.some` coercion, not `Nat.cast`
   (WFR repair log #3, re-hit twice) — fixed both sites with the defeq-coerced
   `have hw' : ((w : ℕ) : ℕ∞) = v := hw` idiom before any cast rewriting.

Traps AVOIDED by design (CN2/CN4/CRL/WFR logs consulted): no `set` fvars; `Nat.lt_or_ge`
not `le_or_lt`; `Nat.mul_le_mul` not the shifting `Nat.mul_le_mul_left`; the
`nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj` chain for every ℕ∞
extraction; `Finset.sum_erase_add` (erase-form) for the corner-pair decomposition;
antidiagonal pairs destructured via `obtain ⟨p, q⟩` before any omega.
