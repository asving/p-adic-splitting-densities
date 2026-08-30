# UNIT CRL — VERDICT: THE e = 3 REMAINDER LAW CLOSED, THE GENERAL-POSITION FORCING PROVED AT THE CARRIER, THE CENSUS FRONT RE-BASED TO e ≥ 4 (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG26.lean` (968 lines, ZERO sorries, zero
warnings; 15 AxCheck footer lines — Lean core `{propext, Classical.choice, Quot.sound}`
on §§0–1/§4/§6-carrier, and Lean core PLUS EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42 = GN15 Thm 2.3 + FGMN Thm 6.6,
r = 0 x-frame) on everything downstream of the Hensel heart; the C.33 (r = 1) cites do
NOT occur — no ChapC import; no landed file touched except the sanctioned one-line
aggregator import in `Uniformity/ChapI.lean`; IFCG25 untouched (imported only); no git
ops). Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG26.lean`
(final: zero diagnostics), targeted `lake build Uniformity.ChapI.IFCG26` green (8934
jobs), aggregator `lake env lean Uniformity/ChapI.lean` green.

**Charge amendment honored:** CN5 landed mid-unit; the family became load-bearing at
EVERY `e ≥ 3`. The amendment's hoped-for outcome (mass-3 remainder EMPTY) is FALSE —
CN4's fence already exhibited the nonempty carrier — but emptiness was never needed:
the member closes by exact EVALUATION. `UnramifiedBlockBridge` untouched, per amendment.

## ★★★ THE HEADLINE — the census family's forced `e = 3` member, CLOSED

    theorem coneRemainderLaw_three (σ) : ConeRemainderLaw 3 σ     -- EVERY σ, no premises
    theorem zeroConeClause_three (σ)  : ZeroConeClause 3 σ        -- the m = 3 clause fires
    theorem decidedSliceAt_all_of_remainder4_bridge :             -- ★★★ the front re-based
      (∀ e ≥ 4, (smaller value laws) → ∀ σ deg-e Witnessed, ConeRemainderLaw e σ) →
      (∀ δ e ≥ 2, UnramifiedBlockBridge δ e) → ∀ n, DecidedSliceAt n

The mass-3 remainder is NOT empty: its carrier is exactly the mixed box
`{v₀ ≥ 2, v₁ = 1, v₂ ≥ 1}` (`remainder_carrier_three`: `(stratum ∩ shallow) \
pureFaceSet = mixedBox`, a set identity needing no decidedness), every class of it is
DECIDED with the mixed type `{(1,1),(2,1)}` (★★ `decidedAt_cubic_mixed`), and the count
is the exact monomial `(q−1)·q^(3K−5)` at every level `K` (`card_mixedBox`,
`coneRemainderCount_three_mixed`); every other type's remainder VANISHES
(`coneRemainderCount_three_ne`, via `decidedAt_unique`). So `ConeRemainderLaw 3 σ` holds
with the pair `(X − 1, X^5)` at the mixed type and `(0, 1)` otherwise — uniform in `q`,
every complete DVR, every uniformizer. Combined with CN5's `coneRemainderLaw_two`, the
census front now rests on exactly: **`ConeRemainderLaw e σ` at `e ≥ 4`** + the block
bridges (§8's wrapper composes IFCG25's capstone).

## ★★ THE ENGINES (the charge's items 1–2, at their reachable scope)

**§1 The general-position bridge (Lean-core).** `onSide_monicPoly_of_npAttains`: strictly
below the frame floor, EVERY class-NP attained abscissa is `OnSide` for EVERY lift, and
the lift's `suppVal` equals the class support. This frees CN2's purity bridge from the
endpoint-spanning hypothesis — purity is the special case `i ∈ {0, m}`. Key consequence
used everywhere: the class polygon's arithmetic stays in ℕ (omega-friendly); no
polynomial-side height computation is ever repeated.

**§2 The Hensel heart (consumes B.42).** `exists_pure_factor_of_two_point_side`: over a
complete DVR, a monic `f` with `f̄ = X̄^deg f` whose x-polygon has a two-point side of
slope `−u/ℓ` (coprime) factors as `f = F·R`, `F` monic `(u,ℓ)`-pure of positive degree,
`R` monic. **The `f(0) = 0` corner is a theorem, not a hypothesis**: an X-strip induction
(`divX`; `suppVal (X·f₁) = suppVal f₁ + u`, sides shift by one abscissa) reduces to
B.42's `dev X f 0 ≠ 0` case. This is why `decidedAt_cubic_mixed` needs NO case split —
lifts with `a₀ = 0` ride the same statement.

**§3 ★ `fracFaceForcesRam_of_stratum`** — the charge's item-1 target at the census
carrier: a visible class NP face of slope `h/e'` (`e' ≥ 2`, coprime) ANYWHERE on the
polygon of a STRATUM class (`f̄ = X̄^m`) forces `e' ∣ ramIndexOf g'` on some monic
irreducible factor of EVERY lift. This is IFCG23 §7's `FracFaceForcesRamStatement`
restricted to the stratum — which is the entire carrier the census consumes (the
remainder count lives inside `stratum(X^m)`).

**§4 The unit-width decision (the residual-refinement sector with trivial residual).**
`dvd_natDegree_of_isPure`: `ℓ ∣ deg` for every monic pure polynomial (each factor's
`ram` is a multiple of `ℓ` and divides its degree). `irreducible_of_isPure_natDegree_eq`:
a monic `(u,ℓ)`-pure polynomial of degree EXACTLY `ℓ` is irreducible with
`efPair = (ℓ, 1)` — the workhorse deciding every unit-width face block.

**§5 mechanism note (m = 3).** The mixed class's decision is pure degree bookkeeping on
top of §§1–4: the `(1,2)`-side `[1,3]` is class-pinned (support 3, attained at 1 and 3,
the corner `v₀ ≥ 2` pushes abscissa 0 strictly above — uniformly over the INVISIBLE
corner, `v₀ = K` and `a₀ = 0` included); B.42 splits off the pure block `F`; `2 ∣ deg F`
(§4) + `deg F + deg R = 3` pins `deg F = 2, deg R = 1`; §4 decides `F` as `(2,1)`; the
linear `R` is `(1,1)`. No residual polynomial is ever computed — that is exactly why
m = 3 closes without the C133mh engine.

## THE EXACT SURVIVING OPEN SET (charge item 3 — the fence)

After this unit the all-degree decided slice (`DecidedSliceAt n` for all `n`) rests on
precisely (via `decidedSliceAt_all_of_remainder4_bridge`):

1. **`ConeRemainderLaw e σ` at `e ≥ 4`** (with the same smaller-value-law supply the law
   carries). Its content splits into exactly two mechanisms, both now with named engines:
   (a) *general-position faces with unit widths* — §§1–4 decide each such block; what is
   missing is the SIMULTANEOUS class-level width bookkeeping of all faces (class-pinned
   `sideMin`/`sideMax` per slope) and the resulting carrier partition/counting. DESIGN
   FINDING for the successor (proved-by-arithmetic here at m = 3, recorded for general
   m): **when every visible face is unit-width, the width pins are FREE by pigeonhole**
   — B.42 gives ≥ 1 degree per two-point slope, and m distinct slopes force degree
   exactly 1 each, so all-staircase polygons are decided totally split at their slopes
   with NO width lemma. (b) *wide faces, `e' < m` with `sideDeg ≥ 2`* — the genuine
   residual refinement: needs the class-stable residual polynomial (the CN1-for-residuals
   development: digits at the side's lattice points are exact below the floor, so the
   side residual IS class data) + the block-splitting engine (C133mh's `theoremA` /
   FP1's GC0 bridge, or B.42's clause 6 residual tie + B.45/B.63 at the x-frame — B.63's
   `order1Type` theorem is the polynomial-level endpoint: separable residuals decide the
   full type). Recursion to smaller masses enters here: a residual factor of degree `d`
   spawns a block of degree `ℓ·d`, whose deeper refinement is the smaller-mass census.
2. **`UnramifiedBlockBridge δ e`** (`δ, e ≥ 2`) — CN5's other named family, not mine.
3. **`FracFaceForcesRamStatement` OFF the stratum** (IFCG23 §7's literal Prop, arbitrary
   classes): the single missing leg is the x-frame unit-part Hensel coprime split
   (`f̄ = X̄^μ·ū`, `ū(0) ≠ 0` ⇒ compatible factorization of `f`) — in neither the corpus
   nor mathlib at the pin. NOT census-blocking (the census carrier is the stratum).

## Why B.42 and not C.33/C133mh (decision record)

The C.33 axioms are the `r = 1` (KeyFrame-relative) siblings of B.42's `r = 0` statement;
the C133mh engine (`theoremA`, `blockFrontier_of_context`) is the KeyFrame-relative
graded Hensel for RESIDUAL refinement (`F.h ≥ 1` required — the x-frame is not a
`KeyFrame`). The face dissection this unit needs is exactly B.42's signed x-frame
instance. Consuming it keeps the footprint at one cite, already owner-signed 2026-08-16
with a faithfulness entry (`blueprint/CHAP-I_capstone_conditionality.md`). Note the
honest grading this creates: `coneRemainderLaw_two` (CN5) is Lean-core;
`coneRemainderLaw_three` carries the polygon-dissection cite — the fractional
multi-face dissection is genuinely Hensel-grade content that m ≤ 2 never needed.

## File map (`leanfinal/Uniformity/ChapI/IFCG26.lean`, 968 lines)

§0 supply (`isKey_X` private, `mem_sideSet_of_onSide`, `irreducible_of_monic_natDegree_one`,
`monicFactors_of_irreducible`, `exists_mem_monicFactors`, `monicPoly_zero'` (CommRing
scope), `npHgt_X_eq_top`) · §1 ★ bridge (`le_suppVal_monicPoly`,
`onSide_monicPoly_of_npAttains`) · §2 ★ heart (`exists_pure_factor_aux` private
induction, `exists_pure_factor_of_two_point_side`) · §3 ★ `fracFaceForcesRam_of_stratum`
· §4 `dvd_natDegree_of_isPure`, ★ `irreducible_of_isPure_natDegree_eq` · §5 `mixedType`,
`typeOf_eq_of_split_two_one` private, ★★ `decidedAt_cubic_mixed` · §6 `mixedBox`,
`mem_mixedBox_iff`, ★ `remainder_carrier_three`, `card_mixedBox`,
★ `coneRemainderCount_three_mixed`, `coneRemainderCount_three_ne` · §7
★★★ `coneRemainderLaw_three`, ★★ `zeroConeClause_three` · §8
★★★ `decidedSliceAt_all_of_remainder4_bridge` · AxCheck footer (15 lines). Aggregator:
one import line in `Uniformity/ChapI.lean`.

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. `isUnit_of_mul_eq_one` renamed at pin → `IsUnit.of_mul_eq_one` (drops one explicit arg).
2. Inf-attainment rewrite direction (`ht₀` not `← ht₀`); pin's `add_le_add_right` builds
   `c + a ≤ c + b` — use `add_le_add h le_rfl` for the right-added form.
3. `Multiset.prod_singleton` does not match `g' ::ₘ 0` — use `prod_cons`/`prod_zero`;
   `Nat.eq_one_of_self_mul_eq_self_left` does not exist — `Nat.eq_of_mul_eq_mul_left`
   with `mul_one`. Multiset literal swap `{a} + {b} = {b, a}`: `decide`.
4. `field_simp` rewrites the ℕ exponent to `3*(M+3) − 5 + 5 − 5` — close with an
   omega-backed `show`-rewrite of the exponent, not `ring`.
5. `set_option ... in` must precede the docstring, not sit between docstring and theorem
   (CN2's trap #1, re-hit). Lint: `Set.mem_diff` → `Set.mem_sdiff`, `push_neg` retired
   for an `rcases` split.

Traps AVOIDED by design (from CN2/CN4 logs): no `set`-fvar in §5 (all `monicPoly a`
literal); Fin mk-vs-literal handled by defeq `exact`/`show`, never `rw`; `faceH`
membership via `mem_filter` unfold, never `decide` (the Classical filter instance is
noncomputable); the class-side ℕ arithmetic does all polygon work, ℕ∞ appears only
through §1's bridge.
