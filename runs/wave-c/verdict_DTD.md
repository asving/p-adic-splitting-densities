# UNIT DTD — VERDICT: THE DEEP TAIL DRAINED BY KÖNIG + KRASNER — `DeepTailDrainAt n` (EVERY n) reduced to TWO decoupled classical Props, the capstone's a2 field now `(∀ m ≥ 4, KrasnerAt m) → (∀ m ≥ 4, DiscNullAt m) → ∀ n, DrainageAt n`, ALL LEAN CORE (2026-08-30)

**Status: DONE — honest conditional of maximal reach; the unconditional fire of
`DeepTailDrainAt` was NOT achieved (the two residuals below are the exact surviving
open set); everything reachable by the design is landed, first-attempt green on 3 of
4 increments.**

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG49.lean` (530 lines, ZERO sorries,
zero warnings; THIRTEEN AxCheck footer lines, ALL pure Lean core `{propext,
Classical.choice, Quot.sound}` — no cite is consumed anywhere in this file).  One-line
aggregator import added to `Uniformity/ChapI.lean` (after IFCG47; IFCG48 is another
unit's and was NOT touched).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG49.lean` (final: zero diagnostics
beyond the 13 expected prints), targeted `lake build Uniformity.ChapI.IFCG49` GREEN
(8959 jobs), aggregator `lake env lean Uniformity/ChapI.lean` GREEN.  NO git ops.

## ★★★ THE HEADLINE

    def KrasnerAt n  : Prop :=      -- THE FIELD-THEORY RESIDUAL (no counting)
      ∀ O (complete DVR, finite residue), ∀ a : Fin n → O,
        resultant (monicPoly a) (derivative (monicPoly a)) n (n−1) ≠ 0 →
        ∃ N σ, DecidedAt O n σ N (proj O n N a)
    def DiscNullAt n : Prop :=      -- THE COUNTING RESIDUAL (no field theory)
      ∀ O (complete DVR, finite residue),
        Tendsto (fun D => #{c : Coeff O n D | classDisc c = 0} / q^(nD)) atTop (𝓝 0)

    theorem deepTailDrainAt_of_krasner_discNull :          -- ★★★ LEAN CORE, EVERY n
      KrasnerAt n → DiscNullAt n → DeepTailDrainAt n
    theorem drainageAt_all_of_krasner_discNull :           -- ★★★ THE CAPSTONE FEED
      (∀ m ≥ 4, KrasnerAt m) → (∀ m ≥ 4, DiscNullAt m) → ∀ n, DrainageAt n
    theorem undecidedDrainAt_of_krasner_discNull :         -- ★★ even the σ-free carrier
      KrasnerAt n → DiscNullAt n → IFCG45.UndecidedDrainAt n
    theorem krasnerAt_one, discNullAt_one                  -- nonvacuity witnesses, n = 1

`KrasnerAt` is quantitative Krasner / Okutsu–Montes completeness in its WEAKEST form:
one point, ∃-level, no rate, no uniformity in `a` — textbook content, citable under
owner gate (b).  `DiscNullAt` is Serre's zero-measure lemma for the ONE explicit
hypersurface `Res(f, f') = 0` — pure counting, no decidedness, no σ, no factorization.
Neither is equivalent in strength to the drain (each is one pure phase of it); the
capstone's ENTIRE `a2` field now rests on this pair at `n ≥ 4` — OR, independently, on
UDR's `DeepTailDrainAt` family (the open set is the minimum of the two supplies).

## ROUTE DECISION (charge item 1 — the design, and the refutation that forced it)

**The charge's case (i) is FALSE as literally stated and was refuted before designing:**
CN4's deep box `{c | ∀ i, m − i ≤ resOrd (c i)}` has `card = q^(mM + m(m−1)/2)` at
level `M + m`, hence CONSTANT proportion `q^(−m(m+1)/2)` — it does NOT drain with the
level.  The deep arm must therefore recurse (the self-similar loop), and the shallow
arms (RECUR's trichotomy) would consume the OPEN `CellTypeScalingAt` (both transport
directions of IFCG47's iff need it), the OPEN CN5 unramified bridge (deg ψ ≥ 2
recentring), and the B.42 face factorization — several units of conditional apparatus.

**The route taken — the KÖNIG/KRASNER dissection.**  The key observation:
`DeepTailDrainAt` is a PER-`O` Tendsto (no uniform rate in `q` is demanded), and
`deepTailSet ⊆ undecidedSet` by definition — so compactness is available per `O`:

1. `DecidedAt` is a ∀-lifts predicate, so undecided classes truncate to undecided
   classes: the undecided sets are NESTED under truncation (§2, trivial from the defs).
2. **The König engine** (§3): a truncation-closed family of nonempty class sets
   contains the projections of a SINGLE integral point at every level.  Machinery:
   extendable elements via the infinite pigeonhole (`Finite.exists_infinite_fiber` over
   the levels), a `Nat.rec` chain of extendable elements, and `IsPrecomplete.prec`
   (adic completeness, the Henselian.lean SMOD idiom) for the limit.  Fully general —
   a reusable jewel for any future compactness argument over `Coeff`.
3. **The envelope** (§4): run the engine on the survivor family
   `{undecided} ∩ {classDisc(trunc_D ·) ≠ 0}` (the discriminant resultant is a
   level-`D` cylinder condition by `resultant_map_map` — §1).  A König point would be
   undecided at EVERY level yet separable — killed by `KrasnerAt`.  So the family dies
   at some `N₀(D)`, and beyond it EVERY undecided class lies in the level-`D`
   discriminant-null cylinder, whose proportion at every level `N ≥ D` is EXACTLY
   `discNullSeq O n D` (IFCG46 §0's fiber count) — which `DiscNullAt` drains.
4. `deepTailSeq ≤ undecidedSeq` + squeeze (§5) ⟹ `DeepTailDrainAt n`, every `n`.

## THE EXACT SURVIVING OPEN SET (the a2 fence after DTD)

`∀ n, DrainageAt n` (the capstone's a2) now rests on EITHER of two independent supplies:

* **`KrasnerAt n` + `DiscNullAt n`, `n ≥ 4`** (this unit) — discharge lanes:
  - `KrasnerAt`: (a) reduce to IRREDUCIBLE `monicPoly a` by factoring over `O[X]` (UFD)
    and recursing through the landed IFCG42 transfer
    `decidedAt_mulClass_of_not_dvd_resultant`; the pairwise resultant nonvanishing
    comes from `Res(f,f') ≠ 0` via mathlib's `resultant_mul_right/left`
    (multiplicativity at controlled degrees) + `resultant_eq_zero_iff` (over
    `Frac O`) + `resultant_map_map`.  (b) The irreducible core is literal Krasner:
    mathlib HAS `IsKrasner` with instance `of_completeSpace`
    (`Mathlib/Analysis/Normed/Field/Krasner.lean`) — bridging the corpus's algebraic
    DVR framing to the normed framing is the work; the faithful cite (owner gate (b))
    is the honest alternative.
  - `DiscNullAt`: Serre's null-count.  One-variable primitive-polynomial root-count
    bound (the Bezout instrument `exists_mul_add_mul_eq_C_resultant` is in mathlib's
    resultant file) + coordinate/Fubini induction; nonvanishing of the disc function
    is witnessed by products of distinct monic linear factors (every DVR is infinite).
    Pure counting — no OM apparatus anywhere.
* **`DeepTailDrainAt n`, `n ≥ 4`** (UDR's IFCG46, unchanged) — the recentring/H.124
  lanes remain as recorded there; note this unit's per-`O` compactness route makes the
  σ/count-free pair strictly more attackable (each residual is a classical statement
  with existing literature and partial mathlib support).

## File map (`leanfinal/Uniformity/ChapI/IFCG49.lean`, 530 lines)

§1 `classPoly`, `classPoly_proj`, `classDisc`, ★ `classDisc_proj` (resultant commutes
with the level projection), `discNullSet`/`discNullSeq`(+nonneg) ·
§2 `coeffFactor_coeffFactor` (lift-mediated, `rfl`-core), `decidedAt_of_coeffFactor`,
`undecidedAt_coeffFactor` · §3 `TruncClosed`, `extSet`, `extSet_nonempty`,
`extSet_step`, ★★ `exists_point_of_truncClosed` (THE KÖNIG POINT) ·
§4 `survivorSet`, `truncClosed_survivorSet`, ★ `not_forall_survivor_nonempty` (the
König–Krasner contradiction), `undecidedSet_subset_discNull`,
★ `undecidedSeq_le_discNullSeq`, ★★ `tendsto_undecidedSeq_zero_of_krasner_discNull`
(THE PER-`O` DRAIN) · §5 `KrasnerAt`, `DiscNullAt`, `deepTailSeq_le_undecidedSeq`,
★★ `undecidedDrainAt_of_krasner_discNull`, ★★★ `deepTailDrainAt_of_krasner_discNull`,
★★★ `drainageAt_all_of_krasner_discNull` · §6 `krasnerAt_one`, `discNullAt_one`
(nonvacuity witnesses) · AxCheck footer (13 lines, ALL Lean core).
Imports: IFCG46 only (everything else transitively).

## Honesty ledger

* `DeepTailDrainAt`, `DrainageAt`, `UndecidedDrainAt`, `DecidedAt`, `UndecidedAt`,
  `undecidedSeq` consumed byte-unchanged; nothing weakened; the reduction is an
  implication INTO the capstone field; the residuals are named, ∀-`O`, uniform in `q`.
* The residual Props carry the same instance pack as `DeepTailDrainAt` (`O : Type`,
  the corpus's universe convention — DTR's logged fence respected).
* The per-`O` Tendsto form is exactly what the capstone consumes — no uniform-rate
  claim is made or needed.
* Nonvacuity: both Props PROVED at `n = 1` (§6) — the conventions (formal resultant
  degrees `n, n−1`, the decision target, level normalization) are machine-checked, not
  eyeballed.
* Axioms: Lean core only, machine-printed for all 13 public declarations; no owner
  cite touched or introduced; B.42/C.33 do not occur.
* PROJECT_STATE folding suggestion: a2's remainder line should now read
  "`KrasnerAt n` + `DiscNullAt n`, n ≥ 4 (IFCG49; or `DeepTailDrainAt n`, IFCG46) —
  pointwise Krasner completeness + the discriminant null-count".

## Repair log (2 error rounds, both mechanical; every theorem landed as designed)

1. `Set.infinite_coe_iff` direction: `.mpr` where `.mp` (Infinite ↥s → s.Infinite) was
   needed — two spots, one-token fixes.
2. `Nat.le_induction` base case: `rw [← ha]` does not auto-close the residual
   `coeffFactor (proj a) = proj a` (defeq beyond reducible-`rfl`) — append `rfl`.

Traps AVOIDED by design (UDR/CN4/DTR logs consulted): every truncation identity routed
through a LIFT (`proj_surjective` + the `rfl` `coeffFactor_proj`) — no `Ideal.Quotient.factor`
API touched; all exponent bookkeeping via the IFCG46 §0 `← Nat.mul_add, Nat.sub_add_cancel`
idiom, no variable products in omega; the SMOD↔membership bridge by Henselian.lean's exact
`← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one` chain; the `D ≤ N` guard in `survivorSet`
bound as a PROOF argument so the family is total and definitional proof irrelevance makes
the guard free; `O : Type` (not `Type*`) in the named Props per DTR's universe fence.
