# UNIT RECUR — VERDICT: THE REMAINDER RECURSION'S TRICHOTOMY MACHINE-CHECKED AT EVERY MASS — the carrier partitions EXACTLY into leaf/power/split sectors, the leaf laws land (d = 1 unconditional), and the census front re-bases on THREE named sector laws + ONE leaf supply (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG35.lean` (1046 lines, ZERO sorries,
zero warnings; 14 AxCheck footer lines — TWELVE are pure Lean core
`{propext, Classical.choice, Quot.sound}` (both leaf laws, the whole minimal-face
machinery incl. the WFR-§3 transport and the residual honesty lemma, the split
dichotomy, THE PARTITION, the assembly, and BOTH spanning decisions), and exactly TWO
carry Lean core PLUS the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42): `sectorLaws_unramified`
(inherits UZL's forcing) and the front `decidedSliceAt_all_of_sectorLaws` (inherits
IFCG31/IFCG33's bridge).  The C.33 cites do NOT occur.  No landed file touched except
the sanctioned one-line aggregator import in `Uniformity/ChapI.lean` (after IFCG34's
line; IFCG34.lean itself untouched); no git ops.)  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG35.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG35` green (8951 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

## ★★★ THE HEADLINE — the recursion's trichotomy is now a THEOREM, at every mass

    theorem remainderCarrier_eq_sectors :        -- ★★ the set partition
      remainderCarrier O m σ M
        = splitSector π m σ M ∪ powerSector π m σ M ∪ leafSector π m σ M
    theorem coneRemainderCount_eq_sector_sum :   -- ★★ exact at EVERY finite level
      coneRemainderCount O m σ M = splitCount + powerCount + leafCount
    theorem coneRemainderLaw_of_sectorLaws :     -- ★★ the assembly
      SplitSectorLaw m σ → PowerSectorLaw m σ → LeafSectorLaw m σ → ConeRemainderLaw m σ
    theorem decidedSliceAt_all_of_sectorLaws :   -- ★★★ THE FRONT
      (three sector-law families at e ≥ 5, σ ramified, each under the < e value laws)
        → (the five e = 4 even-ram laws) → ∀ n, DecidedSliceAt n

Every remainder-carrier class (decided-σ ∩ stratum ∩ shallow ∖ pure faces) has a
UNIQUE minimal-slope last-edge face (`MinFaceAt`, `1 ≤ h < e'` coprime, attained at the
monic point, visible — UZL's construction re-derived with the monic-point attainment
and slope-minimality exported, plus the NEW uniqueness theorem `minFaceAt_unique`:
lowest terms of THE minimum slope), and a canonical class residual polynomial
(`classResidualPoly`, lift-independent by WFR §3's `resPoly_monicPoly_eq`, consumed
verbatim).  The trichotomy on its factorization pattern — IRREDUCIBLE (leaf) / a
PROPER power of one irreducible (the fractional-recentring step's territory) /
neither (coprime-reducible, the smaller-mass convolution's territory) — is an exact
disjoint partition, uniform in `q, m, σ, K`, every complete DVR, every uniformizer.
The front fires through IFCG33's bridge with IFCG32's discharged block bridges — the
unramified types and the bridge family are GONE from the premise list.

## ★★ THE LEAF LAWS — the residual-irreducible leaf at `(e', d)`, `d = 1` CLOSED

    def ResidualLeafLaw (e' d) : Prop     -- pure block, side residual irreducible deg d
                                          --   ⟹ typeOf = ⟨{(e', d)}⟩
    theorem residualLeafLaw_one   : 0 < e' → ResidualLeafLaw e' 1        -- UNCONDITIONAL
    theorem residualLeafLaw_of_supply : ResidualInertiaSupply → ResidualLeafLaw e' d
    def ResidualInertiaSupply : Prop      -- THE ONE OPEN LEAF LEG (B-BOX-1 at φ = X):
      -- irreducible side residual ⟹ its degree ∣ inertiaDegOf of EVERY monic factor

Mechanism: B.61 (`typeOf_leaf_of_resDeg_lower_bound`) at the key `X`; at `d = 1` the
box hypothesis is trivial (`1 ∣ _`), so the whole `d = 1` leaf family is Lean-core and
premise-free — CN2's Eisenstein genre at the BLOCK level, any face position.  The one
named open supply is B.63's perimeter clause specialized to the x-frame — the
classical "the residual field 𝔽_q(ψ) embeds into each factor's residue extension".
**Discharge pointer: IFCG32's §0–§5 norm-transport machinery (mapAdjoin, norm_mk_mul,
addVal transport) is built for exactly this genre** — the supply is the natural next
consumer of the InertiaScaling toolkit.

## ★ THE SPANNING DECISIONS — CN2 recovered through the leaf engine

    theorem decidedAt_of_spanning_leaf : ResidualLeafLaw e' d →
      (stratum class, face h/e' attained at 0 AND m, m = e'·d, coprime, visible,
       class residual IRREDUCIBLE) → DecidedAt O m ⟨{(e', d)}⟩ K c
    theorem decidedAt_of_spanning_eisenstein :   -- the d = 1 instance, NO leaf premise
      (stratum, face h/m spanning, coprime, visible) → DecidedAt O m ⟨{(m, 1)}⟩ K c

Both LEAN-CORE.  The Eisenstein corollary is IFCG23's `decidedAt_of_eisenstein_face`
restricted to the census stratum, re-derived independently through B.58/B.61 + the
class-residual transport — the degree-1 residual is automatically irreducible (its
nonzero constant term and `natDegree = sideDeg = 1` come free from B.30).  This is the
promised firing: the deg-R = 1 leaves are closed, and the general-`d` spanning leaf is
conditional on exactly `ResidualLeafLaw e' d`.

## ★ THE SUPPORTING ENGINES (all Lean-core, all consumable by the discharge units)

* `classResidualPoly_eq` — the transport: the canonical residual IS every lift's side
  residual below the frame floor (WFR §3 consumed; so hypotheses about the class
  residual propagate to every lift).
* `classResidualPoly_natDegree_pos` — THE HONESTY LEMMA: on the minimal face the
  residual has `natDegree = sideDeg ≥ 1` and `coeff 0 ≠ 0` (coprimality forces
  `e' ∣ sideMax − sideMin` with `sideMax = m > sideMin`).  Consequence (compose with
  §2c): EVERY split-sector class residual genuinely admits a coprime monic
  nonconstant factorization — XHS's `wideFace_refinement_of_stratum` input shape.
* `exists_coprime_split_of_not_primary` (§2c, any field): nonconstant ∧ ¬irreducible ∧
  ¬proper-prime-power ⟹ `Associated R (G·H)`, `G, H` monic coprime nonconstant.
  (IFCG17 §5's primary decomposition consumed.)
* `sectorLaws_unramified` — nonvacuity: at every mass and every unramified σ all three
  sectors are EMPTY (UZL's forcing), so all three laws fire with value 0.

## THE EXACT SURVIVING OPEN SET (the recursion record — the census endgame's shape)

`∀ n, DecidedSliceAt n` now rests on precisely:

1. **`SplitSectorLaw e σ`** at `e ≥ 5`, σ ramified, under the `< e` decided value laws
   — the CONVOLUTION step: XHS §4 refines every split-sector lift along the coprime
   residual factorization (§2c + the honesty lemma supply it CLASS-level) into blocks
   of strictly smaller mass; the counting glue is the polygon-block analogue of
   IFCG17's `stratDecCount_mul`.  This is where the descent to smaller masses lives.
2. **`PowerSectorLaw e σ`** (same supply) — the FRACTIONAL RECENTRING step: residual
   `unit·ψ^k`, `k ≥ 2` ⟹ recenter at the face (IFCG20's copy machinery at fractional
   centres; C136's tower machinery was built for repeated refinement); the residual
   mass strictly drops (`new mass = k ≤ (block deg)/(2·deg ψ)`).
3. **`LeafSectorLaw e σ`** (same supply) — the leaf census: the block decisions are
   CLOSED here (`ResidualLeafLaw`, `d = 1` outright, `d ≥ 2` from the supply); what
   remains is the count of leaf cells (block type × the sub-face rest of the class).
4. **`ResidualInertiaSupply`** — the ONE leaf-decision leg (`d ≥ 2` only); IFCG32's
   norm machinery is the discharge route.
5. **The five `e = 4` even-ramification `ConeRemainderLaw`s** — ER4's unit, untouched.

Honest scoping: the sector laws are COUNT-level Props (the trichotomy's three arms).
The charge's "leaf decisions + recentring step" survive INSIDE arms 2–3 as their
discharge mechanisms; what this unit made machine-checked is that the three arms are
EXHAUSTIVE and EXCLUSIVE (so `ConeRemainderLaw m σ ⟸ the three laws` is exact, not an
approximation), that the leaf-decision content reduces to ONE uniform supply Prop, and
that the front consumes the arms in the recursion's own descent shape (each mass's
laws receive the `< e` value laws).  Nothing weakened; the two B.42-marked lines
inherit the cite through landed bridges only.

## File map (`leanfinal/Uniformity/ChapI/IFCG35.lean`, 1046 lines)

§0 supply (`isKey_X` private, `mem_sideSet_iff'` private = B83Kit's idiom) ·
§1 `ResidualInertiaSupply`, `ResidualLeafLaw`, ★ `residualLeafLaw_one`,
★ `residualLeafLaw_of_supply` · §2 `MinFaceAt`, `minFaceAt_support`, `minFaceAt_min`,
`minFaceAt_attained_lt`, ★ `exists_minFaceAt_of_shallow`, ★ `minFaceAt_unique`,
`classResidualPoly`, ★ `classResidualPoly_eq`, ★ `classResidualPoly_natDegree_pos` ·
§2c `exists_coprime_split_of_not_primary` · §3 `remainderCarrier` (+ `rfl` count tie),
`leafSector`/`powerSector`/`splitSector` (+ counts), ★★ `remainderCarrier_eq_sectors`,
`sectors_disjoint`, ★★ `coneRemainderCount_eq_sector_sum` · §4 the three law defs,
★★ `coneRemainderLaw_of_sectorLaws`, ★ `sectorLaws_unramified` ·
§5 ★ `decidedAt_of_spanning_leaf`, ★ `decidedAt_of_spanning_eisenstein` ·
§6 `coneRemainderLaw_ram5_of_sectorLaws`, ★★★ `decidedSliceAt_all_of_sectorLaws` ·
AxCheck footer (14 lines).  Imports beyond the consumers' baseline: `ChapB.B30/B58/B61`
(the leaf engines), `ChapI.IFCG17` (primary decomposition), `ChapI.IFCG28` (WFR §3),
`ChapI.IFCG32` (the discharged bridges), `ChapI.IFCG33` (the front + forcing).

## Design decisions (recorded)

* The sectors are defined through the CANONICAL residual `classResidualPoly π c h e'`
  (choice-based on a fixed lift) at the UNIQUE minimal face — so the partition is
  pure logic (excluded middle on one polynomial's pattern) + existence + uniqueness;
  NO π-independence is needed (ZcURLim families take π as an argument, so π-dependent
  sector counts are legal law carriers).
* `MinFaceAt` needs no separate minimality field: slope-minimality is DERIVED from the
  monic-point attainment (`support = h·m` + `classNPSupport_le_apply`).
* The `d = 1` leaf is proved via B.61-with-trivial-box rather than B.58 — one engine,
  two instances; B.58 remains unconsumed.
* No dead named Prop: every Prop defined here is consumed by a landed theorem in this
  file (the supply by `residualLeafLaw_of_supply`, the leaf law by the spanning
  decision, the sector laws by the assembly + front + unramified instances).

## Repair log (3 error rounds, all mechanical; every theorem landed as designed)

1. Prop-telescope intro arity: `ResidualLeafLaw` has FIVE instance binders after `O`
   — `intro O _ _ _ _ π` grabbed `Finite` as "π" (Application type mismatch at sort
   `Prop`/`Type`); five underscores.
2. `Irreducible.not_unit` does not exist at the pin — the field accessor is
   `Irreducible.not_isUnit`.
3. `sideMin`/`sideMax` are DEFS wrapping `Finset.min'/max'` — omega sees the def and
   the min'/max' as DIFFERENT atoms; `unfold sideMin sideMax` before citing
   `Finset.min'_le`/`le_max'` (then `Nat.le_zero.mp` beats omega on `min' ≤ 0 ⟹ = 0`).

Traps AVOIDED by design (UZL/WFR/XHS/CCA/CN4/CN5 logs consulted): all variable
products kept out of omega (add-cancel chains: `A + B = C` ∧ `D + B = C` ⟹
`Nat.add_right_cancel`; `Nat.mul_le_mul (le_refl b) h` + `ring`-normalized calc for
the cross-slope cancellation); the `WithTop.ne_top_iff_exists` coercion re-typed by
the defeq `have hw' : ((w : ℕ) : ℕ∞) = _ := hw` idiom before ANY cast rewriting; the
ℕ∞ extraction by the recorded `nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add,
Nat.cast_inj` chain; the Classical `sideSet` filter entered only through the B83Kit
defeq-coercion idiom (private copy), never raw `Finset.mem_filter` against the def.
