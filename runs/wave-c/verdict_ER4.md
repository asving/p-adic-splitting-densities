# UNIT ER4 — VERDICT: THE FIVE EVEN-RAMIFICATION e = 4 TYPES — THE RESIDUAL DICHOTOMY LANDED, THE FIVE LAWS REDUCED TO EXACTLY NAMED SECTOR LIMITS, THE `(4,1)` PARITY-EMPTINESS GUESS REFUTED (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG34.lean` (1577 lines, ZERO sorries,
ZERO errors, ZERO warnings; 28 AxCheck footer lines — Lean core
`{propext, Classical.choice, Quot.sound}` on §1 (sector split + counts), §3 (the
trichotomy, the genre partition, all disjointness), AND — the headline surprise — on
the ENTIRE §4 exclusion suite INCLUDING `typeOf_e1_irr_mem` (B.57/B.35c/B.54 are all
Lean-core); Lean core PLUS EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) on the decision/E2/count/law
sections and the census wire; the C.33 cites do NOT occur — verified by grep over the
full axiom dump; no landed file touched except the sanctioned one-line aggregator
import in `Uniformity/ChapI.lean` (placed after IFCG33; IFCG32's line, another unit's,
observed already present and untouched); IFCG32.lean untouched; no git ops).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG34.lean`
(final: zero diagnostics beyond the 28 expected axiom prints), targeted
`lake build Uniformity.ChapI.IFCG34`, aggregator `lake env lean Uniformity/ChapI.lean`,
PLUS the PARI/GP cross-check of the `(4,1)`-at-`p=3` witness.

## The architecture that landed (ALL sections green)

**§1 the sector split (Lean-core, VERIFIED green + Lean-core axioms):**
`forcedBox = e1Box ⊔ e2Box` — E1 = `{v₀ = 2 exact, v₁ ≥ 2, v₂, v₃ ≥ 1}` (the `[0,4]`
slope-1/2 face spans the quartic; every lift `(1,2)`-pure), E2 = `{v₀ ≥ 3, v₁ ≥ 2,
v₂ = 1, v₃ ≥ 1}` (the `[2,4]` width-2 face).  Counts: `card e1Box = (q−1)q^(4K−7)`,
`card e2Box = (q−1)q^(4K−8)`.

**§2 the E1 lift bank (green):** purity, support `4`, left height `2` at the side
minimum, reduction `X⁴`, the residual read is a MONIC quadratic with nonzero constant
term (B.48's monicity recipe replayed), and the residual is a CLASS INVARIANT
(IFCG28's `resPoly_monicPoly_eq` at the pinned height `2`).

**§3 the residual dichotomy (green):** `monic_quadratic_trichotomy` (any monic
quadratic over a field: coprime-split ∨ irreducible ∨ monic-linear square) +
exclusivity legs; the three genre boxes `e1SplitBox/e1IrrBox/e1DdBox` (π-parametrized,
∃-lift form, class-invariant by §2); `e1Box = split ⊔ irr ⊔ dd` with pairwise
disjointness.

**§4 the E1 decisions (green):**
- `decidedAt_e1_split` — the split sector is DECIDED `{(2,1),(2,1)}` (IFCG31 §3b's leaf
  fired on the whole sub-box).
- ★★ `typeOf_e1_irr_mem` — THE PIN: every lift of an irreducible-residual class is an
  IRREDUCIBLE quartic of type `{(2,2)}` OR `{(4,1)}`.  Mechanism: a proper monic factor
  must have degree 2 (evenness by IFCG23's `dvd_ramIndexOf_of_isPure` + purity), B.57
  makes both factors `(1,2)`-pure with linear side-residuals, B.35c's
  `resPoly_mul_of_pure` then SPLITS the irreducible residual — contradiction; B.54
  (`inertiaDegOf_dvd_key_mul_resDeg`) bounds `f ∣ 2`, and `e·f = 4` leaves `(2,2)`,
  `(4,1)`.
- `not_decidedAt_e1_of_odd_member` — on the pure E1 cell EVERY factor of EVERY lift has
  even `e`, so ANY type with even one odd-`e` member is refuted (sharper than IFCG31
  §3's all-odd exclusion; kills both tail types on E1).
- `E1IrrLeafDecision` — THE NAMED OPEN LEAF: the `{(2,2)}` decision of the irreducible
  sector = the `ℓ = 2, deg ψ = 2` instance of the chapter's standing `B-BOX-1`
  perimeter (recorded OPEN-MATH since B.60/B.61).  `e1IrrLeafDecision_of_no41`: by the
  pin it is EXACTLY the `{(4,1)}`-exclusion on the irreducible sector (the missing
  math: residue of `β²/π` is a root of the irreducible residual ⇒ `2 ∣ f` — the graded
  B.52 analogue, norm-peel work of Chapter-B scale).
**§5 the E2 block structure (green):** `exists_ramQuad_factor_of_e2` — every lift
splits as (2,1)-quadratic × monic quadratic (the `[2,4]` block via IFCG26's Hensel
heart; the whole-quartic-pure alternative is killed by `v₀ ≥ 3` against the `OnSide`
equation at 0, via IFCG23's `le_npHgt_monicPoly`); hence NO singleton type (`{(2,2)}`,
`{(4,1)}`) ever decides on E2.

**§6 the dichotomy count (green):**
`coneRemainderCount_four_forced_partition` — for EVERY non-mixed σ, at every level:
count = split-sector + irr-sector + dd-sector + E2-sector (exact Nat.card identity).
Specializations: ramPair = FULL split box + dd + E2; type22 = irr-decided + dd (E2 and
split empty); type41 = irr-decided + dd; odd-member types (both tails) = E2 only
(π-free); under the named leaf: type22's irr term = FULL irr box, type41's VANISHES.

**§7 the conditional laws (green):** `ZcURLim` sector families
(`e1SplitFam`, `e1IrrFam`, `e1SplitDecFam σ`, `e1IrrDecFam σ`, `e1DdDecFam σ`,
`e2DecFam σ`) + the general law `coneRemainderLaw_four_of_sectors` (four premises) and
the sharp per-type laws: ramPair (3 premises), type22 (leaf + 2), type41 (leaf + 1 —
the wild law is PURELY the order-2 recursion term), tails (1 premise each).

**§8 the wire (green):** `decidedSliceAt_all_of_sector_limits` — the all-degree
decided slice from: the four ∀-σ sector-limit families + `e ≥ 5` ramified laws +
bridges, THROUGH IFCG33's `decidedSliceAt_all_of_ram5_even4_bridge` (the even-member σ
is non-mixed since `mixedType4` is all-odd — no five-type enumeration needed).

## ★★★ RECORD CORRECTIONS (both load-bearing for the successor)

1. **`(4,1)` is NOT parity-empty at odd q** — the charge's guess ("at odd q the (4,1)
   sector may be provably empty") is REFUTED by construction: `β = √3·(1 + 3^{1/4})`
   has minimal polynomial `X⁴ − 6X² − 36X − 18` over ℚ₃, irreducible with `e = 4,
   f = 1` (PARI `factorpadic` + `idealprimedec` confirm: one prime, e=4, f=1), and its
   class lies in `e1DdBox` (`v₀ = 2, v₁ = 2, v₂ = 1`; residual `Y² + Y + 1 ≡ (Y−1)²`
   mod 3).  CCA's battery observation "(4,1) only at p = 2" was a 240-sample artifact.
   The `{(4,1)}` law is recursion-only at EVERY residue characteristic.
2. **The E1 double-root recursion is ORDER-2 Montes** — the recentring key is the
   degree-2 `X² − bπ`, NOT a linear recentring: IFCG20's recentred-copy machinery does
   NOT reach it.  `e1DdDecFam` is genuinely the deep-wild OM tower's first appearance
   in the census (consistent with PROJECT_STATE's standing obligation 2).

## THE EXACT SURVIVING OPEN SET after ER4 (the fence)

`ConeRemainderLaw 4` at the five even-ram types now rests on precisely:
1. **`E1IrrLeafDecision`** (named Prop, the `B-BOX-1` instance at `ℓ = 2, deg ψ = 2`) —
   equivalently the `{(4,1)}`-exclusion on irreducible residuals.
2. **`ZcURLim e1SplitFam` / `ZcURLim e1IrrFam`** — the DEPTH-0 box limits.  These are
   CLOSED-FORM targets: with digit-level counting (not yet in the corpus — CN4's
   toolkit is resOrd-only), `card e1SplitBox = ((q−1)(q−2)/2)·q^(4K−8)`,
   `card e1IrrBox = (q(q−1)/2)·q^(4K−8)` (necklace `N₂(q)` — IFCG19's
   `necklacePoly_eval_card` supplies the field count), `card e1DdBox = (q−1)·q^(4K−8)`;
   sanity: sum = `(q−1)q·q^(4K−8) = card e1Box` ✓.  The one missing instrument is a
   per-coordinate DIGIT count lemma (`card {x : Res O K | resOrd x = v ∧ digit_v x = d}`)
   plus a two-coordinate relation count — a CN4-style unit.
3. **`ZcURLim (e1DdDecFam σ)`** for σ ∈ {ramPair, type22, type41} — the order-2
   recursion resummation (the wild tower).
4. **`ZcURLim (e2DecFam σ)`** for σ ∈ {ramPair, splitTail, inertTail} — the E2
   mixed-system recursion: its own depth-0 genres are (a) v₀ even, `2v₁ ≥ v₀+2`:
   fractional `[0,2]` face ⇒ decided `{(2,1),(2,1)}`; (b) `2v₁ < v₀+1`: two integral
   width-1 faces ⇒ decided `{(1,1),(1,1),(2,1)}`; (c) v₀ odd, `2v₁ ≥ v₀+1`: integral
   slope `(v₀−1)/2` width-2 face ⇒ the SAME residual trichotomy one level down (split →
   `{(1,1),(1,1),(2,1)}`, irreducible → `{(1,2),(2,1)}` — an ℓ=1 leaf, B.59b/B.60
   territory, UNCONDITIONAL unlike ℓ=2! — double root → linear recentring, which IS
   IFCG20-shaped); plus the invisible-corner sub-cells.  E2's depth-0 closure is a
   natural next unit (no B-BOX obstruction).
5. `ConeRemainderLaw e σ` at `e ≥ 5` ramified + `UnramifiedBlockBridge` — unchanged.

## Verification

- Per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG34.lean`: increments
  1 (§0–1), 2 (§2), 3+4 (§3–4), 5 (§5) GREEN with only pin-rename repairs (see log).
- PARI/GP cross-check of the `(4,1)` witness at p = 3 (factorpadic + idealprimedec).
- AxCheck footer: 28 lines; expectations — §1/§3 Lean core; decision/count/law sections
  Lean core + exactly B.42 (`exists_slope_factorization`), inherited through
  IFCG26/30/31.  C.33 must not occur.

## Repair log (6 error rounds over 8 compile passes; every theorem landed as designed)

1. `mem_e1Box_iff`/`mem_e2Box_iff` reverse directions: `fin_cases i` leaves coerced
   `(fun i => i) ⟨1,⋯⟩` if-conditions — replaced by IFCG31's `by_cases (i:ℕ) = k` +
   `Fin.ext` pattern (the CCA trap list's fin_cases warning, re-confirmed).
2. `isUnit_of_mul_eq_one` not at the pin → `IsCoprime.isUnit_of_dvd dvd_rfl` (simpler).
3. `dvd_ramIndexOf_of_isPure` lives in IFCG23 (not IFCG26 — the open list was wrong);
   B.54's residual hypothesis wants `(X.map (residue O))^…` — add `Polynomial.map_X`.
4. `Multiset.not_mem_zero` → `Multiset.notMem_zero` at this pin.
5. UNIVERSE FENCE: `E1IrrLeafDecision` quantifies `O : Type` (Type 0, `ZcURLim`'s
   convention) — its four consumers moved to a `{O : Type}` section (`Type*` sections
   cannot apply it).  NOTE FOR SUCCESSORS: every named-Prop consumer must match the
   Prop's universe.
6. `simpa using hp` cannot see through `mixedType4.data` (a def) — defeq-coerce first
   (`have hp' : p ∈ ({(1,1),(3,1)} : Multiset _) := hp`).

Traps AVOIDED by design (CCA/UZL/XHS logs consulted): all `sideSet`-nonemptiness passed
as the CLOSED term `sideSet_nonempty_gen X f 1 2` everywhere (never an fvar — keeps
`rw` patterns syntactic across B.35c/B.30 applications); heights extracted via the
XHS `have hw' : ((w:ℕ):ℕ∞) = _ := hw` defeq-coercion idiom before any cast rewriting,
then `subst`-ed to literals BEFORE `resPoly_mul_of_pure` (so its `H₀f + H₀g` lands as
`1 + 1`, rfl-convertible to `2`); the dependent rewrite `rw [hprod] at hirr` is sound
because the embedded nonemptiness proof term is generic in `f`; the ℕ∞ `OnSide`
extraction by the XHS `nsmul_eq_mul, ← Nat.cast_*, Nat.cast_inj` chain; `Monic.eq_X_add_C`
destructured through ∃-obtain (never rewritten in place — the XHS self-rewrite trap);
type inequalities via `ne_of_data_ne (by decide)` (no `DecidableEq FactorizationType`
assumption).

## File map (`leanfinal/Uniformity/ChapI/IFCG34.lean`, 1577 lines)

§0 `type22`, `type41`, `splitTailType`, `inertTailType` · §1 `e1Box`, `e2Box`,
`mem_e1Box_iff`, `mem_e2Box_iff`, ★ `forcedBox_eq_union`, `disjoint_e1Box_e2Box`,
`card_e1Box`, `card_e2Box` · §2 `isKey_X` (private), `e1_class_bank`, `e1_lift_bank`,
`e1_resPoly_spec`, `e1_resPoly_congr` (all private) · §3 ★ `monic_quadratic_trichotomy`,
`not_irreducible_mul_linear`, `mul_ne_sq_of_coprime_linear`, `e1SplitBox`, `e1IrrBox`,
`e1DdBox`, ★ `e1Box_eq_genres`, `disjoint_e1SplitBox_e1IrrBox`,
`disjoint_e1SplitBox_e1DdBox`, `disjoint_e1IrrBox_e1DdBox` · §4 ★ `decidedAt_e1_split`,
★★ `typeOf_e1_irr_mem` (LEAN-CORE), `not_decidedAt_e1_irr`,
★ `not_decidedAt_e1_of_odd_member` · §4b `E1IrrLeafDecision` (THE named open),
`e1IrrLeafDecision_of_no41` · §5 `e2_class_bank` (private),
★ `exists_ramQuad_factor_of_e2`, `not_decidedAt_e2_of_singleton` · §6 `ne_of_data_ne`
(private), `count_forced`, ★★★ `coneRemainderCount_four_forced_partition`,
`decided_inter_e1Split_eq_self/_eq_empty`, `decided_inter_e1Irr_eq_empty`,
`decided_inter_e1_eq_empty_of_odd`, `decided_inter_e2_eq_empty_of_singleton`,
★★ `coneRemainderCount_four_ramPair/_type22/_type41/_of_odd_member` · §6b (`O : Type`)
`decided_inter_e1Irr_of_leaf`, `decided41_inter_e1Irr_of_leaf`,
★ `coneRemainderCount_four_type22_of_leaf/_type41_of_leaf` · §7 the six families
(`e1SplitFam`, `e1IrrFam`, `e1SplitDecFam`, `e1IrrDecFam`, `e1DdDecFam`, `e2DecFam`),
★★★ `coneRemainderLaw_four_of_sectors`, ★★ the four sharp laws
(`_ramPair_of_sectors`, `_type22_of_sectors`, `_type41_of_sectors`, `_of_odd_member`) ·
§8 ★★★ `decidedSliceAt_all_of_sector_limits` · AxCheck footer (28 lines).
Imports beyond IFCG31/33: `ChapB.B35c` (residual multiplicativity), `ChapB.B54`
(inertia/residual-degree), `ChapB.B57` (purity of factors).  Aggregator: one import
line in `Uniformity/ChapI.lean`.
