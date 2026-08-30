# UNIT DBL — VERDICT: THE DIGIT-COUNT INSTRUMENT LANDED, BOTH DEPTH-0 BOX LIMITS CLOSED (LEAN-CORE!), THE MASS-4 LAWS REWIRED (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG36.lean` (1083 lines, ZERO sorries,
ZERO errors, ZERO warnings; 23 AxCheck footer lines).  ER4's two named depth-0
box-limit premises — `ZcURLim e1SplitFam` and `ZcURLim e1IrrFam` — are **CLOSED,
UNCONDITIONALLY, on Lean core alone** (`{propext, Classical.choice, Quot.sound}`; the
B.42 cite never enters the counting layer).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG36.lean` (final: zero diagnostics
beyond the 23 expected axiom prints), targeted `lake build Uniformity.ChapI.IFCG36`
(8942 jobs, success), aggregator `lake env lean Uniformity/ChapI.lean` (exit 0; one
sanctioned import line appended after IFCG35's, which was observed present and
untouched).  No landed file touched; IFCG35.lean untouched; no git ops.

## The architecture that landed (all sections green)

**§1 THE INSTRUMENT (Lean-core):** `resDig π v x` — the `v`-th π-digit of a truncated
class `x : Res O K`, defined as B.21's scalar digit `digAt` read on the canonical
representative `resOut x`.  The kit: `resDig_mk` (class data for `v < K`; via a replay
of IFCG28's private `digAt_congr`), ★ `card_setOf_resDig` (the missing per-coordinate
count `#{x | v ≤ resOrd x ∧ resDig π v x = d} = q^(K−v−1)` — proved by exhibiting the
level set as a TRANSLATE of the `{v+1 ≤ resOrd}` upper set), and `resOrd_eq_iff_resDig`
(exactness = reachability + nonzero digit).  This is the CN4-genre extension ER4 asked
for ("the one missing instrument"), reusable verbatim for the E2 depth-0 unit.

**§2 the coefficient iso (Lean-core):** `resFieldEquivX : ResidueField O ≃+*
resField X` (the x-frame residual field IS the residue field; surjectivity via
`root (X̄) = 0` + `eval₂_at_zero`), with the two genre transports
(`irreducible_iota_quad_iff` through `Polynomial.mapEquiv` + `MulEquiv.irreducible_iff`;
`sq_iota_quad_iff` by mapping the monic linear square along the iso both ways).

**§3 ★★ THE BRIDGE `e1_resPoly_eq` (Lean-core):** for EVERY lift of an `e1Box` class,
the slope-1/2 residual quadratic is `Y² + ι(δ₁(c₂))·Y + ι(δ₂(c₀))` — the coefficients
are the two class digits.  Proof: purity replay (trimmed IFCG34 bank) + B.35c's
`resPoly_coeff_of_pure` + B.15's `dev_X` + B.24's `digPoly_coeff`; leading coefficient
by `dev_top` + `resMk_one`; above-degree coefficients vanish.  Because the statement
quantifies over ALL lifts, genre membership needs no separate congr step.

**§4 the field-side genre counts (Lean-core):** `irrPairs` ↔ IFCG19's
`IrredOfDeg F 2` (an explicit `Equiv` via monic-quadratic reconstruction
`monic_quadratic_eq_coeffs`); `card_ddPairs = q − 1` (the 1:1 parametrization
`t ↦ (2t, t²)`, `t ≠ 0`; injectivity char-free via `(t−s)² = 0` by
`linear_combination`); `irrPairs_snd_ne_zero` (irreducible ⇒ nonzero constant term).
BONUS closed necklace: `necklacePoly_two_eval` (`2·N₂(x) = x² − x`; the
`divisorsAntidiagonal 2` computed by `decide`) and `two_mul_card_irredOfDeg_two`
(`2N₂ = q² − q` in ℕ).

**§5 the fibers and the three genre counts (Lean-core):**
- `e1Fiber π K β α` (both residual digits pinned — a product box) with
  ★ `card_e1Fiber = q^(4K−8)` (card_pi_set + §1's digit count; q^{K−3}·q^{K−2}·q^{K−2}·q^{K−1});
- `mem_e1Box_iff_fiber` (the fibers with α ≠ 0 tile the E1 cell);
- `mem_e1IrrBox_iff_pairs` / `mem_e1DdBox_iff_pairs` (genre box = e1Box ∧ digit pair in
  the field-side genre set — through the bridge + the iso transports);
- the shared engine `card_genre_box` (fiberwise partition over the digit-pair map,
  IFCG24's private sum-helper replayed), giving
  ★★ `card_e1IrrBox_necklace` : `#e1IrrBox = N₂(q)·q^(4K−8)`,
  ★★ `card_e1DdBox` : `#e1DdBox = (q−1)·q^(4K−8)`,
  ★ `card_e1Box_partition` : `#e1Box = #split + #irr + #dd` (exact, every K ≥ 3);
- ★ THE CLOSED FORMS (ER4's verdict targets, DERIVED not assumed):
  `card_e1SplitBox_closed` : `2·#e1SplitBox = (q−1)(q−2)·q^(4K−8)` (ℤ-cast
  linear_combination through the partition + 2N₂ = q²−q) and `card_e1IrrBox_closed` :
  `2·#e1IrrBox = (q²−q)·q^(4K−8)`.  Sanity (machine-checked, not narrated): the
  partition against `card_e1Box = (q−1)q^(4K−7)` forces split+irr+dd = (q−1)q per
  q^(4K−8) — the charge's normalization question resolves to split = (q−1)(q−2)/2
  (distinct NONZERO roots: C(q−1,2)), irr = (q²−q)/2, dd = q−1.

**§6 ★★ THE TWO LIMITS (charge item 2) — both Lean-core:**
- `zcURLim_e1IrrFam` : witness `(necklacePoly 2, X⁸)` — the family is EXACTLY constant
  `N₂(q)/q⁸` at every level (no error term at all: the count is exact for all K ≥ 3),
  so the Tendsto is `tendsto_const_nhds`.
- `zcURLim_e1SplitFam` : witness `((X−1)X − necklacePoly 2 − (X−1), X⁸)` — constant
  `(q−1)(q−2)/(2q⁸)`, derived through the partition (ℝ-cast, exponent-generalized to
  dodge nested `4(M+4)` rewrites).
- The `∀ σ` decided families discharge: `zcURLim_e1SplitDecFam σ` (UNCONDITIONAL — the
  split box is `{(2,1),(2,1)}`-decided, so σ = ramPair gets the full box and every
  other σ the empty set; Lean core + B.42) and `zcURLim_e1IrrDecFam hL σ` (under the
  named leaf: full box at type22, empty at type41 and elsewhere; LEAN-CORE — ER4's
  irr-sector decision machinery never consumed B.42).

**§7 ★★ the rewired laws + ★★★ the front (charge item 3; Lean core + exactly B.42):**
- `coneRemainderLaw_four_ramPair` : `{(2,1),(2,1)}` now from TWO premises (dd + E2
  recursion terms) — the split-box premise GONE.
- `coneRemainderLaw_four_type22` : `{(2,2)}` now from the leaf + ONE premise (dd) —
  the irr-box premise GONE.
- `decidedSliceAt_all_of_recursion_limits` : the all-degree decided slice from
  EXACTLY (a) `E1IrrLeafDecision`, (b) `∀σ ZcURLim (e1DdDecFam σ)`,
  (c) `∀σ ZcURLim (e2DecFam σ)`, (d) the `e ≥ 5` laws, (e) the block bridges.

## THE EXACT SURVIVING OPEN SET after DBL (the fence, updated from ER4's §5)

ER4's items 1–5 shrink to:
1. **`E1IrrLeafDecision`** (the `B-BOX-1` instance at ℓ = 2, deg ψ = 2) — unchanged.
2. ~~the two depth-0 box limits~~ **CLOSED (this unit, Lean-core).**
3. **`ZcURLim (e1DdDecFam σ)`**, σ ∈ {ramPair, type22, type41} — the order-2 wild
   recursion (unchanged; `{(4,1)}`'s law remains PURELY this term).
4. **`ZcURLim (e2DecFam σ)`**, σ ∈ {ramPair, splitTail, inertTail} — the E2
   mixed-system recursion (unchanged; ER4's §4 genre notes still apply; §1's digit
   instrument is the ready-made counting tool for its depth-0 genres).
5. `e ≥ 5` ramified laws + `UnramifiedBlockBridge` — unchanged.

## Axiom ledger (23 footer lines, verified by script over the full dump)

19 theorems LEAN-CORE ONLY — the whole instrument, the bridge, the iso, ALL counts,
ALL closed forms, BOTH box limits, and `zcURLim_e1IrrDecFam`.  Exactly 4 carry Lean
core + `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, owner-signed,
inherited through IFCG34's decided-set lemmas): `zcURLim_e1SplitDecFam`,
`coneRemainderLaw_four_ramPair`, `coneRemainderLaw_four_type22`,
`decidedSliceAt_all_of_recursion_limits`.  C.33 cites: ZERO occurrences (grep over the
full dump).  No new axioms, no statement changes to landed material.

## Repair log (5 error rounds over 9 compile passes; every theorem landed as designed)

1. `ConeRemainderLaw` missing from the IFCG24 open list (skeleton pass).
2. Bridge k = 0: the `1*0`/`2*0` indices pre-reduce during elaboration — drop the
   `Nat.mul_zero` rewrites, keep `Nat.sub_zero`; k ≥ 3: `Polynomial.coeff_X` emits the
   FLIPPED if-condition `1 = k+1+1+1`.
3. `Monic.natDegree_map` needs `Nontrivial (resField X)` — `letI := instFieldResField
   isKey_X` in `sq_iota_quad_iff`.
4. `rintro rfl` cannot subst `L.coeff 0 = 0` (not a variable) — explicit rewrite.
5. `field_simp` fully closes both limit endgames — trailing `ring` dies with "No goals"
   (twice).  Plus lint polish: two `omit [Finite (ResidueField O)] in` (placed BEFORE
   docstrings — after them is a parse error) and per-site simp-list trims to zero
   warnings.

Traps AVOIDED by design (ER4/CCA logs consulted): all if-branch membership proofs via
IFCG31's `by_cases (i:ℕ) = k` + `Fin.ext` pattern (never `fin_cases`);
`sideSet_nonempty_gen` always the closed term; digit-vs-lift transport routed as
`rw [← congrFun ha i]; exact resDig_mk …` (defeq at `exact`, never a syntactic `proj`
rewrite); the exponent generalization `∃ E, 4K−8 = E ∧ …` before any `pow` rewriting
(nested-occurrence clobber); ℕ-subtraction closed forms proved in ℤ by
`linear_combination` (no omega-with-nonlinear-atoms attempts).

## File map (`leanfinal/Uniformity/ChapI/IFCG36.lean`, 1083 lines)

§1 `resDig`, `digAt_congr` (private replay), `resDig_mk`, ★ `card_setOf_resDig`,
`resOrd_eq_iff_resDig` · §2 `isKey_X` (private replay), `resIota`, `resMk_C` (private),
`resIota_bijective`, `resFieldEquivX` (+ `_apply`, `_symm_iota`), `iota_quad_eq_map`
(private), `irreducible_iota_quad_iff`, `sq_iota_quad_iff` · §3 `e1_pure` (private
replay), ★★ `e1_resPoly_eq` · §4 `irrPairs`, `ddPairs`, `quad_coeff_one/zero`,
`quad_natDegree`, `quad_monic` (private), `monic_quadratic_eq_coeffs`,
`irrPairs_snd_ne_zero`, `card_irrPairs`, `sq_X_add_C` (private), `card_ddPairs`;
`necklacePoly_two_eval`, `two_mul_card_irredOfDeg_two` · §5 `e1Fiber`,
`mem_e1Fiber_iff`, ★ `card_e1Fiber`, `mem_e1Box_iff_fiber`; `natCard_set_eq_card_filter`
+ `natCard_eq_sum_fiber` (private replays), `mem_e1IrrBox_iff_pairs`,
`mem_e1DdBox_iff_pairs`, `card_genre_box` (private), ★★ `card_e1IrrBox_necklace`,
★★ `card_e1DdBox`, ★ `card_e1Box_partition`, ★ `card_e1IrrBox_closed`,
★ `card_e1SplitBox_closed` · §6 ★★ `zcURLim_e1IrrFam`, ★★ `zcURLim_e1SplitFam`,
`zcURLim_e1SplitDecFam`, `zcURLim_e1IrrDecFam` · §7 ★★ `coneRemainderLaw_four_ramPair`,
★★ `coneRemainderLaw_four_type22`, ★★★ `decidedSliceAt_all_of_recursion_limits` ·
AxCheck footer (23 lines).
Imports: Mathlib, IFCG34, IFCG19, IFC7.  Aggregator: one import line appended to
`Uniformity/ChapI.lean` (after IFCG35's).
