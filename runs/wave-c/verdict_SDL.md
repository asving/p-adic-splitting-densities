# UNIT SDL — VERDICT: THE POLYGON-BLOCK PRODUCT ENGINE MACHINE-CHECKED — the class-level Minkowski transfer lands (minimal faces concatenate and the class residual MULTIPLIES under `mulClass`), the sector CONVERSE of SSL's refinement map lands, the defect decomposes EXACTLY into collisions + strays, and `SplitConvolutionDefectLaw` fires outright at mass ≤ 1, under the `< m` value laws at mass ≤ 3, and is proved EQUIVALENT to `SplitSectorLaw` under those laws — while the charged "injective onto" premise is REFUTED and replaced by the correct fiber-exact target (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG40.lean` (1034 lines, ZERO sorries,
zero warnings, zero errors; 14 AxCheck footer lines — TWELVE are pure Lean core
`{propext, Classical.choice, Quot.sound}` (both §1 transfer theorems, both sector
converses, both cancellations, the double count, the mass-≤-3 emptiness, all four §3
law firings INCLUDING the equivalence), and exactly TWO carry Lean core PLUS the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42,
inherited only through SSL's `splitSector_refines_decided`): `one_le_multCount_of_vis`
and `convCount_eq_card_vis_add_defect`.  The C.33 cites do NOT occur.  No landed file
touched except the sanctioned one-line aggregator import in `Uniformity/ChapI.lean`
(appended after IFCG38's line; IFCG39 is another unit's and was not present); no git
ops.  Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG40.lean`
(final: only the 14 footprint infos), targeted `lake build Uniformity.ChapI.IFCG40`
green (8953 jobs), aggregator `lake env lean Uniformity/ChapI.lean` green (exit 0).

## THE TWO STRUCTURAL FINDINGS (read these before the theorem list)

1. **The corpus already held the polynomial-level Minkowski transfer.**  SSL's fence
   ("the general two-block case needs the full Minkowski sum at the minimal faces;
   IFCG30 §5's unit-corner transfer is the one landed piece of this genre") UNDERSOLD
   the corpus: **B.39a §7 — `resPoly_mul_gen`, `sideMin_mul_gen`, `sideDeg_mul_gen`,
   `npHgt_mul_gen`, `suppVal_mul_gen` — is the fully general, purity-free product law**
   (arbitrary monic factors, any key, supports/left-endpoints/residual-degrees add and
   the residual polynomial multiplies).  Charge 1's real gap was only the CLASS-level
   wiring, landed here as §1.
2. **The charged count-exactness premise is FALSE.**  The charge predicted "(decided
   cell₁, decided cell₂) → product cell is injective ONTO the visible split cells …
   injectivity from finite-precision uniqueness at DISTINCT SLOPES."  REFUTED: the
   two-sided pair map has fibers of size `q^{v(Res)}`, where `v(Res)` — the resultant
   valuation of the block pair — is `> 0` whenever BOTH blocks have all roots of
   positive valuation, i.e. everywhere inside the `X^m` stratum, same-slope AND
   distinct-slope alike.  Minimal witness: `(X−a)(X−b)`, `v(a) = v(b) = 1`, distinct
   residual digits; perturb `a' = a + ε, b' = b − ε`: the products differ by
   `ε(a−b) + ε²`, so `ε ~ π^{N−1}` is invisible mod `π^N` — the factor classes are
   determined only mod `π^{N−1}`.  Level-exactness holds ONLY against a residually
   coprime (unit-corner) cofactor — IFCG16 §6/XHS §3's genre, already landed — and in
   each argument SEPARATELY (this file's cancellations).  Consequently the defect is
   NOT zero at the visible-corner genre; the TRUE exact object is the fiber
   decomposition (§2), and the surviving open content of the defect law is the
   RATIONALITY OF THE MIXING-GRADED CENSUS: `convCount = Σ_c multCount c` where
   `multCount c` ladders in the cell's resultant depths (an Igusa-type generating
   structure — this is the honest name of the remaining difficulty, replacing the
   false "polygon-block stratDecCount_mul" bijection target RECUR predicted).

## ★ §1 — THE CLASS-LEVEL MINKOWSKI TRANSFER (charge 1: LANDED, Lean-core)

* ★ `minFaceAt_mulClass` — for classes `c₁ : Coeff O n₁ N`, `c₂ : Coeff O n₂ N` with
  the SAME minimal face `(h, e')` and `n₁ + n₂ ≤ N`:

      MinFaceAt (mulClass c₁ c₂) h e'
        ∧ classResidualPoly π (mulClass c₁ c₂) h e'
            = classResidualPoly π c₁ h e' * classResidualPoly π c₂ h e'

  — the minimal faces CONCATENATE (supports add to `h·(n₁+n₂)`, the two-point
  attainment persists at `j₁+j₂ < n₁+n₂` and the monic point, visibility from
  `h < e'`, `m ≤ N`) and the class residual MULTIPLIES.  Mechanism: B.39a §7 on any
  lift pair + the CN1 class/lift bridges (IFCG22/23/26/28) + `mulClass_proj`; the
  left-endpoint height `H₁+H₂ < N` keeps every read below the frame floor.
* ★ `cornerVisible_mulClass` — corner attainment on both factors ⟹ the product's
  corner is VISIBLE (corner valuations add: `v₀ = V₁+V₂` with `e'(V₁+V₂) = h(n₁+n₂) <
  e'N`).
* `shallow_of_minFaceAt` — any class with a minimal face is shallow (reusable).
* ★ `mulClass_mem_splitSector` / `mulClass_mem_splitSectorVis` — THE SECTOR CONVERSE:
  a coprime-residual same-face pair multiplies INTO the (visible) split sector.  The
  product's residual `G₁·G₂` is automatically non-irreducible and non-primary (coprime
  nonconstant factors; `dvd_prime_pow` argument).  The two honest gate legs are
  HYPOTHESES, and they name exactly the remaining strays: (i) the product's
  DECIDEDNESS (the polygon-block Hensel gap — decidedness does NOT transfer through
  `mulClass` without a splitting engine; the F-1 fence direction), (ii) the
  pure-face-box exclusion (`∉ pureFaceSet` — products CAN land in boxes the upstream
  census already counted).

## ★ §2 — THE EXACT COUNT LAYER (charge 2: the honest replacement)

* ★ `mulClass_cancel_left` / `mulClass_cancel_right` — LEVEL-EXACT cancellation in
  each argument separately: `mulClass c₁ c₂ = mulClass c₁ c₂' → c₂ = c₂'` (and the
  mirror).  Monic polynomials are regular modulo `𝔪^N` (leading-coefficient argument
  over the truncation ring; `coeff_mul_degree_add_degree`).  No polygon, no
  coprimality, no completeness — Lean-core, fully general.  This is everything of the
  charged "injectivity" that is TRUE at level exactness.
* `pairFiber` / `multCount` — the multiplicity of a product cell in SSL's convolution
  table (the pair-fiber count per table entry, summed over `convPairs`).
* ★ `convCount_eq_sum_multCount` — the fiberwise double count: at every finite level
  `convCount O m σ M = Σ_{c : Coeff O m (M+m)} multCount O m σ M c` — SSL's table
  counts every product cell with its multiplicity, exactly.
* `one_le_multCount_of_vis` — every visible split cell is hit at least once (SSL's
  refinement map; the B.42-citing leg).
* ★★ `convCount_eq_card_vis_add_defect` — THE EXACT DEFECT DECOMPOSITION:

      convCount = #vis + [ Σ_{c ∈ vis} (multCount c − 1) + Σ_{c ∉ vis} multCount c ]

  at every finite level, every mass, every type, every uniformizer: SSL's defect
  (`convCount − #vis`) IS the collision excess over the visible sector plus the stray
  mass of the table — the charged "compute the boundary/collision terms", in the only
  form that is true.

## ★ §3 — THE FIRINGS (charge 3: everything fireable, exactly scoped)

* ★ `splitSector_eq_empty_of_mass_le_three` — below mass 4 the split sector is EMPTY:
  a coprime split needs residual degree ≥ 2 at a face of denominator `e' ≥ 2`, and
  `e' · sideDeg ≤ sideMax ≤ m` prices the mass at `≥ 4`.  (Lean-core; also pins the
  FIRST possible split mass: `m = 4`, `e' = 2`, residual `= two coprime linears`.)
* ★ `splitConvolutionDefectLaw_of_mass_le_one` — UNCONDITIONAL (hypothesis-free) and
  Lean-core: the first outright instances of the defect law (table and sector both
  empty; the defect family is identically zero).
* ★ `splitConvolutionDefectLaw_of_mass_le_three` — under the `< m` decided value laws
  (the recursion's own supply): the defect is the full table, whose law is SSL §4's.
* `splitSectorLaw_of_mass_le_three` — the socket fires END-TO-END: `SplitSectorLaw m σ`
  outright for `0 < m ≤ 3`, all σ, under the `< m` value laws — and the footprint is
  LEAN-CORE (the low-mass path never touches B.42).
* ★★ `splitConvolutionDefectLaw_iff_splitSectorLaw` — under the `< m` value laws,
  `SplitConvolutionDefectLaw m σ ↔ SplitSectorLaw m σ`, BOTH directions machine-checked
  (forward: SSL's assembly; backward: vis = split − inv + the ℝ-identity through
  `zcURLim_sub`/`zcURLim_inv`).  Lean-core.  SSL's "re-base, not a strength reduction"
  accounting is now a theorem, and the endgame's split leg is OFFICIALLY:
  `SplitConvolutionDefectLaw m σ` at `4 ≤ m`, σ ramified (mass ≤ 3 landed here,
  unramified σ landed in SSL).

## THE HONEST FENCE (what stays open after this file)

1. **`SplitConvolutionDefectLaw m σ` at `4 ≤ m`, σ ramified** — unchanged as the named
   remainder, but its content is now CORRECTLY identified: by §2's decomposition it is
   the joint law of (a) the collision excess `Σ_vis (multCount − 1)` — the
   resultant-depth (mixing) distribution over visible cells — and (b) the stray mass
   `Σ_{c ∉ vis} multCount c` — pairs whose product fails decidedness-transfer, lands in
   the power/leaf sector (e.g. same-`ψ` residual pairs), in a pure-face box, at an
   invisible corner, or off the shallow stratum.  The discharge toolkit now holds: the
   class-level transfer (§1, which decided pairs CAN land where), the sector converse
   (§1b), the one-sided exactness (§2), and the exact bookkeeping (§2).  The missing
   engines are (i) the decidedness-transfer criterion for `mulClass` at a face
   (polygon-block Hensel — genuinely new), and (ii) the `q`-power fiber law
   `multCount = q^{v(Res)}`-graded rationality (Igusa-genre; the Sylvester-kernel count
   mod `π^N` is the natural route — Smith normal form over the DVR).
2. The gate legs of the sector converse (`hdec`, `hpf`) are hypotheses, NOT discharged
   — deliberately: they are exactly the stray strata of the defect.
3. Not attempted (out of charge): `PowerSectorLaw`, `LeafSectorLaw`, the mass-4
   dd/E2 recursions.

## File map (`leanfinal/Uniformity/ChapI/IFCG40.lean`, 1034 lines)

§0 supply (private `isKey_X`, `mem_sideSet_iff'`, `resPoly_rep` — SSL idiom copies) ·
§1 ★ `minFaceAt_mulClass` (181), ★ `cornerVisible_mulClass` (400),
`shallow_of_minFaceAt` (493), ★ `mulClass_mem_splitSector` (509),
★ `mulClass_mem_splitSectorVis` (560) · §2 ★ `mulClass_cancel_left` (587),
`mulClass_cancel_right` (649), private count bridges, `pairFiber` (738), `multCount`
(751), ★ `convCount_eq_sum_multCount` (758), `one_le_multCount_of_vis` (794),
★★ `convCount_eq_card_vis_add_defect` (842) · §3 ★ `splitSector_eq_empty_of_mass_le_three`
(882), ★ `splitConvolutionDefectLaw_of_mass_le_one` (924),
★ `splitConvolutionDefectLaw_of_mass_le_three` (950), `splitSectorLaw_of_mass_le_three`
(969), ★★ `splitConvolutionDefectLaw_iff_splitSectorLaw` (981) · AxCheck footer (14
lines).  Imports: `Uniformity.ChapI.IFCG38` only (everything else transitive).

## Design decisions (recorded)

* **No new polynomial-level transfer**: after finding B.39a §7, charge 1 was landed as
  pure class-level wiring — no duplication of the Minkowski engine, no new B-chapter
  surface.
* **Hypothesis-form gate legs** in the sector converse: `hdec`/`hpf` are the honest
  fence items; discharging either is a full unit (polygon-block Hensel; box
  exclusion), and carrying them as hypotheses makes the converse consumable by the
  defect-law discharge exactly at its stratification points.
* **Fintype instance binders** (`[Fintype (Coeff O m (M+m))]`) on the two count
  statements instead of statement-level `haveI`: `haveI` is opaque and broke every
  cross-statement `rw` (instance-term mismatch); the binder keeps all sums on ONE
  instance and consumers instantiate via `Fintype.ofFinite`.
* **The cancellation lives over the truncation ring** (map along
  `Ideal.Quotient.mk (𝔪^N)`, then the leading-coefficient regularity argument) — 15
  lines of core instead of a coefficientwise downward induction.
* **The additive decomposition shape** (`convCount = #vis + [...]`) instead of
  ℕ-subtraction: no truncated-subtraction side conditions anywhere; the ℝ-form for the
  defect family is one `push_cast` away for consumers.

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. `OnSide` is a def, not an `Eq` — defeq-retype (`have hOn : … = suppVal … := onSide_of_mem_sideSet …`) before `rw`.
2. `sideMin`-vs-`Finset.min'` atom mismatch for omega — type-ascribed `have h2 : sideMin … ≤ i := Finset.min'_le _ _ himem` bridges by proof irrelevance.
3. `open Classical in` must precede the docstring, not sit between docstring and theorem.
4. `WithTop.ne_top_iff_exists` produces the `WithTop`-coe, B.39a's `nsmul_add_cast_gen` wants the `Nat.cast` — bridge with an ascribed `have hV' : npHgt … = ((V : ℕ) : ℕ∞) := hV.symm` (SSL's own idiom).  Also: `gaussVal_C` lives in the `GateKit` namespace — routed through `dev_X`/`npHgt_X` instead; `Associated G 1 → IsUnit G` is `associated_one_iff_isUnit`.
5. Statement-level `haveI` opacity broke sum-instance defeq (goals displaying `Σ = Σ` unsolvable) — replaced by instance binders (see design decisions); `proj_surjective` needs `[Finite (ResidueField O)]` (moved the section variable up).
