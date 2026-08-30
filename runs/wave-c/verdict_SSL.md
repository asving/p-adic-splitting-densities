# UNIT SSL — VERDICT: THE SPLIT SECTOR'S DESCENT STRUCTURE MACHINE-CHECKED — the refinement map lands (every visible split cell IS a product of two DECIDED strictly-smaller-mass cells), the convolution table MAJORIZES the sector at every finite level, and `SplitSectorLaw m σ` is RE-BASED onto ONE named Prop, the convolution defect law (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG38.lean` (825 lines, ZERO sorries,
zero warnings, zero errors; 14 AxCheck footer lines — NINE are pure Lean core
`{propext, Classical.choice, Quot.sound}` (the residual monicity, the monic coprime
split, the vis/inv partition, the invisible-corner box, all four `ZcURLim` combinators
incl. the new `mul`/`sub`, the value-law-consuming convolution law, and ★★ THE ASSEMBLY
`splitSectorLaw_of_defectLaw` itself), and exactly FIVE carry Lean core PLUS the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42,
inherited through XHS's `wideFace_refinement_of_stratum` / IFCG33's forcing only):
`splitSector_refines`, `splitSector_refines_decided`, `card_splitSectorVis_le`,
`defect_nonneg`, `defectLaw_unramified`.  The C.33 cites do NOT occur.  No landed file
touched except the sanctioned one-line aggregator import in `Uniformity/ChapI.lean`
(after IFCG37's line); no git ops.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG38.lean` (final: zero diagnostics),
targeted `lake build Uniformity.ChapI.IFCG38` green (8952 jobs), aggregator
`lake env lean Uniformity/ChapI.lean` green.

## THE HEADLINE (charge scoping: honest fallback ENGAGED, exactly as sanctioned)

    theorem splitSector_refines_decided :        -- ★ THE REFINEMENT MAP (class level)
      c ∈ splitSector O π m σ M → CornerVisible c →
        ∃ n₁ n₂ (0<n₁) (0<n₂) (hsum : n₁+n₂ = m) σ₁ σ₂ c₁ c₂,
          DecidedAt O n₁ σ₁ (M+m) c₁ ∧ DecidedAt O n₂ σ₂ (M+m) c₂ ∧
          σ₁.data + σ₂.data = σ.data ∧ mulClass c₁ c₂ = hsum.symm ▸ c
    theorem card_splitSectorVis_le :             -- ★ THE MAJORANT, exact at EVERY level
      #(visible split cells) ≤ convCount = Σ_{(n₁,n₂,s), n₁+n₂=m, both>0, s≤σ.data}
                                    decidedCount n₁ ⟨s⟩ (M+m) · decidedCount n₂ ⟨σ.data−s⟩ (M+m)
    def SplitConvolutionDefectLaw (m σ) : Prop :=  -- THE ONE NAMED REMAINDER
      ZcURLim ((convCount − #visible split cells) / q^(m(M+m)))
    theorem splitSectorLaw_of_defectLaw :        -- ★★ THE RE-BASE (Lean-core!)
      (∀ k < m, ∀ σ', σ'.degree = k → DecidedValueLaw k σ') →
        SplitConvolutionDefectLaw m σ → SplitSectorLaw m σ

`SplitSectorLaw m σ` (IFCG35's statement, consumed byte-identical, never touched) now
rests on exactly `SplitConvolutionDefectLaw m σ` under the `< m` decided value laws —
for ALL m and ALL σ (stronger than the charged "ramified, e ≥ 5" scope), uniform in
q, m, σ, every complete DVR, every uniformizer.  The full outright firing of
`SplitSectorLaw` was NOT achieved — its missing leg is precisely the defect law's
content, see THE HONEST FENCE below.

## ★ §1 — the MONIC coprime split (Lean-core; the XHS input upgraded from `Associated` to `=`)

* `classResidualPoly_monic` — NEW: on the minimal face the canonical class residual is
  MONIC.  Mechanism: B.39a's purity-free `resPoly_coeff` at the top coefficient;
  `sideMax = m` (the monic point is on the side and caps the abscissae), coprimality
  forces `m − sideMin = e'·sideDeg` and `H₀ = h·sideDeg`, so the leading coefficient is
  `resMk π X 0 (dev X (monicPoly a) m)` = `resMk π X 0 1` = `1` (`dev_top` +
  `resMk_one`).  RECUR's honesty lemma gave `natDegree ≥ 1 ∧ coeff 0 ≠ 0`; monicity is
  the missing third leg that turns §2c's `Associated R (G·H)` into the EQUALITY
  `classResidualPoly π c h e' = G * H` (`Polynomial.eq_of_monic_of_associated`).
* `splitSector_coprime_split` — every split-sector class, at its (unique) minimal face:
  `∃ G H` monic coprime nonconstant with `classResidualPoly = G·H` — the literal `hres`
  input of XHS §4.  (Field structure on `resField X` brought in by B25's sanctioned
  `letI := instFieldResField isKey_X` idiom.)
* Supply: `resPoly_rep` (private) — for EVERY lift, the class residual IS that lift's
  side residual with side-set/height/finiteness data exported (WFR §3 through
  `classResidualPoly_eq`, packaged once, consumed three times).

## ★ §2 — THE REFINEMENT MAP (Lean core + exactly B.42)

* `splitSector_refines` (lift level): a visible-corner split-sector class carries the
  §1 split `G·H`, and EVERY lift factors `monicPoly a = g · h' · R` with `g, h'` monic
  `(h,e')`-pure of degrees `e'·deg G / e'·deg H` carrying residuals EXACTLY `G, H`
  (∀-pin form), `R` monic — XHS's `wideFace_refinement_of_stratum` fired at the minimal
  face (the corner-visibility gate `CornerVisible` is XHS's own honest fence item 2).
* `splitSector_refines_decided` (class level, the census shape): the cell IS a
  `mulClass` of two DECIDED classes of strictly smaller masses `n₁ + n₂ = m`
  (`n₁ = e'·deg G`), at types summing to `σ` (IFCG17's decided-refinement fired through
  one lift's factorization; `monicPoly_coeff_eq_self` + `mulClass_proj` recover the
  cell from the pair).  Because `mulClass c₁ c₂` RECOVERS `c`, the map
  cell ↦ (masses, types, pair) is injective — the charged "bijection" is landed as a
  bijection onto its image; the image's intrinsic description is the open converse.

## ★ §3 — THE COUNT (the convolution majorant, exact at every finite level)

* `convPairs m σ` / `convCount O m σ M` — the convolution table: pairs `(n₁,n₂)` with
  `n₁+n₂ = m`, both positive (the second mass is FORCED to `m−n₁` by the filter;
  carrying it explicitly is deliberate cast-hygiene — it makes `subst` legal and keeps
  every transport definitional), times sub-multisets `s ≤ σ.data`; entries
  `decidedCount n₁ ⟨s⟩ (M+m) · decidedCount n₂ ⟨σ.data−s⟩ (M+m)`.  π-free.
* `splitSectorCount_eq_vis_add_inv` — the exact corner-visibility partition (Lean-core).
* ★ `card_splitSectorVis_le` — #vis ≤ convCount at EVERY level (the §2 injection +
  `Finset.set_ncard_biUnion_le` + `Set.ncard_prod`; `mulClassAt` = `mulClass` with the
  level a SEPARATE variable so the mass-transport motive never touches it).
* `card_splitSectorInv_le` — #inv ≤ q^((m−1)(M+m)) (Lean-core: an invisible corner pins
  the constant coefficient to the zero window — H107's `resOrd_eq_iff` — and the cell
  injects into the remaining m−1 coordinates; `card_coeff` prices the box).

## §4 — the limit layer (ALL Lean-core)

* `zcURLim_mul`, `zcURLim_sub` — the product/difference combinators IFCG24's calculus
  lacked (same one-rational-pair mechanism as its `add`).
* `zcURLim_inv` — the normalized invisible-corner count is a `ZcURLim` with value 0
  (squeeze against §3's box; `q^((m−1)K)/q^(mK) = (1/q)^K → 0`).
* ★ `zcURLim_conv` — under the `< m` decided value laws the convolution family
  `convCount/q^(m(M+m))` IS a `ZcURLim`: each entry is `decidedSeq · decidedSeq` read
  at the diverging level `M+m` (`tendsto_decidedSeq_comp`, CN5's consumption pattern),
  the value laws pin each factor's limit to ONE rational function of q, and
  degree-mismatched entries vanish identically (`typeOf_degree`).  The normalization is
  EXACT: `q^(n₁(M+m))·q^(n₂(M+m)) = q^(m(M+m))` — the convolution's level bookkeeping.

## ★★ §5 — the re-base and the defect law's semantics

* `SplitConvolutionDefectLaw m σ` — THE ONE NAMED REMAINDER: the normalized overcount
  `(convCount − #vis)/q^(m(M+m))` is a uniform rational limit.
* `defect_nonneg` — the defect is pointwise ≥ 0 (§3's majorant): the Prop is a genuine
  overcount, never a signed fudge.
* ★ `defectLaw_unramified` — nonvacuity in the recursion's own premise shape: at every
  unramified σ the visible split sector is EMPTY (UZL's forcing via IFCG33), so the
  defect law FIRES under the value laws (defect = the full table).
* ★★ `splitSectorLaw_of_defectLaw` — defect law + `< m` value laws ⟹
  `SplitSectorLaw m σ`.  Mechanism: `#split = #vis + #inv` (exact), `vis-family =
  conv-family − defect-family` (an ℝ-identity, so the assembly needs NO inequality and
  stays Lean-core), `inv-family → 0`.

## THE HONEST FENCE (what stays open after this file)

1. **`SplitConvolutionDefectLaw m σ` at ramified σ, m ≥ 5** — the surviving open leg of
   the split arm.  Honest strength accounting: GIVEN the `< m` value laws it is
   equivalent to `SplitSectorLaw m σ` (both directions follow from this file's landed
   pieces), so the unit's claim is a RE-BASE, not a reduction in logical strength.  Its
   value: the residual content is now isolated in the discharge mechanism's OWN terms —
   the defect counts exactly the convolution-table pairs that do NOT arise as visible
   split cells, so the route is the CONVERSE of §2's map: (a) which decided pairs
   multiply INTO the split sector (the product's polygon = Minkowski of the factors';
   IFCG30 §5's unit-corner transfer is the one landed piece of this genre), and (b) the
   finite-precision uniqueness of the polygon-block factorization (IFCG16 §6's Hensel
   uniqueness is the coprime-reduction instance; the polygon-block analogue at equal
   reductions `X̄^{n₁}·X̄^{n₂}` is the missing engine — the "polygon-block
   `stratDecCount_mul`" RECUR's verdict predicted).  Everything else about the arm —
   the descent structure, the mass bookkeeping, the level normalization, the limit
   calculus — is machine-checked here.
2. The invisible-corner split cells are BOXED (≤ q^((m−1)(M+m))), not refined — their
   refinement is WFR's fence item 2 (the X-strip), another unit's; for the LAW they are
   handled exactly (they vanish in the limit, `zcURLim_inv`).
3. Not attempted (out of charge): `PowerSectorLaw`, `LeafSectorLaw`, the e = 4 laws.

## File map (`leanfinal/Uniformity/ChapI/IFCG38.lean`, 825 lines)

§0 supply (private `isKey_X`, `mem_sideSet_iff'` — B83Kit idiom copies) ·
§1 `resPoly_rep` (private), ★ `classResidualPoly_monic`, ★ `splitSector_coprime_split` ·
§2 `CornerVisible`, ★ `splitSector_refines`, ★ `splitSector_refines_decided` ·
§3 `splitSectorVis`/`splitSectorInv`, `convPairs`, `convCount`, `mulClassAt`,
`splitSectorCount_eq_vis_add_inv`, ★ `card_splitSectorVis_le`,
`card_splitSectorInv_le` · §4 `zcURLim_mul`, `zcURLim_sub`, `zcURLim_inv`,
★ `zcURLim_conv` · §5 `SplitConvolutionDefectLaw`, `defect_nonneg`,
★ `defectLaw_unramified`, ★★ `splitSectorLaw_of_defectLaw` · AxCheck footer (14 lines).
Imports beyond the consumers' baseline: `ChapB.B39a` (the purity-free `resPoly_coeff`),
`ChapI.IFCG16`, `ChapI.IFCG30` (XHS), `ChapI.IFCG35` (RECUR).

## Design decisions (recorded)

* **Monicity over associates**: landing `classResidualPoly_monic` (one new ~90-line
  Lean-core theorem) buys the EQUALITY form of the coprime split, which is what
  `wideFace_refinement_of_stratum` consumes — no weakened `Associated`-shaped variants
  anywhere.
* **The two-mass index** (`convPairs` carries `(n₁, n₂)` with the filter `n₁+n₂ = m`
  rather than `(n₁, m−n₁)`): `subst` on `n₁ + n₂ = m` is legal (RHS is the variable),
  `subst` on `n₁ + (m−n₁) = m` is circular — this one choice removed every `▸` from the
  majorant's subset proof.
* **`mulClassAt` with the level as a separate variable**: an inline `h ▸` rewrote `m`
  in BOTH the mass and the level `M + m` (motive over-capture); the standalone def pins
  the motive to the mass alone.
* **The assembly is subtraction, not sandwich**: `vis = conv − defect` is an ℝ-identity,
  so `splitSectorLaw_of_defectLaw` never consumes the majorant and stays Lean-core; the
  majorant's role is the defect's SEMANTICS (`defect_nonneg`).
* No file-level `Classical.propDecidable` instance (unlike IFCG35): it poisons
  `if_pos`'s instance unification against B39a's `Nat.decLt` ite (a whnf grinder); the
  one proof needing classical choice opens with the `classical` tactic locally.

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. `sideMin ≤ m` omega: RECUR's logged trap #3 verbatim — `unfold sideMin` first (the
   def and `Finset.min'` are different omega atoms).
2. whnf timeout ×2 in `classResidualPoly_monic`'s final step: (a) the file-level
   classical instance (removed), and (b) `exact resMk_one hπ X` — elaborating the
   explicit `X` standalone grinds; `exact resMk_one hπ _` (unify from the goal) is
   instant.  Diagnosed by stepping the LSP goal through the rw chain (every rewrite was
   clean; only the closing `exact` hung).
3. `Field (resField X)` is NOT a global instance (B25's B-D3 repair): consumers must
   `letI := instFieldResField isKey_X` — a second whnf-timeout-shaped failure.
4. Inline `h ▸ mulClass` over-capture + literal-pair projections opaque to omega
   (`dsimp only` before omega) — both in the majorant; fixed by `mulClassAt` + dsimp.
5. `tendsto_add_atTop_nat` needs the `Filter.` prefix; `div_le_div_right` renamed at
   the pin (→ `gcongr`); one exponent-identity calc had congr's orientation reversed.
