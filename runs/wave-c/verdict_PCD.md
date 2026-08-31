# UNIT PCD — VERDICT: RCD'S TEMPLATE REPLAYS ON THE POWER SECTOR ESSENTIALLY VERBATIM — the power defect decomposition is EXACT (`convCount = #powerVis + collisions + strays`), `PowerConvolutionDefectLaw m σ` is RE-BASED cite-free onto the `< m` value laws + ONE Prop (`PowerVisCountLaw`), the UNIFICATION LANDS (`VisCensusLaw : VisGenre → …` with DEFINITIONAL bridges to both count laws), and the census master's TWO defect premises are now ONE genre-quantified Prop; the proper power sector is EMPTY at `m ≤ 4` — one mass better than split (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG58.lean` (741 lines, ZERO sorries,
zero warnings, zero errors; 25 AxCheck footer rows — FOURTEEN pure Lean core
`{propext, Classical.choice, Quot.sound}` including the cite-free re-base
`powerConvolutionDefectLaw_of_powerVisCountLaw`, the full power-front re-base
`powerSectorLaw_of_visCountLaw` (BETTER than designed: PSL4's `powerSectorLaw_of_rebase`
chain is itself Lean-core), the `m ≤ 4` emptiness pair, the mass fires, the genre
disjointness, and BOTH unified-census consumers; ELEVEN carry Lean core + exactly the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42,
inherited through PSL4's refinement / SDL / IFCG33 / IFCG35's front — never
re-consumed).  C.33 and `AX_cellRecursion` do NOT occur.  Verification:
`timeout 580 lake env lean Uniformity/ChapI/IFCG58.lean` (exactly the 25 footprint
infos, nothing else); targeted `lake build Uniformity.ChapI.IFCG58` GREEN (8968 jobs);
sanctioned aggregator import appended after IFCG57's line, aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0); IFCG57.lean untouched.  NO git
operations.

## ★★★ THE HEADLINES

1. **★ THE POWER DEFECT DECOMPOSITION IS EXACT** (charge 1 —
   `convCount_eq_card_powerVis_add_totals`, §1, B.42): at every finite level, mass,
   type, uniformizer:
   `convCount = #powerSectorProperVis + (powerCollisionTotal + powerStrayTotal)`,
   with `powerCollisionTotal = Σ_{c ∈ powerVis}(multCount c − 1)` and
   `powerStrayTotal = Σ_{c ∉ powerVis} multCount c` instance-free ℕ totals — SDL's
   engine at the power fibers.  Mechanism: `one_le_multCount_of_powerVis` (every
   visible proper power cell is hit by the table ≥ once — PSL4's
   `powerSectorProper_refines_decided` fired into SDL's fiber argument, byte-parallel
   to `one_le_multCount_of_vis`).  The exact ℝ casts
   (`powerCollisionTotal_cast`/`powerStrayTotal_cast`) and the conditional collision/
   stray `ZcURLim`s under (`PowerVisWeightLaw`, `PowerVisCountLaw`) replay RCD §5.
2. **★★ THE CITE-FREE RE-BASE** (`powerConvolutionDefectLaw_of_powerVisCountLaw`,
   §2, PURE Lean core): `PowerConvolutionDefectLaw m σ` (PSL4's named Prop,
   byte-untouched) rests on the `< m` decided value laws + the SINGLE Prop

       PowerVisCountLaw m σ := ZcURLim (#powerSectorProperVis / q^{m(M+m)})

   (defect = `conv − #powerVis` pointwise; the table law is IFCG38's) — exactly
   RCD's split re-base, replayed.  ★★ `powerSectorLaw_of_visCountLaw` then rests
   `PowerSectorLaw m σ` on {`< m` laws, `PowerVisCountLaw`, `PowerFullSpanLaw`} —
   and prints PURE LEAN CORE.
3. **★★ THE UNIFICATION LANDS — AND ITS HONEST FORM IS DETERMINED** (charge 2, §4):
   `VisGenre := split | power` (exactly the convolution-descending residual genres),
   `visGenreSet` (.split ↦ `splitSectorVis`, .power ↦ `powerSectorProperVis`), and

       VisCensusLaw g m σ := ZcURLim (#visGenreSet g / q^{m(M+m)})

   with `visCensusLaw_split_iff : VisCensusLaw .split ↔ VisCountLaw` and
   `visCensusLaw_power_iff : VisCensusLaw .power ↔ PowerVisCountLaw` both `Iff.rfl`
   (DEFINITIONAL — the unified Prop adds zero semantic distance).  The genres are
   DISJOINT sub-genres of the visible carrier (`visGenreSet_disjoint`, Lean-core,
   via RECUR's `sectors_disjoint`).  **The determination:** ONE Prop covers both,
   but as a genre-INDEXED family, NOT a union count — a union/sum limit does not
   split into its parts, so `∀ g, VisCensusLaw g m σ` is the honest joint form
   (recorded in the docstring).  Leaf is deliberately NOT a `VisGenre`: leaf cells
   do not descend through the table (no mass drop), and full-span power cells
   descend through the fractional recentring (`PowerFullSpanLaw` keeps them).
4. **★★★ THE MASTER'S LIST RECOMPUTED** (charge 3, §5): two new census masters.
   `decidedSliceAt_all_of_visCounts` — the all-degree decided slice on
   {`VisCountLaw`, `PowerVisCountLaw`, `PowerFullSpanLaw`, `LeafSectorLaw`, R4};
   `decidedSliceAt_all_of_visCensus` — **the master's two convolution-defect
   premises FUSED into ONE**: the all-degree decided slice rests on

       { ∀ g, VisCensusLaw g e σ   (e ≥ 5 ramified witnessed, under < e laws)
         PowerFullSpanLaw e σ
         LeafSectorLaw e σ
         ConeRemainderLaw 4 σ (the five e = 4 remainder laws) }

   (`SplitConvolutionDefectLaw` and `PowerConvolutionDefectLaw` are GONE from the
   premise list, replaced by the one visible-genre census family.)
5. **★ THE `m ≤ 4` EMPTINESS — one mass better than split** (§3, Lean-core):
   `powerSectorProper_eq_empty_of_mass_le_four` — a proper power cell carries face
   data `e' ≥ 2, k ≥ 2, deg ψ ≥ 1` with `e'·k·deg ψ < m`, so `4 ≤ e'·k·deg ψ < m`
   forces `m ≥ 5` (the power residual needs multiplicity `k ≥ 2` where split needs
   two coprime factors; PSL2's `powerSector_data` + face uniqueness, cite-free).
   FIRES: `PowerVisCountLaw`/`PowerVisWeightLaw` unconditional at `m ≤ 4` AND at
   every unramified type; ★ `powerConvolutionDefectLaw_of_mass_le_four` is a NEW
   fire (PSL4 had only the unramified one); `visCountLaw_of_mass_le_three`/
   `visCountLaw_unramified` fire RCD's Prop from RCD's own emptiness (not fired
   there); `visCensusLaw_of_mass_le_three` (Lean-core!) and `visCensusLaw_unramified`
   fire the unified Prop in both genres.
6. **THE TILING CHECK** (charge 1's second item, verified — NO code needed): RCD's
   entire tiling toolkit (IFCG56 §§1–4: depth transport, N-free digit-box root
   counts, the drainage tiling, `tendsto_slice_drainage_of_complete`) is stated at
   FREE `(n₁, n₂, σ₁, σ₂, N, v)` on the decided pair table with no sector
   reference — and the power defect grades through the SAME `convPairs` table
   (PSL4's majorant is `≤ convCount`, the identical genre).  The toolkit is
   consumable for the power census verbatim; duplicating it would have added
   nothing.

## THE HONEST FENCE (what remains of the convolution front, exactly)

`VisCensusLaw g m σ` at σ ramified — `.split` at `4 ≤ m` (= RCD's `VisCountLaw`
fence), `.power` at `5 ≤ m` — NOT fired here; plus the weight censuses
(`VisWeightLaw`/`PowerVisWeightLaw`, same ranges) if the collision/stray GRADED
refinements are wanted separately.  The master consumes only `e ≥ 5`, where the one
family `∀ g, VisCensusLaw g e σ` is the entire convolution-sector premise.  Their
discharge toolkit on the pair side is complete and SHARED (RCD's tiling, headline 6);
the open territory is the CELL side, per genre: which visible split cells carry how
many table pairs (B.42's block-decomposition genre) and the image description of
PSL4's proper-power refinement (the polygon-factorization-uniqueness converse — PSL4
§7's docstring already notes the two defects share one converse mechanism, which the
unified Prop now makes structural).  NOT attempted (out of charge):
`PowerFullSpanLaw` (OM decision transport, C136's territory), `LeafSectorLaw`, the
general depth-stratum values, the Tannery assembly.  Nothing weakened; every
consumed statement byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG58.lean`, 741 lines)

§0 kit (private replicas: `natCard_set_eq_card_filter`, `toFinset_card_eq_natCard`,
`isKey_X`) ·
§1 `powerCollisionTotal`, `powerStrayTotal`, `powerVisWeight`,
`one_le_multCount_of_powerVis` (B.42), ★ `convCount_eq_card_powerVis_add_totals` ·
§2 `PowerVisCountLaw`, `PowerVisWeightLaw`, `powerCollisionTotal_cast`,
`powerStrayTotal_cast`, `powerVisWeight_eq_zero_of_empty`,
`powerCollisionTotal_eq_zero_of_empty`, ★ `zcURLim_powerCollision_of_visLaws`,
★ `zcURLim_powerStray_of_visWeightLaw`,
★★ `powerConvolutionDefectLaw_of_powerVisCountLaw` (Lean-core),
★★ `powerSectorLaw_of_visCountLaw` (Lean-core) ·
§3 ★ `powerSectorProper_eq_empty_of_mass_le_four` (+`Vis`, Lean-core),
`powerSectorProperVis_eq_empty_unramified` (B.42 via IFCG33),
`powerVisCountLaw_of_mass_le_four`, `powerVisCountLaw_unramified`,
`powerVisWeightLaw_of_mass_le_four`, `powerVisWeightLaw_unramified`,
★ `powerConvolutionDefectLaw_of_mass_le_four` (NEW fire, Lean-core),
`visCountLaw_of_mass_le_three`, `visCountLaw_unramified` ·
§4 `VisGenre`, `visGenreSet`, ★★ `VisCensusLaw`, `visCensusLaw_split_iff`/
`visCensusLaw_power_iff` (both `Iff.rfl`), `visGenreSet_disjoint` (Lean-core),
★★ `splitConvolutionDefectLaw_of_visCensus` (Lean-core),
★★ `powerConvolutionDefectLaw_of_visCensus` (Lean-core),
`visCensusLaw_of_mass_le_three` (Lean-core), `visCensusLaw_unramified` ·
§5 ★★★ `decidedSliceAt_all_of_visCounts`, ★★★ `decidedSliceAt_all_of_visCensus` ·
AxCheck footer (25 rows).  Imports: `Uniformity.ChapI.IFCG44` + `IFCG56` only.

## Design decisions (recorded)

* **No new named collision/stray Props for the power sector**: IFCG41 pre-named
  `CollisionLaw`/`StrayLaw` for split, so RCD had to fire them; the power side has no
  such names, so the collision/stray results are stated as raw `ZcURLim` conclusions
  under the census pair — no Prop proliferation.
* **The unified Prop is definitional, not translated**: `visGenreSet` pattern-matches
  INSIDE the census family, so both genre instances iota-reduce to the existing laws
  (`Iff.rfl` bridges); consumers can move between the unified and per-sector forms at
  zero proof cost, and no existing statement changed.
* **Union-count unification REJECTED on honesty grounds**: `ZcURLim` of a sum does
  not recover the summands, so a single union census would be strictly weaker than
  the master needs; the genre-indexed ∀ is the correct joint strength (this is the
  determination charge 2 asked for).
* **The tiling is consumed by citation, not replay** (headline 6): sector-agnostic
  machinery must not be duplicated per sector.

## Repair log (1 error round)

1. Skeleton + all proofs: compiled with exactly ONE error — a wrapped `exact` term in
   `visCensusLaw_of_mass_le_three`'s power branch (continuation line under-indented,
   parser closed the term); rejoined under the case arm.  Every statement and every
   other proof landed first-pass (the file is a near-verbatim replay of
   IFCG40/41/44/56 idioms, which is the point of the template).
