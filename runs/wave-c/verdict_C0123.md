# Verdict C0123 — deep-witness consumer legs C0/C1/C2/C3

**Date:** 2026-08-29
**Unit:** C0123 / DEEP_WITNESS_CAMPAIGN §6.5 rows C0–C3 (+ [DWR] appendix constraints)
**Overall verdict:** **LANDED — all four rows, one file, zero `sorry`, zero warnings,
all 46 AxCheck footprints Lean-core `{propext, Classical.choice, Quot.sound}` subsets.**

New file: `leanfinal/Uniformity/ChapC/C136c0.lean` (885 lines; no split needed).
No landed `.lean`, leanspec, or scratch file was edited; no git operation performed.
Landing note for the orchestrator: the chapter aggregator `Uniformity/ChapC.lean` takes
the one-line `import Uniformity.ChapC.C136c0` at commit time (the C136r0–r4 pattern).

## Re-grounding (what these rows are)

The R67 keystone (`C136r4`) landed the depth-four witness — `s2SplitNodeFour` /
`s2FourChainRealization` / `s2FourRealizedInputOf` — and the G4 shared-record constructor
`s2Four_deepLevelExport_of_site`, whose ONE missing leg was the G3 site package (a
`WleClearedLevelExport` at the witness and the unique deep-live level `j = 3`) plus a
letter tie.  Rows C0–C3 are the four consumer legs: build that site (C0 + its cleared-law
input C1), prove the three WLE consumer dictionaries and fire the signed
`WiredGentowDemand` (C2), and convert the canonical generator descent into the project's
first live-index `VarthetaRes` (C3).

## Row → artifact

* **C1 — the single-`w` law.**
  `s2TruncThree := (s2DepthFour).trunc 3` (the trunc is data-definitional; `u 4 = 85` vs
  `s2DepthThree`'s junk `21` — R5's recorded transport handoff made explicit) ·
  `s2SiteKeyChain` (chain function = `(s2DepthThreeKeyChain).keyAt` VERBATIM, so the
  landed law bank's key mentions match by projection) · `s2SiteSourceData`/
  `s2SiteSourceLaws` (the SAME seven μ₄ operators as D3-18, all thirteen laws discharged
  by the landed D3 bank verbatim — the constant-`stageField` defeq carried every
  cross-tower typing) · ★ `s2SiteMu4Calculus` (via `fgmnCalculusOf`) +
  `s2Site_calculus_nonempty` (exit-gate-4 packaging discipline: only
  `fgmn_model_calculus_nonempty` after records) · `s2Trunc_towerNorm_two_eighty_five`
  (T4's `(8, 0, ![0,1])` re-proved at the trunc — `towerNorm 2` reads only rungs ≤ 3) ·
  `s2Site_chainNormBelow_three_eighty_five` (`= 2⁸Φ₂`) · the three B-1 supplies
  (grade `170 = 2·85` exact / degree `4 < 8` / nonzero — D3-13's tower-free facts) ·
  ★★ `s2Site_gentow5w : GENTOW5WCleared (s2TruncThree) 2 1 85 (s2SiteMu4Calculus)`
  through the new depth-generic `gentow5w_cleared_of_B1` (the `C132sg3.gentow5w_two_cleared`
  proof at generic depth; engine `ratio_power_law_cleared` was already depth-generic;
  unused signed-scope binders dropped, noted in the docstring).
* **C0 — the shared export inhabitant.**
  `s2Four_towerReadFamily_live/junk` (the wired read is `1` on the live range, junk `0`
  off it — no swallowing) · `s2Four_gc13Wiring` (the signed GC-13 law at the witness's
  own exported read and the site calculus, universal in `(N, q, φ)`: both sides are `1` —
  the wired read by construction, the FGMN read by `s2Site_Rgr_eq_one` = `Rgr_ne_zero` at
  the B-1 supplies + the card-2 collapse) · ★★ `s2FourWleSite` (the G3 site: literal
  `(e', f', u') = (2, 1, 85)`, `f_pos` = `one_pos`, C1's calculus + cleared law, the
  wiring leg) · ★★★ `s2Four_deepLevelExport` — **the G4 `DeepLevelExport` INHABITED** at
  the exact `X` and `j = 3` (the keystone constructor fired; `hletterZ := fun _ => rfl` —
  both calculi carry the forced constant-`1` letters, exactly R5's recorded mitigation) ·
  `s2Four_deepLevelExport_nonempty` (the literal nonvacuity tooth) · the dictionary
  projections (tauDictionary/wleExport examples) · ★ `s2Four_deepLevelPerWitnessExporter`
  (DWR §11.4's per-witness exporter AT THE WITNESS: `DeepLive 4 j` forces `j = 3`) +
  `s2Four_wleClearedPerLevelExporter` (the G3 projection).
* **C2 — the WLE dictionaries + the wired demand.**
  ★ `s2Four_thetaCompatibleAt` / `s2Four_peelCompatibleAt` (witness `wC = 1`) /
  `s2Four_rangeCompleteAt` — all three collapse in the card-2 terminal field (units read
  `1`; `thetaRatioCleared 1 = a·a⁻¹ = 1` at the nonzero `Rgr`) ·
  ★★ `s2Four_wiredGentowDemand` — the LANDED `DeepExport.wiredDemand_of_level_export`
  fired: the signed sitewise `IFC3.WiredGentowDemand` at the witness's own
  arena/use-height/read/peel-unit exports, site calculus, and receiver — campaign exit
  gate 4 closed at the literal site.
* **C3 — canonical tau/vartheta.**
  Production promotions (namespace `Uniformity.Density.DeepExport`, byte-identical to
  `scratch/TAU_probe.lean` with the descent leg = the landed G4
  `CanonicalGeneratorDescent`): `CanonicalTauLetterSource`, `canonical_tau_mem`,
  `varthetaRes_of_canonicalTauLetterSource` (the intermediate probe record inlined;
  final consumer is D62w's `hvarthetaRes_of_tau_letters`) + the general helper
  `kernelRead_snd_congr` · `s2CanonicalReadFour3_eq_one` (the witness's level-3 canonical
  read is CONSTANTLY `1` — every ambient letter is the unit `1`) →
  `s2Four_canonicalResAt_eq_one` → `s2Four_canonicalResFamily_eq_one` (through the CC-12
  view's `KernelRead` equality) · `s2Four_tau_mem` · ★★ `s2Four_canonicalTauLetterSource`
  (the record at the exact `X`, the canonical socket view — `eG := MulEquiv.refl`,
  `view := X.gaugeFamilyViewEq`, C130s18's socket-application pattern — `tau_word` at
  `m = 0, t = 0`) · ★★★ `s2Four_varthetaRes` — **THE FIRST LIVE-INDEX `VarthetaRes` IN
  THE PROJECT**: `Ladder.VarthetaRes (GaugeLattice 4) Kt L N₀ (gaugeHeightFamily X)
  (canonicalResFamily X) (useHeightFamily X) 3` at the witness's own exports.

Campaign-gate cross-check: gates 4 and 5 of DWC §8 are the C0/C2 and C3 exits above;
gate 7's same-`X` discipline holds by construction (every statement is at the one
`s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop`; no view or
owner is swapped — the C3 view is literally `X.gaugeFamilyViewEq`).

## Honesty scope

* Everything at the witness inherits EXACTLY the keystone's conditionality: the four open
  threshold datums `w₁..w₄`, the parametric R8/R8r payload (`F₀`/monic/`μ`/degree-block/
  key-coprimality — NO payload instance invented; G9 stays gated), and `IsAdicComplete`.
* `tau_word` is proved AT THIS WITNESS by the S2 collapse (read ≡ 1); the general
  triangular spanning (`LVS-TAU-WORD`) remains OPEN — the production record keeps it as
  an honest field for non-collapsed witnesses.
* The theta/peel/range discharges are card-2-field facts; GCW-4/GCW-5 at general residue
  cardinality remain open consumer laws (I10DeepExport §3's status unchanged).
* G10's UNIVERSAL exporter is untouched: `s2Four_deepLevelPerWitnessExporter` is the
  per-witness (one-`X`) exporter, exactly DWR §11.4's shape at this occurrence.

**Flagged for human review** (new statements): `CanonicalTauLetterSource` (production
promotion), `s2FourWleSite`, `s2Four_deepLevelExport`, `s2Four_wiredGentowDemand`,
`s2Four_canonicalTauLetterSource`, `s2Four_varthetaRes`.  General lemmas (flagged):
`kernelRead_snd_congr`, `gentow5w_cleared_of_B1`, `c0_eq_one_of_ne_zero` (a third copy of
the private R1/R67 card-2 collapse — a dedup candidate if anyone de-privatizes the R1
original).

Cite ledger: **empty** — Lean core over the landed corpus.

## Verification

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136c0.lean
```
Exit 0; zero errors, zero warnings, zero `sorry`; all 46 footer declarations report only
Lean-core axiom subsets (machine-checked incl. line-wrapped reports).  Repository scope:
`git status` shows only this new file + this verdict.

## Proof notes (for the next porter)

* **The cross-tower `1` blocks keyed rewriting.**  Terms mixing the trunc-typed and
  depth-four-typed stage fields make targets "not type-correct under `instances`
  transparency"; `rw [map_one]`, `rw [one_pow]`, and unit-coercion rewrites then fail
  with "pattern not found" even when the pattern is visibly present.  Fix genre: term
  mode — `exact map_one _`, `exact (one_pow 1).symm`,
  `(congrArg Units.val (s2FourUnit_eq_one …)).trans (map_one _).symm`, and the
  `c0_eq_one_of_ne_zero`-collapse of whole products (`mul_ne_zero` + `Units.ne_zero`).
* **`norm_num` cannot see `core.r`.**  Every `1 < core.r`-shaped side goal needs the
  projection-reducing pin `s2FourCore_one_lt_r` (proved by `show (1:ℕ) < 4`).
* **`GaugeLattice`'s universe metavar can survive proof-irrelevant unification.**
  `s2Four_tau_mem` needed the statement's tau ascribed to `GaugeLattice.{uG} 4` AND the
  explicit instantiation `canonical_tau_mem.{uG, 0, uL}` at the final `exact`.
* **`mem_ker` under mixed types:** don't `rw [MonoidHom.mem_ker]` when the membership's
  `Subgroup` carrier displays `GaugeLattice core.r` against an element at
  `GaugeLattice 4`; use `show f x = 1` (mem_ker is `Iff.rfl`) plus a hom-level equality
  (`gaugeHeightFamily X 3 = levelHeight …` via `simp only [gaugeHeightFamily]; rw
  [dif_pos hlive]; rfl` — the `dif_pos` witness must be pre-cast to the `core.r` form).
* The trunc-typed records were the big defeq bet and they all landed FIRST TRY: reuse
  `(s2DepthThreeKeyChain).keyAt` (not `s2DepthThreeKeyAt`) as the chain function so the
  landed laws' key mentions match by projection reduction; `(trunc).Dcum = parent.Dcum`
  and `(trunc).towerNorm = parent.towerNorm` are `rfl`.
