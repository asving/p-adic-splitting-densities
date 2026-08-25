# Unit NP4 verdict — S2-source plan node NP-4 (threshold source)

## Verdict: LANDED (partial, honestly split — see caveat)

New file `leanfinal/Uniformity/ChapC/C130np4.lean` (imports `C80`, `C10`). Sorry-free, no new
axiom, no `unsafe`; every `#print axioms` line is Lean core (`propext, Classical.choice,
Quot.sound`) only. No `NodePointSource` instance is constructed, named, or claimed anywhere in
the file — none exists at S2 under the current signature (unit U13: `no_s2_node_source`,
`no_s2_source_frontier`).

## The search (row NP-4's actual charge)

Read first: `docs/PROJECT_STATE.md` §4.2, `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` (row
NP-4, §5's `thresholdZ`/`thresholdNat`/`threshold_nonneg` verdict row), `C130th.lean` (CC-7),
`runs/wave-b/verdict_CC07.md`, `runs/wave-b/verdict_C130A.md`.

Searched (per the brief's grep list, plus the trails it opens): `spec/EFF-T2*.md`,
`spec/EFF-GENTOW5*.md`, `spec/EFF-GENHN*.md`, `spec/EFF-HE6R1.md`, `spec/EFF-HE7*.md`,
`lean/notes/openmath/he7rat_brief_2026-08-09.txt`, `lean/notes/openmath/
towerrat2_discharge_brief_2026-08-10.txt`, `blueprint/CHAP-C_tower_grammar.md`,
`blueprint/CONVENTIONS_2026-08-15.md`, `blueprint/CHAP-B_leaf_layer.md`,
`docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md`,
`docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md`, and the landed Lean corpus
(`C09`, `C10`, `C42`, `C44`, `C80`, `C130a`, `C130s2`, `C130th`).

**Two distinct thresholds, two distinct answers — both real findings, not one BLOCKED node:**

1. **Level 1 (the base carrier, `i = 1`): confirmed, again, no formula.** `EFF.T2.04` is a
   `[hypothesis]` ("the carrier has ... an inherited threshold `T ∈ 𝐙`") with no formula
   anywhere in the corpus. `s2DepthTwo`'s stage-1 data is literally `s2Frame h2 hq`'s own
   `(e₁,f₁,h) = (2,1,1)` (`C130s2.s2DepthTwo_stage1`) — level 1 is the base `KeyFrame`, not
   built from any `LevelDatum` composition, so there is no prior-level datum to derive a
   threshold from. This independently reconfirms CC-7/`C130A`'s ruling at the concrete S2
   instance. **Not a new blocker — the same one, re-checked and still standing.**

2. **Level 2 (the terminal stage of the depth-two S2 tower, `i = 2`): a genuine source
   formula, already landed.** `EFF.HE6R1.18` (`spec/EFF-HE6R1.md`, an `[instrument-record]`,
   verbatim: `"T₂ = ℓd_rλ = 1·2·λ = 2λ"`) fixes the **level-2 disk threshold** as
   `T₂ = ℓ·d_r·λ`, cleared at `λ = u/ℓ` to the integer `d_r·u`. HE7's own text names this the
   level-2 legality boundary — `"dv₂(Ψ(ξ)) > T₂ iff ξ is a level-2 point"`
   (`he7rat_brief_2026-08-09.txt:571-572`) — and `docs/in-progress/
   LEAN_SCOPING_consumption_map_2026-08-12.md` independently lists "HE7+HE6R1 (level 2)" as one
   of five *span-pinned instances* of the exact `EFF.T2.11` `(WINDOW)` schema `T < d(Φ(ρ)) <
   ∞`. This is already transcribed, faithfully, in landed Lean: `LevelDatum.seam` (`C09.lean`,
   SOURCE line names `EFF.HE6R1.18`) defines `L.seam := L.r.natDegree * L.u`; `TowerDatum.
   levelDatum` (`C44.lean`) bridges a `TowerDatum` (hence `s2Tower`, C.80) into a `LevelDatum`;
   `LevelDatum.seam_mul` (`C10.lean`) proves the cleared identity as a theorem. None of this is
   new — it predates this node by weeks. What NP-4 adds is the concrete S2 evaluation and the
   identification argument tying it to `CanonicalThresholdAt`'s vocabulary.

## What is proved in `C130np4.lean`

At `s2Tower h2 hq : TowerDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq)` (C.80's landed
`(e₂,f₂,u₂,ψ₂) = (2,1,5,X-1)`):

* `levelDatum_natDegree_s2Tower` — `d_r = ((s2Tower h2 hq).levelDatum h2).r.natDegree = 1`
  (`towerLabel_spec`, the same step `C80.keyDeg₂_s2Tower` already extracts).
* `seam_s2Tower` — **`seam = 5`** (`= d_r·u = 1·5`), the level-2 disk threshold `T₂` in
  `EFF.HE6R1.18`'s own (rational-cleared) normalization. Cross-checked independently: this
  campaign's S2 instance IS the `(e₁,f₁,h)=(2,1,1), D″=4, T₂=2λ, μ₂=2` frame blueprint `C.09`'s
  TEETH section names as `EFF.HE6R1.18`'s audited regression instance
  (`blueprint/CHAP-C_tower_grammar.md:855,951`); `λ = u₂/ℓ = 5/2` gives `T₂ = 2λ = 5`, the same
  numeral by an independent route.
* `seam_s2Tower_intCast` / `seam_s2Tower_nonneg` / `seam_s2Tower_natAvatar` — the integer/
  natural dictionary the plan's row NP-4 asks for, in the same shape as `C130th`'s
  `thresholdZ_eq_natCast`/`thresholdZ_nonneg`/`thresholdNat_unique`: `(seam : ℤ) = 5`,
  `0 ≤ (seam : ℤ)`, and `5` is the unique `ℕ` avatar.
* `ell_mul_seam_s2Tower` / `ell_mul_seam_s2Tower_via_seam_mul` — the **companion value in
  chapter C's internal `ℓ`-cleared height convention** (`dvSupp`/`dv2Hgt`): `ℓ · seam = 10`,
  proved twice (direct computation, and via the general `LevelDatum.seam_mul` theorem as a
  cross-check).

## The one honest open question (not resolved here, by design)

Chapter C uses TWO normalizations for level-2 quantities: the source's own rational-cleared one
(giving `seam = 5`) and an internal `ℓ`-multiplied height convention (`dvSupp`/`dv2Hgt`, giving
`ℓ·seam = 10`). **Which of the two a future, ambient-split-corrected `NodePointSource.
thresholdZ 2`/`pointHgt` should use is a normalization-convention design question for whichever
node builds `pointHgt` concretely** (`NP-0`, itself blocked on `SF-2`/`NV-6` per the plan) — not
something this node decides. Both numerals are proved and on record so that node does not have
to invent one under time pressure; this node does not pick a winner, and does not construct or
claim any `NodePointSource`/`CanonicalThresholdAt` instance.

## NP-5 (window inequalities)

**Not attempted.** NP-5 needs `S.pointHgt`/`S.point_exists` (NP-0) and the slot-value
dictionary (NP-2), neither landed. Out of scope once the level-1 threshold turned out to have
no formula and the level-2 threshold's consumer (`pointHgt`) does not exist yet.

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130np4.lean
```

Exit 0, zero errors/warnings. `#print axioms` for all seven new declarations prints exactly
`[propext, Classical.choice, Quot.sound]` (Lean core only).
