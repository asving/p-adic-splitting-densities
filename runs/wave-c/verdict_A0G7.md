# UNIT A0G7 — VERDICT: nodes A0G-HE + A0G-CH LANDED (`leanfinal/Uniformity/ChapI/IFCG6.lean`)

Date: 2026-08-29 (unit header tag [A0G7 2026-08-28]).  Campaign:
`docs/in-progress/A0_GENERAL_2026-08-28.md` §6 rows A0G-HE0/A0G-HE1 (merged) + A0G-CH.
File: 729 lines, sorry-free, verified per the discipline
(`lake env lean Uniformity/ChapI/IFCG6.lean`, exit 0, warnings none).
Campaign count: NINE of sixteen nodes down (Z, RP, CV, PD, RS, FP, NP, **HE, CH**).

## Gate verification (the two §6 gates, both MET — printed by the AxCheck footer)

* **A0G-CH gate ("field-free arithmetic"):** all nine CH declarations print Lean core only
  (several need only `{propext, Quot.sound}`).  No ring, no field, no cite anywhere in §2.
* **A0G-HE gate ("core plus inherited C.33 cite"):** all nine per-face HE declarations
  (`dv_multi_split`, `schema_split`, `levelDatumOfEntry*`, `hasLabel_of_block`,
  `block_natDegree_keyDeg₂`, `face_split_unique`, `validFace_singleton`,
  `realizesFaceAt_of_pure`) print Lean core ONLY.  Exactly two declarations —
  `blockFactor_realizes_face` and `context_split_face`, the ambient engine bindings —
  additionally print `Uniformity.Density.Tower.exists_dvDissection` (the allowlisted C.33
  dissection cite, inherited through `C133mh15.blockFrontier_of_context` /
  `C134csx.context_split`) and NOTHING else.  A0G-HE1's "certify (e,f), not only degrees"
  is delivered by `hasLabel_of_block` + `block_natDegree_keyDeg₂` (+ the keyDeg₂ pin on the
  entry datum): the block carries `HasLabel L` and `deg = L.keyDeg₂ · μ` with `μ` EXACTLY
  the pattern entry's multiplicity.

## A0G-CH — what landed (dedup-honest remainder)

**Dedup check performed FIRST** (per the standing lesson): IFCG5 §5 already owns the
loop-conditioned decrease (`entry_snd_lt_mass_of_ne_loop`, `childEntry_lt_mass_or_loop`,
`childSizes_lt_mass_of_ne_loop`) and the cleared quotient bound
(`two_mul_entry_snd_le_mass_of_two_le_den`).  None restated.  The remainder, all new:

| decl | content |
|---|---|
| `entry_snd_lt_mass_of_fractional` | `μ < m` on every `b ≥ 2` face, NO loop hypothesis (the row's literal statement) |
| `faceResDeg_le_mass_div_den`, `entry_snd_le_mass_div_den`, `decrease_chain_of_fractional` | §4.2's `μ ≤ d ≤ m/b < m` verbatim in exact ℕ-division form; `1 ≤ m` derived, not assumed |
| `entry_snd_lt_mass_of_key` ★ | `μ < m` for EVERY entry with H.01's key condition `2 ≤ b·D` — the sharpest unconditional decrease |
| `childEntry_lt_mass_of_key` | the same at the `IsChildEntry` surface (GC3's shape) |
| `loopFace_not_key` | the loop face carries NO key entry — with the above, the decrease/loop dichotomy is closed at the face level |
| `genreDatumOfChildEntry_μ_lt_mass` ★ | every H.01 `GenreDatum` packaged by IFCG5's constructor from a valid mass-`m` skeleton has `μ < m` (hkey is exactly what excludes the loop child) |
| `childSizes_sum_le_mass` | TOTAL recursive child mass `≤ m` (via IFCG5's `mass_conservation`) |

## A0G-HE — what landed

* `dv_multi_split` ★★ — **the n-ary Theorem A**: monic dv-pure `g` with `D′ ∣ deg g` and
  level residual `∏ Gᵢ` (pairwise-coprime monic positive-degree factors) splits as
  `g = ∏ gᵢ`, each `gᵢ` monic, dv-pure, of EXACT degree `ℓ·D′·deg Gᵢ` and EXACT ∀-pin
  residual `Gᵢ`.  Iterates `C133mh9.theoremA` down the list; the constant-coefficient
  hypotheses are DERIVED from C.26's `natDegree_dvResPoly` (nonzero residual constant term),
  not assumed.  Lean-core.
* `schema_split` ★★ — the split AT A SCHEMA: residual factors `rᵢ^{μᵢ}` along pattern
  entries `(Dᵢ, μᵢ)` with pairwise-distinct monic irreducibles (`deg rᵢ = Dᵢ`); pairwise
  coprimality of the powers DERIVED from distinctness over the stage field.  Each block
  additionally gets `ValidFace` + `RealizesFaceAt F gᵢ u (ℓ, {(Dᵢ, μᵢ)})` — discharging
  exactly the residual-factorization binding IFCG5's scoping note deferred to this node.
* `levelDatumOfEntry` (+ `_u/_ℓ/_r` simp pins + `_keyDeg₂`) — the engine-side twin of
  IFCG5's `genreDatumOfChildEntry`: an entry's residual data as a C.09 `LevelDatum`, with
  the numerator and the stage irreducible as explicit arguments (IFCG5's D4 discipline).
* `hasLabel_of_block` + `block_natDegree_keyDeg₂` — the HE1 typing: block ⟹ `HasLabel L`
  with multiplicity exactly `μ`, and `deg = keyDeg₂ · μ`.
* `face_split_unique` — `C133mh11.dv_oneSlope_split_unique` bound at the `RealizesFaceAt`
  surface: the labelled/complement split of a face-realizing polynomial is UNIQUE, so
  `schema_split`'s blocks are THE declared blocks.
* `blockFactor_realizes_face` ★ / `context_split_face` ★ (cite carriers) — the ambient
  binding: under the signed `BlockContext`, C.35's `blockFactor L f` REALIZES the
  single-entry face `(L.ℓ, {(deg L.r, mult₂ L f)})` (valid face, label, divisibility,
  positive multiplicity), and C134csx's full split `f = block · g₂ · Wf` is re-exported
  with that face clause attached.

## Design decisions (recorded in the file header, D1–D5)

D1 no new Prop wrapper for HE0 (raw `Forall₂` packaging); D2 ∃-pin hypotheses in, ∀-pin
conclusions out; D3 constant-coefficient hypotheses derived, degree positivity taken from
face validity; **D4 `theoremC_placement` enters transitively** (it is the maximality step
inside both ambient bindings; a direct re-wrap would be a hypothesis relay with no content —
per-face maximality is delivered through `face_split_unique` instead); D5 cite isolation —
only the two ambient theorems touch the cite-bearing chain, so downstream pays the C.33 cite
exactly when invoking the ambient dissection, never for schema algebra.

Private plumbing (`isKey_X`, `localFieldStageField`, `dvOnSide_of_mem'`, `exists_pin`)
re-declared byte-identical in mechanism from C133mh14/C134csx Part 0 (private there;
credited per declaration; no landed file edited).

## A0G-GC readiness (the requested honest assessment)

GC is **not yet startable as a single unit**, but its four sub-rows are now unevenly fed.
**GC3 (recursive soundness) is essentially fully provisioned at the arithmetic level**: the
decrease tooth is closed (every hkey-packageable child has `μ < m`, fractional faces
decrease unconditionally, the loop face carries no key entry, IFCG5 pins the loop as the
sole full-mass skeleton, and total child mass is bounded), and the per-face soundness
surface exists (`schema_split` + `hasLabel_of_block` certify exact degrees/residuals/labels;
`blockFactor_realizes_face` transports the ambient engine output onto a skeleton face).
**GC2 (disjointness)** has its residual-level ingredient (`face_split_unique`), but its
parameter-level half needs **A0G-NP1 (gap/slope parameters + Presburger regions), which is
NOT landed** — NP1 must precede GC.  **GC0/GC1 (classifier + exhaustion, the stop line)
remain untouched**: nothing yet produces, from an arbitrary recentred cluster input, the
data `schema_split` consumes.  Two honest observations for the GC planner: (a) the
hypothesis package of `schema_split` now IS the formal spec of GC1's required output —
distinct monic irreducibles matching a pattern, purity, and the ∃-pin residual equation —
so GC1's target is fully pinned; (b) a useful pre-GC bridge unit is now nearly mechanical:
compose the C.33 dissection (per-slope factors) with per-slope `schema_split` and the stage
field's UFD factorization of `dvResPoly` (existence of the `rᵢ^{μᵢ}` factorization is free
over a field, and within a face the pattern is a MULTISET, so no canonicity obstruction
arises there) to get a whole-skeleton existence theorem "every context realizes SOME valid
skeleton" — i.e. `RealizesSkeletonAt` inhabited.  What that bridge still would NOT give is
GC1's real content: the recentring walk from a raw coefficient vector to its pure stages,
the canonicity/measurability of the assignment, and the NP1 parameter bookkeeping.  Next
node recommendation: **A0G-NP1 first, then the dissection→skeleton bridge, then GC0**.
