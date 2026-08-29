# UNIT BRIDGE — VERDICT: the dissection-skeleton bridge LANDED (`leanfinal/Uniformity/ChapI/IFCG8.lean`)

Date: 2026-08-29. Charge: `runs/wave-c/verdict_A0G7.md`'s GC-readiness note — compose the
C.33 dissection (`exists_dvDissection`) with per-slope `schema_split`-style residual
factorization and the stage field's UFD factorization to produce a whole-skeleton existence
theorem, "every context realizes SOME valid skeleton" (`RealizesSkeletonAt` inhabited) — GC0's
doorstep. File: 446 lines, sorry-free, verified per the discipline (`lake env lean
Uniformity/ChapI/IFCG8.lean`, exit 0, zero warnings).

## What landed (all four declarations, AxCheck footer printed and checked)

* **§1 `exists_sorted_list_of_finset`** — pure `ℕ` combinatorics: any `Finset (ℕ × ℕ)` with
  positive second coordinates and pairwise cross-multiplied-distinct elements (exactly
  `DvDissection.hdistinct`'s shape) lists into strictly increasing cross-multiplied order.
  Strong induction on cardinality peeling the ℚ-minimal element (`Finset.exists_min_image`);
  the chain property lands in the exact `Fin`-`.get`-indexed form IFCG7's `SlopeChain`
  consumes. Lean-core.
* **§2 `exists_ers_of_monic`** — every monic polynomial over a field groups into
  `IFCG6.schema_split`'s `ers` shape (pairwise-distinct monic irreducible factors with
  explicit `(degree, multiplicity)` labels reconstructing the polynomial exactly), via
  mathlib's `UniqueFactorizationMonoid.normalizedFactors` + `Multiset.count` grouping — THE
  "UFD residual factorization (mathlib)" leg the charge names. No new axiom; existence only
  (no canonicity claim, matching the A0G7 verdict's "no canonicity obstruction" note — face
  patterns are multisets). Lean-core.
* **§3 `exists_face_of_dissection_slope`** ★ — the per-slope face: a C.33 dissection slope
  `p = (u, ℓ) ∈ D.slopes` yields an `IFCG5.FaceShape (ℓ, σ)` (`σ` the §2 UFD-grouped pattern
  of the slope factor's level residual `dvResPoly`) with `ValidFace (ℓ, σ)`,
  `RealizesFaceAt F (D.factor p) u (ℓ, σ)`, and the exact degree identity
  `D'·faceLen(ℓ,σ) = deg(D.factor p)` that §4's mass bookkeeping consumes. Built from
  `C133mh4.dvResPoly_monic_of_isDvPure` (M-monic residual) + `C26.natDegree_dvResPoly` +
  `IFCG6.realizesFaceAt_of_pure`/`validFace_singleton`-style assembly + §2. Lean-core — it
  takes an already-constructed `D : DvDissection F f` as an argument and never invokes
  `exists_dvDissection` itself.
* **§4 `exists_realizesSkeletonAt_of_dissection`** ★★ — **THE BRIDGE**. For a monic `f` with
  `D' ∣ deg f` whose C.33 dissection has a trivial below-floor remainder
  (`hbelow1 : ∀ D, D.below = 1`), `RealizesSkeletonAt F S num blocks` is inhabited at mass
  `m = deg f / D'` — i.e. an actual `S : ClusterSkeleton m` from IFCG5's finite
  `clusterSkeletonFinset m`, with matching numerators and blocks, is produced. Assembled
  exactly as charged: `exists_dvDissection` (obtains `D`) → §1 (sorts `D.slopes`) → §3 per
  sorted slope (choice over the `Fin`-indexed family) → the mass law recovered by summing §3's
  degree identity against `Polynomial.natDegree_prod_of_monic` on `D.hprod`'s
  `f = below · ∏ factor`, cancelling `D'` via `hm`. **Footprint: Lean core + EXACTLY
  `Uniformity.Density.Tower.exists_dvDissection`** — the allowlisted C.33 cite, and nothing
  else (verified: `#print axioms` on all four declarations; only §4 carries the cite).

## The honest scope boundary (recorded, per the charge's BLOCKED-BECAUSE instruction)

`exists_dvDissection` alone does **not** pin `D.below` (the below-floor remainder): C.33's
existence axiom says nothing about it for a general monic `f`. §4 therefore takes
`hbelow1 : ∀ D : DvDissection F f, D.below = 1` as an **explicit hypothesis** — this is the one
genuinely missing leg. It is exactly true for a "clean" recentred size-`m` cluster (all `m`
roots at positive valuation ⟹ no below-floor mass), but *proving that from a raw coefficient
vector* is GC1's real content (the recentring walk + canonicity/measurability the A0G7 verdict
flagged as outside this bridge's scope: "What that bridge still would NOT give is GC1's real
content… and the NP1 parameter bookkeeping"). So: **§1–§3 are unconditional**; **§4 is
conditional on `hbelow1`**, honestly stated as a hypothesis rather than smuggled in. This
hypothesis is GC0/GC1's opening discharge target.

## Design notes

* Reused `IFCG6.realizesFaceAt_of_pure`/`validFace_singleton` and `IFCG7`'s
  `slopesOrdered_iff_chain` directly — no restatement of landed material (dedup checked).
* Re-declared, byte-identical in mechanism and explicitly credited, two small private helpers
  already private-and-unreachable elsewhere: `isKey_X'`/`localFieldStageField'` (from
  `C133mh14.lean`/`IFCG6.lean`'s Part 0, needed for the stage field's `Field` instance) and
  `exists_pin_of_nonempty` (the same small pin-existence fact IFCG6/IFCG7 each independently
  re-derive off the public `dvOnSide_of_mem_dvSideSet`). Neither source file touched.
* Two small fresh private list lemmas (`list_prod_monic''`, `list_prod_natDegree_sum`,
  `list_mul_sum`) — `List.prod`-shaped analogues of mathlib's `Multiset`/`Finset` versions,
  needed because `exists_ers_of_monic`'s conclusion is `List`-shaped.
* `σ`'s pattern is the UFD grouping of the slope factor's OWN level residual (not merely a
  dummy single-entry placeholder) — chosen deliberately for downstream faithfulness (GC1 will
  want the real residual pattern, not a placeholder), even though the coarser
  `RealizesFaceAt`/`ValidFace` predicates alone would not have forced this choice.

## GC-readiness update

The bridge closes the gap A0G7 flagged as "nearly mechanical" — it now IS landed, modulo the
one honest `hbelow1` hypothesis. Recommended next node: **GC1** discharges `hbelow1` (and the
rest of the recentring-walk/canonicity content) for the coefficient-box's recentred clusters,
then composes with this file's §4 to get the unconditional exhaustion half of GC0/GC1's stop
line.
