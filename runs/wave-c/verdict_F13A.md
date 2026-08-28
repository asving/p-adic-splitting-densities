# UNIT F13A verdict — F1.3 SIGNED LANDED (modulo one recorded binder delta); F1.4–F1.6 remain BLOCKED-BECAUSE (2026-08-28)

## Headline

**F1.3 (`dv2Supp_translation`, NODE C.37) is now assembled and LANDED**, conclusion
byte-as-is, in the new file `leanfinal/Uniformity/ChapC/C134f13a.lean` (185 lines).
`verdict_DV2G.md`'s three named premises are all discharged tonight: **(P1)**
`C134p1d.isMuKey_of_isTestKey`, **(P2)** `C134p1.block_complement_not_muDvd`, **(P3)**
A-C.22's engine-honest floor. One further binder delta was found and recorded (not a
blocker): `hh : 0 < F.h`, following the exact precedent `C134cfs.lean`'s header already
established for F1.1/F1.2/F1.8. **F1.4, F1.5, F1.6 remain BLOCKED-BECAUSE** — reassessed
against `C133mh1`/`C133mh8`/`C133mh9` per the charge, and confirmed structurally
unreachable from that bank (see rows below for the exact missing lemma each needs).

Verified: `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134f13a.lean`
— exit 0, zero errors, zero warnings, zero `sorry`. Also scoped-built via
`lake build Uniformity.ChapC.C134f13a` (8782/8782 jobs, success) after adding the file to
the `Uniformity/ChapC.lean` aggregate import list (mechanical plumbing, alphabetical
insertion between `C134f12c` and `C134frt`; the only other file touched).

## Row table

| row | node | status | mechanism / exact missing subgoal |
|---|---|---|---|
| **F1.3** | C.37 `dv2Supp_translation` | **LANDED** (`dv2Supp_translation`, conclusion byte-as-is) | `C134p1d.isMuKey_of_isTestKey` (P1) + `dvSupp_testKey` (this file's Part 1, the test key's grade `KΨ = L.ℓ*L.seam`, re-derived PUBLICLY since `C131aa`'s own `dvSupp_testKey` is `private`) + `C134p1.block_complement_not_muDvd` (P2) + A-C.22's floor (P3), fired through `C134dv2g.dv2Supp_translation_of_muKey`. **Binder delta**: `hh : 0 < F.h`, recorded per the F1.1/F1.2/F1.8 precedent (`C134cfs.lean` header) — the signed C.37/C.38/C.39/C.64 binder lists omit it, but every engine step needs it; `h=0` is a formally-admitted degenerate `KeyFrame` (C01.lean:84–86) not excluded by `LevelDatum.hκ`. The signed `hnd : ¬ Ψ ∣ blockFactor L f` is carried but PROVABLY UNUSED — `block_complement_not_muDvd` supplies the carrier's `hcomp` unconditionally, so the landed proof is strictly stronger than the signed statement demands. |
| **F1.4** | C.39 `dv2ResPoly_scalar` | **BLOCKED-BECAUSE** | Needs a level-2 residue PRODUCT law — `dv2Res L (dev Ψ (A*B) 0)` in terms of `dv2Res L A`, `dv2Res L B` (values in `AdjoinRoot L.r`) — the exact level-2 twin of `C133mh3.dvResPoly_mul_gen` (Theorem M clause 3). `Dv2ResSurv` (DV2G's subgoal (i), consumed here) packages only the HEIGHT (`ℕ∞`-valued `dv2Hgt`) survival of slots 0/1, nothing about the residue. C.39's own conclusion (`γg L f * root^cocycle * dv2ResPoly(blockFactor)`) shows the level-2 story sits at the MH.1-era stage (uncancelled cocycle, `M1SlotCarryLawStatement`'s shape) — F1.4 is asking for the level-2 analogue of the WHOLE MH.1→MH.3 pipeline, not a reusable lemma. |
| **F1.5** | C.38 `dv2ResPoly_radical_eq` | **BLOCKED-BECAUSE** | A unit-scalar cancellation applied to F1.4's identity (blocked) plus F1.6's side-degree equality (blocked) — inherits both gaps, no independent route. |
| **F1.6** | C.64 `mult₂_readable` | **BLOCKED-BECAUSE** (one direction now free, recorded in prose only) | Needs `dv2SideMin`/`dv2SideDeg` EQUALITY between `f` and `blockFactor L f`. The `≤` direction now falls out for free: the complement `g := f /ₘ blockFactor L f` has `dv2SideSet L Ψ g u₂ ℓ₂ = {0}` (the SINGLETON, not merely nonempty — `dv2Supp_collapse_of_not_muDvd`'s own `≥`-proof is STRICT at every `j ≥ 1` by the fence's slack), so `C132nv2.dv2SideMin_mul_le` gives `dv2SideMin(f) ≤ dv2SideMin(blockFactor L f) + 0`. The REVERSE direction is the genuine gap: a PER-SLOT (not just per-endpoint) bound `dv2Pin L Ψ f j ≥ dv2Pin L Ψ (blockFactor L f) j + dvSupp F g L.u L.ℓ` at every `j`, i.e. `dv2SideMin_mul` as an EQUALITY — exactly Theorem M clause 2's level-2 twin, which DV2G's own header already flagged as "a full MH-scale lift one level up." No landed lemma (MH-series or otherwise) supplies a per-slot (rather than per-endpoint) product bound at level two. |

## Why `C133mh1`/`C133mh8`/`C133mh9` don't move F1.4–F1.6 (the charge's specific question)

Structural, not a missed search: MH.1/MH.3/MH.8/MH.9 are **level-1** machinery — Theorem M
(`dvSupp_mul`, `dvSideMin_mul`, `dvResPoly_mul_gen`) and Theorem A's existence engine,
stated over the frame's own `(F, u, ℓ)`. `C134dv2g` already spent this engine in full:
`dv2ResSurv_of_muKey` (subgoal (i)) fires `C133mh3.dvSupp_mul` AT the level datum's inner
pair `(L.u, L.ℓ)`, and `dv2Pin_mul_complement` (subgoal (ii)) is built from it. Nothing in
MH.1/MH.3/MH.8/MH.9 operates on `dv2ResPoly`/`dv2Res` — level-2 objects (residues over
`AdjoinRoot L.r`, built from `dev Ψ f j` digits of the level-2 key `Ψ`) one grading level
above anything the MH series reaches. MH.8/MH.9's window/graded-limit content
(`exists_dvGradedLimit`, Theorem A) is existence machinery for level-1 Hensel lifts,
orthogonal to both F1.4/F1.5's residue-product need and F1.6's minimizer-equality need.

## Footprint record

* `C134f13a.dvSupp_testKey` — `[propext, Classical.choice, Quot.sound]` (Lean core only).
* `C134f13a.dv2Supp_translation` (F1.3) — `[propext, Classical.choice, Quot.sound,
  Uniformity.Density.Tower.exists_dvDissection]` (the one allowlisted C.33 cite,
  inherited through `C134p1d` → `C134p1` → `C134f12c` → `C134cfs.blockFactor_spec`).

No `sorry`; no new axiom; no landed `.lean` or leanspec file edited (the only other file
touched, `leanfinal/Uniformity/ChapC.lean`, is the mechanical aggregate import list — one
line added, alphabetically placed, matching how every prior C134-series unit registered
itself there). No git operations performed.

## Statements flagged for human review (trust boundary — new content)

* `dvSupp_testKey` (this file) — re-derivation of `C131aa`'s private lemma from public
  API; same content, different proof route (via `isTestKey_isDvPure` +
  `dvSideMin_eq_zero_of_isDvPure` + `dvSupp_eq_of_dvOnSide`), so this is a proof-route
  flag, not a new statement.
* `dv2Supp_translation` (this file) — the `hh` binder-delta convention applied to F1.3,
  following the F1.1/F1.2/F1.8 precedent already accepted in `C134cfs.lean`'s header.
