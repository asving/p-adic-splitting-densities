/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134p1d

/-!
# Uniformity.ChapC.C134f13a — `[F13A 2026-08-28]`: F1.3 signed assembly; F1.4–F1.6 attempted

**[F13A 2026-08-28]** (`runs/wave-c/verdict_DV2G.md`'s Part 7, closed by `verdict_P1D.md`'s
P1 + `verdict_A22E.md`'s A-C.22): DV2G's three named premises for the SIGNED F1.3
(`dv2Supp_translation`, NODE C.37) are now all discharged — **(P1)**
`C134p1d.isMuKey_of_isTestKey`, **(P2)** `C134p1.block_complement_not_muDvd`, **(P3)** the
engine-honest floor `ℓ₂ * (L.ℓ * L.seam) < u₂` (A-C.22 re-signed at C.37/C.38/C.39/C.64).
This file assembles them against the carrier `C134dv2g.dv2Supp_translation_of_muKey`.

## The one extra binder delta (the F1.1/F1.2/F1.8 precedent, `C134cfs.lean`'s header)

Every engine step used here (`isMuKey_of_isTestKey`, `block_complement_not_muDvd`, the
carrier itself) additionally requires `hh : 0 < F.h` — the standing frame-nondegeneracy
hypothesis (`h = 0` is a formally-admitted degenerate `KeyFrame`, C01.lean:84-86, not
excluded by `LevelDatum.hκ`; the corpus frame has `1 ≤ h`).  None of the four signed
C.37/C.38/C.39/C.64 binder lists carry it.  Per the established F1.1 (`C134cfs.lean`
header) / P1D convention, this is recorded as ONE binder delta, not a blocked premise:
the theorem below is named identically to the signed `dv2Supp_translation`, conclusion
byte-as-is, with `hh` added.

## What lands

* Part 1 — `dvSupp_testKey`, a PUBLIC re-derivation of `C131aa`'s `private dvSupp_testKey`
  (the test key's own level grade `dvSupp F Ψ L.u L.ℓ = L.ℓ * L.seam`), from
  `isTestKey_isDvPure` + `dvSideMin_eq_zero_of_isDvPure` + `dvSupp_eq_of_dvOnSide` alone —
  needed because the private lemma cannot cross files.
* Part 2 — **F1.3 SIGNED, modulo the `hh` delta**: `dv2Supp_translation`, NODE C.37's
  conclusion byte-as-is.
* Part 3 — F1.4/F1.5/F1.6 assessment against tonight's landed banks
  (`C133mh1`/`C133mh8`/`C133mh9`): still BLOCKED-BECAUSE — see the record at the end of
  the file. The MH series is LEVEL-1 machinery (`dvSupp`/`dvResPoly` at the frame's own
  `(F, u, ℓ)`), already fully consumed by DV2G (via `C133mh3`) to build the level-2
  SUPPORT engine (subgoals (i)/(ii)); it supplies nothing further for the level-2
  RESIDUAL-POLYNOMIAL per-slot telescope F1.4/F1.5 need, or the level-2 minimizer
  EQUALITY F1.6 needs beyond what Part 4/5 of `C134dv2g` already give.

## Status

Sorry-free.  Axiom footprint: Lean core `{propext, Classical.choice, Quot.sound}` on
`dvSupp_testKey`; `dv2Supp_translation` additionally inherits the allowlisted
`Uniformity.Density.Tower.exists_dvDissection` (through `C134p1d` → `C134p1` →
`C134f12c` → `C134cfs.blockFactor_spec`, the sole dissection occurrence).  No new axiom;
no landed file edited; no `sorry`.

**Flagged for human review** (parent CLAUDE.md trust boundary — the `hh` binder delta is
a NEW recorded fact about the signed statements, following the established F1.1/F1.2/F1.8
precedent, not a fresh finding): `dv2Supp_translation`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C134f13a

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C134dv2g

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 1 — the test key's own level grade, publicly

`C131aa.dvSupp_testKey` proves exactly this but is `private` there (file-scoped), so it
cannot be imported. Re-derived here from public API only: `isTestKey_isDvPure`
(`C131aa`, public) pins the side-min at `0`; the value there reads off `IsTestKey`'s
own clause 5 at `t = 0`. -/

private theorem dvHgt_zero_of_testKey (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O}
    (hΨ : IsTestKey L Ψ) :
    dvHgt F Ψ 0 = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
  have hzero := (hΨ.2.2.2.2 0 L.hrdeg).2 L.hr0
  have hzero' : F.stageHeight (dev F.key Ψ 0) = ((L.r.natDegree * L.u : ℕ) : ℕ∞) := by
    simpa using hzero.1
  rw [dvHgt, hzero']

/-- The seam grade of a test key, PUBLICLY: `dvSupp F Ψ L.u L.ℓ = L.ℓ * L.seam` (the
public twin of `C131aa`'s private `dvSupp_testKey`). -/
theorem dvSupp_testKey (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    dvSupp F Ψ L.u L.ℓ = ((L.ℓ * L.seam : ℕ) : ℕ∞) := by
  have hpure := isTestKey_isDvPure L hΨ
  have hne : (dvSideSet F Ψ L.u L.ℓ).Nonempty := ⟨0, hpure.1⟩
  have hmin0 : dvSideMin F Ψ L.u L.ℓ hne = 0 :=
    dvSideMin_eq_zero_of_isDvPure hpure hne
  have hon : DvOnSide F Ψ L.u L.ℓ 0 :=
    hmin0 ▸ Uniformity.Density.Tower.C130nv2.dvOnSide_dvSideMin F Ψ L.u L.ℓ hne
  have hHgt0 := dvHgt_zero_of_testKey L hΨ
  have hval := Uniformity.Density.Tower.C130nv2.dvSupp_eq_of_dvOnSide hHgt0 hon
  rw [hval, LevelDatum.seam]
  congr 1

/-! ## Part 2 — F1.3 SIGNED (NODE C.37), modulo the `hh` binder delta -/

/-- ★ **F1.3 signed** — NODE C.37's `dv2Supp_translation`
(`leanspec/Leanspec/ChapC.lean:1651-1657`, conclusion byte-as-is; the A-C.22
engine-honest floor `hseam`), from `BlockContext` + `IsTestKey`, with the one recorded
binder delta `hh : 0 < F.h` (see the file header; the F1.1/F1.2/F1.8 precedent).
Assembled from `C134p1d.isMuKey_of_isTestKey` (P1), `dvSupp_testKey` above (the key
grade `KΨ = L.ℓ * L.seam`), `C134p1.block_complement_not_muDvd` (P2), and the carrier
`C134dv2g.dv2Supp_translation_of_muKey`.  The signed hypothesis `hnd` (`Ψ` excludes the
`level2_peel`/C.40 jump case) is carried but unused: `block_complement_not_muDvd` proves
the carrier's `hcomp` UNCONDITIONALLY from `hΨ`/`hctx` alone, so the proof below is
strictly stronger than the signed statement requires — `hnd` is kept only so the
signature matches C.37 verbatim. -/
theorem dv2Supp_translation (L : LevelDatum F H₀ hpin) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hh : 0 < F.h)
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (_hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂) :
    dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞) := by
  have hkeyμ : IsMuKey L Ψ := C134p1d.isMuKey_of_isTestKey L hπ hh hΨ
  have hKΨ : dvSupp F Ψ L.u L.ℓ = ((L.ℓ * L.seam : ℕ) : ℕ∞) := dvSupp_testKey L hΨ
  have hcomp : ¬ MuDvd L Ψ (f /ₘ blockFactor L f) :=
    C134p1.block_complement_not_muDvd L hπ hh hΨ hctx
  exact dv2Supp_translation_of_muKey L hπ hh hctx hkeyμ hKΨ hℓ₂ hseam hcomp

/-! ## Part 3 — F1.4–F1.6 re-assessed against tonight's landed banks: still BLOCKED-BECAUSE

The charge asked whether `C133mh1`'s TW-δ and `C133mh8`/`C133mh9`'s window/graded-limit
machinery (landed since `verdict_DV2G.md` was written) now supply the "per-slot `dv2Res`
cocycle telescope" DV2G's Part 7 named. They do not, and the reason is structural, not a
missing search: `C133mh1`/`C133mh3`/`C133mh8`/`C133mh9` are LEVEL-1 machinery — Theorem M
(`dvSupp_mul`, `dvSideMin_mul`, `dvResPoly_mul_gen`) and Theorem A's existence engine, all
stated over the FRAME's own `(F, u, ℓ)` pair. `C134dv2g` already spent this engine in
full: `dv2ResSurv_of_muKey` (subgoal (i)) fires `C133mh3.dvSupp_mul` AT the level datum's
inner pair `(L.u, L.ℓ)` to get the level-2 SUPPORT survival, and `dv2Pin_mul_complement`
(subgoal (ii)) is built from it. Nothing among MH.1/MH.3/MH.8/MH.9 operates on `dv2ResPoly`
or `dv2Res` (level-2 objects: residues over `AdjoinRoot L.r`, built from `dev Ψ f j`
digits of the LEVEL-2 key `Ψ`, one grading level above what any MH-series file reaches).

* **F1.4 `dv2ResPoly_scalar`, F1.5 `dv2ResPoly_radical_eq`** — both need a level-2 residue
  PRODUCT law: `dv2Res L (dev Ψ (A*B) 0)` in terms of `dv2Res L A`, `dv2Res L B`, at
  digit-bounded `A, B` — the exact level-2 twin of `C133mh3.dvResPoly_mul_gen` (Theorem M
  clause 3), which itself needed the whole MH.1 (TW-δ + twist product law) → MH.3
  (mixed residual law assembly) pipeline to reach its CLEAN product form. `Dv2ResSurv`
  (subgoal (i)) packages only the HEIGHT survival (`dv2Hgt`-valued, `ℕ∞`) of slots 0/1 of
  `dev Ψ (A*B) J` — it says nothing about the RESIDUE (`AdjoinRoot L.r`-valued) at those
  slots. C.39's own conclusion shape (`γg L f * root^cocycle`, no clean product) shows the
  level-2 story is presently at the MH.1-era stage (`M1SlotCarryLawStatement`'s
  uncancelled cocycle form), not the MH.3-era resolved form `dvResPoly_mul_gen` reaches —
  i.e. F1.4/F1.5 are asking for the level-2 analogue of the ENTIRE MH.1→MH.3 pipeline
  (multiple files, ~600+ lines at level 1), not a lemma reachable by re-using it.
  **Missing premise, precisely**: a `Dv2ResSurv`-shaped hypothesis at the RESIDUE level —
  `∀ A B, dv2Res L (dev Ψ (A*B) 0) = dv2Res L A * dv2Res L B * (unit factor)` (slot 0) plus
  a slot-1 floor — discharged frame-generically. Not attempted here: out of the
  "combine landed pieces" scope of this unit.
* **F1.6 `mult₂_readable`** — needs `dv2SideMin`/`dv2SideDeg` EQUALITY between `f` and
  `blockFactor L f`. The landed `≤` half (`C132nv2.dv2SideMin_mul_le`) DOES combine with
  F1.3's collapse (Part 4/5 of `C134dv2g`) to give ONE direction for free: since the
  complement `g := f /ₘ blockFactor L f` has `dv2SideMin L Ψ g u₂ ℓ₂ = 0` (derivable —
  `dv2Supp_collapse_of_not_muDvd`'s own `≥`-proof is STRICT at every `j ≥ 1`, by the
  fence's slack `u₂ - ℓ₂·KΨ ≥ 1`, so `g`'s side set is the SINGLETON `{0}`, not merely
  nonempty), `dv2SideMin_mul_le` gives `dv2SideMin(f) ≤ dv2SideMin(blockFactor L f) + 0`.
  The REVERSE inequality is the genuine gap: it needs a per-slot (not just per-inf) lower
  bound `dv2Pin L Ψ f j ≥ dv2Pin L Ψ (blockFactor L f) j + dvSupp F g L.u L.ℓ` at EVERY
  `j` (not only the two factors' own minimizers, which is all `dv2Supp_mul_eq_add_of_endpoint_le`
  / `dv2SideMin_mul_le`'s endpoint-only proofs supply) — exactly Theorem M clause 2's
  level-2 twin (`dv2SideMin_mul` as an EQUALITY), which DV2G's header already named as
  "a full MH-scale lift one level up." No landed piece, MH-series or otherwise, supplies
  a per-slot (rather than per-endpoint) product bound at level two; re-confirmed here.
  **Missing premise, precisely**: `dv2SideMin_mul` as an equality (or, sufficient for
  this specific application, the per-slot bound above for a side-length-0 second factor).

Per the F12C/DV2G discipline, no signed name for F1.4/F1.5/F1.6 is declared (partial
progress on one direction of F1.6 is recorded in prose above, not as a named lemma, since
it does not close the row). -/

end Uniformity.Density.Tower.C134f13a

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134f13a.dvSupp_testKey
#print axioms Uniformity.Density.Tower.C134f13a.dv2Supp_translation

end AxCheck
