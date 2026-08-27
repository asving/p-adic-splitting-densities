# Verdict FGCW — GC-13 wiring at the realized S2 exports (FDTB's blocker, adjudicated)

Unit FGCW (Fable), 2026-08-27.  Landed: `leanfinal/Uniformity/ChapI/IFC2.lean` (new;
imports IFC1 + C130sg; no existing file touched) + the decomposer blueprint
`docs/in-progress/GC13_WIRING_2026-08-27.md`.  Build: scoped `lake build
Uniformity.ChapI.IFC1 Uniformity.ChapC.C130sg` then `lake env lean
Uniformity/ChapI/IFC2.lean` — clean, zero sorry, zero new axiom.

## (2) What hread/htheta REDUCE TO at the concrete S2 instance — the answer

The pair is NOT symmetric.  Genre split:

* **htheta = COMPUTATION, now closed at `s = 1`.**  `A.theta q 1 =
  res(n̂(1·q)·(n̂(q)¹)⁻¹) = res(1) = 1` for EVERY arena (`theta_one`, pure D.04/D.08);
  and the μ₃ `thetaRatioCleared 1` has numerator = denominator (`n̂(u')¹ = n̂(1·u')`),
  hence `= 1` since the `d = 1` read is nonzero by A-C.21's landed supplies.  So IFC1's
  `htheta` is a THEOREM for every arena and every receiver (`s2Mu3_htheta_discharged`) —
  including the witness's own exported arena family (universal ⇒ D-D12-clean).  The μ₃
  tooth is re-landed on `hread` alone (`s2Mu3_gentowWWindow_of_hread`).
* **hread = OPEN-DICT-3/4 CONTENT, and REFUTED at the landed exports.**  The μ₃ FGMN read
  is the UNIT `1` of the 2-element terminal field (`s2Mu3_read_eq_one`), receivers
  preserve it, so `hread ↔ towerRead(ladder point) = 1` (`s2Mu3_hread_iff`).  But the
  landed `s2SplitNode` exports NP-8's FREE convenience choice `towerRead ≡ 0`
  (`s2_towerReadFamily_zero`), so `hread` is FALSE at the landed witness's OWN exports —
  every level, receiver, lattice point (`s2_hread_refuted_at_landed_exports`); the full
  D.44 `GentowW` fails there too (`s2_gentowW_false_at_landed_exports`).  The equally
  admissible read `≡ 1` satisfies FULL `GentowW` (`s2_gentowW_of_read_one`, hard
  D-D12-fenced: adjudication artifact, NOT supply).  Both truth values realized by
  admissible node data ⇒ the landed laws UNDERDETERMINE GC-13 ⇒ the wiring is a missing
  source-faithful LAW (FIELDLIST §8 items 3–4; D.44's GC-13 note
  `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`), not a missing proof.  BLOCKED-BECAUSE: no signed
  statement ties `towerRead` to the FGMN residual read; blueprint delivered (GCW-0..6,
  with the placement fork P1/P2/P3 and the depth-≥4 tension record GCW-6: a zero-read
  deep witness would refute `DeepGentowSupplier` outright).

## (3) Landed in IFC2.lean (node [FGCW, 2026-08-27]) — all proved, Lean-core

§0 general: `theta_one` · `theta_zero` (D.44's `s = 0` clause ≡ `R(N.n 0) = 1`) ·
`thetaRatioCleared_one` · `gentowW_false_of_read_zero` (anti-cook tooth).
§1 μ₃: `s2Mu3_read_ne_zero` · ★ `s2Mu3_read_eq_one` · `s2Mu3_thetaRatioCleared_one` ·
★★ `s2Mu3_htheta_discharged` · ★★ `s2Mu3_gentowWWindow_of_hread` · ★ `s2Mu3_hread_iff`.
§2 realized exports: ★ `s2_towerReadFamily_zero` · ★ `s2_htheta_discharged_at_realized_arena`
· ★★ `s2_hread_refuted_at_landed_exports` · ★★ `s2_gentowW_false_at_landed_exports`.
§3 (⚠ fenced): `s2_gentowW_of_read_one`.

Honesty: no swallowing — no canonical/arena read identification stated; the ϑ half
untouched; §3 carries the D-D12 fence in section header AND docstring; the `towerRead ≡ 1`
re-assembly is NOT performed (would be cooking before the law is signed — blueprint GCW-3
fence).  REVIEW FLAGS (standing queue): ALL fifteen statements are new; load-bearing
shapes = `theta_one`/`theta_zero` (arena telescope facts), `s2Mu3_hread_iff` (the reduced
wiring equation), the two refutations, and the fenced freedom half.

## Remains open

The signed wiring law (GCW-0/GCW-1: source print-read + leanspec) · general-`s` θ
dictionary (`f' ≥ 2`, GCW-4) · `s = 0`/tail supply at honest witnesses (GCW-5) ·
depth-`≥ 4` witnesses + per-level calculi · `DeepVarthetaSupplier` · CIFACE non-vacuity
teeth · `S2LevelOneThreshold`.

## AxChk footer (verbatim `lake env lean` output, 2026-08-27)

```
'Uniformity.Density.IFC2.theta_one' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.IFC2.theta_zero' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.IFC2.thetaRatioCleared_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.gentowW_false_of_read_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_read_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_read_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_thetaRatioCleared_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_htheta_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_gentowWWindow_of_hread' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2Mu3_hread_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2_towerReadFamily_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2_htheta_discharged_at_realized_arena' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.IFC2.s2_hread_refuted_at_landed_exports' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2_gentowW_false_at_landed_exports' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.IFC2.s2_gentowW_of_read_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```
