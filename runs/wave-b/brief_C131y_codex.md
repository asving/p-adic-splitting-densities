# Unit C131y (codex) — C.72 FAITHFUL BAND (`shadow_faithful_band`), dv-engine node C.131y′

You are a Lean 4 unit in the p-adic-splitting-densities campaign. Two prior Fable attempts
died to API errors before writing anything — you own this node now. Repo root:
/data/users/asvin/math-and-lean/p-adic-splitting-densities. Lean project: leanfinal/
(mathlib v4.31.0, built). Verify per-file with `lake env lean <file>` from inside
leanfinal/; module builds (e.g. `lake build Uniformity.ChapC.C131w`) fine; NEVER bare
`lake build`. Write the file INCREMENTALLY (skeleton with the statement elaborating
against `sorry`-free helper stubs is NOT allowed — instead land helper lemmas bottom-up,
verifying as you go, so partial progress survives).

## The target (SIGNED, leanspec/Leanspec/ChapC.lean ~L3366; land the theorem twin
byte-identical modulo axiom→theorem and namespace qualification)

theorem shadow_faithful_band {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂)
    {m : ℕ} (hm : m < T.theta μ₂ j)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)

## Read first
1. docs/PROJECT_STATE.md.
2. docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md §3.9 (the faithful band — the proof
   prose) + §5 row C.131y′ (deps C.22/C.25/C.38a, w′–x′).
3. Landed inputs (REUSE, never redefine), in leanfinal/Uniformity/ChapC/:
   - C131w.lean + runs/wave-b/verdict_C131w.md — `shadow_floor` (LANDED, Lean-core) + its
     two pricing ledgers `dev_coeff_paid_floor`, `dv2Hgt_dev_floor`.
   - C131v.lean — `shadow_discrepancy` (shadowDev − dev = −dev(censusOverflow)) and
     `shadowDev_eq_dev_corrected`.
   - C131t.lean — `dv2Hgt_add_eq_left_of_lt` (strict height exactness below a deeper
     summand — the height half's key).
   - C.22/C.25/C.38a for `dv2Res` stability vocabulary (`rg dv2Res leanfinal/Uniformity/ChapC/ -l`).
4. Proof shape: shadowDev = dev + discrepancy; shadow_floor's machinery prices the
   discrepancy ≥ theta > m; x′ gives dv2Hgt(shadowDev) = dv2Hgt(dev) = m; the residual
   half needs dv2Res stability under adding a strictly-higher-dv2Hgt term (prove the
   stability lemma if missing — in scope per §3.9).

## Deliverable
ONE new file leanfinal/Uniformity/ChapC/C131y.lean (house style of C64.lean; docstring
"Chapter C, NODE C.131y′ — C.72 faithful band", citing the blueprint doc). `#print axioms`
for every declaration — the headline MUST be Lean-core only (no cite; if a step forces
`fgmn_dv_exact_mul`, STOP and report BLOCKED naming the step).

## Rules
- NO `sorry`, NO new axioms, NO `unsafe`, NO statement weakening (extra hypotheses =
  BLOCKED verdict). `rg` every lemma name first. Do NOT touch roll-ups, leanspec/, or
  other units' files (in flight: C130cr.lean, C99gt.lean, C131ae.lean, ChapE/E57p.lean,
  C78adj.lean). Do NOT `git commit`.

## Final act
Write runs/wave-b/verdict_C131y.md: LANDED/SUPPLY/BLOCKED, declarations, headline
footprint verbatim, verification command.
