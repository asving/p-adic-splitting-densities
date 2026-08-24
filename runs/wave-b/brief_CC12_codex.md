# Unit CC-12 (codex) — transports/views: the four live-only view equalities

You are a Lean 4 unit in the p-adic-splitting-densities campaign, executing node CC-12 of
the chain-realization carrier plan (docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md §10
row CC-12: "Land four live-only view equalities and cross-universe transports; add
off-range lint"). Repo root: /data/users/asvin/math-and-lean/p-adic-splitting-densities.
Lean project: leanfinal/ (mathlib v4.31.0, built; `lake env lean <file>` from leanfinal/;
module builds like `lake build Uniformity.ChapC.C130cr` fine; NEVER bare `lake build`).

## Read first
1. docs/PROJECT_STATE.md; the design doc §4.4 (the assembled layer — where the four view
   equalities live: freeze layer C.130j/k's live-only views + shared export witness) and
   §10 row CC-12; the freeze doc's C.130j/k layer text
   (docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md) + runs/wave-b/verdict_F3.md.
2. Landed inputs (REUSE): C130st.lean (CC-5 stage carrier), C130in.lean (CC-8 RealizedInput
   + inputBlock views), C130cr.lean (CC-10 canonical read + kerGaugeEquiv Type-uG export),
   C130ar.lean (CC-11 arena family + towerRead/peelUnit), C130a.lean (ArisingCore),
   C130k/C130tr/C130pt as needed. Read verdict_CC10/CC11.md for their supply notes.

## Your node
Land the four LIVE-ONLY view equalities tying the layers (per the freeze's C.130k: the
stage view, the input-block view, the canonical-read view, and the arena view all read the
SAME arising witness on the live range), the cross-universe (ULift) transports, and the
off-range lint (explicit lemmas that nothing is asserted off the live range — the
non-swallowing discipline). Do NOT state any canonical/arena read agreement (the two reads
stay separate; the views tie each read to the SHARED WITNESS, not to each other).

## Deliverable
ONE new file leanfinal/Uniformity/ChapC/C130vw.lean (house style; docstring "chain-carrier
node CC-12"). `#print axioms` per declaration — all Lean-core.

## Rules
NO sorry/new axioms/unsafe/read-identification. `rg` names first. Do NOT touch roll-ups,
leanspec/, or other units' files (in flight: C131y.lean [codex], C99gt.lean, C131ae.lean,
C78adj.lean, and unit AE7 editing leanspec ChapE + a new ChapE/E57s.lean). Do NOT git
commit. Write runs/wave-b/verdict_CC12.md (LANDED/SUPPLY/BLOCKED, declarations,
verification command).
