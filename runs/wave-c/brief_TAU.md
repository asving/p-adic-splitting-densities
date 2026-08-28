# UNIT TAU — LVS-CANONICAL-TAU-EXPORT: the source-faithful tower export (the vartheta live leg's one open lemma)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

LVS (runs/wave-c/verdict_LVS.md — READ FIRST, especially the OPEN-LEMMA and BLOCKED rows;
math record in the [LVS 2026-08-28] section of docs/in-progress/LADDER_SUPPLY_2026-08-27.md)
reduced the capstone ladder's live vartheta leg to ONE open lemma:

**LVS-CANONICAL-TAU-EXPORT** — inhabit `LVSProbe.VarthetaTauLevelExport`
(leanfinal/scratch/LVS_probe.lean:72-91: tau kernel membership + embedded-Kt residue
values, attached to explicit X/eG and the exact family view) for every explicit arising
witness and every live 3 ≤ j < core.r.

Known walls (machine-anchored, do not re-hit them blindly):
- CC-18's twist freedom (`twistNode`/`twistRealization`/`twistRealizedInput`,
  C130s18.lean:407-465; `canonicalResAt_twist` :467-474; `embeddedValue_not_uniform`
  :527-543) REFUTES deriving the export from bare `ChainRealization`/`RealizedInput`
  fields — a new SOURCE-FAITHFUL tower export is necessary (the export must come from
  the tower/calculus structure the realization is built FROM, not from the realization
  interface, which is twist-degenerate).
- The fixed-depth model is D62w's tau descent (`Gauge.hvarthetaRes_of_tau_letters`,
  D62w.lean:94-120 — the exporter's consumer, already landed).
- This is the general-depth content of LS-V10/OPEN-LETTERS (the held C.102/htie fence —
  read the OPEN-LETTERS records: rg 'OPEN-LETTERS' across docs/ and leanfinal/).
- The depth-2 witness needs nothing (r = 2 live range empty — LVS proved it); the FIRST
  real instance is r = 4, j = 3. The deep (r ≥ 4) arising witnesses do not exist in the
  landed corpus yet (the deep witness campaign is itself open) — so this unit's job is
  the EXPORT MECHANISM at the level of the tower/calculus data (FGMNCalculus /
  ChainRealization sources), stated so that when deep witnesses land, the export fires.

## Your charge

1. READ: verdict_LVS + the [LVS] doc section + LVS_probe.lean in full; D62w.lean's tau
   descent; C130s18's twist lemmas; the FGMNCalculus class definition and the landed
   depth-2 instance route (C130pk.lean's fgmn_model_calculus_nonempty; C132fd0/kp6b for
   the μ₃ instance); the OPEN-LETTERS records.
2. THE MATH: design and prove (math level, full rigor) the source-faithful export — from
   which structure do the tau letters and embedded-Kt residue values at level j
   canonically COME? Candidates to evaluate: (a) the FGMNCalculus laws at level j (the
   letter field + normalizedResidual — the calculus carries letters BY CONSTRUCTION);
   (b) a strengthened ChainRealization variant carrying per-level residue embeddings
   (a new structure — price the consumer ripple); (c) the SplitNodeWired route (IFC4's
   wired witnesses carry towerRead — can the export ride the wiring law?). Pick by the
   end-to-end criterion (which choice can BOTH be supplied by arising witnesses AND
   discharge VarthetaTauLevelExport) and prove the discharge for the chosen route.
3. THE LEAN SURFACE: exact statements in landed vocabulary; probe
   leanfinal/scratch/TAU_probe.lean (verify `cd leanfinal && timeout 580
   ~/.elan/bin/lake env lean scratch/TAU_probe.lean`; NEVER bare `lake build`; sorries
   allowed for shape validation, marked). Prove in the probe whatever is reachable.
4. If the export genuinely requires new per-level data that no landed or plausibly-
   landable structure carries, say so precisely: name the minimal new field, its
   supplier obligation at arising witnesses, and whether the FGMN literature's calculus
   (the cites' Def 3.10/3.12 apparatus) actually provides it (faithfulness check — the
   export must not smuggle an unprovable demand into the supplier side).

## Deliverables

- Dated `[TAU 2026-08-28]` section APPENDED to docs/in-progress/LADDER_SUPPLY_2026-08-27.md.
- `runs/wave-c/verdict_TAU.md`: route chosen + why, per-claim PROVED/OPEN/BLOCKED-BECAUSE
  with exact citations, the supplier obligation ledger.

## Rules

No git commits. No edits to landed .lean/leanspec/existing scratch. Owner's paper never
citable. Rigor paramount; quantifier placements machine-anchored (this campaign's
refutation record is long).
