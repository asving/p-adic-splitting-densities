# UNIT WLE — design the WleCleared per-level exporter (the universal DeepGentowSupplier blocker)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

The capstone `deepTwist` half routes through the GCW chain (2026-08-27/28):
- A-I.5 signed the GC13 wiring law and the sitewise `WiredGentowDemand`
  (leanspec/Leanspec/ChapI.lean, NODES I.10c/I.10d; enactment
  leanfinal/Uniformity/ChapI/IFC3.lean + IFC4.lean).
- IFC4 landed the FIRST honest supply tooth: `s2SplitNodeWired` (towerRead := 1),
  `s2Wired_gc13Wiring`, and `s2Wired_gentowWWindow_at_own_exports` — the first
  `GentowWWindow` at an arising witness's OWN exports, through the μ₃ endpoint
  (`s2Mu3Calculus`, the unconditional depth-2 calculus in
  leanfinal/Uniformity/ChapC/C132kp6b.lean + C132sg2.lean/C132sg3.lean with the signed
  `GENTOW5WCleared` consumer `s2Mu3_gentow5w_two`).
- BLOCKED-BECAUSE (recorded in the GCW verdicts + IFC3/IFC4 headers +
  docs/in-progress/GC13_WIRING_2026-08-27.md, esp. the GCW-6 tension record): the
  UNIVERSAL wired `DeepGentowSupplier` cannot be stated correctly yet — every
  site-quantifier placement tried was machine-anchored defective. The missing mechanism
  is a **`WleCleared` per-level exporter**: for a wired witness at level r, its own
  exports clear the W≤ demand LEVEL-BY-LEVEL, so the universal supplier can quantify
  over wired witnesses and export per-level cleared data instead of quantifying over
  raw sites.

## Your charge

1. READ (in this order): docs/in-progress/GC13_WIRING_2026-08-27.md in full (the GCW-0..6
   records and the orchestrator's P2 adjudication), IFC1.lean → IFC4.lean (headers +
   the GentowWWindow/translation declarations), runs/wave-b/verdict_GCW3.md (and the
   other GCW verdicts in runs/wave-b/), the `GENTOW5WCleared`/`WleCleared` machinery
   (grep for `WleCleared` and `GENTOW5W` across leanfinal/ and spec/EFF-GENTOW5-*.md),
   and the DT0 decomposition in IFC0.lean (the deepTwist supplier interfaces).
2. DESIGN the exporter. Deliver, precisely:
   (a) the exact Lean statement of the per-level exporter — for a wired witness
       (the `SplitNodeWired`-shaped data) at depth r, and each live level j, the export
       of the W≤-cleared datum at level j from the witness's own calculus/exports;
   (b) the exact Lean statement of the universal wired `DeepGentowSupplier` it enables
       (quantify over wired witnesses; conclusions at their own exports — respect the
       GCW-1 ruling: sockets and `CapstoneHypotheses` byte-frozen, no guard extension);
   (c) the proof plan for (a) at the landed S2 witness (r = 2) wired to exact landed
       declaration names — this must RECOVER `s2Wired_gentowWWindow_at_own_exports` as
       the level-2 instance, or explain the discrepancy;
   (d) the genuinely-new mathematics needed for deep levels (r ≥ 4, the deep shape tooth
       recorded OPEN in IFC4) as named open lemmas with statements — the arising-witness
       campaign's demand list.
3. ANCHOR every quantifier placement against the machine: for each defective placement
   recorded in the GCW verdicts, say why your placement avoids that defect. If your
   design hits the same wall, record BLOCKED-BECAUSE with the exact defective instance —
   that is a valid outcome; do not paper over it.
4. Optional but valuable: a compiling statement-level probe
   `leanfinal/scratch/WLE_probe.lean` (statements + sorry bodies allowed HERE ONLY —
   scratch probes may carry sorries for statement-shape validation; mark each) verified
   via `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/WLE_probe.lean`
   (elaboration errors are the anti-drift signal; NEVER bare `lake build`).

## Deliverables

- Dated `[WLE 2026-08-28]` section APPENDED to docs/in-progress/GC13_WIRING_2026-08-27.md
  with (a)–(d).
- `runs/wave-c/verdict_WLE.md`: design summary + claims labeled DESIGNED-ANCHORED /
  OPEN-LEMMA / BLOCKED-BECAUSE.

## Rules

No git commits. No edits to landed .lean, leanspec, or existing scratch files. The GCW-1
ruling binds: no socket/capstone byte changes, no guard extensions. Quote exact
declaration names + line numbers. Optimism is not a deliverable.
