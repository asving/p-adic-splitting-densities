# UNIT DWC — the DEEP WITNESS CAMPAIGN decomposer (the capstone's critical path)

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context: why this campaign, now

The capstone `CapstoneHypotheses n` (post-A-I.6/A-I.7 shape) has its remaining honest
content CONCENTRATED at deep arising occurrences. The 2026-08-28 findings (all
machine-anchored; read the four verdicts in runs/wave-c/: verdict_LVS.md, verdict_TAU.md,
verdict_SRX.md, verdict_WLE.md, plus the GCW-6/[WLE] sections of
docs/in-progress/GC13_WIRING_2026-08-27.md):

- vartheta-live: real content first at r = 4, i = 3 (LVS); the export mechanism is proved
  (TAU: `CanonicalTauLiveSource` + `CanonicalGeneratorDescent`, scratch/TAU_probe.lean);
  deep witnesses must SUPPLY the dictionary.
- mp1-live: vacuous at the landed S2 parent (μ = 1 kills MP1StepCore universally — SRX);
  a genuine μ ≥ 2 recentering occurrence is needed, plus GNCitePayload surface
  refinements (SRX's per-field table: the Newton-slope membership predicate missing; the
  residual field bound to the wrong operator for GN's R_{r+1,λ} indexing).
- deepTwist: IFC4's wired witness is r = 2; the deep shape tooth is OPEN; the WLE
  exporter design is anchored but `WleCleared … 2` is vacuous and `DeepLive 2 j` empty —
  deep inhabitants are the missing objects.
- The landed model for this whole genre: the μ₃ campaign
  (docs/in-progress/MU3_CAMPAIGN_2026-08-26.md — 29 nodes, closed in ~2 days) built the
  DEPTH-2 calculus `s2Mu3_calculus_nonempty` at (2,1,21) on the S2 tower over ℤ₂. The
  deep campaign must produce a DEPTH-4 (r = 4) arising witness — presumably extending
  the same S2 tower two more levels (μ₄, μ₅ machinery), or a different, better-suited
  tower if the S2 extension hits a structural wall (adjudicate!).

## Your charge: a formalization-trivial blueprint (the MU3_CAMPAIGN doc is the template)

1. READ (beyond the four verdicts): MU3_CAMPAIGN_2026-08-26.md in full (structure +
   what made its nodes land fast); the C132 series' architecture (C132fd0's
   records/laws pattern, C132sg's packaging through `fgmn_model_calculus_nonempty`);
   C130s2/C130s17/C130sg (the S2 tower, its input data, the socket suppliers);
   IFC4's wired-witness construction; I10RecenterLive.lean (the mp1 payload shapes);
   TAU_probe.lean's `CanonicalTauLiveSource`/`CanonicalGeneratorDescent`.
2. ADJUDICATE THE TOWER: can the landed S2 depth-2 tower extend to depth 4 over ℤ₂
   (keys g₈-then-next, per the bank's proper successor — SRX proved g₈'s key math
   landed), or does the campaign need a fresh tower (e.g. over ℤ₂ with different input,
   or q = 3) to reach μ ≥ 2 at some level (the mp1 occurrence demands it)? Work the
   numerics BY HAND for the leading candidate (the examples-first discipline): the
   (e', f', u') triples at depths 3 and 4, which levels have μ ≥ 2, whether the GN
   recentering at some level is genuine (Λ ≠ 0 with the divisibility). A candidate
   tower whose numerics are verified in a small Python cert (verification/ pattern)
   before any Lean is the deliverable here.
3. THE NODE DAG: decompose into formalization-trivial nodes (≈30–60 min per node for a
   Sonnet/Fable transcriber — the blueprint-formalization standard), wired to EXACT
   landed declarations: the depth-3 and depth-4 operator/record/laws nodes (the C132
   pattern per level), the calculus packaging node, the ChainRealization/RealizedInput
   witness node, the wired-witness node (IFC4 pattern), and the four consumer legs
   (WleCleared per-level data; CanonicalGeneratorDescent; the mp1 RecenterStep at the
   genuine recentering level — WITH the GNCitePayload surface refinements as their own
   nodes, since SRX showed the current payload shape cannot be honestly filled;
   the deepTwist arising-witness tooth). Per node: statement sketch, inputs (exact decl
   names), sizing, and what blocks it.
4. THE GATES: name the stop-line checks BEFORE the fleet fires (the μ₃ campaign's
   lesson: signed-consumer amendments first; here: the GNCitePayload refinement is
   probably an amendment to I10RecenterLive's shapes — scope it precisely; also check
   whether TAU's dictionary and WLE's exporter want a SHARED per-level export record —
   designing them separately then merging costs a ripple).
5. Numeric certificate for the chosen tower's depth-3/4 data (new
   verification/dwc_tower_cert.py; state parameters + counts).

## Deliverables

- `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` — the blueprint (MU3 template:
  verdict up front, node table §6-style, gates, the tower adjudication with numerics).
- `runs/wave-c/verdict_DWC.md` — decomposer verdict: tower chosen + why, node count,
  gate list, the single highest-risk node named.

## Rules

No git commits. No edits to landed .lean/leanspec files. Scratch probes allowed
(leanfinal/scratch/DWC_probe.lean, verified per-file; NEVER bare `lake build`). Rigor:
numerics verified by the cert before being written into the blueprint; a pattern from
examples is labeled conjecture; every node's inputs are exact landed decl names (no
optimism). Owner's paper never citable.
