# Verdict — UNT: the C130nv→C131ae import untangle; `fgmn_dv_exact_mul` PHYSICALLY RETIRED

**Date:** 2026-08-28
**Unit:** UNT
**Charge:** untangle the textual import cycle H0LEG found (`runs/wave-c/verdict_H0LEG.md`)
that blocked the physical removal of the declared cite `fgmn_dv_exact_mul` (C66b.lean:90),
then execute the retirement.

## RESULT

DONE, both parts. The cycle was import-line-and-move surgery only (route (a): a shallow,
single-lemma snip) — no re-proof was needed, so charge item 5's STOP condition never
triggered. The `axiom` keyword is now gone from the build: `fgmn_dv_exact_mul` is a
`theorem`, statement bytes byte-identical to the retired axiom text. Scoped roll-up
`lake build Uniformity.ChapC` (8903 jobs) is GREEN, zero errors, zero `sorry`. The
declared-cite allowlist is physically SIX.

## 1. The cycle, mapped exactly

Import chain (unchanged facts, confirmed by import-graph BFS + `grep`):
`C133mh3 → C133mh1 → C130nv3 → C130nv2 → C130nv → C131ae → C131ac → C66b`, and
`C131ac.lean:120` (inside `fgmn_dv_exact_pow`'s induction) was the axiom's **only** proof
consumer anywhere in `leanfinal/` (full grep accounting in §4).

**What `C130nv` actually used from `C131ae`:** exactly ONE declaration,
`Uniformity.Density.Tower.C131ae.suppVal_add_eq_left_of_lt`, at two call sites (both
inside `C130nv.suppVal_add_eq` — C.05's budget-floor case split, lines 148/150). Nothing
else from `C131ae` is referenced, qualified or via `open`, anywhere in `C130nv.lean`
(checked against every one of `C131ae`'s 20 top-level declarations).

**What that lemma actually depends on:** its own self-contained "Part 1" section in
`C131ae.lean` (former lines 90–160, `section Ultrametric … end Ultrametric`:
`addVal_neg_one`, `addVal_neg`, `gaussVal_neg`, `dev_zero_any`, `dev_neg_of_monic`,
`suppVal_neg`, `suppVal_add_eq_left_of_lt`), which uses only `dev_add_of_monic`
(`B32a.lean`) and `min_suppVal_le_suppVal_add` (`B32b.lean`) — chapter B, never
`C131ac`. `C131ae`'s OWN main theorem (`mem_towerLocus_of_budget`) is a separate,
unaffected consumer of `C131ac`'s `composedKey_pow_mem_towerLocus` — that edge is
legitimate and stays.

**What `C131ae` uses from `C131ac`:** exactly that — `composedKey_pow_mem_towerLocus`,
for `mem_towerLocus_of_budget`'s own proof, unrelated to the moved section.

Confirmed by BFS over the import graph (script over `^import` lines) that
`C130nv → C131ae` is the **sole** edge on **every** path from `C133mh3` (hence
`C133h0leg`) to `C131ae`/`C131ac`/`C66b` — `C130rp2`, `C130rp4`, `C133mh1` all funnel
through it; none of `C133mh3`'s other ancestors (`C130rp0/1`, `C130nv5`, `C08`, `C23`,
`C26`, `C35`, `C131f`, `C141defs`, `C05`, `C84d`, `B39a`, `B43`, `B59a`) reach
`C131ac`/`C66b` independently.

## 2. The route executed — (a), a verbatim single-lemma snip

Moved the self-contained "Part 1" section (former `C131ae.lean` lines 90–160) VERBATIM
into a **new file**, `C131ae0.lean`, under the **same namespace**
(`Uniformity.Density.Tower.C131ae`) so every existing qualified reference (in both
`C131ae.lean` itself and `C130nv.lean`) resolves unchanged — no proof text was touched
anywhere, only import lines:

* `C131ae0.lean` imports only `Uniformity.ChapB.B32b` (which transitively supplies `B32a`,
  `B14`, `B07`, `B02` — `dev`/`gaussVal`/`suppVal`/`dev_add_of_monic`/
  `min_suppVal_le_suppVal_add`). No `C131ac` import, no cycle.
* `C131ae.lean`: the moved block deleted, replaced by a dated pointer comment; added
  `import Uniformity.ChapC.C131ae0` (its own later theorems —
  `stageHeight_add_eq_left_of_lt`, `dvHgt_add_eq_left_of_lt`, `dvHgt_add_ge` —
  reference the moved names unqualified and resolve fine since the namespace is shared).
  `C131ac`/`C131ad`/`C118a`/`C118b`/`C131v`/`C109`/`HenselFactorization` imports
  untouched (still needed by `mem_towerLocus_of_budget`).
* `C130nv.lean`: **one import line changed** (`C131ae` → `C131ae0`); the two call sites
  `C131ae.suppVal_add_eq_left_of_lt` at lines 148/150 are **byte-unchanged** (the
  qualifier still resolves — same namespace, different file). One doc-comment line
  updated for accuracy.

**Machine-checked structurally** (BFS over the post-edit import graph): `C133h0leg`'s
transitive-import closure (203 modules) now contains `C131ae0` but **not** `C131ae`,
`C131ac`, or `C66b`. `C131ac`'s own closure still contains `C66b` (expected — it's the
declared consumer) but not `C133h0leg` or `C133mh3` (no return edge). Cycle broken.

## 3. Moved-decl table (verbatim-move audit)

| Decl | Old location | New location | Diff |
|---|---|---|---|
| `addVal_neg_one` (private) | `C131ae.lean` (former L97-98) | `C131ae0.lean` | body text identical |
| `addVal_neg` | `C131ae.lean` (former L101-103) | `C131ae0.lean` | identical |
| `gaussVal_neg` | `C131ae.lean` (former L106-110) | `C131ae0.lean` | identical |
| `dev_zero_any` (private) | `C131ae.lean` (former L113-120) | `C131ae0.lean` | identical |
| `dev_neg_of_monic` | `C131ae.lean` (former L123-128) | `C131ae0.lean` | identical |
| `suppVal_neg` | `C131ae.lean` (former L131-139) | `C131ae0.lean` | identical |
| `suppVal_add_eq_left_of_lt` | `C131ae.lean` (former L143-158) | `C131ae0.lean` | identical |

Verification command run: `diff <(sed -n '92,160p' C131ae.lean [pre-edit]) <(sed -n
'52,120p' C131ae0.lean [post-write])` → **empty diff** (the `section Ultrametric … end
Ultrametric` body, byte for byte). Only the docstring/imports/opens wrapping the section
are new text (clearly marked `[UNT 2026-08-28]`), never the decl bodies.

## 4. The retirement — axiom → theorem in place

`C66b.lean`: added `import Uniformity.ChapC.C133h0leg`; `axiom fgmn_dv_exact_mul ...`
became `theorem fgmn_dv_exact_mul ... := C133h0leg.fgmn_dv_exact_mul_full hπ H₀ hpin hg
hg' hℓ hcop hfloor hdg hdg' hpos hpos' hpg hpg'`. Binder telescope + conclusion are
**byte-identical** to the retired axiom text — re-verified independently of H0LEG's own
diff (`diff` on the extracted binder+conclusion spans, normalizing only the
`axiom fgmn_dv_exact_mul`/`theorem fgmn_dv_exact_mul_full` head and the trailing
`:= by` — empty diff). Docstring/status/AxCheck-comment updated (comment-only) to record
`[UNT 2026-08-28] PHYSICALLY RETIRED`. No cycle risk: `C131ac`'s transitive closure
(checked) contains neither `C133h0leg` nor `C133mh3`.

## 5. Full grep accounting — every `fgmn_dv_exact_mul` hit in `leanfinal/`

One **code-level** consumer, unchanged text, now resolving to the theorem:
`C131ac.lean:120` — `have hmul := fgmn_dv_exact_mul hπ H₀ hpin hgk hg hℓ hcop hfloor hdgK
hdg hposK hpos`.

The declaration site: `C66b.lean` (theorem decl + `#print axioms` line + docstrings).

All remaining hits are **prose/docstring mentions** (backtick-quoted, non-code), naming
the cite as inherited provenance — untouched by this unit, per H0LEG precedent (not a
proof/statement, low priority, still roughly accurate since the name is unchanged):
`C131aa.lean`, `C133h0leg.lean`, `C131uf.lean` (×3), `C131af.lean` (×2), `C123r.lean`
(×3), `C130sg.lean`, `C134frt.lean` (×2), `C131ag.lean`, `C27x.lean`, `C134f12c.lean`,
`C131ae.lean` (×3, one is the new `[UNT]` note), `C131ac.lean` (×3 more, all prose),
`C133mh3.lean` (×2), `C130s17.lean`, `C131ae0.lean` (×2, its own docstring explaining the
move), plus one comment in `leanfinal/scratch/MHENS_probe.lean` (scratch, not in the
build graph). Every hit accounted for; none is a second code-level consumer.

## 6. Footprint verification

Per-file `lake env lean` (exit 0, no errors) on every touched file: `C131ae0.lean`,
`C131ae.lean`, `C130nv.lean`, `C66b.lean`, `C131ac.lean`. Then `lake build` per target
(each green) and finally the scoped roll-up:

```
timeout 580 lake build Uniformity.ChapC   →   Build completed successfully (8903 jobs).
EXIT: 0.  Zero errors, zero `sorry` anywhere in the log.
```

`#print axioms` footprints, before → after (all confirmed in both the per-target builds
and the full roll-up log):

| Declaration | Before (H0LEG state) | After (this unit) |
|---|---|---|
| `Uniformity.Density.Tower.fgmn_dv_exact_mul` (C66b) | `axiom` (not printable as a theorem) | `[propext, Classical.choice, Quot.sound]` |
| `C131ac.fgmn_dv_exact_pow` | `[..., fgmn_dv_exact_mul]` | `[propext, Classical.choice, Quot.sound]` |
| `C131ac.isDvPure_pow` | `[..., fgmn_dv_exact_mul]` | `[propext, Classical.choice, Quot.sound]` |
| `C131ac.dvResPoly_pow_exact` | `[..., fgmn_dv_exact_mul]` | `[propext, Classical.choice, Quot.sound]` |
| `Uniformity.Density.Tower.composedKey_pow_mem_towerLocus` (C131ac) | `[..., fgmn_dv_exact_mul]` | `[propext, Classical.choice, Quot.sound]` |
| `Uniformity.Density.Tower.mem_towerLocus_of_budget` (C131ae) | `[..., fgmn_dv_exact_mul]` | `[propext, Classical.choice, Quot.sound]` |
| `C131ae0.{addVal_neg, gaussVal_neg, dev_neg_of_monic, suppVal_neg, suppVal_add_eq_left_of_lt}` | (lived in `C131ae`, same footprint) | `[propext, Classical.choice, Quot.sound]` (new file, re-checked) |
| `C133h0leg.{isKey_key, frameRes_eq_map, dvSideSet_eq_sideSet, dvResPoly_eq_map_resPoly, fgmn_dv_exact_mul_h0, fgmn_dv_exact_mul_full}` | Lean-core | unchanged, Lean-core (sanity re-check post-edit) |
| `C133mh9.theoremA` | Lean-core (per PROJECT_STATE.md) | unchanged, Lean-core (sanity re-check) |
| `C133mh15.blockFrontier_of_context` | Lean core + `exists_dvDissection` | unchanged (different, unrelated allowlisted cite; sanity re-check) |
| `C130nv.*` (all decls) | (already Lean-core; `C131ae` import was for a Lean-core lemma) | unchanged, Lean-core |

Whole-roll-up grep for `fgmn_dv_exact_mul` inside the `#print axioms`-style `info:` lines
(`/tmp/build_chapc.txt`, 8903-job log): the name appears ONLY as the subject of a
Lean-core footprint line (`'…fgmn_dv_exact_mul' depends on axioms: [propext,
Classical.choice, Quot.sound]` and its siblings `_of_twistLaw`/`_thm`/`_h0`/`_full`) —
**never** inside another declaration's axiom-dependency LIST. The axiom is gone from the
entire scoped build graph.

## 7. Files touched

* **NEW:** `leanfinal/Uniformity/ChapC/C131ae0.lean` — the verbatim-moved Ultrametric
  section (see §3), imports only `B32b`.
* **EDITED (import + comment only, no proof/statement change):**
  `leanfinal/Uniformity/ChapC/C131ae.lean` (moved block removed + pointer comment;
  `+1` import), `leanfinal/Uniformity/ChapC/C130nv.lean` (`1` import line swapped; 1
  doc-comment line), `leanfinal/Uniformity/ChapC/C66b.lean` (`+1` import;
  `axiom` → `theorem ... :=`, statement bytes unchanged; docstring/status/AxCheck
  comments updated).
* **EDITED (docs):** `docs/AXIOM_FAITHFULNESS.md` (`fgmn_dv_exact_mul` entry: added the
  PHYSICALLY RETIRED record), `docs/PROJECT_STATE.md` (§3 trusted-base allowlist: SEVEN
  declared/SIX effective → SIX, physically).
* **Not touched** (per H0LEG precedent, left for the orchestrator's checkpoint):
  `docs/LOG.md`, `docs/CITE_REVIEW_LIST.md` row 2 (still OPEN for the owner's literature
  spot-check — now not load-bearing for the mathematics, since the statement stands on
  Lean core regardless of the cite's fidelity), the ~13 files with prose-only mentions of
  the retired name (§5), and the `Uniformity/ChapC.lean` roll-up (already listed `C66b`
  and `C133h0leg` — no edit needed, confirmed by the green scoped build).
* **Not mine, unrelated:** `leanfinal/Uniformity/ChapC/C134p1.lean` appeared untracked
  during this unit's run — a concurrent process on this shared machine (confirmed via
  `ps aux`, several other `lean --worker` processes building unrelated files); not
  touched, not included in any of the above.

## 8. Charge-item-5 check

The untangle needed **only** import-line + verbatim-move surgery, exactly route (a) as
anticipated by H0LEG/the charge — no re-proof, no statement change, no BLOCKED-BECAUSE.
