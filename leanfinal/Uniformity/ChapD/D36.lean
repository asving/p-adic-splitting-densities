/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D36 — the C7 package interface and scope fence (anchor `D-C7-TABLE`)

**Chapter D, NODE D.36** [table] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5, the read bundle
and the B-law; amendments A-1 and A-D.1 govern — this node carries no `[repaired: …]` /
`[re-signed: …]` tag, so the composed text is its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none (a
blueprint interface table — no Lean declaration; the B.86-precedent class of node-with-no-public-decl
… `dag_build.py` accepts edge-less declared nodes)`, with `PROOF. n/a`, `SIZE. 0 Lean lines`,
`ENVIRONMENT. n/a`; the leanspec stub gate held it ("**D.36** [table] … NO Lean declaration; the
blueprint table is the artifact"). This landed copy is the artifact's home in `leanfinal`: it
**imports nothing and defines nothing**, so it cannot become a silent dependency of a proof, and
no chapter-F weld face acquires a chapter-D name here.

What the node *is*: the answer to "what does the T-chain supply to each WELD-M-PKG field?" —
the interface chapter F cites — together with the fence that says what it does **not** supply.

## The effective C7 table, transcribed verbatim (`EFF.T1.22`)

Per-row fences INCLUDED — **"the table does not merge field types."**

| Package field | T1 datum available to that field (Lean home) |
|---|---|
| `M0`, division chains | common tower and canonical division-chain anchor; **no new identity is proved here** |
| `M1` | the unconditional value-zero ratio and level-two letter formula in (C1) — D.20, D.21; arbitrary-depth letter monomiality **only under `(H-JA-CONJ)_i`** (inline, D-H10) |
| `M2` | the dictionary and canonical read in (C3) — D.31, D.32, D.33 — plus (C4-origin) — D.22; support transport **only under `(H-JA-RES-CONJ)`** — D.23. The graded-read bundle consumed, in full: ladder-multiplicativity, slot-grade, scalar-covariance, zero-read, nonvanishing, codomain = D.29's fields (+ D-H3's packaging notes); corrected-key coefficients additionally use the coefficient space — D.30. At depth `i ≥ 3` the scalars `ϑ_{i,s}`, `Θ_i(t)`, `c_tϑ` are `K_i`-scalars **only under `(H-VARTHETA-RES)_i`** — D.67 |
| `M3` | the cocycle/telescope (C2) — D.03, D.05, D.08 — and canonical twist in (C3) — D.34 — only on the scored stratum; at `i ≥ 3` the `K_iˣ`-valued telescope **only under `(H-VARTHETA-RES)_i`** |
| `M4` | the exact-height formulas (C5)–(C6) — D.19, D.24–D.26 — at W2-C3's accepted fence; polygon clearance **only under `(H-GENHN-CLEAR)`** (no D node — D-H4(5)) |

⚠ **One stale ID inside the verbatim rows, corrected here rather than silently edited.** The
`M2` row's trailing "`(H-VARTHETA-RES)_i` — **D.67**" is a *pre-A-1 carrier ID*: in the post-A-1
numbering `(H-VARTHETA-RES)_i` is **D.62** (`HVarthetaRes`, landed as
`Uniformity.ChapD.D62`/`D62w`), and D.67 is a gate (FRAME-C). A-D.1's rider R-2 is explicit that
the residual pre-A-1 carrier IDs in prose rows were **not** swept and that the sweep is an
orchestrator item; the row above is therefore transcribed byte-faithfully and this note is the
correction. A consumer must read the `M2` and `M3` conditionality as **D.62**.

## The scope fence `(C7-scope)`, verbatim (`EFF.T1.23`)

> "T1 organizes five named fields around one tower cocycle; it proves no cross-face coherence
> theorem. It also proves no uniqueness of the gauge and makes no classification of the fiber of
> gauges having a fixed coboundary."

Chapter F's weld faces cite THIS anchor for what the T-chain supplies. **A NODE asking chapter D
for a cross-face compatibility square is a blueprint defect** — i.e. a fleet agent handed such a
node returns BLOCKED against this row rather than inventing the square. The same fence covers the
two non-claims: no gauge uniqueness, no torsor classification of the coboundary fiber.

## The row targets in landed Lean names

All in `Uniformity.Density.Gauge` unless marked, all green at HEAD. This mapping is the reason
the table is worth a file: it turns "D.31, D.32, D.33" into names a chapter-F author can `#check`.

| row | landed names |
|---|---|
| `M1` | `GaugeArena.res_ratio_factor` (D.20) · `levelOne_rho` (D.21) |
| `M2` | `dict_iff` (D.31) · `ReadBundle.blaw` (D.32) · `ReadBundle.canonical_coeff` (D.33) · `c4_origin`, `c4_origin_raw_iff` (D.22) · `c4_support` (D.23) · the structure `ReadBundle` and its fields (D.29) · `correctedKey`, `correctedKey_monic` (D.30) |
| `M3` | `NormSection.tau_cocycle` (D.03) · `NormSection.varthetaEl_zero/_one/_succ` (D.05) · `GaugeArena.vartheta`, `GaugeArena.theta`, `GaugeArena.vartheta_succ` and the four `mem_ker` facts (D.08) · `wtwist` + its transport lemmas (D.34a/b/c) |
| `M4` | `varpiSection`, `chi_varpi`, `res_chi_varpi` (D.19) · `liftC6` (D.24) · `liftC6_spec`, `liftC6_zero`, `liftC6_exp_nonneg` (D.25a) · `liftC6_support`, `liftC6_xfree` (D.25b) · `gammaCoord`, `gammaCoord_liftC6` (D.26) |
| `M0` | **none, by the row itself** — "no new identity is proved here" |

## Reading notes for a consumer

* **The conditional rows are conditional in Lean too, and the hypotheses have no chapter-D
  discharge.** `(H-JA-CONJ)_i`, `(H-JA-RES-CONJ)`, `(H-VARTHETA-RES)_i` (= D.62) and
  `(H-GENHN-CLEAR)` are carried inline at their consumption sites (the D-H10 carrier ruling);
  `(H-GENHN-CLEAR)` has **no D node at all** (D-H4(5)). A weld face that drops one of them is
  citing an unconditional statement chapter D never made.
* **`M0` is deliberately empty of theorems.** Asking chapter D for a division-chain identity is
  asking for content the table says does not exist.
* **This file adds nothing to the DAG.** It is edge-less by construction (`dag_build.py` accepts
  edge-less declared nodes); its DEPENDS list below is a *row-target* list, not an import list.

**DEPENDS.** D.20–D.23, D.29–D.34 (row targets).

**SOURCE.** `EFF.T1.22` (the effective C7 table, all five rows with their fences), `EFF.T1.23`
(`(C7-scope)` + the uniqueness/torsor non-claims).

**TEETH.** T1 §4.2 check 6; §7 attack 4 → §12 (signed rows: interface, nothing to execute).

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
