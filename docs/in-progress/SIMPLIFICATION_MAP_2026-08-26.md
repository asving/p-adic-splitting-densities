# SIMPLIFICATION MAP — 2026-08-26 (unit SIMP)

**Status: DESIGN ONLY, READ-ONLY SURVEY.** No Lean file was edited to produce this map (per
the unit charge). No statement is proposed to change; every recommendation below is either
a pure move/rename/visibility change or an explicitly-flagged proof-touching consolidation
that a later enactment wave must re-verify (full 2-clean-equivalent: build green +
`#print axioms` unchanged + the absorbed statement byte-identical after the merge). Scope:
the ~90 files `leanfinal/Uniformity/ChapC/C130*.lean` / `C131*.lean` (+ a dozen siblings:
C99gt, C99r, C102gt, C105gt, C106m, C107ac14, C107gt5, C123, C123r, C78adj, C84d, C140defs,
C141defs, C150rb1-3, C27x, C64, C66b) added by the 2026-08-24–26 sprint, plus the
project-wide refutation/quarantine record conventions.

**Method.** Four parallel read-only research passes (general-purpose subagents), one per
suspect named in the charge; this document synthesizes their findings. Every file:line
datum below was independently verified by direct read, not inferred from names.

## 0. Standing caveat — the PK-in-flight defer set

`docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §5 names 13 files under active retype by
unit **PK12 (RUNNING** per `docs/PROJECT_STATE.md` §6 as of this survey): `C130k2.lean`,
`C130fg.lean`, `C130in.lean`, `C130pt.lean`, `C130st.lean`, `C130cr.lean`, `C130th.lean`,
`C130ar.lean`, `C130vw.lean`, `C130pk.lean`, `C130s17.lean`, `C130s18.lean`, `C130sg.lean`.

**No recommendation below touches any of these 13 files.** Anywhere a finding involves one
of them (e.g. the `C130k`/`C130k2` field-docstring twin in §1), it is marked
**DEFER-until-PK-lands** and excluded from the enactment plan's actionable tiers. A second,
looser ring — files that import one of the 13 directly, or that feed into `C130sg`'s funnel
(`C130la`, `C130lb`, and the tail of the RP/KP/NP ladders: `rp6/rp8/rp9/rp11`,
`kp5/kp7`, `np0/np6/np7/np8`, `C130fd0`) — is marked **HOLD** (no live edit conflict
expected, but scheduling sense says wait for PK12 to land before restructuring anything
one hop away from it).

---

## 1. Duplicate lemma clusters

### 1a. The headline finding: `C131ae.lean` ↔ `C131y.lean`, an 11-pair duplicated chain

Both files independently build the same "ultrametric equality-off-ties + negation
prerequisites" chain for `suppVal`/`stageHeight`/`dvHgt`/`slotRes`/`twistRead`, and **neither
imports the other** (confirmed via the import graph), so this is genuine parallel
re-invention, not one file legitimately citing the other under a different name.

| # | fact | `C131ae.lean` | `C131y.lean` | same statement? |
|---|---|---|---|---|
| 1 | `addVal O (-1) = 0` | `:97 addVal_neg_one` | `:48 addVal_neg_one` | identical name+statement |
| 2 | `addVal O (-x) = addVal O x` | `:101 addVal_neg` | `:52 addVal_neg` | identical |
| 3 | `gaussVal (-p) = gaussVal p` | `:106 gaussVal_neg` | `:57 gaussVal_neg` | identical |
| 4 | `dev(0)=0` at any abscissa | `:113 dev_zero_any` (private) | (cites `C118a.dev_zero_any`, canonical, public) | **C131ae re-derives a fact its own imports already supply — same name, shadows the public one** |
| 5 | `dev(-A)=-dev A` (monic) | `:123 dev_neg_of_monic` | (via `C131w.dev_neg`, canonical) | same fact, different route |
| 6 | `suppVal(-A)=suppVal A` | `:131 suppVal_neg` | `:64 suppVal_neg` | identical |
| 7 | `suppVal` eq-off-ties (one-sided `<`) | `:143 suppVal_add_eq_left_of_lt` | `:75 suppVal_add_eq_left_of_lt` | identical |
| 8 | `stageHeight` eq-off-ties | `:164 stageHeight_add_eq_left_of_lt` | `:96 stageHeight_add_eq_left_of_lt` | identical |
| 9 | `dvHgt` eq-off-ties | `:171 dvHgt_add_eq_left_of_lt` | `:102 dvHgt_add_eq_left_of_lt` | identical |
| 10 | `dvHgt` ultrametric ineq | `:179 dvHgt_add_ge` | `:220 dvHgt_add_min` | same statement, different name |
| 11 | `slotRes`/`twistRead` eq-off-ties | `:273 slotRes_add_eq_left_of_lt`, `:295 twistRead_add_eq_left_of_lt` | `:182 slotRes_add_deep`, `:204 twistRead_add_deep` | same statement, different name |

Both copies are **load-bearing**: `C130rp2.lean:293,724` calls `C131y.twistRead_add_deep`
directly, and `C131ae.lean:190` uses its own `dvHgt_add_ge` internally. A merge must produce
one shared file both `C131ae`'s and `C131y`'s downstream consumers can cite — this is not a
delete-one-copy operation, it needs a small new home file (or folding into `C131w`, which
both already sit near in the DV-engine import graph).

### 1b. Other true duplicates in the ultrametric/negation family

| concept | canonical / best-sited copy | duplicate(s) | verdict |
|---|---|---|---|
| `dvSupp` eq-off-ties (symmetric `min` form) | `C130s6.lean:284 dvSupp_add_eq` (★ author-marked canonical) | `C131y.lean:268 dvSupp_add_eq_left_of_lt` (same statement, different proof technique) | duplicate — cite C130s6's |
| char-2 field negation (`-x=x`, scalar + poly) | `C130rp11.lean:164,173 s2Fld2_neg_eq_self` / `s2Fld2_poly_neg_eq_self` | `C130kp5.lean:294,303` (private, byte-identical proof; **C130kp5's own docstring calls this "private copy of RP-11's char-2 identity"**) | duplicate, self-acknowledged |
| `n • (⊤:ℕ∞) = ⊤` for `0<n` ("the omega-bridge lemma") | `C118a.lean:80 smul_top_pos` — public, **well-reused** at 40+ call sites across 15 files | `C127.lean:710`, `C131y.lean:132`, `C27.lean:110`, `C72.lean:201` — **four independent private redefinitions**, `nsmul_top_pos`, each a different tactic proof | duplicate, self-acknowledged (`C72.lean:200`'s own docstring: *"C.127 carries a private copy; `private` does not export"*) — this is the real instance of the brief's "omega-workaround bridge" suspect; the literal word never appears, the pattern does |
| `KeyFrame.stageHeight` ultrametric inequality | should be one line from `ChapB/B32b.min_suppVal_le_suppVal_add` | `C127.lean:742 min_stageHeight_le_add` — 20-line from-scratch re-derivation | true duplicate, but **C127 is upstream of nearly all of ChapC** — high blast radius for a low-value fix; not recommended for this wave |

### 1c. `twistRead` additivity forms

| lemma shape | homes | verdict |
|---|---|---|
| `twistRead` of `0` | public `C130rp2.lean:256 twistRead_zero` vs private `C131aa.lean:61 twistRead_zero` (from scratch) | duplicate, privacy-forced |
| `twistRead` of `1` at height `0` | private generic `C131aa.lean:39 twistRead_zero_one` vs public S2-instance `C130rp1.lean:397 twistRead_zero_one` | same fact, forced-concrete re-derivation because the generic form is private |
| `twistRead` unchanged when the added summand's height strictly exceeds the read height | `C131ae.lean:295 twistRead_add_eq_left_of_lt` ≡ `C131y.lean:204 twistRead_add_deep` | exact duplicate (part of §1a's chain) — `C131y`'s is the one already cited externally, keep it |
| `twistRead` additive at a common height floor | ★ `C130rp2.lean:280 twistRead_add_of_le` | unique, canonical — not a duplicate |
| finite-sum iterate of the floor law | `C130rp4.lean:273 twistRead_finsetSum_of_le` | legitimate n-ary generalization, not a duplicate |
| everything else grep found (`C26:341`, `C35b:305`, `C118b:301`, the six S2-concrete computations in `C130rp1`/`C130rp2`, `C130np3`'s point-level composition) | — | distinct facts, cleared as non-duplicates |

### 1d. `toZ` dictionary — NOT a duplication problem

`toZ : ℕ∞ → WithTop ℤ` is defined exactly once (`C130s6.lean:120`); every dictionary lemma
(`toZ_top`, `toZ_coe`, `toZ_eq_top_iff`, `toZ_le_toZ_iff`, `toZ_min`, `toZ_inj`,
`toZ_eq_intCast_iff` — all in `C130s6`) has exactly one definition site. Two later
additions, `C130rp0.lean:115 toZ_lt_toZ_iff` and `C130nv.lean:97 toZ_add`, are genuine
extensions (both docstring-declared as such), not redefinitions. The recurring "`toZ`
wrapper" pattern (`C130nv.lean:209/218 s2Hgt₁_add_ge/eq`, `C130np0.lean:161 s2PHgt₁_add_ge`,
`C130s6.lean:337/343 s2Hgt₂_add_ge/eq`) is 3–6 lines of hand-conjugation repeated by hand
each time, not a re-proof — a candidate for a **generic combinator** ("an order-embedding
transfers an ultrametric ineq/eq-off-ties pair"), not a dedup.

### 1e. PK-related pair (excluded from enactment — DEFER)

`C130k.lean:150-191` and `C130k2.lean:85-127` carry near-identical field-docstring pairs
(`NodePointSource`/`SplitNodePointSource`'s ultrametric law fields). This is the PK retype's
own deliberate design (`PACKAGING_ROUTE_2026-08-25.md`: `C130k2` was carved out "to avoid
touching landed C130k content") — **DEFER-until-PK-lands**, not a naive dedup target.

---

## 2. Private-helper re-derivation table

~141 `private` declarations exist across the new `C130*`/`C131*` files; ~35–40 of them
collapse into the 13 rows below (the rest are genuine one-off proof-local scaffolding,
correctly excluded). `private` removal never changes a statement or a proof — only
visibility — so every "Yes" row is a pure hygiene fix *except* where a name collision is
flagged.

| # | re-derived fact | private original | re-deriving file(s) | promote? |
|---|---|---|---|---|
| 1 | slot-digit normalizer identity `e₁·⌊(k−(i+e₁t)h)/e₁⌋+(i+e₁t)h=k` | `C21.lean:118 slotDigit_index_spec` (byte-copied already at `C26.lean:145`) | `C131ae.lean:205`, `C131y.lean:111`, `C130rp2.lean:194` (all `private digAt_index_spec`; all self-docstring "private-copy pattern") | **Yes** — no public bare-name collision |
| 2 | `(k:ℕ∞) ≤ addVal O x → π^k ∣ x` | `C26.lean:140 pow_dvd_of_le_addVal` | `C131ae.lean:235`, `C131y.lean:135`, `C130rp2.lean:212`, `C130np3.lean:127` (all `private dvd_of_le_addVal`) | **Yes** |
| 3 | ADD-perturbation coefficient floor (`e₁m+pos·h=k, k<stageHeight B → v(coeff)≥m+1`) | none — independently invented | `C131ae.lean:243`, `C131y.lean:140` (byte-identical `addVal_coeff_of_stageHeight_lt`) | **Yes** — pick one, delete the other |
| 4 | `gaussVal(C c)=addVal O c`; `addVal O (-1)=0` | none | `C131ae.lean:222/97`, `C131y.lean:128/48` (byte-identical) | **Yes** — bundle with #3 |
| 5 | S2 key-degree numeral `deg Φ′=2` | none — fans out from `C130rp8.lean:181` (root) | **7 copies**: `C130kp0:418`, `kp1:147`, `kp3:141`, `kp5:147`, `kp7:152`, `rp8:181`(root), `rp11:137` — all self-docstring "the private-copy pattern" | **Yes** — promote rp8's; kp0/kp1/kp3/kp5/kp7/rp11 already import rp8 transitively |
| 6 | squared-key degree `deg(Φ′·Φ′)=4` (`WithBot`) | `C130rp11.lean:383 s2_g_key_sq_degree` | `C130kp3.lean:153 key_sq_degree_withBot` (different, shorter proof route) | Depends — optional, low priority either way |
| 7 | S2-specialized "`stageHeight 1 = 0`" + two riders | general public form `C131ae.lean:227 stageHeight_one` | 5×: `C130rp1:407/411`, `C130s6:464/469/474`, `C130np0:216/221/226`, `C130np5:120`, `C130rp11:142` | **No promotion needed — delete and cite the existing public lemma** |
| 8 | "unique nonzero element of a 2-element field is 1" | `C80.lean:315 eq_one_of_card_two` (old, private) | `C130s6:359`, `C130kp5:281`, `C130rp11:149` (rp11's own docstring names both prior copies) | **Yes** |
| 9 | S2 dev digits `natDegree < 2` | fan-out; `C130rp6.lean:133` is imported by the others | `C130rp4:135/320`, `C130rp8:187` (self-docstring "private copy of RP-4/RP-6") | **Yes** — promote rp6's |
| 10 | parity-floor pair `a≤2x→⌈a/2⌉≤x` / `a≤2x+1→⌊a/2⌋≤x` | none | `C130rp4:330/342` ≡ `C130rp2:145/157` (byte-identical) | **Yes**, trivial |
| 11 | slot-normalizer lift identity `slot_eq` + `window_data` | `C14.lean:215 slot_eq` — **already** re-declared (same namespace `Uniformity.Density.Tower`) at `C46.lean:123` and `C47.lean:321` | `C131f.lean:55/62` (4th generation copy) | **Yes, but REAL COLLISION RISK**: C14/C46/C47 already share one namespace — cannot blanket-unprivate all four. Promote exactly ONE (C14's, oldest), delete the other three including C131f's, repoint call sites |
| 12 | `dev` of the zero polynomial vanishes at every index | `ChapB/B04.lean:54 dev_zero` (private) | `C131ae.lean:113 dev_zero_any` (private re-derivation of B04's induction) | **Yes** — cross-chapter reuse, zero risk |
| 13 | `gaussVal_neg`/`dev_neg`/`suppVal_neg` — **already public, not actually private** | `ChapB/B39b.lean:656/663/670` — public, transitively imported by all four re-derivers | `C131ae:106/131`, `C131w:134`, `C131y` all redeclare from scratch anyway | **N/A — delete-and-reuse, not promotion.** **Live risk**: `C131af.lean:46-47` already `open`s both B39b's namespace and `C131ae`'s namespace simultaneously — a future bare reference to `gaussVal_neg`/`suppVal_neg` there will be genuinely ambiguous. Not yet triggered only because that file hasn't used the bare name. **Flag for immediate attention independent of the SIMP enactment wave** — this is a live landmine, not just style debt. |

Rows 11 and 13 are the only two with real collision/landmine risk; every other row is a
safe mechanical fix (unprivate the original, delete N re-derivations, repoint their call
sites at the promoted name).

---

## 3. Refuter/quarantine record conventions

Four conventions currently coexist for "this failed / this is dead / this is retired."

| Convention | Location | Naming grammar | Index? | Captures uniquely |
|---|---|---|---|---|
| **A — dedicated directory (old project)** | `lean/quarantine/` (22 files) | `<Name>_<date>.lean.txt` | `README.md` (~175 lines, dated entries) — **not 1:1**: 4/22 files have no matching entry | Full provenance narrative + a re-verified importer census at move time |
| **B — scattered in-place** | directly in `leanfinal/Uniformity/ChapC/` (~23 files) | `*_REFUTATION\|FROZEN_REFUTED\|CERT\|REDRAFT_CERT\|RESIGN_CERT\|CITE_CERT\|VACUITY.lean.txt` or `*_BLOCKED\|REFUTED\|DEFECT_<date>.md` | **None** — findable only by `ls`/grep | `.lean.txt`: real compilable Lean disproof code, kept `.lean.txt` (not `.lean`) *specifically* so `lake build` skips it. `.md`: pure prose blocker narrative |
| **C — in-file `QUARANTINE` marker** | e.g. `C130s17.lean:259,288,322`, `C130k2.lean:19` | `QUARANTINE (<unit>, <date>): ...` docstring prefix, no file move | none (grep target only) | Dead code kept *compiling* because a live `IsEmpty`/emptiness theorem (`C130sg`) quantifies over it — **cannot** be moved to a `.lean.txt` without breaking that live proof (confirmed against `PACKAGING_ROUTE_2026-08-25.md:149-151`) |
| **D — process verdict records** | `runs/wave-a/`, `runs/wave-b/` | `verdict_<UNIT>.md` (one per unit-of-work, not per lemma) | none (flat dir) | LANDED/SUPPLY/BLOCKED table + exact-blocker prose + verification commands + files touched |

**Concrete overlap found**: `runs/wave-b/verdict_FD01.md` and `C130k2.lean:288-292`'s
QUARANTINE comment record the *same* refutation (`FGMNSourceLaws (s2DepthTwo…) 2 1 5` is
unsatisfiable for every key chain) in near-verbatim prose, each pointing at the other by
filename, while the actual proof lives in a third place
(`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`). A reader has three places to check for one
fact.

**Proposed uniform convention**: keep B/C/D exactly as they are (moving them is
unnecessary churn, and C is *structurally* immovable per the PK note above) but add **one**
new project-wide append-only index, `docs/DEAD_ENDS_INDEX.md`, one row per dead/refuted
node: `{node ID, convention, file(s), one-line reason, superseded-by}`. Make the citation
direction mandatory going forward: the Lean-side artifact (B or C) cites the process record
(D) by path (as `C130k2.lean` already does for `verdict_FD01.md`), and D-side prose should
stop re-narrating the mathematical content — just cite the B/C artifact. Backfill convention
A's 4 orphaned README entries (documentation-only, zero proof risk). **Nothing needs to
move.**

---

## 4. Structural file sprawl — the C130*/C131* consolidation grouping

### 4a. Per-file map (grouped by topic; S/M/L = size <10KB / 10–30KB / >30KB)

**Freeze-v2 preamble** (CC-0,b,d,f): `C130a`(S, carrier core) · `C130b`(S, layers b/c) ·
`C130d`(S, layers d/e, BLOCKED, no decls) · `C130f`(S, Laurent lattice export)

**Chain-carrier backbone core** (CC-1..6, HOLD — imported by the PK-deferred ring):
`C130k`(M) · `C130s2`(M) · `C130tr`(M) · `C130ln`(M) · `C130s6`(L)

**Chain-carrier PK-retype cluster** (CC-5,7-13,16-18 — **DEFER**, PK12 RUNNING):
`C130k2`(M) · `C130st`(M) · `C130th`(M) · `C130in`(M) · `C130pt`(M) · `C130cr`(L) ·
`C130ar`(M) · `C130vw`(M) · `C130fg`(M) · `C130pk`(M) · `C130s17`(L) · `C130s18`(L) ·
`C130sg`(L)

**FGMN scalar-law pair** (CC-14,15, HOLD — downstream of deferred `fg`): `C130la`(M) ·
`C130lb`(M)

**S2-source NV ladder** (level-two product law, staged CORE 1–4/4, STAY SEPARATE):
`C130nv`(M) · `C130nv2`(L) · `C130nv3`(L) · `C130nv5`(M)

**S2-source RP ladder** (`graded_mul`/`normalized_mul`, staged, STAY SEPARATE, HOLD-adjacent
to `fg`): `C130rp0`(M) · `C130rp1`(M) · `C130rp2`(L, 67KB — largest file in the set) ·
`C130rp4`(L) · `C130rp6`(M) · `C130rp8`(L) · `C130rp9`(M) · `C130rp11`(M)

**S2-source KP ladder** (`key_criterion`/`initial_iff_residual`, staged, STAY SEPARATE,
HOLD-adjacent): `C130kp0`(L) · `C130kp1`(L) · `C130kp3`(M) · `C130kp5`(M) · `C130kp7`(L)

**S2-source NP family + FD-0/1 + SG funnel** (mixed; several one-hop from the deferred
ring): `C130np0`(L) · `C130np1`(M) · `C130np3`(M) · `C130np4`(S, hedged status) ·
`C130np5`(M) · `C130np6`(M) · `C130np7`(M) · `C130np8`(M) · `C130fd0`(L) · `C130sg`(L,
**DEFER**, named funnel target)

**DV-graded-engine family C.131a′–y′** (19 files, one blueprint doc
`DV_GRADED_ENGINE_V2_2026-08-24.md`): shared bases `C131a`(S) `C131f`(M) `C131k`(S)
`C131p`(S) — STAY SEPARATE, each has 3–4 importers; small bridge pair `C131d`(S) `C131u`(S)
— **MERGE candidate**; exact-half pair `C131aa`(S) `C131ac`(M) — **MERGE candidate**
(aa is a linear predecessor of ac only); headline/hub results `C131h` `C131m` `C131n`
`C131v`(L) `C131w`(L, C.72 `shadow_floor` headline theorem) `C131y`(M) `C131ad`(M)
`C131ae`(L) — STAY SEPARATE (cross-imported widely outside this sub-cluster); AF-reverse
pair `C131af`(M, 23.7KB) `C131ag`(S) — STAY SEPARATE for now (combined would cross into L
for modest benefit; flagged as the *next* natural merge target if revisited, and per §2 row
13 `C131af` also carries a live namespace-collision risk that should be fixed before any
merge touches it).

**GENTOW2/GENTOW5 supply-cascade + manifest family**: `C99gt`(S, BLOCKED stub) + `C99r`(M,
re-signs it) — **MERGE candidate**; `C102gt`(S) + `C105gt`(S, hedged status) — **MERGE
candidate** (both small, single-consumer `C106m`); `C107gt5`(M) + `C107ac14`(M, sequential
extension of it) — **MERGE candidate** (~31KB combined); `C106m`(S, pure `#check` manifest)
— keep separate (distinct role, not math); `C84d`(M, standalone construction) — keep
separate.

**C.123 "q=2 gate" pair**: `C123`(M) + `C123r`(M) — **STAY SEPARATE by explicit design**
(`C123r`'s own docstring: *"C123.lean (unedited, untouched by this file)"* — a deliberate
non-interference boundary, not incidental sprawl).

**FGMN/exact-degree landmark trio**: `C78adj`(L, ADJUDICATED TRUE) · `C64`(S, REFUTED
FALSE) · `C66b`(S, literature CITE) — **STAY SEPARATE**: each is an individually decisive
verdict on a different node; small size reflects terse decisiveness, not incompleteness.

**Definitional-twin batches**: `C140defs`(S, DT1) + `C141defs`(M, DT2) — **MERGE
candidate**: same category (structure/def-only transcription, "no proof content"),
combined ~30KB of inert definitions, cheapest possible merge.

**READY-batch grab-bags + C27x**: `C150rb1`(S, theta/faithful-band) · `C150rb2`(S, pure
arithmetic) · `C150rb3`(S, composedKey-unblocked family) · `C27x`(M, standalone re-sign) —
**STAY SEPARATE from each other**: these are grouped by *readiness* (drawn from
`verdict_CCUR.md`'s batch lists), not by mathematics; if anything each should eventually be
re-filed next to its true topical cluster (rb1 near `C131y`, rb3 near the `C118`/`C51`
family) rather than merged with its siblings. Low-confidence flag: the RB docstrings name
`verdict_CCUR.md`'s batches but that file was not independently opened to verify.

### 4b. Files flagged low-confidence (need a human/orchestrator double-check, not blocking)

`C130np4`, `C105gt` (both self-hedge "BLOCKED" status in-docstring, not independently
verified against declarations); `C150rb1/rb2/rb3` (topic read off docstring phrasing, not
cross-checked against `verdict_CCUR.md`); `C131af`/`C131ag` (reference
`AF_REVERSE_PLAN_2026-08-25.md` §3 for a unit list not independently opened — unclear if
this "pair" is complete or more C.131af′-family files are still planned).

---

## 5. Ranked enactment plan

Legend: **Effort** (LOW/MED/HIGH person-time), **Risk** (LOW/MED/HIGH of a build regression
or hidden collision), **Payoff** (LOW/MED/HIGH duplication removed / discoverability
gained), **Kind** = MOVE (pure move/rename/visibility, no proof semantics change) vs
PROOF-TOUCH (edits a proof body, even if the statement is unchanged — needs a build +
`#print axioms` re-check per file touched).

### Tier 1 — do first (cheap, safe, mostly MOVE)

| item | effort | risk | payoff | kind |
|---|---|---|---|---|
| Create `docs/DEAD_ENDS_INDEX.md` (§3) | LOW | NONE | MED (discoverability) | new file only |
| Backfill 4 orphaned entries in `lean/quarantine/README.md` (§3) | LOW | NONE | LOW | MOVE (doc only) |
| Promote §2 rows 1,2,4,5,8,9,10,12 (unprivate + delete N re-derivations + repoint citers) | LOW–MED | LOW (no bare-name collisions found) | MED–HIGH (removes ~25 duplicate declarations) | PROOF-TOUCH but mechanical (citation swap, no statement change) |
| Delete §2 row 7's 5 S2-specialized `stageHeight_one` re-derivations, cite `C131ae.stageHeight_one` directly | LOW | LOW | LOW–MED | PROOF-TOUCH, mechanical |
| Consolidate the 4 private `nsmul_top_pos` copies (`C127`, `C131y`, `C27`, `C72`) onto `C118a.smul_top_pos` (§1b) | LOW | LOW | MED–HIGH (self-documented duplication) | PROOF-TOUCH, mechanical |
| Merge `C140defs`+`C141defs` (inert definitional twins, §4a) | LOW | NONE | LOW | MOVE |
| Merge `C130a`+`C130b`+`C130d`+`C130f` (freeze-v2 preamble, §4a — file-sprawl agent's own "lowest-risk merge in the whole set") | LOW | LOW | LOW–MED | mostly MOVE, 2 internal imports to redirect |
| Relocate `toZ_lt_toZ_iff` (`C130rp0`) and `toZ_add` (`C130nv`) into `C130s6` next to the rest of the `toZ` dictionary (§1d) | LOW | LOW | LOW (cosmetic) | MOVE |

### Tier 2 — urgent-flavored, fix regardless of the general wave's scheduling

| item | effort | risk | payoff | kind |
|---|---|---|---|---|
| **Fix the live ambiguous-name landmine in `C131af.lean:46-47`** (opens both `B39b`'s and `C131ae`'s namespaces; §2 row 13) | LOW–MED | the risk *is* the finding — currently dormant, will surface as a hard-to-diagnose error the moment anyone writes a bare `gaussVal_neg`/`suppVal_neg`/`dev_neg` there | MED (prevents a future break) | PROOF-TOUCH, small |
| Resolve the `slot_eq`/`window_data` 4-way namespace collision (`C14`/`C46`/`C47`/`C131f`, §2 row 11): promote `C14`'s, delete the other 3, repoint call sites | MED | MED (same-namespace collision, must sequence carefully) | MED | PROOF-TOUCH |

### Tier 3 — real duplication removal, moderate effort

| item | effort | risk | payoff | kind |
|---|---|---|---|---|
| Unify `C131ae`↔`C131y`'s 11-pair chain (§1a) into one shared home (new small file, or fold into `C131w`) | MED–HIGH | MED (both files are externally consumed — `C130rp2` cites `C131y.twistRead_add_deep`; every external call site must be verified against the merged names) | HIGH (single biggest duplication in the corpus) | PROOF-TOUCH |
| Dedupe `C131ae`'s `dev_neg_of_monic`/private `dev_zero_any` against `C118a`/`C131w`'s public canonical forms (§1b, §2 row 13) | LOW–MED | LOW | MED | PROOF-TOUCH |
| Dedupe `C130kp5`'s char-2 field negation against `C130rp11`'s (§1b) | LOW | LOW | LOW–MED | PROOF-TOUCH |
| Merge GENTOW2/5 supply-cascade pairs: `{C99gt,C99r}`, `{C102gt,C105gt}`, `{C107gt5,C107ac14}` (§4a) | MED | LOW–MED (confirm `C99gt`/`C105gt`'s hedged BLOCKED status first — bookkeeping risk, not proof risk) | LOW–MED | MOVE, after a status check |
| Merge DV-engine small pairs `{C131d,C131u}` and `{C131aa,C131ac}` (§4a) | LOW–MED | LOW | LOW–MED | MOVE |

### Tier 4 — defer or schedule separately (design risk / scheduling)

| item | reason |
|---|---|
| **Everything touching the 13 PK-deferred files** (§0) | PK12 RUNNING — do not touch until it lands |
| Backbone-core merge (`C130k`,`C130s2`,`C130tr`,`C130ln`,`C130s6`) and the FGMN-law pair (`C130la`,`C130lb`) | HOLD — one hop from the PK ring; no live conflict expected but wait for scheduling sanity |
| Generic `toZ`-conjugation combinator lemma (§1d) absorbing the `s2Hgt₁`/`s2Hgt₂`/`s2PHgt₁` wrapper boilerplate | HIGH design risk — this is a genuinely NEW abstraction (cf. the 2026-08-10 SIMPLIFICATION_BLUEPRINT's T1/T2 experience: new general lemmas need a statement-skeleton gate + adversarial pass BEFORE composing, not a mechanical merge) |
| `C127`'s from-scratch ultrametric inequality vs. `ChapB/B32b` (§1b) | real duplicate, but `C127` is upstream of nearly all of ChapC — high blast radius, low reward; not recommended for this wave |
| Re-filing the RB batches (`C150rb1/2/3`) into their true topical neighborhoods rather than merging them with each other (§4a) | cosmetic re-organization, no urgency, lowest priority in the whole map |

---

## Honesty note

This map is a survey, not a commitment. Every Tier 1/2/3 item that touches a proof body
(PROOF-TOUCH) must re-enter the project's standard verification bar when enacted: per-file
`lake env lean`, `#print axioms` unchanged (Lean-core + declared cites only), and the
merged/promoted statement byte-identical to whichever pre-image copy is kept as canonical.
No item here proposes changing any theorem statement. The PK-deferred and HOLD sets (§0,
§4a) are exclusions, not recommendations-to-do-later-without-recheck — re-survey them once
PK12 lands, since the retype may change which files import which.
