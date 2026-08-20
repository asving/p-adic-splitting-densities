# SIGNED-NAME CENSUS — chapters B through I (2026-08-20)

**READ-ONLY AUDIT. No `.lean` file was changed; nothing was proved.**

## Why this document exists

Project progress has been reported off a proxy — *"612 blueprint nodes, 526 landed,
86 open"* — where **"landed" means only that a per-node
`leanfinal/Uniformity/Chap*/<node>.lean` file exists and is green.** Three
independent findings on 2026-08-20 showed that proxy breaking in three separate
ways:

1. **File-existence ≠ statement-proved.** C.72, C.114 and H.122 all have green,
   Lean-core, `sorry`-free files while their SIGNED statements are not proved.
2. **Node headings ≠ signed names.** The chapter-H unit's by-name audit of all
   signed ChapH spec names found FIVE unlanded where the node-heading count said
   one (commit `371287c4`).
3. **Landed ≠ asserts anything.** Five of chapter I's landed declarations have
   `True` bodies (blueprint defect I-D12, commit `97dca60c`); E.51's frozen TYPE
   was machine-proved equivalent to bare ℕ arithmetic (`peelRowLawFrozen_iff_arith`,
   commit `ca82c11f`).

This census replaces the proxy with a **per-signed-name** classification.

## STATUS OF THIS DOCUMENT

Chapters are banked one at a time. Anything marked TODO below is **not yet
audited** and must not be read as a result.

| chapter | census status |
|---|---|
| B | banked — mechanical (see §MECH) |
| C | banked — mechanical (see §MECH) |
| D | banked — mechanical (see §MECH) |
| E | banked — mechanical (see §MECH) |
| F | banked — mechanical (see §MECH) |
| G | banked — mechanical (see §MECH) |
| H | banked — hand audit (§H) **and** mechanical (§MECH); scopes differ, see §MECH-4 |
| I | banked — hand audit (§I) **and** mechanical (§MECH); scopes differ, see §MECH-4 |

## Buckets

* **PROVED** — a `theorem`/`lemma` of that name is landed in `leanfinal` with a
  real proof.
* **CARRIER** — landed as a `def`/`structure` naming a `Prop`, asserting nothing
  by itself.
* **PLACEHOLDER-BODY** — the signed statement's own body is `True` or otherwise
  provably content-free.
* **CONDITIONAL** — landed only under an added hypothesis, a carried binder, or
  at a restricted/degenerate stratum.
* **UNLANDED** — no landed declaration of that name.
* **CITE** — discharged by one of the six signed cites.

A seventh label, **DEFN**, is used for signed names that are ordinary
*definitions* rather than statements (`iexp`, `readEquiv`, `CertFamily`, …).
These are not statements and are excluded from the PROVED denominator; they are
counted separately so the arithmetic is auditable rather than hidden.

---

## §I — chapter I (capstone and conditionality)

Signed source: `leanspec/Leanspec/ChapI.lean` (25 blueprint nodes I.01–I.25 plus
A-I.1's two sockets). This section **independently reproduces** the chapter-I
placeholder census of commit `97dca60c` (8 landed declarations, 3 with real content,
5 signed `True`) and adopts its attribution. My instrument found the same 5.

| bucket | count |
|---|---|
| CARRIER | 3 |
| PLACEHOLDER-BODY | 5 |
| UNLANDED | 7 |
| **total signed names** | **15** |

#### CARRIER — 3

| signed name | leanspec form | evidence |
|---|---|---|
| `DecidedSliceAt` | L438 DEF | Prop-def leanfinal/Uniformity/ChapI/I02.lean:98 |
| `MenuLawAt` | L470 DEF | Prop-def leanfinal/Uniformity/ChapI/I03.lean:123 |
| `MenuLawAtVoided` | L484 DEF | Prop-def leanfinal/Uniformity/ChapI/I03.lean:137 |

#### PLACEHOLDER-BODY — 5

| signed name | leanspec form | evidence |
|---|---|---|
| `NS7Termination` | L422 DEF | landed Prop-def body reduces to `True` after peeling binders |
| `WindowPinningAt` | L521 DEF | landed Prop-def body reduces to `True` after peeling binders |
| `GenhnHEAt` | L545 DEF | landed Prop-def body reduces to `True` after peeling binders |
| `GenhnTow1At` | L564 DEF | landed Prop-def body reduces to `True` after peeling binders |
| `TypeOfFaithful` | L1096 DEF | landed Prop-def body reduces to `True` after peeling binders |

#### UNLANDED — 7

| signed name | leanspec form | evidence |
|---|---|---|
| `CanonicalLadderConfig` | L626 DEF | no landed declaration of this name in leanfinal |
| `CanonicalDeepTwistConfig` | L644 DEF | no landed declaration of this name in leanfinal |
| `CapstoneHypotheses` | L714 STRUCTURE | no landed declaration of this name in leanfinal |
| `drainage_of_capstoneHypotheses` | L991 THEOREM | no landed declaration of this name in leanfinal |
| `decided_of_capstoneHypotheses` | L1002 THEOREM | no landed declaration of this name in leanfinal |
| `uniformity_of_capstoneHypotheses` | L1014 THEOREM | no landed declaration of this name in leanfinal |
| `totalMassOne_of_capstoneHypotheses` | L1022 THEOREM | no landed declaration of this name in leanfinal |

**Chapter I verdict: ZERO signed statements PROVED.** Chapter I lands eight
`Prop`-valued carriers and nothing else; five of the eight assert nothing. Its
four signed theorems (I.15–I.18, the assembly toward `UniformityStatement`) and
its capstone hypothesis block `CapstoneHypotheses` are UNLANDED.

Two further facts that the bucket table alone does not carry:

* `CanonicalLadderConfig` (I.10a) is signed with the body `True`, and
  `CanonicalDeepTwistConfig` (I.10b) is signed as
  `CanonicalLadderConfig … ∧ True`. Both are currently UNLANDED, so they are not
  counted in PLACEHOLDER-BODY — but **they are placeholders in the signature**,
  and landing them verbatim would add two more content-free declarations.
* `MenuLawAtVoided` is a `Prop`-def with real content whose *name* records that
  the shape it carries was voided.


---

## §MECH — THE MECHANICAL CENSUS, ALL EIGHT CHAPTERS (2026-08-20)

**Author: the orchestrator (Opus instance) — taking the unit's work over directly.**
The fleet agent built the parsing instrument (`spec/signed_name_census.py`) and the
chapter-I hand audit, then kept dying to API errors every ~25 minutes. Rather than
resume it a fifth time, the orchestrator wrote the driver
(`spec/census_driver.py`) and completed all eight chapters in one context. The
instrument is the agent's; the driver, the run and every number below are the
orchestrator's.

Reproduce: `python3 spec/census_driver.py` (full per-name listing committed at
`docs/SIGNED_NAME_CENSUS_TABLE_2026-08-20.txt`, 1261 lines).

### §MECH-1 The table

| chapter | signed names | PROVED | CONDITIONAL | CARRIER | PLACEHOLDER | UNLANDED | CITE | UNRESOLVED |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| B | 141 | 113 | 3 | 24 | 0 | 0 | 1 | 0 |
| C | 356 | 73 | 1 | 133 | 0 | **147** | 1 | 1 |
| D | 130 | 72 | 0 | 51 | 0 | 7 | 0 | 0 |
| E | 116 | 68 | 1 | 44 | 0 | 3 | 0 | 0 |
| F | 60 | 15 | 0 | 45 | 0 | 0 | 0 | 0 |
| G | 139 | 100 | 0 | 32 | 0 | 7 | 0 | 0 |
| H | 276 | 197 | 0 | 57 | 0 | 22 | 0 | 0 |
| I | 18 | **0** | 0 | 4 | **5** | 9 | 0 | 0 |
| **total** | **1236** | **638** | **5** | **390** | **5** | **195** | **2** | **1** |

### §MECH-2 The headline, stated carefully

**638 of 1236 signed names (52%) are PROVED outright.** But the naive comparison
to the node-level "526 of 612 landed (86%)" would be unfair, and this document
will not make it. The 390 CARRIER entries are signed **definitions**, for which
*landing the definition IS the whole obligation*. Adding those:
`(638 + 390) / 1236 = 83%`, against the node-level 86%. **So the node count was
not wildly wrong, and the earlier framing of a huge hidden gap was overstated.**

What the node count genuinely *hides* is not a headline percentage but four
specific things:

1. **195 UNLANDED signed names, 147 of them in chapter C** — three quarters of
   all unlanded work sits in one chapter. This is the real remaining-work
   concentration and the node count spreads it invisibly.
2. **5 PLACEHOLDER-BODY names, every one of them in chapter I** — statements
   that are LANDED and green while asserting nothing, their body being `True`
   or content-free after peeling binders. Full list at §MECH-3. These are the
   green ticks that prove nothing, and they are the reason this census exists.
3. **5 CONDITIONAL names** (B ×3, C ×1, E ×1) — landed only with more
   hypotheses than signed. C.114's `ht_branch`/`ht_global` and H.122 are the
   known cases; that only 5 are *mechanically* detectable means the
   hypothesis-count heuristic is weak, not that only 5 exist. See §MECH-5.
4. **Chapter I is 0/18 PROVED.** Seven chapter-I nodes were transcribed on
   2026-08-20 and the honest count of statements proved by that work is zero.

### §MECH-3 Every PLACEHOLDER-BODY name (the list that matters most)

All five are chapter I. This is blueprint defect **I-D12**, declared by the
blueprint itself — not a shortcut taken by any agent. This driver and the
independent hand audit of `97dca60c` agree on **exactly these five**, by
different methods.

| name | leanspec | why it asserts nothing |
|---|---|---|
| `TypeOfFaithful` | L1096 `def` | definiens `True` — **and this one is ledger HYP.01 [CORE-SET] + HYP.105, THE TRUST BOUNDARY** |
| `NS7Termination` | L422 `def` | content-free after peeling binders |
| `WindowPinningAt` | L521 `def` | definiens `True` |
| `GenhnHEAt` | L545 `def` | definiens `True` |
| `GenhnTow1At` | L564 `def` | definiens `True` |

**Placeholders in the SIGNATURE that are not yet landed** are counted UNLANDED,
not here, since nothing green rests on them — but landing them verbatim would
add content-free declarations, so they are named for the record:
`CanonicalLadderConfig` (I.10a, signed `True`), `CanonicalDeepTwistConfig`
(I.10b, signed `CanonicalLadderConfig … ∧ True`), and the two leanspec
self-test scaffolding names `axchkSelfTestAxiom` / `axchkSelfTestConsumer`
(result type `True`). **I.10a/I.10b are the tower-instantiation sockets on the
project's critical path** — the census records that their signed form is
currently a placeholder.

**The load-bearing one is `TypeOfFaithful`.** Because its body is `True`, any
theorem carrying it as a hypothesis is *unconditionally true*: hypothesizing the
trust boundary costs nothing and buys nothing. Audit row **A-1 is live-but-unrun**
— its trigger is "before any node hypothesizes `TypeOfFaithful`", which landing
the name does not fire but the first consumer will.

### §MECH-4 Scope differs from the hand audits — both are right

The hand audits counted **node-level signed statements**; this driver counts
**every signed declaration in the leanspec**, a wider net. Neither is wrong; they
answer different questions, and the difference is recorded rather than reconciled
away:

* Chapter I: hand audit 15 names, driver 18. The driver additionally counts
  `a1LabelCell` (a helper def) and the two `axchkSelfTest*` scaffolding names.
  **Both agree the PROVED count is ZERO and both name exactly the same five
  PLACEHOLDER-BODY declarations**, by different methods — a genuine
  decorrelated cross-check, and the only place in this census where one exists.
  The two disagreements were both driver bugs and both are fixed (§MECH-5,
  BUG 2 and BUG 4); the hand audit was right each time.
* Chapter H: hand audit 76 node-level names with 5 unlanded (`371287c4`);
  driver 276 names with 22 unlanded. The hand audit's five — H.122, H.121 (iii),
  H.116b, H.116b4, H.123 — are the *node* statements and remain the operative
  list for planning; the driver's 22 includes helper-level names.

### §MECH-5 METHOD, and three driver bugs found and fixed during construction

Recorded because a census is only worth its method, and because each of these
would have produced a confidently wrong published number.

* **Comments stripped first** (the instrument's own design), which is what
  defeats the `package_three_of_drainage` trap: a naive name-grep hits
  declaration syntax quoted inside a module docstring's fenced code block.
* **BUG 1 — `content_free` returns `(bool, reason)`, not `bool`.** The first
  driver did `if SNC.content_free(rt):`, and a non-empty tuple is always truthy,
  so **every** parseable Prop was marked PLACEHOLDER-BODY: a false headline of
  **494 placeholders**. Fixed by unpacking. The true count is 8.
* **BUG 2 — definiens compared as a raw string.** `∀ x, True` did not match the
  trivial-terms set, so `NS7Termination` was filed CARRIER while the chapter-I
  hand audit had found its conclusion to be `True`. That disagreement is what
  exposed the bug. Fixed by running `content_free` (which peels quantifiers) on
  the definiens too.
* **BUG 3 — the retirement form was filed UNRESOLVED.** Where the leanspec
  deletes a stub and leaves an `example` that *uses* the landed declaration, the
  leanspec elaborating **is** a type-level check that the landed name carries the
  signed type — the strongest evidence available. The driver had no signature
  string to compare and filed these as unresolved, producing a spurious
  100/148 unresolved bucket in G and H, and an absurd **0 PROVED for chapter G**
  (a chapter that is nearly complete). Fixed: retirement form + landed
  theorem = PROVED. UNRESOLVED fell from 254 to 1.
* **BUG 4 — placeholder-ness ranked above landedness.** The driver returned
  PLACEHOLDER-BODY before checking whether anything was landed, so signed-but-
  unlanded placeholders (`CanonicalLadderConfig`, the `axchkSelfTest*` pair)
  were counted as placeholders: 8 instead of 5. The hand audit had the right
  precedence — PLACEHOLDER-BODY must mean *landed AND asserts nothing*, because
  the thing worth counting is a green tick that proves nothing. Fixed; the two
  methods now agree on exactly five.
* **Known weakness, not fixed.** CONDITIONAL is detected by comparing binder
  *arity* textually between signed and landed signatures. That catches an added
  hypothesis but misses a *restricted stratum* (C.114's added scope equations
  `hone`/`hnil` are extra binders and are caught; a narrowed range inside an
  existing binder is not). So **5 CONDITIONAL is a floor, not a count.** Any
  planning that depends on the conditional set must use the per-node records,
  not this number.
* Nothing in this census was proved, no `.lean` file was changed, and no
  judgement was upgraded to make a bucket tidier.
