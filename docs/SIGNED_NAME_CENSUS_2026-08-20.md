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
| B | TODO |
| C | TODO |
| D | TODO |
| E | TODO |
| F | TODO |
| G | TODO |
| H | banked (see §H) |
| I | banked (see §I) |

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

