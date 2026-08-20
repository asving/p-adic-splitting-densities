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

