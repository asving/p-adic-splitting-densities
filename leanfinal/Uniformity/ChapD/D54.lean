/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapD.D54 — instance `GT6-CERT-TOP`: the sealed `f₁ = 1, μ₂ = 2` instance

**Chapter D, NODE D.54** [interface] [fresh — GC-13 placeholders]
(`blueprint/CHAP-D_gauge_tchain.md` §7, the certificate witness (T4); amendments A-1 and A-D.1
govern — this node carries no `[repaired: …]` / `[re-signed: …]` tag, so the composed text is
its signed text). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none in
chapter D`, and says exactly why: "the exposure equation `(omega j*) σ* = digit` is the C-side
calculation `EFF.GENTOW6 [supplied-by: chapter C]` — the R5-63A legs live in GENTOW6's spans; D
supplies D.51's firing." Also `PROOF. n/a`, `SIZE. 0 Lean lines`, `ENVIRONMENT. n/a`. §12
rule 4 forbids stubbing a supplier's theorem ("axiomatizing a supplier's theorem would fake the
discharge"), the stage-0e stub gate held it, and this landed copy holds it: the file **imports
nothing and defines nothing**, so it cannot become a silent dependency of a proof.

The chapter-D side of this instance is one thing only: **D.51 fires.** `CertFrame.touched_of_exposed`
(`Uniformity.Density.Gauge`, landed and green) takes `(F.omega j) σ = ξ` and `ξ ≠ 0` to
`F.Touched j`; supplying that premise at `j*`, `σ*` is GENTOW-6's calculation, not D's.

## ⚠ THE SCOPE FENCE — a signed row, and a BLOCKED trigger

> R5-63A: **"YES at the sealed scope — `f₁ = 1`, `μ₂ = 2`, `2i_{t*} ≥ D′` — and NO elsewhere."**

The blueprint's TEETH block makes this operational, verbatim: *"the scope fence ('NO elsewhere')
is a signed row — a fleet agent instantiating CERT-TOP outside `f₁ = 1, μ₂ = 2, 2i_{t*} ≥ D′`
must return BLOCKED."* Nothing in this file instantiates CERT-TOP at any scope, so the fence is
not exercised here; it is recorded so that the next agent who reaches for the instance meets it
before writing anything.

## The instance data (source-owned algebra, retained per N-5)

`N-5` is a source-side retention note, not expanded in this chapter: the algebra below stays the
source's, and no chapter-D name is asserted to be any of these objects.

| datum | value |
|---|---|
| the support | `T = {t < f₂ : ĉ_t ≠ 0}` |
| the top index | `t* = max T` |
| the lift monomials | `ĉ_t π^{a_t} x^{i_t}` |
| the standing hypothesis | `2i_{t*} ≥ D′` |

The `(t*, t*)` pair extracts into

| extracted | value |
|---|---|
| coordinate | `j* = ⌊(2e₂t* + 1)/(e₂f₂)⌋` |
| slot residue | `b* = (2e₂t* + 1) mod e₂f₂` |
| height offset | `a* = 2i_{t*} − D′` |
| normalized digit | `(ĉ_{t*})² π^{2a_{t*}} · (wrap unit) ≠ 0` |

with the nonvanishing argued in one line, quoted: **"A product of units in `K₂ˣ`: nonzero — no
binomial coefficient, no characteristic condition."** That is the source's own justification and
it is *unconditional* — it is the fifth of the R5-63A legs below.

## The conditional invocation, and its discharge

Invoking D.51 (LEMMA T4.2(c)) requires **FULL EXPOSURE** in the r3 sense — "the displayed
contribution is the sole summand in its canonical height-`Θ_{j*}` slot" — which is an
ALL-PROVENANCE premise (`EFF.T4.08`, ledger `HYP.113`, D.51's ⚠): uniqueness among
single-extraction contributions does not discharge it. **R5-63A discharges it, at the sealed
scope only**, through `EFF.T4.41`'s five byte-quoted legs:

1. whole-layer classification;
2. weight separation `≥ Θ + δ` for multi-extraction;
3. tracked carries;
4. slot uniqueness;
5. the unconditional nonzero digit.

**Conclusion at that scope:** `ω_{j*} ≠ 0`; `j*` is touched; `ν_{j*}(f_key) = Θ_{j*}` — i.e.
D.51's `CertFrame.touched_of_exposed` followed by D.49's `CertFrame.touched_iff_nu_eq` (the
attainment corollary D.51's own file deliberately does not restate).

## Withdrawn text, carried

The r0 sentence claiming a "literal exposed-slot instance" on the **pre-r3** basis is
**WITHDRAWN** (R5-F2). The governing status of the exposure question is: *"resolved at the
`f₁ = 1` scope, **and only there**"*. A consumer who cites the r0 sentence is citing withdrawn
text.

## Reading notes for a consumer

* **This node discharges nothing in chapter D.** D.51 is unconditional at frame level and
  conditional at instance level; D.54 records that the instance-level condition is met *inside
  the seal* by C's R5-63A legs, and records that it fails outside. The GT3 half of the same
  ledger is D.53.
* **The five legs are not re-proved here and must not be re-stated as Lean facts.** They live in
  GENTOW6's spans (the R5-63A legs X33–X39); giving any of them a Lean name in chapter D would
  be precisely the faked discharge §12 rule 4 fences.

**DEPENDS.** D.45–D.49, D.51 · `EFF.GENTOW6 [supplied-by: chapter C]` (spans 1 and 3 of T4's
GT6 stack; the R5-63A legs X33–X39).

**SOURCE.** `EFF.T4.22` (the instance data), `EFF.T4.23` (the conditional invocation and the r0
withdrawal), `EFF.T4.41` (R5-63A — the discharge, its scope fence, and its acceptance
re-adjudication note).

**TEETH.** S8 PE1(5)/(6) and PE2 GT6 consumption → §12. §13's routing row for T4 S8 PE1(4)–(7)
reads PE1(5) as "**Lean theorem** (D.51/D.52) + D.54's scoped discharge". The scope fence is the
signed BLOCKED row quoted at the top of this file.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
