/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapE.E22 — the LEVEL-ONE instance record (HE3+HE6 composite), as an obligation table

**Chapter E, NODE E.22** [instance-record] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §4 — the
master HE7.A suite). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none
(obligation record; the stub stage checks the table's B-node citations against committed CHAP-B
signatures)`, `PROOF. n/a`, `SIZE. n/a (table)`, and the leanspec census names E.22 and E.23 as
the chapter's only two declaration-free nodes ("**109 signed blueprint declarations** … Nodes
with NO declaration: **E.22** and **E.23**, the two instance-records, which the blueprint itself
signs as tables"). The artifact IS the table below. This file is the landed copy, so the
instance's obligation map survives in the repo next to the chapter's mathematics; like
`Uniformity.ChapD.D64` it deliberately imports nothing and defines nothing, so it can never
become a silent dependency of a proof.

## What is being instantiated

The corpus's S3.1/S3.2 records (`EFF.T2.33` = HE3-INSTANCE, `EFF.T2.34` = HE6-INSTANCE)
instantiate the §4 structures (E.10 `SlotCarrier`, E.11 `LadderKeyData`/block layer, E.12
`RungInterface`) at the level-one frame

* `K = 𝔽_{Q^{f₁}}`, `Φ = Φ′`, `D = D′ = e₁f₁`, `(e_𝒞, f_𝒞) = (e₁, f₁)`,
* `d = dv = e₁v`, `T = D′h`, `dig(A) = γ_{dv(A)}(A)`, `gcd(h, e₁) = 1`,
* dictionary `(e, f) = (e₁e_s, f₁f_s)`,

and `EFF.T2.34` records the block count/degree read `|S_{λ,r}| = D′ℓ·deg r`, `(e,f) =
(e₁ℓ, f₁·deg r)`.

## The obligation map (one row per §4 field, transcribed from the blueprint)

| field (E.10–E.12) | supplier at level 1 | citation form |
|---|---|---|
| `hgt`/`dig` data + `(SLOT-V)/(SLOT-R)` laws | B's digit layer on the `e₁ = 1` slice (B.21 `digAt`, B.22); `e₁ ≥ 2` normalizer reads | B.21/B.22 by node ID; `EFF.HE6.09 [supplied-by: chapter C]` (honesty E-2) |
| `Full`/`hlift` | fullness criterion `k ≥ (i(k)+e₁(f₁−1))h`, uniform `(D′−1)h` | `EFF.T2.10`'s HE6 row: `EFF.HE6.15 .17 [supplied-by: chapter C]`; arithmetic half = E.08/E.32 |
| `hef` `(DEG-EF)` | `D′ = e₁f₁` definitional at the instance | E.01 base rung |
| block `(DEV)`/`(KEY-FREE)`/`hA0` | B's development layer (B.01–B.14) | B node IDs (committed) |
| `sides`/`len`/`hlen_sum` | B's polygon side data (B.16–B.20) via GC-2 | B.16–B.20 by node ID |
| `linFac`/`hiFac`/`hresdeg` | B's residual factorization (B.28–B.30, `sideMin` pin per GC-1/PA-1) | B.28–B.30 by node ID |
| `haccount` (D-E3) + the INTEGRAL `(ACCOUNT)` | `HE6-ACCOUNT` (the resultant identity, κ > D′h) + `HE6-BETA-GUARD` transitivity (Rider 2) | `EFF.HE6.56 [supplied-by: chapter C]` — B's H-2 refusal covers the class-size route |
| `hforce` | test-package clause 6 (local invariants divisible) | `EFF.T2.15` clause 6: `EFF.HE6.29 [supplied-by: chapter C]` |
| `hnonempty`/`hexhaust` | test-package clauses 3–4 (resultant symmetry / disjoint exhaust) | same placeholder family |
| `W`/`wf`/`σRank` `(SEC-RANK)` | `HE3-A-PROOF`'s stage-α termination — an `ℕ`-valued rank (window bound minus current floor) | `EFF.T2.52`'s level-one bullet: `EFF.HE3.02-area [supplied-by: chapter C]`; B's certificates (B.79–B.82) fire the leaf reads |
| `(RISE)` at recenterings | `HE3-A-PROOF` stage-α + `HE6-FAMILY`/`HE6-PROOF` | `EFF.T2.19`'s X02/X10–X11 pins → C placeholders |
| test clauses 1/2/7 + `(WINDOW)`/proxy safety | HE6 test package | C placeholders |

## Fences carried verbatim (`EFF.T2.33`)

* clause-4 block construction is **`(LB1)`-conditional**;
* a clause-5 peel at a **RECENTERED** level-one key is **`(MP1)`-conditional**;
* the **ORIGINAL-key** peel is supplied by `HE6-PEEL-CONVENTION` (a chapter-C placeholder).

**Grade cap** (`EFF.T2.38`): HE3 is consumed at attempt grade 0/2 (clean 1/2), so this instance
and every level-two chain consuming it through S1.8C "remain capped there" — recorded for
chapter I's conditionality bookkeeping, **NOT as a Lean object**.

## The stub-stage obligation, EXECUTED (the B-citation check)

The node's SIGNATURE line makes the stub stage responsible for one mechanical check: that the
table's CHAP-B citations exist, at the kinds cited. `leanspec/Leanspec/ChapE.lean` ran it and
records the result verbatim:

> **E.22's B-node citations all exist in the committed CHAP-B blueprint**, at the kinds cited:
> B.16 [def], B.17–B.19 [lemma], B.20/B.21 [def], B.22 [lemma], B.28/B.29 [def], B.30 [lemma],
> B.51 [lemma], B.58 [theorem], B.63 [theorem], B.73 [def], B.74 [lemma], B.77 [lemma],
> B.79/B.80 [theorem], B.81 [lemma], B.82 [theorem]. (Note the live CHAP-B re-sign log A-F.6…
> A-F.10 has moved several of those signatures since; E.22 cites them by node ID, so the rows
> survive, but the instance-supplier reading must be re-checked when B freezes.)

That check is a citation-existence check ONLY. It does not verify that the cited B declarations
have the strength the row needs — the A-F.6…A-F.10 caveat above is exactly the residual, and it
is owed at B's freeze, not here.

## Four reading notes the landed copy must carry

1. **Nothing in this table is discharged by chapter E.** Every row names a supplier OUTSIDE the
   node: chapter B (by committed node ID, on the `e₁ = 1` slice), chapter C (as a GC-13
   `[supplied-by: chapter C]` placeholder), or E's own arithmetic nodes E.01/E.08/E.32 for the
   arithmetic halves only. A fleet agent who finds a chapter-E node that appears to *prove* one
   of these rows has found a defect, not a discharge.
2. **Honesty E-2 binds the pin anchors.** The nine HE6 pin anchors
   (`EFF.HE6.09 .13 .14 .15 .17 .29 .30 .32 .56`) resolve to CHAP-B node IDs only on the
   `e₁ = 1` slice, where B transcribed them. The class-size/count route in `.30`/`.32` is CHAP-B's
   H-2 refusal and the `e₁ ≥ 2` twist/ϖ-normalizer content of `.13`/`.14` is CHAP-B H-1
   out-of-scope: all four resolve to **chapter-C GC-13 placeholders**, "never to HE6 frozen text
   and never to a nonexistent B node. No chapter-E node may cite those four anchors any other
   way."
3. **Honesty E-1's HE7-side residual rides every row whose supplier is an HE7 unit citing an HE6
   span**: HYP.150 is scoped to T2 only, so those rows carry the flag
   `[HE6-A3-UNADJUDICATED FOR HE7]` and state content from HE7's own displays, never from HE6
   frozen text.
4. **The integral `(ACCOUNT)` identity is quoted here in full**, per DECISION D-E3's promise
   (E.12 transcribes only the jump form; the integral form is this instance's obligation):
   *"`Σ_{ρ:F(ρ)=0} min(w_ρ, κ) = D Σ_{λ∈Sides(P)} L_λ min(λ, κ)` — This is the only
   side-accounting identity used by the master proof"*, at `κ > T`, with HE6 proving it on
   `κ > D′h`.

**DEPENDS.** E.10–E.12 (the field list); the CHAP-B nodes cited above; chapter-C placeholders as
listed. No Lean dependency: this file imports nothing.

**SOURCE.** `EFF.T2.33` (HE3-INSTANCE, boxed); `EFF.T2.34` (HE6-INSTANCE, boxed;
`|S_{λ,r}| = D′ℓ deg r`, `(e,f) = (e₁ℓ, f₁ deg r)`); `EFF.T2.16` (the integral `(ACCOUNT)`,
quoted in full in reading note 4 per D-E3); `EFF.T2.56`/`.96` (the final Source-pin line
discipline this table mirrors).

**TEETH.** HE6 seam gate; level-one `(RISE)` discharge tooth; the five-instance perimeter gate →
disposition: the table rows are checked at the stub stage (0e) against B's signatures (executed,
quoted above); C-side rows enter chapter C's TEETH tables. This landed copy discharges no tooth.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.
-/
