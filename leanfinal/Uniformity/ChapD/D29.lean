/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D07

/-!
# Uniformity.ChapD.D29 — `ReadBundle`, the sitewise C3 read bundle

**Chapter D, NODE D.29** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §5, the read bundle
and the B-law; amendments A-1, A-D.1, A-D.2 govern — A-D.1 corrected this node's SIGNATURE
DOCSTRING in place, rider R-2, because a stale carrier ID inside a docstring reaches
`leanfinal`, and recorded defect D-D14 against it; the structure itself is byte-unchanged).
ENV-D2 + ENV-D3. One signed declaration, definitional — the head of §5.

*The sitewise read bundle.* Over an arena `A : GaugeArena G K N` (D.07) and a ladder step
`q : ℤ`, a **read bundle** carries:

| field | corpus clause |
|---|---|
| `R : G → K` | the site read `R_{i+1,κ̄_i}` |
| `w : Kˣ` | the ladder unit `w_i := R_{i+1,κ̄_i}(N_i)` |
| `read_n : R (N.n q) = w` | `(C3-ladder-unit)` |
| `ladder_mult : ∀ s, R ((N.n q) ^ s) = w ^ s` | `(C3-ladder-multiplicativity)` |
| `scalar_cov : R (X · g) = R X · res g` (value-zero `g`) | `(C3-graded-scalar-covariance)` |

The `Kˣ` typing of `w` is not cosmetic: it carries BOTH `(C3-read-codomain)` (the read of the
ladder element is a scalar of the level field, not a positive-grade element) and
`(C3-ladder-nonvanishing)` (it is nonzero) — the two-clause gate of T1 r12, honesty item D-H6.
A consumer therefore never has to carry a separate `≠ 0` hypothesis at the ladder site.

## Why a bundle, and why it is never instantiated here

`EFF.T1.03`'s five clauses are "site obligations … not assertions about every homogeneous
initial form". This structure carries exactly the clauses the B-law derivation consumes, at ONE
site (one level `i`, one ladder step `q`), as fields; D.33's B-law is then a two-step proof FROM
the fields. The corpus's own non-import — "T1 does not prove the supplier identity itself"
(`EFF.T1.31`) — is the statement that INSTANTIATING the bundle is somebody else's theorem:
`i = 2` is GENTOW2-B′/B″ `[supplied-by: chapter C]`; `i ≥ 3` is `[GENTOW5-W(i)]` (D.44) behind
`𝒲_{≤i}` (D.55) together with `(H-VARTHETA-RES)_i` (D.62). **No chapter-D node constructs a
`ReadBundle`.**

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (one structure; parent CLAUDE.md trust boundary).
Two disclosed points, both from the blueprint's FAITHFULNESS block, the first **flagged for the
chapter cross-read (§13 item 3)**:

* *(i) `(C3-zero-read)` is absent as a field, deliberately.* `R(0) = 0` has no group-level zero
  to name — `R` is defined on the commutative group `G`, which has no additive zero. In this
  packaging the zero digit multiplies at the `K` level instead (D.34's coefficient `u(β_t)·c_t`
  with `c_t = 0`), which is exactly the corpus's own zero-branch bookkeeping: "For `c_t = 0`,
  `k̂_t = 0` and no finite height is assigned" (`EFF.T1.12`). No consumer in this chapter reads
  a zero slice through `R`.
* *(ii) the fields are independent, so all of them are carried.* The corpus records
  countermodels for exactly this — "a read vanishing on every positive-grade component defeats
  nonvanishing; the initial-form read into `gr(μ_i)` … defeats the scalar codomain"
  (`EFF.T1.03`). In Lean the clauses are CARRIED, not derived, so there is nothing to prove
  here; the countermodels survive as §12's executable regressions guarding the packaging
  (`EFF.T1.42`/`.43`, §12 checks 8–9).

⚠ **A-D.1 / D-D14 (minor, recorded, no change of statement).** `read_n` is DERIVABLE from
`ladder_mult` at `s = 1`: `R ((N.n q) ^ 1) = (w : K) ^ 1`, then `pow_one` on both sides. Both
fields stay signed anyway, because they are two separate corpus clauses (`(C3-ladder-unit)` and
`(C3-ladder-multiplicativity)`, `EFF.T1.03`) and this structure is a transcription of the
corpus's clause list. The practical consequence for a fleet agent CONSTRUCTING an instance: only
one of the two needs real work, the other is `by simpa using …`. The redundancy is not a defect
in the corpus, and it is not repaired here.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: D.01 (`NormSection`) and D.07 (`GaugeArena`, whose `v`/`res` the covariance clause
names), both landed at `Uniformity.ChapD.D01` / `Uniformity.ChapD.D07` (the import of D.07 pulls
D.01) · mathlib `MonoidHom.ker`, `Units`. Nothing else — in particular this file does NOT depend
on D.04/D.08's telescope, which is D.32's business.

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapD.lean` stub body
verbatim, with the blueprint's `namespace Uniformity.Density.Gauge` header restored (the
leanspec wrapper `LeanspecD` is a stub-side artifact; the landed namespace assignment is
`Uniformity.Density.Gauge`, GC-6.2) and per-field docstrings added. The declaration docstring is
the blueprint SIGNATURE's, as corrected in place by A-D.1 rider R-2 — `[GENTOW5-W(i)]` is
**D.44**, `𝒲_{≤i}` is **D.55** and `(H-VARTHETA-RES)_i` is **D.62** in the post-A-1 numbering
("D.62"/"D.60"/"D.67" pre-A-1) — one of the only two ID corrections A-D.1 applied rather than
deferring, precisely because a docstring is landed text.

SOURCE: `EFF.T1.03` (the five boxed clauses, `w_i := R_{i+1,κ̄_i}(N_i)`, `(C3-ladder-unit)`, and
the sitewise sentence); `EFF.T5.04` (`(WF-w)` — the same `w` under T5's naming); `EFF.T5.09` (the
per-level nonvanishing suppliers, transcribed at D.61's interface); `EFF.T1.31` (the
non-import: T1 does not prove the supplier identity).

**TEETH.** T1 §4.2 checks 5, 8, 9 (the read-bundle checks) → carried to INSTANCES, not scored
here: the gates run the FRAME-C tables against a concrete bundle (D.67). A definition supplies
nothing to score; that is why the countermodels of FAITHFULNESS (ii) live in §12 as regressions.

ENVIRONMENT: ENV-D2 + ENV-D3 (`{G : Type*} [CommGroup G]` and `{K : Type*} [Field K]`, written
inline per the B.42 binder rule — this file has no `variable` block; `A` and `q` are the
structure's own explicit parameters, `N` implicit, as signed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- The sitewise C3 read bundle (`EFF.T1.03`): exactly the clauses the B-law consumes, as
fields. Instantiation = the external supplier's theorem (never proved in chapter D): `i = 2` —
GENTOW2-B′/B″ [supplied-by: chapter C]; `i ≥ 3` — `[GENTOW5-W(i)]` (D.44) behind `𝒲_{≤i}`
(D.55) plus `(H-VARTHETA-RES)_i` (D.62). The `w : Kˣ` typing carries BOTH
`(C3-read-codomain)` and `(C3-ladder-nonvanishing)` (D-H6). -/
structure ReadBundle {G K : Type*} [CommGroup G] [Field K] {N : NormSection G}
    (A : GaugeArena G K N) (q : ℤ) where
  /-- The site read `R_{i+1,κ̄_i} : G → K` at this one site (one level, one ladder step). -/
  R : G → K
  /-- The ladder unit `w_i := R_{i+1,κ̄_i}(N_i)`, typed in `Kˣ`: the `Kˣ` typing IS both
  `(C3-read-codomain)` and `(C3-ladder-nonvanishing)` (D-H6). -/
  w : Kˣ
  /-- `(C3-ladder-unit)`: the defining read of the ladder element. ⚠ D-D14 — derivable from
  `ladder_mult` at `s = 1`; signed anyway, as a separate corpus clause. -/
  read_n : R (N.n q) = w
  /-- `(C3-ladder-multiplicativity)`: the read is multiplicative along the ladder. -/
  ladder_mult : ∀ s : ℕ, R ((N.n q) ^ s) = (w : K) ^ s
  /-- `(C3-graded-scalar-covariance)` (+ `(C3-read-codomain)` at the consumed sites): a
  value-zero factor comes out of the read as its arena residue. -/
  scalar_cov : ∀ (X : G) (g : MonoidHom.ker A.v), R (X * (g : G)) = R X * (A.res g : K)

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.ReadBundle
#print axioms Uniformity.Density.Gauge.ReadBundle.mk

end AxCheck
