/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C134cfs
import Uniformity.ChapC.C134csx
import Uniformity.ChapC.C131aa
import Uniformity.ChapC.C28
import Uniformity.ChapC.C60
import Uniformity.ChapC.C130s6

/-!
# Uniformity.ChapC.C134frt — `[FRT 2026-08-28]`: landing F1.2–F1.8 on the context-split export
(UNIT FRT)

`runs/wave-c/verdict_CFS.md` named F1.2
`block_complement_notdvd` through F1.8 `level2_peel` as the BlockFrontier-family rows
blocked on the dropped internal split data; `runs/wave-c/verdict_CSX.md` landed
`C134csx.context_split`, the re-export of that data (`f = blockFactor L f * g₂ * Wf`,
`g₂`/`Wf` monic, `Wf` point-sided at `(L.u, L.ℓ)`, `g₂`'s residual not `L.r`-divisible at
every pin), and predicted F1.2 needs one more step: the quotient bridge
`f /ₘ blockFactor L f = g₂ * Wf` (monic-division exactness against `context_split`'s
product equation, since `blockFactor L f` is monic).

This file's charge: land the quotient bridge, then each of F1.2–F1.8 per the verdict's
row table, or record BLOCKED-BECAUSE with the exact missing piece when a row's demands
exceed what `context_split` (+ the landed engine) exports.

## Final status

**Landed** (five theorems, all Lean core + the one allowlisted `exists_dvDissection`
cite, inherited through `context_split`):

* `context_split_quotient` — the quotient bridge `f /ₘ blockFactor L f = g₂ * Wf`,
  carrying `context_split`'s clauses on `g₂`/`Wf` verbatim.  Monic-division exactness
  (`Polynomial.div_modByMonic_unique`) against `context_split`'s product equation, since
  `blockFactor L f` is monic (`C134cfs.hasLabel_blockFactor`).
* `hasLabel_of_isTestKey` / `keyDeg₁_dvd_natDegree_of_isTestKey` — a test key IS a
  labelled, degree-pinned block (`C.13`'s own shape unfolds to `HasLabel` with witness
  multiplicity `1`, via `C131aa`'s `isTestKey_isDvPure` + `dvResPoly_testKey`).
* `testKey_dvd_iff_dvd_blockFactor` — **clause 1 of the signed F1.2
  `block_complement_notdvd`**: a test key divides `f` iff it divides `blockFactor L f`.
  Route: `blockFactor L f`'s OWN maximality (`C133mh15.blockFrontier_of_context`'s
  `hmax`), NOT `context_split` — this clause needs none of the complement/point-sided
  data.
* `quotient_dvSupp_ne_top` — **clause 3 of F1.2**: `dvSupp` of the quotient is finite.
  Route: `dvSupp` of any nonzero polynomial is finite (`C130s6.dvSupp_ne_top_of_ne_zero`,
  no purity needed), applied to `g₂ * Wf ≠ 0`.

**BLOCKED-BECAUSE** (documented in prose below, no `theorem`/`axiom`/`sorry` declared):
F1.2's clause 2 (hence the signed `block_complement_notdvd` as a whole), and F1.3–F1.8
in full.  The common missing piece: a level-one (resp. level-two) residual/support
PRODUCT LAW for a factor that is merely "point-sided" (`dvSideDeg = 0`), not fully
`IsDvPure` — the only landed product laws (`fgmn_dv_exact_mul`, `fgmn_residual_mul`,
and the general `C130nv2` chain) either demand full one-sidedness on both factors or
need an "endpoint height" hypothesis the corpus's own in-progress NV-2–NV-4 plan
(`S2_SOURCE_PLAN_2026-08-24.md`) states is not yet available unconditionally.  Exact
per-row accounting in the BLOCKED-BECAUSE section.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Tower.C134frt

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-! ## Part 0 — the quotient bridge -/

/-- **The quotient bridge.** `context_split`'s product equation `f = blockFactor L f * g₂ *
Wf`, transported through monic division: since `blockFactor L f` is monic (`HasLabel`'s
first clause, via `hasLabel_blockFactor`), `f /ₘ blockFactor L f` is exactly `g₂ * Wf`,
carrying the same clauses `context_split` names. -/
theorem context_split_quotient {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    ∃ g₂ Wf : Polynomial O,
      f /ₘ blockFactor L f = g₂ * Wf ∧
      g₂.Monic ∧ Wf.Monic ∧
      (∀ hneW : (dvSideSet F Wf L.u L.ℓ).Nonempty, dvSideDeg F Wf L.u L.ℓ hneW = 0) ∧
      ∀ (hne₂ : (dvSideSet F g₂ L.u L.ℓ).Nonempty) (M₂ : ℕ)
        (hp₂ : dvHgt F g₂ (dvSideMin F g₂ L.u L.ℓ hne₂) = (M₂ : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g₂ L.u L.ℓ hne₂ M₂ hp₂ := by
  obtain ⟨g₂, Wf, hsplit, hg₂mon, hWmon, hWpt, hg₂res⟩ := C134csx.context_split L hπ hh hctx
  refine ⟨g₂, Wf, ?_, hg₂mon, hWmon, hWpt, hg₂res⟩
  have hblockmon : (blockFactor L f).Monic := (C134cfs.hasLabel_blockFactor L hπ hh hctx).1
  have heq : (0 : Polynomial O) + blockFactor L f * (g₂ * Wf) = f := by
    rw [zero_add, ← mul_assoc]; exact hsplit.symm
  have hdeg0 : (0 : Polynomial O).degree < (blockFactor L f).degree := by
    rw [Polynomial.degree_zero, Polynomial.degree_eq_natDegree hblockmon.ne_zero]
    exact WithBot.bot_lt_coe _
  exact (Polynomial.div_modByMonic_unique (g₂ * Wf) 0 hblockmon ⟨heq, hdeg0⟩).1

/-! ## Part 0b — the test-key/`blockFactor` maximality bypass (clause 1 of F1.2, and the
supply for F1.8's `hdvd`) -/

/-- **A test key IS a labelled block** (`HasLabel`, with witness multiplicity `1`): its
degree is pinned at `L.keyDeg₂` (C.13, conjunct 2), it is `dv`-pure at `(L.u, L.ℓ)`
(`isTestKey_isDvPure`, `C131aa`), and its own residual read is exactly `L.r`
(`dvResPoly_testKey`, `C131aa`) — i.e. `L.r ^ 1`. -/
theorem hasLabel_of_isTestKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) : HasLabel L Ψ := by
  have hmon : Ψ.Monic := hΨ.1
  have hdeg : Ψ.natDegree = L.keyDeg₂ := hΨ.2.1
  have hne : (dvSideSet F Ψ L.u L.ℓ).Nonempty := dvSideSet_nonempty F hmon.ne_zero L.u L.hℓ
  have hmem : dvSideMin F Ψ L.u L.ℓ hne ∈ dvSideSet F Ψ L.u L.ℓ := Finset.min'_mem _ _
  have hfin : dvHgt F Ψ (dvSideMin F Ψ L.u L.ℓ hne) ≠ ⊤ :=
    (dvOnSide_of_mem_dvSideSet hmem).2
  obtain ⟨M₀, hM⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨hmon, by rw [hdeg]; exact keyDeg₂_pos L, isTestKey_isDvPure L hΨ,
    hne, M₀, hM.symm, 1, one_pos, ?_⟩
  rw [dvResPoly_testKey hπ L hΨ hne M₀ hM.symm, pow_one]

/-- **The A-C.20 degree pin, from `IsTestKey` alone.** `Ψ.natDegree = L.keyDeg₂`
(`C.13`'s own conjunct 2) unfolds to `(F.e₁ * F.f₁) * (L.ℓ * L.r.natDegree)` under
`LevelDatum.keyDeg₂`'s associativity. -/
theorem keyDeg₁_dvd_natDegree_of_isTestKey {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    (F.e₁ * F.f₁) ∣ Ψ.natDegree :=
  ⟨L.ℓ * L.r.natDegree, by rw [hΨ.2.1, LevelDatum.keyDeg₂]; ring⟩

/-- ★ **Clause 1 of the signed F1.2 `block_complement_notdvd`, landed as its own reusable
lemma.** A test key divides `f` iff it divides `blockFactor L f` — the (→) direction is
`blockFactor_dvd` alone (F1.1), and the (←) direction is `blockFactor L f`'s OWN
maximality clause (`C133mh15.blockFrontier_of_context`'s `hmax`, the same one
`C134cfs.keyDeg₁_dvd_blockFactor_natDegree` reads), fed the test key's `HasLabel` +
degree-pin certificate above. This route needs NEITHER `context_split` NOR the
level-one product law — `context_split`'s complement/point-sided data is not consumed
here. -/
theorem testKey_dvd_iff_dvd_blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {f : Polynomial O} (hctx : BlockContext L f)
    {Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) :
    Ψ ∣ blockFactor L f ↔ Ψ ∣ f := by
  constructor
  · intro hdvd; exact hdvd.trans (C134cfs.blockFactor_dvd L hπ hh hctx)
  · intro hdvd
    obtain ⟨fS, hlab, hdvdf, hdeg, hmax⟩ := C133mh15.blockFrontier_of_context L hπ hh hctx
    rw [blockFactor_eq_of_frontier L hlab hdeg hdvdf hmax]
    exact hmax Ψ ⟨hasLabel_of_isTestKey L hπ hΨ, keyDeg₁_dvd_natDegree_of_isTestKey L hΨ⟩ hdvd

/-- ★ **Clause 3 of the signed F1.2 `block_complement_notdvd`, landed as its own reusable
lemma.** `dvSupp` of ANY nonzero polynomial is finite (`dvSupp_ne_top_of_ne_zero`,
`C130s6`, no purity needed) — apply it to `f /ₘ blockFactor L f = g₂ * Wf`
(`context_split_quotient`), nonzero since both factors are monic. -/
theorem quotient_dvSupp_ne_top {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 0 < F.h) {f : Polynomial O} (hctx : BlockContext L f) :
    dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤ := by
  obtain ⟨g₂, Wf, hq, hg₂mon, hWmon, _, _⟩ := context_split_quotient L hπ hh hctx
  rw [hq]
  exact C130s6.dvSupp_ne_top_of_ne_zero F L.u L.ℓ (mul_ne_zero hg₂mon.ne_zero hWmon.ne_zero)

/-! ## Rows recorded BLOCKED-BECAUSE — F1.2 (clause 2 only) and F1.3–F1.8

None of the seven signed statements below is declared as a `theorem`, `axiom`, or `sorry`
in this file, per the C.33/C.34/C.40 convention: a signed statement is either proved or
left to the leanspec stub.  What follows is the exact accounting of what `context_split`
(+ the landed engine) does and does not reach, established by actually attempting each
row above before writing this section.

### F1.2 `block_complement_notdvd` (leanspec `ChapC.lean:1623-1631`) — TWO OF THREE
CLAUSES LANDED, clause 2 BLOCKED

The signed conclusion is a 3-way conjunction.  Clauses 1 and 3 are landed above as
reusable lemmas (`testKey_dvd_iff_dvd_blockFactor`, `quotient_dvSupp_ne_top`) and are
each a genuine, unconditional theorem — but the signed name asserts all three at once,
and clause 2 does not reduce to anything landed:

* **Clause 1** (`∀ Ψ, IsTestKey L Ψ → (Ψ ∣ blockFactor L f ↔ Ψ ∣ f)`) — LANDED
  (`testKey_dvd_iff_dvd_blockFactor`). Route: `blockFactor L f`'s OWN maximality clause
  (`C133mh15.blockFrontier_of_context`'s `hmax`), fed a test key's `HasLabel` + degree-pin
  certificate (`hasLabel_of_isTestKey`, `keyDeg₁_dvd_natDegree_of_isTestKey`). Does NOT
  consume `context_split` at all — `blockFactor`'s own frontier witness suffices.
* **Clause 3** (`dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤`) — LANDED
  (`quotient_dvSupp_ne_top`). Route: `dvSupp` of ANY nonzero polynomial is finite
  (`C130s6.dvSupp_ne_top_of_ne_zero`, no purity needed at all), applied to
  `g₂ * Wf ≠ 0` via `context_split_quotient`.
* **Clause 2** (`∀ hne' M₀' hp', ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ
  hne' M₀' hp'`) — **BLOCKED.** Via `context_split_quotient`, this reduces to
  `¬ L.r ∣ dvResPoly F H₀ hpin (g₂ * Wf) L.u L.ℓ …`, i.e. transporting `g₂`'s own
  non-divisibility THROUGH multiplication by `Wf` to the product. The only landed
  machinery for `dvResPoly`-of-a-product (`fgmn_dv_exact_mul`, `C66b.lean`,
  `fgmn_residual_mul`, `C66.lean`) demands BOTH factors be `IsDvPure` with
  `(F.e₁*F.f₁) ∣ natDegree` and positive degree — fences `Wf` does not carry (`Wf` is
  "point-sided", not one-sided/pure, and `context_split` exports no degree-divisibility
  or positivity for it). The more general (non-purity) level-one product law
  (`C130nv2.dvSupp_add_le_dvSupp_mul`, the `≥`-direction, universal) bounds `dvSupp` from
  BELOW, not enough to pin the residual value; the EXACT form
  (`C130nv2.dvSupp_mul_eq_add_of_endpoint_le`) needs an extra hypothesis `hup` — "the
  endpoint slot's height upper bound" — that the module's own header states is NOT
  unconditionally available ("No unconditional level-two product law: the endpoint
  height upper bound … enters here only as the hypothesis `hup`") and is discharged only
  inside the S2 numeric instantiation, not for a general frame/datum. This is exactly
  the open "no-interaction lemma" the CFS/CSX verdicts named for F1.3
  (`dv2Pin_mul_complement`, plan sizing 70–120 lines) — the SAME missing multiplicative
  transport, one level down. Not attempted here as new mathematics; out of this charge's
  scope (combine-landed-pieces, not author-new-node).

Since clause 2 is unreachable, the signed `block_complement_notdvd` itself is NOT
declared in this file (declaring it would require either a `sorry`, forbidden by the
corpus's zero-banked-`sorry` policy, or weakening the conjunction, forbidden by the
statement fence).

### F1.3 `dv2Supp_translation` (`ChapC.lean:1635-1641`) — BLOCKED

Needs F1.2 in full (clause 2, blocked above) plus the level-TWO analogue of the same
missing transport (the `dv2`-graded product law): `docs/in-progress/
S2_SOURCE_PLAN_2026-08-24.md`'s NV-1–NV-4 chain is the corpus's own in-progress
infrastructure for exactly this, and `C130nv2.lean`'s header states in so many words that
no unconditional (frame-generic) form exists yet. Missing piece: `dv2Pin_mul_complement`
(the no-interaction lemma), not yet written.

### F1.4 `dv2ResPoly_scalar` (`ChapC.lean:1714-1724`) — BLOCKED

Needs F1.3 (blocked) — the scalar identity is stated relative to the SAME translated
`dv2` pin that F1.3 would supply; no independent route.

### F1.5 `dv2ResPoly_radical_eq` (`ChapC.lean:1689-1699`) — BLOCKED

Needs F1.4 (blocked) — a unit-scalar cancellation over `K₂` applied to F1.4's identity.

### F1.6 `mult₂_readable` (`ChapC.lean:2307-2315`) — BLOCKED

Needs F1.3 (blocked) — the same-min/same-sideDeg conclusion is F1.3's translation read at
the two chosen minimizers.

### F1.7 `dv2_length_sum` (`ChapC.lean:2320-2328`) — BLOCKED

Needs F1.6 (blocked) per the verdict's chain (F1.1, landed, is not enough alone).

### F1.8 `level2_peel` (`ChapC.lean:1728-1735`) — BLOCKED (unchanged from `C40.lean`,
re-verified today)

`C40.lean`'s standing analysis (2026-08-20, last re-verified in this unit 2026-08-28)
still applies verbatim: clause (ii) needs C.61's `tier1_typeOf` at GENERAL `L.ℓ`, and
`C61.lean`'s own header confirms it remains "BLOCKED at general `L.ℓ`; PROVED
UNCONDITIONALLY at `L.ℓ = 1`" only — no unconditional general-`ℓ` supplier has landed.
Clause (iii) sits on leanspec defect D13 (the two multiplicities — C.35's `mult₂` and
`HasLabel`'s existential `m` — are not tied in general; `C35b.lean`'s
`hasLabel_natDegree_dvd_false` machine-refutes the one-unit question that would have
settled it). `context_split` supplies split data `block_complement_notdvd` would have
needed, but neither C.61 nor D13 is a `BlockFrontier`/split-data gap — this row's block
is orthogonal to what `context_split` exports, so re-deriving the split changes nothing
here.
-/

end Uniformity.Density.Tower.C134frt

/-! ## AxCheck footer — only the landed declarations; the seven BLOCKED-BECAUSE rows
above are documentation, not declarations, so there is nothing to print for them. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C134frt.context_split_quotient
#print axioms Uniformity.Density.Tower.C134frt.hasLabel_of_isTestKey
#print axioms Uniformity.Density.Tower.C134frt.keyDeg₁_dvd_natDegree_of_isTestKey
#print axioms Uniformity.Density.Tower.C134frt.testKey_dvd_iff_dvd_blockFactor
#print axioms Uniformity.Density.Tower.C134frt.quotient_dvSupp_ne_top

end AxCheck
