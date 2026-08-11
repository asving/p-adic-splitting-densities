Reading additional input from stdin...
2026-08-11T10:17:16.585632Z ERROR codex_models_manager::manager: failed to refresh available models: timeout waiting for child process to exit
2026-08-11T10:17:16.673085Z ERROR codex_models_manager::manager: failed to refresh available models: timeout waiting for child process to exit
2026-08-11T10:17:21.676448Z ERROR codex_models_manager::manager: failed to refresh available models: timeout waiting for child process to exit
OpenAI Codex v0.145.0
--------
workdir: /data/users/asvin/math-and-lean/p-adic-splitting-densities
model: gpt-5.6-sol
provider: openai
approval: never
sandbox: workspace-write [workdir, /tmp, $TMPDIR]
reasoning effort: high
reasoning summaries: none
session id: 019ff053-a60c-72d1-93bf-60ca9d222533
--------
user
EXTREME-DETAIL LEAN FORMALIZATION BLUEPRINT — STAGE-TWO SLICES 1+2.
You are a mathematician-formalizer in a fresh context; you cannot read
files — everything needed is pasted below (the Lean 4 / mathlib target
files verbatim, then the statement ledger of the informal corpus).

CONTEXT: an informal proof corpus (the general-degree p-adic splitting
uniformity theorem) is accepted; formalization (Lean 4 + mathlib) is
beginning. The anchor file Stage2/UniformityTarget.lean (pasted) states
the target over a parameter bundle `RealInstanceAt q n` whose `faithful`
field is a declared placeholder. The existing single-prime gates file
OM/RealInstanceV2Gates.lean (pasted) shows what realness gates look like
at the committed prime. Interface.lean and MontesV2.lean (pasted) carry
the consumed structures.

YOUR CHARGE — produce the formalization blueprint IN EXTREME DETAIL for:
SLICE 1: the `RealInstanceAt` GATES unit — generalize the pasted
  RealInstanceV2Gates content to arbitrary prime q: exactly which gate
  propositions replace `faithful : True`, each stated as a Lean
  `def`/`structure` field IN LEAN SYNTAX (compilable-shaped, not
  pseudocode), with the informal source obligation it encodes.
SLICE 2: the STATEMENT FAN-OUT for the ledger's chain-head statements
  (W-12.A/C/D, GENIND heads, GENHN heads, HE7.A/A', the tower heads —
  pick the ~15 highest statements by the ledger's own labels): for each,
  the Lean statement sketch (types + hypotheses in Lean syntax), which
  existing structures it uses vs which NEW definitions it forces, and
  the dependency edges among the 15.

FOR EVERY UNIT, DELIVER: (a) the Lean statement/def sketch; (b) new
definitions forced (each with its own sketch); (c) dependency list;
(d) mathlib surface needed (name the areas; flag anything mathlib may
lack, e.g. p-adic measure gaps); (e) difficulty tag [mechanical /
standard / hard]; (f) an acceptance test (what compiling+checking looks
like); (g) THE TRANSLATION SPEC: instructions detailed enough that a
LESS CAPABLE model can implement the unit mechanically without making
any mathematical decision — every choice pre-made here.

Rules: do NOT weaken any statement; where the informal ledger and the
Lean shapes diverge, flag the divergence loudly rather than resolving it
silently; number every unit; end with a dependency-ordered
implementation queue and the single line UNITS: <count>.

=== FILE: lean/LeanUrat/Stage2/UniformityTarget.lean (verbatim) ===
/-
# STAGE-2 ANCHOR — the general-degree uniformity target (STATEMENT ONLY)

**FENCE.** This file is the first artifact of stage two (the formalization of the
informal accepted corpus, 2026-08-10). It is NOT imported by any module of the
trusted capstone graph, and it contains exactly one `sorry` — the target theorem's
body — following the established E-phase precedent (HC1/MovesT campaigns: compiling
sorry-statements in fenced campaign files; the repo's zero-banked-sorries policy
governs the trusted corpus, which this file is outside of). `sorryAx` is expected
in THIS file and nowhere else.

**TRUST BOUNDARY — REVIEW REQUESTED.** Lean checks proofs, not statements; this
statement and the `RealInstanceAt` parameter bundle below are new formalized
statements and are flagged for Asvin's review BEFORE any unit targets them
(docs/PROJECT_STATE.md dated append #24).

**WHAT THE TARGET SAYS.** The informal theorem (accepted-text-complete at the
2-clean bar, PROJECT_STATE appends #14–#23): for every degree n and splitting
type σ of degree n there is ONE rational law — a pair of polynomials
(num, den) — such that at EVERY prime p (including wild), the density of monic
degree-n polynomials over ℤ_p with type σ equals num(p)/den(p). The existing
machine-checked capstone (`OM.RealInstanceV2.montes_unconditional`) is the
instance of this at the single real prime `M9.realP`, for the DECIDED (order-0)
density, conditional on the tame functional equation; the target below quantifies
the density tie over an arbitrary real instance family and states the full-density
version behind the exhaustiveness hypothesis, mirroring
`montes_unconditional_exhaustive`'s shape.

**PARAMETER PROVENANCE (S-0 ledger sources).** The `RealInstanceAt` bundle
packages, at an arbitrary prime, exactly the data the real instance supplies at
`M9.realP`: a counting model + Montes data + a density foundation with the honest
bridge (`hbridge` of `MontesV2.goal_theorem_montes`), plus the two standing
conditionalities as explicit hypotheses (the tame functional equation;
exhaustiveness for the full tie). Its realness conditions (that `model` counts
actual ℤ_p-polynomial factorizations — the analogue of the RealInstanceV2Gates)
are recorded as the `faithful` field, stated abstractly here and REVIEW-FLAGGED:
making `faithful` precise per prime is itself a stage-two unit
(mirroring `OM/RealInstanceV2Gates.lean`).
-/
import LeanUrat.MontesV2

namespace LeanUrat.Stage2

open LeanUrat LeanUrat.MontesV2 LeanUrat.CountingModel Polynomial Filter Topology

/-- The data of a real p-adic counting instance at prime `q`, degree `n`:
the abstract objects `MontesV2.goal_theorem_montes` consumes, bundled with the
faithfulness predicate tying the model to genuine ℤ_p counting.
REVIEW-FLAGGED: `faithful` is an abstract placeholder field here; the per-prime
realness gates (the general analogue of `OM/RealInstanceV2Gates.lean`) are a
named stage-two unit and must replace it before this bundle is consumed at
theorem strength. -/
structure RealInstanceAt (q n : ℕ) where
  /-- The counting model (as in `realM2` at the committed prime). -/
  model : CountingModel q n
  /-- The Montes data over the model (as in `realD2`). -/
  data : MontesDataV2 q n model
  /-- The tame density foundation (as in `realF2`). -/
  foundation : DensityFoundation
  /-- The honest measure-wall bridge of `goal_theorem_montes`. -/
  hbridge : ∀ σ : FactorizationType, ∀ q' : ℕ, 1 < q' →
    foundation.density n σ q' = ∑ T ∈ data.shapesOf σ, data.C T q'
  /-- REVIEW-FLAGGED realness placeholder: the model counts monic degree-`n`
  ℤ_p-polynomial factorizations at the prime `q` (the general
  `RealInstanceV2Gates` content). Stated as `True` pending the gates unit so
  that this file compiles as a pure statement anchor; any consumption of
  `RealInstanceAt` at theorem strength before the gates unit lands is
  ILLEGITIMATE and the docstring says so. -/
  faithful : True

/-- **THE STAGE-2 TARGET (the general-degree uniformity theorem, decided
density).** One rational law per (n, σ), valid at every prime
carrying a real instance, conditional per instance on the tame functional
equation — the general form of `montes_unconditional`'s conclusion. The full
(exhaustive) tie is `uniformity_target_exhaustive` below. -/
theorem uniformity_target
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (q : ℕ) (_ : 1 < q) (R : RealInstanceAt q n),
        TameFunctionalEquation R.foundation n σ →
          den.eval (q : ℚ) ≠ 0 ∧
          R.model.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  sorry

/-- **THE STAGE-2 TARGET, full density.** The same law ties the FULL density at
every instance additionally satisfying the exhaustiveness (drainage) hypothesis,
mirroring `montes_unconditional_exhaustive`: the undecided mass at depth `N`
vanishes as `N → ∞`. `undecidedCount` is the model's field, as at the committed
prime. -/
theorem uniformity_target_exhaustive
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (q : ℕ) (_ : 1 < q) (R : RealInstanceAt q n),
        TameFunctionalEquation R.foundation n σ →
        Filter.Tendsto
          (fun N => R.model.undecidedCount N / (q : ℚ) ^ (n * N))
          Filter.atTop (nhds 0) →
          den.eval (q : ℚ) ≠ 0 ∧
          R.model.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  sorry

end LeanUrat.Stage2

/- Statement revision note (2026-08-10, per Asvin's review): palindromicity
DROPPED from both targets — "it might be cleaner not to mention the
palindromicity at all and simply to prove uniformity at all primes"; the
palindromy content remains a capstone-level fact at the committed instance
(montes_unconditional) and is not part of the stage-2 target. -/

=== FILE: lean/LeanUrat/OM/RealInstanceV2Gates.lean (verbatim) ===
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.Order0Alpha

/-!
# OM/RealInstanceV2Gates — the W3 machine-checked gates (G1 non-vacuity, G2 σ-separation)

This module is **Wave 3 of `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`** (§4-W3): the mandatory
machine-checked gates pinned to the CORRECTED real V2 instance's own density
`g_σ(q') := ∑_{T ∈ omMenu n σ} omCount T q'` — the exact sum appearing in the conclusion of the
W2 capstone `RealInstanceV2.montes_unconditional` (named `montes_unconditional_v2` until the W4a
swap, 2026-07-21).

* **G1 (V1 reversal — non-vacuity at the capstone's own density).** At `n = 2`, the INERT type
  `unramType 2 (indiscrete 2)`, and the real prime `realP = 2`, the capstone's menu-sum density
  is EXACTLY `1/4` (`gate_v2_value_inert2`) and hence strictly positive (`gate_v2_nonvacuous`).
  Bonus pin to the instance: the genuine DECIDED-LIMIT density of `realM2` at the inert type is
  `1/4` too (`gate_v2_countingDensity_inert2`, via `realD2`'s decomposition theorem) — the gate
  is against the REAL instance, not the free interface (blueprint D2 mitigation).
* **G2 (O1 reversal — genuine σ-dependence).** At `n = 2`, `q' = 3`: the SPLIT type
  (λ = (1,1)) and the INERT type (λ = (2)) are DISTINCT types with DISTINCT menu-sum values —
  `1/9` vs `1/3` (`gate_v2_split_q3` / `gate_v2_inert_q3` / `gate_v2_sigma_separation`).
  RAMIFIED half: the totally ramified quadratic type `⟨{(2,1)}⟩` has an EMPTY order-0 menu
  (`omMenu_ramified_empty` — order-0 honesty: ramified types stay in the undecided pool), so its
  menu sum is `0` (`gate_v2_ramified_zero`) ≠ the inert `1/4 > 0` at `realP`
  (`gate_v2_ramified_vs_inert`). A σ-discarding regression (the old `if σ = σ₀` shape) fails
  these gates.

The evaluation spine is the singleton-menu collapse `sepShapesOf n (unramType n lam) =
{sepShape n lam}` (`unramType` is injective), which reduces every menu sum to the single
per-shape `omCount` pinned by the OMCountV2 CAL-p gates (`gate3_*`) and the Phase-A `1/4` gate
(`Order0.gate_rootCount_inert2`).

Footprints (`AxCheck` section): every gate must be Lean core ONLY.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.RealInstanceV2Gates

open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM

/-! ## 0. The singleton-menu evaluation bank -/

/-- `unramType n` is INJECTIVE: the type's `(1, d)` multiset recovers the partition's parts
(`d ↦ (1, d)` is injective on multisets), and a partition is its parts. -/
theorem unramType_injective (n : ℕ) : Function.Injective (Order0.unramType n) := by
  intro lam lam' h
  have hdata : lam.parts.map (fun d => ((1 : ℕ), d))
      = lam'.parts.map (fun d => ((1 : ℕ), d)) := congrArg FactorizationType.data h
  have hinj : Function.Injective (fun d : ℕ => ((1 : ℕ), d)) := fun a b hab =>
    ((Prod.mk.injEq _ _ _ _).mp hab).2
  exact Nat.Partition.ext (Multiset.map_injective hinj hdata)

/-- **The σ-keyed order-0 menu of an unramified type is the SINGLETON of its own shape**:
`sepShapesOf n (unramType n lam) = {sepShape n lam}` — injectivity of `unramType` makes the
partition filter pick exactly `lam`. -/
theorem sepShapesOf_unramType (n : ℕ) (lam : Nat.Partition n) :
    Order0.sepShapesOf n (Order0.unramType n lam) = {Order0.sepShape n lam} := by
  ext T
  rw [Order0.sepShapesOf, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_filter] at hl
    rw [unramType_injective n hl.2]
  · rintro rfl
    exact ⟨lam, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- **The V2 capstone's own density collapses to the single per-shape count** at an unramified
type: `∑_{T ∈ omMenu n (unramType n lam)} omCount T q' = omCount (sepShape n lam) q'`. -/
theorem menuSum_unramType (n : ℕ) (lam : Nat.Partition n) (q' : ℕ) :
    (∑ T ∈ OMCountV2.omMenu n (Order0.unramType n lam), OMCountV2.omCount T q')
      = OMCountV2.omCount (Order0.sepShape n lam) q' := by
  rw [OMCountV2.omMenu_order0, sepShapesOf_unramType, Finset.sum_singleton]

/-! ## 1. G1 — non-vacuity (V1 reversal) at the V2 capstone's own density -/

/-- **G1, exact value.** The V2 capstone's menu-sum density at `n = 2`, the INERT type
`unramType 2 (indiscrete 2)`, and the real prime `realP = 2` is EXACTLY `1/4` (the audit's
"1/4 gate", now tied to the W2 capstone's own sum: singleton menu + the Phase-A
`gate_rootCount_inert2` through the D3 compatibility lemma). -/
theorem gate_v2_value_inert2 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
        OMCountV2.omCount T M9.realP) = 1 / 4 := by
  rw [menuSum_unramType, OMCountV2.omCount_sepShape_eq_rootCount]
  exact Order0.gate_rootCount_inert2

/-- **G1 (V1 reversal).** The V2 capstone's menu-sum density is STRICTLY POSITIVE at a concrete
type: the corrected σ-keyed engine density certified by `RealInstanceV2.montes_unconditional` is NOT the
vacuous constant `0`. -/
theorem gate_v2_nonvacuous :
    (0 : ℚ) < ∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
        OMCountV2.omCount T M9.realP := by
  rw [gate_v2_value_inert2]
  norm_num

/-- **G1, pinned to the REAL instance** (blueprint D2 mitigation: gates are stated against the
instance, never the free interface): the genuine DECIDED-LIMIT density of the corrected real
counting model `realM2` at the inert `n = 2` type equals `1/4` — via `realD2`'s decomposition
theorem, so this consumes the instance's `partition` + `stratum_tendsto_C` discharges, not just
the engine evaluator. -/
theorem gate_v2_countingDensity_inert2 :
    (RealInstanceV2.realM2 2 (by norm_num)).countingDensity
        (Order0.unramType 2 (Nat.Partition.indiscrete 2)) = 1 / 4 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (RealInstanceV2.realD2 2 (by norm_num))]
  exact gate_v2_value_inert2

/-! ## 2. G2 — σ-separation (O1 reversal), unramified half -/

/-- **G2, split value.** At `q' = 3` the SPLIT degree-2 type (λ = (1,1)) has menu-sum `1/9`. -/
theorem gate_v2_split_q3 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11), OMCountV2.omCount T 3)
      = 1 / 9 := by
  rw [menuSum_unramType]
  exact OMCountV2.gate3_split_q3

/-- **G2, inert value.** At `q' = 3` the INERT degree-2 type (λ = (2)) has menu-sum `1/3`. -/
theorem gate_v2_inert_q3 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2), OMCountV2.omCount T 3)
      = 1 / 3 := by
  rw [menuSum_unramType]
  exact OMCountV2.gate3_inert_q3

/-- **G2 (O1 reversal).** Two DISTINCT degree-2 factorization types get DIFFERENT V2 capstone
menu-sum values at `q' = 3` (`1/9` vs `1/3`): the certified density is genuinely σ-DEPENDENT —
the old `shapesOf σ₀ σ = if σ = σ₀ then … else ∅` σ-discarding shape is machine-checked dead. -/
theorem gate_v2_sigma_separation :
    Order0.unramType 2 OMCountV2.lam11 ≠ Order0.unramType 2 OMCountV2.lam2
      ∧ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
            OMCountV2.omCount T 3)
        ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
            OMCountV2.omCount T 3) := by
  refine ⟨OMCountV2.gate6_sigma_separation.1, ?_⟩
  rw [gate_v2_split_q3, gate_v2_inert_q3]
  norm_num

/-! ## 3. G2 — σ-separation, ramified half -/

/-- The totally RAMIFIED quadratic type: one factor with `(e, f) = (2, 1)`, degree `2·1 = 2`. -/
def ramType2 : FactorizationType := ⟨{(2, 1)}⟩

/-- `ramType2` has degree 2 (a genuine degree-2 type, comparable with the unramified ones). -/
theorem ramType2_degree : ramType2.degree = 2 := by
  simp [ramType2, FactorizationType.degree]

/-- **The ramified menu is EMPTY** (order-0 honesty: order 0 cannot decide ramified types — they
live in the undecided pool until Phase B): no partition's `unramType` carries an `e = 2` pair. -/
theorem omMenu_ramified_empty : OMCountV2.omMenu 2 ramType2 = ∅ := by
  rw [OMCountV2.omMenu_order0, Order0.sepShapesOf, Finset.image_eq_empty,
    Finset.filter_eq_empty_iff]
  intro lam _ heq
  have hdata : ramType2.data = lam.parts.map (fun d => ((1 : ℕ), d)) :=
    congrArg FactorizationType.data heq
  have hmem : ((2 : ℕ), (1 : ℕ)) ∈ lam.parts.map (fun d => ((1 : ℕ), d)) := by
    rw [← hdata]
    simp [ramType2]
  rw [Multiset.mem_map] at hmem
  obtain ⟨d, -, hd⟩ := hmem
  exact absurd (congrArg Prod.fst hd) (by norm_num)

/-- **G2, ramified value**: the V2 capstone's menu-sum density of the ramified type at `realP`
is `0` (empty menu — the honest "order 0 certifies nothing ramified", NOT a claim that the true
ramified density vanishes). -/
theorem gate_v2_ramified_zero :
    (∑ T ∈ OMCountV2.omMenu 2 ramType2, OMCountV2.omCount T M9.realP) = 0 := by
  rw [omMenu_ramified_empty, Finset.sum_empty]

/-- **G2, ramified separation**: at the real prime the ramified type's menu sum (`0`) differs
from the inert type's (`1/4`) — σ-dependence is visible across the ramified/unramified split
too. -/
theorem gate_v2_ramified_vs_inert :
    (∑ T ∈ OMCountV2.omMenu 2 ramType2, OMCountV2.omCount T M9.realP)
      ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
          OMCountV2.omCount T M9.realP) := by
  rw [gate_v2_ramified_zero, gate_v2_value_inert2]
  norm_num

/-! ## 4. G1-tame — the `htameFE` hypothesis constrains a NONZERO value (semantic audit item 2) -/

/-- **G1-tame (2026-07-19 fresh-context semantic audit, item 2 — the audit's single
JUSTIFICATION GAP, closed).** The capstone hypothesis `htameFE : TameFunctionalEquation realF2 n σ`
quantifies its value clause over TAME primes `q > n` only — and every previously banked positive
value (the `1/4` gate) sits at the WILD prime `q = 2 = n`, outside that quantifier. So no banked
fact excluded the degenerate reading "`realF2.density` vanishes at all tame primes", under which
`htameFE` would be dischargeable by the vacuous `num = 0, den = 1` witness and the capstone's
palindromy clause (P) would constrain nothing.

This gate closes that gap: `3` is prime, `3 > 2` is TAME for `n = 2`, and
`realF2.density 2 (unramType 2 lam2) 3 = 1/3 > 0` (the inert menu sum, `gate_v2_inert_q3` — the
value clause of any `htameFE` witness at the inert type must hit `1/3` at `q = 3`, forcing
`num ≠ 0`). Hence `TameFunctionalEquation realF2 2 σ_inert` genuinely constrains a nonzero
rational function, and (P) is a substantive palindromy claim about it. -/
theorem gate_v2_htameFE_nontrivial :
    Nat.Prime 3 ∧ 2 < 3 ∧
    (0 : ℚ) < RealInstanceV2.realF2.density 2 (Order0.unramType 2 OMCountV2.lam2) 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  show (0 : ℚ) < ∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
      OMCountV2.omCount T 3
  rw [gate_v2_inert_q3]
  norm_num

end LeanUrat.OM.RealInstanceV2Gates

section AxCheck

-- Blueprint W3 gate: every gate theorem must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_value_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_nonvacuous
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_countingDensity_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_split_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_inert_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_sigma_separation
#print axioms LeanUrat.OM.RealInstanceV2Gates.omMenu_ramified_empty
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_zero
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_vs_inert
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_htameFE_nontrivial

end AxCheck

=== FILE: lean/LeanUrat/Interface.lean (verbatim) ===
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.PadicMeasure

/-!
# LeanUrat.Interface — the axiomatic interface ("stated hypotheses")

This module fixes the **axiomatization boundary** for the formalization of the Goal Theorem
(uniform rationality of `p`-adic factorization-type densities at all primes; see
`notes/HUMAN_PROOF.md`). The architecture is "formalize modulo stated hypotheses": everything that
is already in mathlib is *used* from mathlib and is **not** axiomatized here; everything that the
proof legitimately *cites* from the literature is encoded here as a `structure`/`class` carrying the
needed hypotheses, or as a named `axiom`, each with a doc-comment citing its justification.

The boundary, decided minimally (only what later lemmas actually consume):

* **From mathlib (NOT axiomatized).** Finite fields are perfect (`PerfectField.ofFinite`);
  every irreducible over a perfect field is separable (`PerfectField.separable_of_irreducible`);
  `Separable ↔ Squarefree` over a perfect field (`PerfectField.separable_iff_squarefree`);
  polynomial rings, unique factorization (`UniqueFactorizationMonoid`), `degreeLT` and its basis;
  Haar measure existence and valuations (`MeasureTheory`, `Valuation`); finite-field cardinality
  arithmetic. These are real mathlib objects; L1–L7 consume them directly.

* **Axiomatized here (legitimately cited).**
  1. The Guàrdia–Montes–Nart higher-order Okutsu–Montes (OM) structure, distilled to the three
     `p`-independent structural facts **(I)** finite-field residuals, **(II)** lattice Newton
     polygons, **(III)** finite repeated-factor descent (`notes/GMN_citations.md §0`).
  2. The `p`-adic factorization-density / cluster-tree-stratification measure foundations: the
     density `ρ(n,σ;q)`, the cluster-tree stratification, and the per-stratum Haar volume
     (`notes/HUMAN_PROOF.md §0`; cf. paper §2–4 / Igusa §7.4).

Everything in §1 below (the OM facts) is `p`-independent: GMN works over an arbitrary complete
discretely valued field, and the wild/inseparable case is the *generic* case, not an exception.
The *uniformity / rationality* consequences are **derived** (L2core / BB3-∞), never imported.
-/

namespace LeanUrat

open Polynomial MeasureTheory

/-! ## 0. Basic combinatorial data shared by the interface -/

/-- A **factorization shape** at a single OM node: a finitely-supported assignment `d ↦ r_d`
recording the number `r_d` of irreducible factors of degree `d ≥ 1` (counted with multiplicity).
The total degree is `∑ d • r_d`. This is the object L3 / BB3 counts (`notes/L3_proof.md §2.2`). -/
structure FactorizationShape where
  /-- `mult d` is the number of degree-`d` irreducible factors (with multiplicity). -/
  mult : ℕ → ℕ
  /-- Only finitely many degrees occur. -/
  support_finite : (Function.support mult).Finite

namespace FactorizationShape

/-- The total degree `∑_d d · r_d` of a shape. -/
noncomputable def totalDegree (sh : FactorizationShape) : ℕ :=
  ∑ d ∈ sh.support_finite.toFinset, d * sh.mult d

end FactorizationShape

/-! ## 1. The Guàrdia–Montes–Nart order-`r` OM structure (the single load-bearing import)

Source: **J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic number
theory*, Trans. Amer. Math. Soc. 364 (2012), 361–416 (arXiv:0807.2620v2)**. Pinned theorem numbers
are in `notes/GMN_citations.md`. We import *only* the three `p`-independent structural facts (I),
(II), (III); the uniformity consequence is derived, not imported. -/

/-- **GMN order-`r` OM type / cluster node**, carrying exactly the data the cluster recursion
consumes, with the three `p`-independent structural facts attached as fields.

The base residue field is `Fq` (the residue field `F_q` of the unramified `K/Q_p`). The fields of
this structure encode:

* **(I) finite-field residuals** (`GMN §2.1` tower, `Def 2.21`): the order-`r` residual polynomial
  lives in `Fr[y]` with `Fr` a *finite* field, of `p`-independent degree `f₀⋯f_{r-1} ∣ n` over
  `Fq`. This is the linchpin that lets the finite-field building block L3/BB3 apply verbatim at
  every order. Encoded by `[Field Fr] [Finite Fr]` and `residualDegree`.
* **(II) lattice Newton polygon** (`Def 2.3`, `Def 1.1`): the order-`r` polygon `N_r` is a
  principal/lattice object with `p`-independent combinatorics, recorded by `newtonVertices`
  (integer lattice vertices). This is what L4/BB1 consumes.
* **(III) repeated-factor descent** (`Cor 1.20 / 3.8`, `Lemma 3.11(3)`, `Thm 4.18 / Cor 4.19`): a
  multiplicity-1 residual factor is a leaf; a multiplicity-`≥2` factor descends; descent is
  triggered *exactly* by a non-separable residual and terminates at finite, `p`-independently
  bounded order. Encoded by `clusterSize` (strictly decreasing on descent) and `descentBound`. -/
structure OMType (Fq : Type*) [Field Fq] [Finite Fq] where
  /-- The OM/Montes order `r ≥ 0` of this node. -/
  order : ℕ
  /-- The cluster size `e ≤ n` carried at this node. -/
  clusterSize : ℕ
  /-- **(I)** The order-`r` residue field `F_r`. A *finite* field at every order (GMN §2.1). -/
  Fr : Type*
  /-- `F_r` is a field … -/
  [field_Fr : Field Fr]
  /-- … and is finite (the linchpin of fact (I)). -/
  [finite_Fr : Finite Fr]
  /-- The residue degree `f₀⋯f_{r-1}` of `F_r` over `F_q`, a `p`-independent divisor of `n`. -/
  residualDegree : ℕ
  /-- **(II)** The integer lattice vertices of the order-`r` Newton polygon `N_r` (fact (II)). -/
  newtonVertices : List (ℕ × ℕ)
  /-- **(III)** A `p`-independent bound on the descent depth from this node (GMN Thm 4.18 / Cor
  4.19): the OM descent of a separable polynomial terminates at finite, `p`-independently bounded
  order. -/
  descentBound : ℕ

attribute [instance] OMType.field_Fr OMType.finite_Fr

/-- **(III) — the descent trigger, GMN Lemma 3.11(3), stated as a clean interface predicate.**
Descent past order `r` is triggered **exactly** when some order-`r` residual polynomial
`R ∈ F_r[y]` is *non-separable* (equivalently, by finite-field perfectness, *non-squarefree*).

This is the precise locus that L3 counts as `Q_r^{d_r-1}`. We state it as the mathlib predicate
`¬ R.Separable`; the GMN content is that this predicate is the descent trigger, which we record as
the *definition* of `NeedsDescent`. (Citation: `notes/GMN_citations.md §2.3`, Lemma 3.11(3).) -/
def NeedsDescent {Fr : Type*} [Field Fr] (R : Fr[X]) : Prop := ¬ R.Separable

/-- **GMN order-`r` residual-coefficient equidistribution (M6), as a stated hypothesis.**
Fix an OM node `t`. On the Haar-conditioned cell realizing a given finite-slope side, the order-`r`
residual polynomial `R_r(g) ∈ F_r[y]` is **Haar-equidistributed over all monic degree-`d_r`
polynomials over `F_r`**: each fibre has the same conditional measure `|F_r|^{-d_r}`. This converts
L3's *counts* into L2core's *Haar volumes* at every order.

At order 1 this is L4/BB1 (proved exactly); at order `r` it is derived from the GMN order-`r`
coordinate description (`notes/M6_lemma.md`). We expose it as the conclusion the recursion uses: a
uniform conditional probability `condProb` on monic residuals, equal to `(card of the value set) /
|F_r|^{d_r}`. Citation: `notes/M6_lemma.md`; GMN `Def 2.20–2.21`, `Prop 3.5(4)`. -/
structure ResidualEquidistribution {Fq : Type*} [Field Fq] [Finite Fq] (t : OMType Fq) where
  /-- The residual degree `d_r` of the chosen side. -/
  residualSideDegree : ℕ
  /-- The conditional Haar probability that the order-`r` residual lands in a given set of
  monic residual values. -/
  condProb : Finset t.Fr → ℚ
  /-- **Equidistribution.** The conditional probability of any value set `S` of monic residuals
  is `#S / |F_r|^{d_r}` — the uniform measure on `𝔸^{d_r}(F_r)`, the *same* `p`-independent value
  at every prime (M6 conclusion (1)–(2)). -/
  uniform : ∀ S : Finset t.Fr,
    condProb S = (S.card : ℚ) / (Nat.card t.Fr : ℚ) ^ residualSideDegree

/-! ## 2. The `p`-adic factorization-density measure foundations

These encode the measure-theoretic objects of `notes/HUMAN_PROOF.md §0`: the projective/monic
factorization-type density `ρ(n,σ;q)` (an honest Haar **volume**, not a value-weighted integral),
the cluster-tree stratification, and the per-stratum Haar volume. Justification: `p`-adic density
foundations, cf. paper §2–4 / Igusa, *Local Zeta Functions* §7.4. We expose only what L1, L2core,
L6M4, M1 consume: that the density is a real number in `[0,1]`, that the stratification is a finite
partition by cluster-tree shape, and that the total mass is `1`. -/

/-- A **factorization type** `σ` of degree `n`: a multiset of pairs `(eᵢ, fᵢ)` (ramification /
residue data of the irreducible `p`-adic factors) with `∑ eᵢ fᵢ = n` (`notes/HUMAN_PROOF.md §0`). -/
structure FactorizationType where
  /-- The multiset of `(e, f)` pairs. -/
  data : Multiset (ℕ × ℕ)

/-- The degree `n = ∑ eᵢ fᵢ` of a factorization type. -/
def FactorizationType.degree (σ : FactorizationType) : ℕ :=
  (σ.data.map (fun p => p.1 * p.2)).sum

/-! ### `ClusterShape` — the cluster-tree / OM-type shape index (ENRICHED, decision 2b)

A **cluster-tree / OM-type shape** `T` is the index of the cluster recursion (a decorated
Okutsu–Montes tree). For the assembly (L6M4) it is used only as a *decidable index* carrying a
per-shape volume; its internal data is the decorated tree (nodes recorded as
`(order, clusterSize, residualDegree)`). Finitely many shapes contribute to each `(n, σ)` by L5fix
(GMN termination, `p`-independent bound). This object is **distinct** from `FactorizationType`: a
single type `σ` is realized by *many* shapes `T` (different root configurations), and the per-type
density is the multiplicity-weighted sum of per-shape volumes (`DensityFoundation.decomposition`).

**ENRICHED (decision 2b, faithful-by-construction).** Besides the count-native slot list `tree`
(unchanged: it carries the root `(order, clusterSize, residualDegree)` tuple read by
`M5.nodeSizeOf`/`M6.treeSize`/the decoder), the shape now carries the genuine per-node **cell data**
`cells : List ShapeCell`, so that the decoder reconstructs the REAL `MontesAxiom.CountCell` list
faithful-by-construction (NOT the lossy schematic reconstruction the bare `tree` slot would force —
cf. `OMSTEP_BLUEPRINT.md §6/§7.8`). The `tree` slot stays so the descent measure read-back
(`treeSize`/`nodeSizeOf` reading `tree.head.2.1`) and every `⟨tree⟩`-based size lemma are unchanged. -/
mutual
/-- A **cluster-tree / OM-type shape**: the count-native `tree` slot list PLUS the faithful per-node
cell payload `cells` (decision 2b). See the section comment above for the full discussion. -/
structure ClusterShape where
  /-- Count-native slot encoding of the decorated OM tree (root tuple `(order, clusterSize, dr)`
  followed by the concatenated child subtrees). Read by `M5.nodeSizeOf`/`M6.treeSize`. -/
  tree : List (ℕ × ℕ × ℕ)
  /-- **Faithful per-node cell payload** (decision 2b): the genuine `CountCell` data of every cell of
  this node, so the decoder is lossless. Empty for a leaf / order-0 shell. -/
  cells : List ShapeCell
/-- A faithful per-node OM **cell datum**: the genuine `MontesAxiom.CountCell` data of one OM cell —
the residual-stratum degree `dS`, the residue-extension degree `δ`, the lattice Newton-polygon face
`polygon`, and the descent children (each itself a `ClusterShape`). Mirrors `MontesAxiom.CountCell`
but lives upstream (in `Interface`) so the enriched `ClusterShape` can carry it; the down-stream M7
reader erases it back to a genuine `CountCell`. -/
structure ShapeCell where
  /-- residual-stratum degree `d_S`. -/
  dS : ℕ
  /-- residue-extension degree `δ`. -/
  δ : ℕ
  /-- the cell's lattice Newton-polygon face. -/
  polygon : L4.LatticePolygon
  /-- the descent children of this cell (each a strictly smaller cluster shape). -/
  children : List ClusterShape
end

/-- `DecidableEq` for the enriched (recursive, polygon-carrying) `ClusterShape`. The structural
`deriving` handler does not support recursion through `List` nor the function-typed fields of
`L4.LatticePolygon`, so the instance is supplied classically (a legitimate `Decidable` instance, not
an escape hatch). It is `noncomputable`; every consumer of shape-equality in the development is
already `noncomputable` (the sole exception, `Witness.trivCells`, is marked `noncomputable`). -/
noncomputable instance : DecidableEq ClusterShape := Classical.decEq _

/-- `DecidableEq` for `ShapeCell` (classical, as for `ClusterShape`). -/
noncomputable instance : DecidableEq ShapeCell := Classical.decEq _

/-- **The `p`-adic factorization-density foundations, as a stated-hypothesis interface.**

`q` is the residue cardinality (a prime power). `density n σ q` is the **monic/projective
factorization-type density** `α/ρ(n,σ;q)`: the Haar volume of the locus of degree-`n` forms of type
`σ`. The fields record exactly the measure-foundational facts L1/L6M4/M1 consume:

* `density_nonneg`: densities are nonnegative (Haar volumes), not value-weighted integrals
  (load-bearing: at `p=2`, `∫|disc| ≠ volume`; cf. `HUMAN_PROOF §0`).

(C1 docstring fix, `notes/MONTES_AUDIT.md`, 2026-07-02: earlier versions of this docstring advertised
`density_le_one` (densities in `[0,1]`) and `total_mass` (`∑_σ density = 1`) fields that the structure
does NOT carry. The structure is intentionally WEAK — it does not pin `density` to be a probability,
which is exactly why statements about a FREE `F : DensityFoundation` must never be axioms (see
`TameFunctionalEquation` below, the U1 lesson). If those fields are ever added, re-audit every `∀ F`
statement.)

Citation: `p`-adic density foundations, cf. paper §2–4 / Igusa §7.4; cluster-tree stratification
`notes/HUMAN_PROOF.md §0`, L1 `notes/HUMAN_PROOF.md §3`. -/
structure DensityFoundation where
  /-- The factorization-type density `ρ(n,σ;q)` (projective), a rational-valued Haar volume indexed
  by degree `n`, type `σ`, and residue cardinality `q`. -/
  density : (n : ℕ) → FactorizationType → (q : ℕ) → ℚ
  /-- The per-**shape** cluster volume `C_T(q)` — the object of the GMN/BB3-∞ boundary
  (`clusterVolume_rational`). Distinct from the per-type `density`. -/
  clusterVolume : ClusterShape → ℕ → ℚ
  /-- The finite set of cluster-tree shapes contributing to `(n, σ)` (finiteness & `p`-independence
  are L5fix / GMN termination, `notes/L5fix_complete.md`). -/
  shapes : (n : ℕ) → FactorizationType → Finset ClusterShape
  /-- The combinatorial multiplicity `m_T(·)` of a shape — a **polynomial** in `q` (a residue-
  configuration count over `P^1(F_q)`; that it is a *polynomial* in `q` is L3,
  `notes/L3_proof.md §2`). -/
  multiplicity : ClusterShape → Polynomial ℚ
  /-- **Structural decomposition (L1 Hensel-splitting + cluster-tree stratification).** The per-type
  density is the finite, multiplicity-weighted sum of per-**shape** cluster volumes. This is the
  honest measure-foundational / recursion-structure content; it is **NOT** a rationality claim
  (the multiplicities and volumes are arbitrary here). Combined with the per-shape rationality axiom
  `clusterVolume_rational`, L6M4 *derives* that the density is a uniform rational function of `q`.
  Citation: `notes/HUMAN_PROOF.md §3` (L1, splitting), §10 (L6M4 assembly). -/
  decomposition : ∀ (n : ℕ) (σ : FactorizationType), σ.degree = n → ∀ q : ℕ, 1 < q →
    density n σ q = ∑ T ∈ shapes n σ, (multiplicity T).eval (q : ℚ) * clusterVolume T q
  /-- Densities are nonnegative (Haar volumes). -/
  density_nonneg : ∀ n σ q, 0 ≤ density n σ q

/-- **The OM bridge (D1) — the per-shape cluster volume IS a GMN/OM cluster measure.**

This structure is the **structural bridge** (independent-verification defect D1) that ties the
abstract per-shape `clusterVolume` of a foundation `F` to the A0-faithful GMN/Okutsu–Montes cluster
measure of `LeanUrat.PadicMeasure`. It is STRUCTURAL — it asserts only that `F.clusterVolume` is
realized by the FIXED OM cluster measure `PadicMeasure.clusterMeasure` over a decoding
`decode : ClusterShape → OMShape` of the cluster-tree shapes — and is **NOT** a rationality claim.

Rationality is then a THEOREM (`clusterVolume_rational`, below): the FIXED OM cluster measure
`PadicMeasure.clusterMeasure` satisfies the Igusa/Denef cell-decomposition axiom
`PadicMeasure.AX_cellRecursion`, and the proved engine `OMInduction.clusterVol_isRational` (run on
the proved blocks `T_BB1`, `T_BB3`, `L5fix.selfLoop_geometric`) concludes it is a uniform rational
function of `q`. The conclusion is never assumed here; only the realization-as-OM-cluster-measure
(the genuine GMN cluster-tree-stratification content of `notes/BB3_infinity.md`) is.

**Separated out (2026-06-20).** The OM bridge was FACTORED OUT of `DensityFoundation` into this
separate structure so that the measure-free `DensityFoundation` (and the tame functional equation
stated about it) no longer drags `PadicMeasure.clusterMeasure` into the footprint. The only-Montes
Goal theorem (`MontesV2.goal_theorem_montes` — the V2 carrier of the canonical name since W4b,
2026-07-21; the old-`MontesData` sibling is in `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`)
routes rationality through the count-native `MontesDataV2.countingDensity_isRational` and never
references this bridge; the OLD `Goal.goal_theorem`
still consumes it (the measure route — kept for the historical derivation, NOT only-Montes).

**Soundness note (2026-06-19 fix, preserved).** The bridge ties `clusterVolume` to the SINGLE fixed
interface object `PadicMeasure.clusterMeasure` (the actual conditional p-adic Haar cluster volume),
not to a free per-foundation `clusterMeasure` field. With the fixed object, the bridge genuinely
records that `clusterVolume` IS the p-adic cluster measure the Igusa/Denef axiom factors.

Citation: GMN cluster-tree stratification + Igusa/Denef cell decomposition,
`notes/BB3_infinity.md` §4 / `notes/MINIMAL_PADIC_AXIOMS.md`. -/
structure OMBridge (F : DensityFoundation) where
  /-- The decoding of a cluster-tree shape `T` to its GMN order-`r` OM shape (the cluster-tree
  stratification: each `ClusterShape` is the data of a decorated OM tree node, decoded to an
  `OMShape` carrying the finite residue field / lattice polygon / residual). -/
  decode : ClusterShape → PadicMeasure.OMShape
  /-- **The bridge (structural, NOT a rationality claim).** The per-shape cluster volume equals the
  FIXED GMN/OM cluster measure `PadicMeasure.clusterMeasure` of the decoded shape, at every residue
  cardinality. This records that `clusterVolume` is a genuine p-adic cluster Haar measure (the object
  the Igusa/Denef cell-decomposition axiom factors), not an arbitrary function. -/
  clusterVolume_eq_measure :
    ∀ (T : ClusterShape) (q : ℕ), F.clusterVolume T q = PadicMeasure.clusterMeasure (decode T) q

/-! ## 3. The two cited `p`-independence statements feeding the Goal Theorem — NEITHER is an
`axiom` any more (section header refreshed 2026-07-30 verify-2 fold-in)

These are the two genuinely-external `p`-independence statements (the "G-A′" import of
`notes/BB3_infinity.md`, and the tame functional equation H-tame of `notes/HUMAN_PROOF.md §12`).
They were ORIGINALLY stated as named axioms with explicit citations so that the assembled Goal
Theorem's dependence on them would be auditable. Both have since left the axiom base, as each
item's own docstring below records: `clusterVolume_rational` was DE-AXIOMATIZED to a THEOREM
(2026-06-18, soundness-repaired 2026-06-19, bridge separated 2026-06-20), and
`TameFunctionalEquation` is a `def`/predicate consumed as an explicit hypothesis by the Goal
theorems (U1 soundness fix, 2026-07-02). This section contributes ZERO axioms to the trusted
base. -/

/-- **(G-A′) Per-SHAPE cluster volume is a `p`-independent rational function of `q` — NOW A THEOREM.**
For every cluster-tree shape `T`, the per-shape cluster volume `C_T(q)` is represented by a single
`num/den ∈ ℚ(t)` at *every* prime power `q` (all `p`, wild included), at every OM order.

**Scope (the fix for the earlier vacuity bug):** this is about the per-**shape** volume
`F.clusterVolume T`, NOT the per-**type** density `F.density n σ`. The density's rationality is
**derived** from this theorem together with `DensityFoundation.decomposition` (the finite
multiplicity-weighted sum) in `L6M4.density_rational` — it is *not* assumed.

**DE-AXIOMATIZED (2026-06-18, soundness-repaired 2026-06-19; bridge separated 2026-06-20).** This
was an asserted `axiom` (the historical conclusion-shaped boundary); it is now a **THEOREM**, derived
from:
* the OM bridge `B : OMBridge F` fields `decode`/`clusterVolume_eq_measure` (the STRUCTURAL fact —
  GMN cluster-tree stratification — that `F.clusterVolume` is the FIXED genuine OM cluster Haar
  measure `PadicMeasure.clusterMeasure`, NOT a rationality claim). The bridge is now a SEPARATE
  argument (factored out of `DensityFoundation`), so only this OLD measure-route theorem carries it;
* the Igusa/Denef cell-decomposition axiom `PadicMeasure.AX_cellRecursion`, now stated about the FIXED
  objects `PadicMeasure.clusterMeasure`/`omPivot` (the load-bearing analytic boundary, a
  measure-FACTORIZATION identity — and CONSISTENT, witnessed by `PadicMeasure.clusterMeasureModel`,
  not a rationality claim);
* the proved engine `OMInduction.clusterVol_isRational` run on the proved blocks (`T_BB1`, `T_BB3`,
  `L5fix.selfLoop_geometric`, the `RatFn` closure lemmas) and the GMN structural axioms
  (`omCells`, `descend_size_lt`).

Rationality is therefore **never assumed**; it emerges only through the proved engine applied to the
measure-factorization axiom. NOTE: the count-native only-Montes path (since W4b 2026-07-21 the V2
spine: `MontesDataV2.C_isRational` / `MontesDataV2.countingDensity_isRational` in
`LeanUrat/MontesV2.lean`; the old `Decomposition.coeff_isRational` route is quarantined) does NOT
use this theorem and carries NONE of these measure
axioms. Citation: `notes/HUMAN_PROOF.md §8` (L2core / BB3-∞), `notes/BB3_infinity.md`,
`notes/MINIMAL_PADIC_AXIOMS.md`. -/
theorem clusterVolume_rational
    (F : DensityFoundation) (B : OMBridge F) :
    ∀ T : ClusterShape,
      ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
        ∀ q : ℕ, (1 < q) → (den.eval (q : ℚ) ≠ 0) ∧
          F.clusterVolume T q = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  intro T
  -- The decoded shape's FIXED OM cluster measure is a uniform rational function of `q`, by the proved
  -- engine run on the Igusa/Denef cell-decomposition axiom (`AX_cellRecursion`). This is exactly the
  -- `IsRationalFn` predicate of `RatFn`, whose unfolding is the existential below.
  obtain ⟨num, den, hden, h⟩ :=
    PadicMeasure.clusterMeasure_isRational_of_AX (B.decode T)
  refine ⟨num, den, hden, fun q hq => ?_⟩
  obtain ⟨hdenq, hval⟩ := h q hq
  -- Transport along the structural bridge `clusterVolume T q = clusterMeasure (decode T) q`.
  exact ⟨hdenq, by rw [B.clusterVolume_eq_measure T q, hval]⟩

/-- **Semantic palindromy of a rational function `num/den`.** `R := num/den` satisfies the
functional equation `R(1/x) = R(x)` at every `x ≠ 0` where both `R(x)` and `R(1/x)` are defined:
```
    ∀ x ≠ 0, den(x) ≠ 0 → den(1/x) ≠ 0 → num(1/x)/den(1/x) = num(x)/den(x).
```
This is the FAITHFUL, degree-robust encoding of `R(1/t) = R(t)`. The earlier coefficient-reversal
encoding `num.reverse * den = num * den.reverse` was DEGREE-BLIND: via `(reverse f).eval x =
x^(natDegree f)·f.eval(1/x)` it means `x^(deg num − deg den)·R(1/x) = R(x)`, i.e. genuine palindromy
only when `deg num = deg den` (weight-0); it wrongly REJECTS palindromic `R` of unequal reduced
degree (e.g. `t/(t²+1)`). Projective densities are weight-0, but that was nowhere enforced, so the
old clause was an unfaithful statement of the functional equation. (Statement-audit B1, 2026-06-15.) -/
def IsPalindromic (num den : Polynomial ℚ) : Prop :=
  ∀ x : ℚ, x ≠ 0 → den.eval x ≠ 0 → den.eval x⁻¹ ≠ 0 →
    num.eval x⁻¹ / den.eval x⁻¹ = num.eval x / den.eval x

/-- **(H-tame) The tame functional equation, as a `Prop`-valued PREDICATE** (the U1 soundness fix,
2026-07-02).

`TameFunctionalEquation F n σ` says: at tame primes `q > n` the density `F.density n σ` is represented
by a single *palindromic* rational function `R^{tame}_σ ∈ ℚ(t)`, `R^{tame}_σ(1/t) = R^{tame}_σ(t)`.
This is the paper's tame palindromic-weight machinery (§5), untouched by the Prop 5.3 failure; the
proofs use it only via "infinitely many tame `p`," sufficient for the `ℚ(t)` identity theorem (L7).

**HISTORY / WHY THIS IS A `def`, NOT AN `axiom` (U1, `notes/MONTES_AUDIT.md`).** This statement was
previously the GLOBAL AXIOM `tame_functionalEquation (F : DensityFoundation) : ∀ n σ, …` quantified
over an ARBITRARY `F`. That axiom was FALSE-AS-STATED (machine-checked `False`-witness: a legal `F`
with `density := fun _ _ q => q` satisfies every `DensityFoundation` field but is not palindromic —
the axiom then forces `x⁻¹ = x`), so every capstone that consumed it rested on an inconsistent base.
The mathematics (paper §5, Del Corso–Dvornicich (2000), Yin) is a true statement about the REAL
density `ρ`, not about an arbitrary `DensityFoundation.density`. The sound encoding is therefore:

* this PREDICATE, consumed as an explicit HYPOTHESIS `htame : TameFunctionalEquation F n σ` by the
  Goal theorems (`Goal.goal_theorem`, and since W4b 2026-07-21 the V2 carriers of the only-Montes
  names, `MontesV2.goal_theorem_montes` / `MontesV2.goal_theorem_via_montes`) —
  free-`F` statements carry it conditionally;
* (RETIRED, W4a 2026-07-21) the interim concrete NAMED-CITE axiom about the REAL count-native
  density (`OM.M9.realDensity_tame_functionalEquation`) that discharged `htame` for the OLD vacuous
  capstone is GONE with that capstone (blueprint D4; see
  `quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt`) — the current capstone
  `RealInstanceV2.montes_unconditional` consumes this predicate as the explicit HYPOTHESIS
  `htameFE`, so the trusted base carries NO tame axiom;
* the coupled non-vacuity witness (`Witness.trivF_tame`) PROVES the predicate outright for the
  witness bundle (its density is the constant `1`), so the witness instance is now tame-axiom-free.

Citation: `notes/HUMAN_PROOF.md §12` (L7, H-tame); paper §5; Del Corso–Dvornicich (2000), Yin. -/
def TameFunctionalEquation (F : DensityFoundation) (n : ℕ) (σ : FactorizationType) : Prop :=
  ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
    (∀ q : ℕ, q.Prime → n < q → F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
    -- palindromy R(1/t) = R(t), in the FAITHFUL degree-robust semantic form (audit B1):
    IsPalindromic num den

end LeanUrat

=== FILE: lean/LeanUrat/MontesV2.lean (verbatim) ===
/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.RatFn
import LeanUrat.CountingModel
import LeanUrat.L7

/-!
# LeanUrat.MontesV2 — the abstract-coefficient V2 spine (blueprint W1)

This module is **Wave 1 of `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`** (signed off 2026-07-19):
the ADDITIVE V2 spine that replaces the old `MontesAxiom.MontesData`'s hard-pinned per-node
coefficient shape (`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` — the numerically-REFUTED
box-sum semantics, blueprint §1) with an ABSTRACT per-shape coefficient (blueprint D2).

Contents:
* `MontesDataV2` — the minimal abstract-coefficient interface: shape menu + stratum counts +
  partition + an abstract coefficient `C` with rationality and the per-shape counting limit.
* `MontesDataV2.countingDensity_eq_sum_coeff` / `countingDensity_isRational` — the V2 siblings of
  `Decomposition.countingDensity_eq_sum_coeff` / `countingDensity_isRational` (same proofs; the
  abstraction does the work).
* `goal_theorem_montes` / `goal_theorem_via_montes` — the V2 siblings of the OLD
  `Goal.goal_theorem_montes` / `Goal.goal_theorem_via_montes`, verbatim modulo `MontesData →
  MontesDataV2` and `D.coeff → D.C`. Footprint must be Lean core only. (W4b, 2026-07-21: renamed
  from `goal_theorem_montes_v2` / `goal_theorem_via_montes_v2` — they now CARRY the canonical
  names; the old-`MontesData` siblings are retired to
  `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`.)

This was landed as a LEAF module (W1); as of W4a/W4b it is the ONE capstone spine: the W2 real
instance `OM/RealInstanceV2.lean` and the ported `Witness.lean` fire the goal theorems below, and
the old `MontesData` chain is retired.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MontesV2

open Polynomial CountingModel RatFn Filter Topology

/-- **The abstract-coefficient Montes data (blueprint D2) — the V2 replacement of
`MontesAxiom.MontesData`.**

The old `MontesData` froze the ENGINE INTERNALS into the interface: its
`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` fields pinned every instance to the per-node
box-sum coefficient shape, which the 2026-07 numeric campaign REFUTED (blueprint §1, defects
D1–D6). The Goal layer never consumed that shape — it only ever consumed the three derived facts
(the menu-sum decomposition, its rationality, the value tie). `MontesDataV2` therefore carries the
per-shape coefficient ABSTRACTLY: a function `C` together with (i) its uniform rationality and
(ii) the per-shape counting limit `stratumCount T N / q^{nN} → C T q`, plus the level-`N`
partition of the decided count over the shape menu.

⚠ **Statement-fence note (blueprint D2, verbatim intent).** This interface is DELIBERATELY WEAK —
weaker than the old `MontesData`: it demands no per-node recursion shape, so it is satisfiable by
degenerate instances (e.g. an empty menu with `C ≡ 0`). That is by design: the semantics are pinned
at the INSTANCE, not the interface — the corrected real instance sets `C := omCount` (W2), and
non-vacuity/σ-separation are enforced against the REAL instance by the W3 gates
(`gate_rootCount_inert2`-style positivity, the O1-reversal σ-separation examples), NOT here.
Interface-weakening is how vacuity crept in before, so this weakening is flagged for audit
explicitly; any consumer claiming non-vacuity must cite the instance gates, never this structure. -/
structure MontesDataV2 (q n : ℕ) (M : CountingModel q n) where
  /-- For each factorization type `σ`, the finite menu of cluster-tree shapes `T` attached to `σ`
  (the shapes whose strata make up the level-`N` decided count of type `σ`). -/
  shapesOf : FactorizationType → Finset ClusterShape
  /-- The level-`N` stratum count `# S_T^{(N)}` of a shape `T` (the count of level-`N` decided
  monic cosets realizing the combinatorial shape `T`). A `ℚ`-valued integer count. -/
  stratumCount : ClusterShape → ℕ → ℚ
  /-- **PARTITION (`ax:partition`).** At each level `N`, the decided count of type `σ` is the
  finite sum over the σ-menu of the per-shape stratum counts (each decided coset realizes exactly
  one shape). -/
  partition : ∀ (σ : FactorizationType) (N : ℕ),
    M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N
  /-- **The abstract per-shape coefficient `C T q'`** — the limiting normalized stratum measure of
  shape `T`, as a function of the residue cardinality `q'`. Carried abstractly (no per-node
  recursion shape is demanded — blueprint D2); the corrected real instance sets `C := omCount`. -/
  C : ClusterShape → ℕ → ℚ
  /-- **Uniform rationality of the abstract coefficient**: each `C T` is one `num/den ∈ ℚ(t)`,
  denominator nonvanishing at every `q' > 1`, representing `C T q'` there. (For the real instance
  this is `OMCountV2.omCount_isRational`.) -/
  C_isRational : ∀ T : ClusterShape, IsRationalFn (fun q' => C T q')
  /-- **The per-shape counting limit (the value tie).** For every shape on some type's menu, the
  normalized level-`N` stratum count converges to the abstract coefficient evaluated at THIS
  model's residue cardinality `q`. (For the real instance these are the `hNodeLimit` legs.) -/
  stratum_tendsto_C : ∀ (σ : FactorizationType), ∀ T ∈ shapesOf σ,
    Filter.Tendsto (fun N => stratumCount T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (C T q))

/-- Finite `Finset`-indexed sums of uniform rational functions are uniform rational functions.

NOTE (deliberate duplication): this is a local re-proof of `OM.Order0.isRationalFn_finsetSum`
(`OM/Order0Capstone.lean`). Importing that module would drag the heavy `OM/RealInstance` chain
into this deliberately-light leaf, so the 10-line general closure lemma is re-proved here instead. -/
theorem isRationalFn_finsetSum {α : Type*} (s : Finset α) (f : α → ℕ → ℚ)
    (h : ∀ a ∈ s, IsRationalFn (f a)) :
    IsRationalFn (fun q => ∑ a ∈ s, f a q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRationalFn_const 0
  | insert a s ha ih =>
      have hfa : IsRationalFn (f a) := h a (Finset.mem_insert_self a s)
      have hs : IsRationalFn (fun q => ∑ b ∈ s, f b q) :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      simpa [Finset.sum_insert ha] using isRationalFn_add hfa hs

namespace MontesDataV2

variable {q n : ℕ} {M : CountingModel q n} (D : MontesDataV2 q n M)

/-- **The V2 DECOMPOSITION THEOREM: `countingDensity σ = ∑_{T ∈ shapesOf σ} C T q`** — the sibling
of `Decomposition.countingDensity_eq_sum_coeff` over `MontesDataV2`. The genuine DECIDED-LIMIT
density is the finite menu-sum of the abstract per-shape coefficients at this model's `q`. PROVED
modulo the `MontesDataV2` hypotheses:
* at each `N`, `decidedMeasure σ N = ∑_T (stratumCount T N / q^{nN})` (`partition` over the box);
* each summand `→ C T q` (`stratum_tendsto_C`), so the FINITE sum tends to `∑_T C T q`;
* but `decidedMeasure σ N → countingDensity σ` (`CountingModel.density_isLimit`);
* limits in `ℚ` are unique.
No rationality is used. -/
theorem countingDensity_eq_sum_coeff (σ : FactorizationType) :
    M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.C T q := by
  -- (1) at each level `N`, the decided measure is the menu-sum of normalized stratum counts
  -- (`partition`, divided by the box `q^{nN}`):
  have hN : (fun N => M.decidedMeasure σ N)
      = (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) := by
    funext N
    unfold CountingModel.decidedMeasure
    rw [D.partition σ N, Finset.sum_div]
  -- (2) each normalized summand tends to `C T q` (`stratum_tendsto_C`), so the finite sum tends
  -- to the menu-sum of coefficients:
  have hsum_tendsto :
      Tendsto (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) atTop
        (nhds (∑ T ∈ D.shapesOf σ, D.C T q)) :=
    tendsto_finsetSum (D.shapesOf σ) (fun T hT => D.stratum_tendsto_C σ T hT)
  -- (3) but the decided measures tend to `countingDensity σ` (`density_isLimit`); limits are unique:
  have hdec_tendsto :
      Tendsto (fun N => M.decidedMeasure σ N) atTop (nhds (∑ T ∈ D.shapesOf σ, D.C T q)) := by
    rw [hN]; exact hsum_tendsto
  exact tendsto_nhds_unique (M.density_isLimit σ) hdec_tendsto

/-- **The V2 RATIONALITY THEOREM: the menu-sum density function is a uniform rational function of
`q'`** — the sibling of `Decomposition.countingDensity_isRational` over `MontesDataV2`. Each
abstract coefficient is rational (`C_isRational`, an interface field here — for the real instance a
THEOREM, `omCount_isRational`), and `IsRationalFn` is closed under finite `Finset` sums.

Honest scope: this is rationality of the FUNCTION `q' ↦ ∑_T C T q'`; the decomposition theorem
ties `countingDensity σ` (at this `M`'s `q`) to that function's value at `q`. -/
theorem countingDensity_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.C T q') :=
  isRationalFn_finsetSum (D.shapesOf σ) (fun T q' => D.C T q') (fun T _ => D.C_isRational T)

end MontesDataV2

/-- **The V2 only-Montes GOAL THEOREM — the sibling of the OLD `Goal.goal_theorem_montes` over
`MontesDataV2` (blueprint W1, verbatim modulo `MontesData → MontesDataV2`, `D.coeff → D.C`;
W4b 2026-07-21: renamed from `goal_theorem_montes_v2`, now carrying the canonical name — the
old-`MontesData` sibling is retired to `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`).**

For a counting model `M`, abstract-coefficient Montes data `D`, a degree-`n` type `σ`, and an
abstract foundation `F`, GIVEN (i) the honest measure-wall identification `hbridge` (the abstract
foundation's density coincides with the count-native menu-sum `g_σ := q' ↦ ∑_T C T q'` at every
`q' > 1` — NOT a rationality or palindromy claim) and (ii) the tame functional equation `htameFE`
(explicit HYPOTHESIS per the U1 fix — the old global axiom over a free `F` was FALSE-AS-STATED),
there is a single `num/den ∈ ℚ(t)` with: `den ≠ 0`; uniform rationality of `g_σ` at every
`q' > 1`; the genuine counting density at THIS model's `q` equal to `num(q)/den(q)`; and
`IsPalindromic num den` (the faithful semantic `R(1/x) = R(x)`).

The conclusion clauses are IDENTICAL to the old `Goal.goal_theorem_montes`'s; only the hypothesis bundle changed
(abstract `C` in place of the refuted box-sum `coeff`). Rationality flows through
`MontesDataV2.countingDensity_isRational`, the value tie through
`MontesDataV2.countingDensity_eq_sum_coeff`, palindromy through L7's identity-theorem transfer
(`L7.tame_to_all_primes` + `L7.isPalindromic_of_agree`) — all against the SAME `num/den`.

`#print axioms` must show Lean core ONLY (`propext, Classical.choice, Quot.sound` — see the
`AxCheck` section below): every Montes/counting/tame input is a HYPOTHESIS, never an axiom. -/
theorem goal_theorem_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesDataV2 q n M)
    (σ : FactorizationType) (F : DensityFoundation) (hσ : σ.degree = n)
    -- The honest measure-wall identification: the abstract tame foundation's density coincides
    -- with the count-native menu-sum `g_σ` at every residue cardinality (NOT a
    -- rationality/palindromy claim; see docstring):
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q')
    -- (U1 fix) the tame functional equation is an explicit HYPOTHESIS (the old global axiom over
    -- a free `F` was FALSE-AS-STATED; see `Interface.TameFunctionalEquation`):
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      -- (uniform rationality of the count-native density family `g_σ`):
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ D.shapesOf σ, D.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      -- (the genuine counting density at THIS model's `q` IS that rational function's value):
      (1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ)) ∧
      -- (palindromy R(1/t) = R(t), the FAITHFUL semantic form, about the SAME num/den):
      IsPalindromic num den := by
  -- (1) RATIONALITY — count-native, abstract-coefficient path:
  obtain ⟨num, den, hden, hall0⟩ := D.countingDensity_isRational σ
  -- beta-reduce the `IsRationalFn` lambda so the count-native sum appears literally:
  have hall : ∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
      (∑ T ∈ D.shapesOf σ, D.C T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ) := hall0
  -- (2) The genuine counting density at this model's `q` is `g_σ(q)` (V2 decomposition theorem),
  -- hence the value of the rational function `num/den` at `q`:
  have hdensq : 1 < q → M.countingDensity σ = num.eval (q : ℚ) / den.eval (q : ℚ) := by
    intro hq
    rw [D.countingDensity_eq_sum_coeff σ]
    exact (hall q hq).2
  -- (3) Tame palindromic representative for `F.density n σ` (the H-tame hypothesis):
  obtain ⟨tnum, tden, htden, htame, hpalin⟩ := htameFE
  refine ⟨num, den, hden, hall, hdensq, ?_⟩
  -- (4) `num/den` represents `F.density n σ` at every prime power (via `hbridge` + the count-native
  -- rationality), so it agrees in ℚ(t) with the tame palindromic `tnum/tden` (L7 identity theorem),
  -- and the tame functional equation transfers to `num/den` (L7 palindromy transfer):
  have hF : ∀ q' : ℕ, 1 < q' →
      den.eval (q' : ℚ) ≠ 0 ∧ F.density n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ) := by
    intro q' hq'
    obtain ⟨hdenq', hgeq⟩ := hall q' hq'
    exact ⟨hdenq', by rw [hbridge q' hq', hgeq]⟩
  have hagree : num * tden = tnum * den :=
    L7.tame_to_all_primes F n σ hσ num den tnum tden hden htden hF htame
  exact L7.isPalindromic_of_agree num den tnum tden hden htden hagree hpalin

/-- **The V2 re-based uniformity capstone — the sibling of the OLD `Goal.goal_theorem_via_montes`
over `MontesDataV2` (blueprint W1, verbatim modulo names; W4b 2026-07-21: renamed from
`goal_theorem_via_montes_v2`, now carrying the canonical name — the old-`MontesData` sibling is
retired to `quarantine/MontesData_oldSpine_2026-07-21.lean.txt`).** Produces the `F.density`-shaped conclusion
(uniform rationality of the per-type density + palindromy), routing rationality through the
count-native abstract-coefficient pair `(M, D)` plus the honest measure-wall identification
`hbridge`, with the tame functional equation as the explicit hypothesis `htameFE`.

Proof: obtain the count-native `num/den` (rationality + palindromy) from `goal_theorem_montes`,
drop its value clause, and rewrite the count-native rationality onto `F.density` via `hbridge`.

`#print axioms` must show Lean core ONLY (see the `AxCheck` section below). -/
theorem goal_theorem_via_montes
    {q n : ℕ} (M : CountingModel q n) (D : MontesDataV2 q n M)
    (F : DensityFoundation) (σ : FactorizationType) (hσ : σ.degree = n)
    (hbridge : ∀ q' : ℕ, 1 < q' →
      F.density n σ q' = ∑ T ∈ D.shapesOf σ, D.C T q')
    -- (U1 fix) the tame functional equation is an explicit HYPOTHESIS (the old global axiom over
    -- a free `F` was FALSE-AS-STATED; see `Interface.TameFunctionalEquation`):
    (htameFE : TameFunctionalEquation F n σ) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        F.density n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      IsPalindromic num den := by
  obtain ⟨num, den, hden, hgrat, _hval, hpalin⟩ :=
    goal_theorem_montes M D σ F hσ hbridge htameFE
  refine ⟨num, den, hden, fun q' hq' => ?_, hpalin⟩
  obtain ⟨hdenq', hgeq⟩ := hgrat q' hq'
  exact ⟨hdenq', by rw [hbridge q' hq', hgeq]⟩

end LeanUrat.MontesV2

section AxCheck

-- The V2 spine (blueprint W1 gate): every footprint below MUST be Lean core only
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
#print axioms LeanUrat.MontesV2.MontesDataV2.countingDensity_isRational
#print axioms LeanUrat.MontesV2.goal_theorem_montes
#print axioms LeanUrat.MontesV2.goal_theorem_via_montes

end AxCheck

=== FILE: docs/STATEMENT_LEDGER_2026-08-10.md (verbatim) ===
# STATEMENT LEDGER — 2026-08-10 (unit S-0)

**Unit:** S-0, the simplification campaign's byte-tracking instrument
(SIMPLIFICATION_BLUEPRINT_2026-08-10.md S5.1). One row per NAMED
STATEMENT (THEOREM/LEMMA/COROLLARY/PROPOSITION/DEFINITION block with its
label) in the 26-text accepted corpus (blueprint S1 corpus map).
**Instrument:** `verification/openmath/statement_ledger.py --check`
re-extracts and compares md5s against the sealed baseline
(`statement_ledger_baseline.json`); exit 1 with a diff on ANY changed or
deleted statement; additions allowed. This is blueprint S5.3 item 3's
tripwire: "a simplification never weakens a statement" — consumption
checks must display absorbed statements md5-identical to this ledger.

**Baseline:** repo HEAD `1f9e8ae354e0`, generated
2026-08-10T09:50:00+00:00, extractor S0-v1.
**Totals:** 166 statements over 26 notes; 4 unlabeled
(numbered deterministically); 4 truncated at the 120-line cap.

**Normalization (declared):** blockquote markers stripped as block
syntax at extraction; then whitespace-collapse ONLY. A single-token
change to any statement changes its md5 and fires the tripwire.
**Grade provenance:** the blueprint S1 corpus map (25 texts ACCEPTED 2/2;
JD0 PROVED grade, machine 68,523/0, sub-bar) — the notes' own status
headers are heterogeneous free text and are NOT parsed for grades.
**Flags:** T = span truncated at cap; S = span contains struck (~~)
text; U = unlabeled (label assigned by deterministic numbering).

## S1. The ledger (one row per statement)

### LIFTCORNER_2026-08-08.md — commit `fdf1d995`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM (unlabeled) | 962–992 | `b652f278` | U |
| 2 | COR 1 | 994–998 | `8bcb7d3e` | — |
| 3 | COR 2 | 1000–1004 | `650d435a` | — |
| 4 | PROP (unlabeled) | 1034–1069 | `3859bfb8` | TU |

### GRTW2_PROOF_2026-08-08.md — commit `a27ed687`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA W2-C1a | 474–503 | `be975688` | S |
| 2 | THEOREM W2-C1 | 507–526 | `ee27f7cd` | — |
| 3 | LEMMA W2-ID1 | 707–779 | `cd5037b9` | TS |
| 4 | LEMMA W2-T3E | 910–936 | `6bde997e` | — |

### GRTJA_PROOF_2026-08-08.md — commit `fdf1d995`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM JA-PIN | 110–169 | `663c87cc` | S |
| 2 | THEOREM JA-RES | 307–315 | `8a1345fc` | — |
| 3 | COROLLARY JA-VDIND | 326–335 | `fd8c3357` | — |
| 4 | COROLLARY JA-MIN | 388–411 | `68a50d4b` | — |

### GRTJB_PROOF_2026-08-08.md — commit `fdf1d995`, grade: ACCEPTED 2/2, 7 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM JB-DEV | 1402–1495 | `51c79ed1` | TS |
| 2 | LEMMA JB-AFF | 1615–1621 | `8f37bc75` | — |
| 3 | THEOREM JB-VTX | 1623–1694 | `6b2498e5` | S |
| 4 | THEOREM JB-TREE | 1790–1903 | `123aa097` | S |
| 5 | COROLLARY (unlabeled) | 2064–2169 | `8149211c` | SU |
| 6 | LEMMA JB-EPS | 2171–2177 | `83fbac6b` | — |
| 7 | THEOREM JB-CREAD | 2186–2221 | `af2ebcbb` | S |

### GRTJC_PROOF_2026-08-08.md — commit `63091cef`, grade: ACCEPTED 2/2, 11 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-6 | 664–684 | `4cddd908` | S |
| 2 | LEMMA JC-LOC | 1037–1045 | `571c13dc` | — |
| 3 | LEMMA JC-PIINV | 1106–1115 | `0a80a843` | — |
| 4 | LEMMA JC-BSURJ | 1145–1153 | `dec2acb5` | — |
| 5 | COROLLARY JC-COB | 1335–1413 | `478e5ada` | S |
| 6 | THEOREM W-7 | 1419–1438 | `15ddb376` | S |
| 7 | THEOREM JC-CARRY-m | 1479–1485 | `dbd49a4c` | — |
| 8 | THEOREM JC-INNER | 1512–1516 | `f59557de` | — |
| 9 | THEOREM JC-IND | 1552–1553 | `72f6a958` | — |
| 10 | THEOREM W-8 | 1658–1664 | `a400bc0a` | — |
| 11 | COROLLARY W-9 | 1777–1787 | `222be4a8` | — |

### WELDMASTER_2026-08-08.md — commit `fdf1d995`, grade: ACCEPTED 2/2, 3 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM WELD-M | 284–311 | `30b82e4d` | — |
| 2 | THEOREM WM-COB | 344–369 | `4813269b` | — |
| 3 | THEOREM WM-FENCE | 483–599 | `f023af52` | S |

### JD0_PROOF_2026-08-08.md — commit `9387eb1a`, grade: PROVED (machine 68,523/0; sub-bar), 1 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA J-D0 | 49–57 | `68254d43` | — |

### SIGMALAW_PROOF_2026-08-08.md — commit `a27ed687`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA SL-L1 | 122–133 | `69c5cb7c` | — |
| 2 | THEOREM SL-1 | 168–177 | `2ffdbb04` | — |
| 3 | LEMMA SL-L2 | 197–311 | `1868220f` | T |
| 4 | COROLLARY SL-C1 | 332–335 | `0f4d08f8` | — |
| 5 | COROLLARY SL-C2 | 361–372 | `738e49e8` | — |

### W11_PROOF_2026-08-08.md — commit `35e65450`, grade: ACCEPTED 2/2, 1 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-11 | 109–148 | `58d463fc` | S |

### W12_PROOF_2026-08-08.md — commit `2fcbd0c7`, grade: ACCEPTED 2/2, 7 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM W-12.A | 197–231 | `06b4e5d3` | — |
| 2 | THEOREM W-12.C | 250–266 | `afe5b2c0` | — |
| 3 | THEOREM W-12.D | 267–315 | `70bc878f` | — |
| 4 | LEMMA W12-S2.1 | 469–473 | `a9794cfa` | — |
| 5 | LEMMA W12-L0 | 694–706 | `239c0ffe` | — |
| 6 | LEMMA W12-L1 | 742–753 | `3690f7d5` | — |
| 7 | LEMMA W12-S3.2 | 837–839 | `3ee0843d` | — |

### HMENU3_PROOF_2026-08-08.md — commit `19c02857`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM HM3.A | 113–144 | `bb779df1` | — |
| 2 | THEOREM HM3.B | 145–210 | `f07e9cb8` | S |
| 3 | THEOREM HM3.C | 211–225 | `288959f7` | — |
| 4 | COROLLARY HM3.D | 231–267 | `3ba094ba` | — |
| 5 | LEMMA HM3-4 | 383–385 | `4c9dd40d` | — |

### HEX3_PROOF_2026-08-08.md — commit `7e29d9e5`, grade: ACCEPTED 2/2, 3 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM HEX3.A | 123–143 | `30756ab1` | — |
| 2 | THEOREM HEX3.B | 144–157 | `01183b2d` | — |
| 3 | COROLLARY HEX3.C | 158–166 | `9b3f15cf` | — |

### GENIND_PROOF_2026-08-08.md — commit `dfd58316`, grade: ACCEPTED 2/2, 8 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENIND.A | 127–178 | `52f2b4a4` | — |
| 2 | THEOREM GENIND.B | 186–224 | `02dc45ce` | — |
| 3 | LEMMA GENIND-1 | 231–243 | `6d20c11a` | — |
| 4 | LEMMA GENIND-2 | 290–306 | `792e554d` | — |
| 5 | LEMMA GENIND-3 | 346–378 | `49982180` | — |
| 6 | LEMMA GENIND-0 | 525–534 | `5232e76c` | — |
| 7 | LEMMA GENIND-6 | 604–660 | `dd96cd1b` | — |
| 8 | LEMMA GENIND-4 | 1213–1233 | `afa8214b` | — |

### GENH4_PROOF_2026-08-08.md — commit `65681144`, grade: ACCEPTED 2/2, 10 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENH4.A | 86–116 | `1b90bda3` | — |
| 2 | LEMMA GENH4-4 | 138–147 | `5b8d5ba8` | — |
| 3 | THEOREM GENH4.B | 149–169 | `d5545164` | — |
| 4 | THEOREM GENH4.C | 171–181 | `4ed66333` | — |
| 5 | COROLLARY GENH4.D | 183–199 | `c244247c` | — |
| 6 | LEMMA GENH4-1F | 240–251 | `d5605398` | — |
| 7 | LEMMA GENH4-CAP | 294–333 | `8fcbb9de` | — |
| 8 | LEMMA GENH4-2 | 337–354 | `50d638e9` | — |
| 9 | LEMMA GENH4-3 | 376–403 | `6067ad94` | — |
| 10 | LEMMA GENH4-6 | 607–617 | `b1c4f078` | — |

### GENHN_PROOF_2026-08-08.md — commit `59c1966d`, grade: ACCEPTED 2/2, 9 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENHN.CLASS | 127–154 | `1b6bdada` | — |
| 2 | THEOREM GENHN.A | 156–211 | `eb606039` | — |
| 3 | THEOREM GENHN.C | 259–273 | `c8c98e43` | — |
| 4 | LEMMA GENHN-T | 275–301 | `d81fbc66` | — |
| 5 | THEOREM GENHN.B | 303–373 | `4ef55318` | — |
| 6 | LEMMA GENHN-1 | 531–548 | `1b516265` | — |
| 7 | LEMMA GENHN-2 | 699–717 | `73a1d718` | — |
| 8 | LEMMA GENHN-3 | 741–763 | `1d6aa5f6` | — |
| 9 | LEMMA GENHN-T #2 | 1127–1210 | `c932ac30` | — |

### HE3_PROOF_2026-08-08.md — commit `8ba8c878`, grade: ACCEPTED 2/2, 16 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION 1 | 242–251 | `14e5992f` | — |
| 2 | DEFINITION 2 | 288–310 | `2d144eb4` | — |
| 3 | THEOREM HE3.A | 312–331 | `ef48e8d3` | — |
| 4 | COROLLARY HE3.B | 333–367 | `6c44365c` | — |
| 5 | COROLLARY HE3.C | 369–378 | `b5efc2d1` | — |
| 6 | LEMMA HE3-1 | 450–478 | `022b3a55` | S |
| 7 | LEMMA HE3-1L | 498–514 | `d910b382` | — |
| 8 | LEMMA HE3-1′ | 548–559 | `93410450` | S |
| 9 | LEMMA HE3-0 | 648–671 | `db0aeb83` | — |
| 10 | COROLLARY HE3-0′ | 684–687 | `8dcbef7f` | — |
| 11 | LEMMA HE3-2 | 702–747 | `2bba660b` | S |
| 12 | COROLLARY HE3-2′ | 811–815 | `eeafb977` | — |
| 13 | LEMMA HE3-3 | 830–833 | `bf91e937` | — |
| 14 | LEMMA HE3-4 | 983–989 | `8e344d4f` | — |
| 15 | LEMMA HE3-6 | 1118–1121 | `531b7d3b` | — |
| 16 | LEMMA HE3-5 | 1238–1258 | `b8d77bc3` | — |

### HE6_PROOF_2026-08-08.md — commit `dc63a84e`, grade: ACCEPTED 2/2, 13 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA HE6-1L | 130–199 | `0d03d1da` | — |
| 2 | DEFINITION HE6-1 | 201–213 | `187ff3a9` | — |
| 3 | LEMMA HE6-0″ | 215–238 | `376a2177` | — |
| 4 | LEMMA HE6-0 | 240–242 | `01ae336b` | — |
| 5 | LEMMA HE6-0′ | 244–248 | `887f79b7` | — |
| 6 | LEMMA HE6-1 | 250–253 | `85d23d67` | — |
| 7 | LEMMA HE6-2 | 255–264 | `b2ee5808` | — |
| 8 | LEMMA HE6-2′ | 266–269 | `779f1a73` | — |
| 9 | LEMMA HE6-3 | 271–278 | `c6644fa6` | — |
| 10 | LEMMA HE6-4 | 280–282 | `7dcc0367` | — |
| 11 | LEMMA HE6-5 | 284–287 | `5e137498` | — |
| 12 | THEOREM HE6.A | 289–301 | `e31bea9d` | — |
| 13 | COROLLARY HE6.B | 311–331 | `9cb6d5da` | — |

### HE7_PROOF_2026-08-08.md — commit `fe589460`, grade: ACCEPTED 2/2, 24 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION HE7-1 | 93–109 | `8c7fa1b9` | — |
| 2 | THEOREM HE7.A | 197–251 | `0a90b21f` | — |
| 3 | THEOREM HE7.C | 253–277 | `821982b0` | — |
| 4 | COROLLARY HE7.B | 279–293 | `a4f763be` | — |
| 5 | LEMMA HE6R1-2 | 294–305 | `94c22908` | — |
| 6 | THEOREM HE7.D | 307–314 | `79ed380f` | — |
| 7 | LEMMA HE7-L1 | 379–402 | `e3efbb57` | — |
| 8 | DEFINITION HE7-3 | 519–535 | `1a71e1c8` | — |
| 9 | LEMMA HE7-4 | 539–542 | `d29eed83` | — |
| 10 | LEMMA HE7-5 | 552–554 | `261ee4fb` | — |
| 11 | LEMMA HE7-7 | 567–569 | `cb7abb1e` | — |
| 12 | LEMMA HE7-7′ | 659–664 | `69027ae6` | — |
| 13 | COROLLARY HE7-7″ | 673–683 | `d3d888bd` | — |
| 14 | LEMMA HE7-6 | 688–689 | `881d4167` | — |
| 15 | LEMMA HE7-9 | 736–739 | `6b592d5e` | — |
| 16 | LEMMA HE7-10 | 740–741 | `8a86d600` | — |
| 17 | LEMMA HE7-11 | 776–777 | `dba01731` | — |
| 18 | LEMMA HE7-12 | 812–857 | `60bd963c` | — |
| 19 | LEMMA HE7-13 | 918–934 | `0caa3639` | — |
| 20 | DEFINITION HE7-2 | 976–992 | `16f71144` | — |
| 21 | THEOREM HE7.D #2 | 994–1002 | `1e0199f3` | — |
| 22 | LEMMA HE7-8 | 1087–1115 | `36fc0fc6` | — |
| 23 | THEOREM HE7.A′ | 1224–1231 | `c934a492` | — |
| 24 | LEMMA HE6R1-2 #2 | 1337–1346 | `53daa436` | — |

### HE6R1_RECON_2026-08-08.md — commit `06971c36`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | COROLLARY HE6.B | 90–98 | `54da07e3` | — |
| 2 | LEMMA HE6R1-1 | 270–282 | `1c64ae1c` | — |
| 3 | LEMMA HE6R1-2 | 316–347 | `58329fbc` | — |
| 4 | LEMMA HE6R1-3 | 469–477 | `593ab005` | — |

### HETOW_RECON_2026-08-09.md — commit `7fb88236`, grade: ACCEPTED 2/2, 5 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA HETOW-1 | 152–169 | `a3424ec7` | — |
| 2 | LEMMA HETOW-2 | 198–211 | `1bffd7bf` | — |
| 3 | LEMMA HETOW-3 | 264–270 | `b245e335` | — |
| 4 | THEOREM HETOW.A | 286–327 | `6b4a7dc4` | — |
| 5 | LEMMA HETOW-4 | 689–746 | `2500c2f4` | — |

### GENTOW1_PROOF_2026-08-09.md — commit `4caf0fb8`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-1 | 150–172 | `4b4d9f21` | — |
| 2 | COROLLARY GENTOW-1.1 | 273–277 | `84643df8` | — |
| 3 | LEMMA GENTOW-2 | 319–345 | `cd64f476` | — |
| 4 | LEMMA GENTOW-5 | 411–452 | `75f4b14f` | — |

### GENTOW2_PROOF_2026-08-09.md — commit `33f86204`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENTOW2-A | 187–219 | `5d1ae5f0` | — |
| 2 | LEMMA GENTOW2-B | 303–340 | `8a00bf44` | — |
| 3 | LEMMA GENTOW2-B′ | 518–538 | `bae471b0` | — |
| 4 | LEMMA GENTOW2-B″ | 729–738 | `d4c8b885` | — |

### GENTOW3_PROOF_2026-08-09.md — commit `607fc694`, grade: ACCEPTED 2/2, 2 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | THEOREM GENTOW-3 | 186–216 | `a6d97dfe` | — |
| 2 | COROLLARY GENTOW-3.C | 320–338 | `f2459aa5` | — |

### GENTOW4_PROOF_2026-08-09.md — commit `4545b4d7`, grade: ACCEPTED 2/2, 4 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-4.1 | 170–195 | `d7d1bf2b` | — |
| 2 | THEOREM GENTOW-4.A | 253–324 | `f77a8145` | — |
| 3 | LEMMA GENTOW-4.2 | 378–383 | `73f54036` | — |
| 4 | COROLLARY GENTOW-4.C | 406–416 | `0096e69a` | — |

### GENTOW5_PROOF_2026-08-09.md — commit `43b42e9c`, grade: ACCEPTED 2/2, 2 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | DEFINITION (unlabeled) | 191–207 | `c9a95972` | U |
| 2 | LEMMA GENTOW5-A1 | 209–223 | `9d473730` | — |

### GENTOW6_PROOF_2026-08-09.md — commit `b1b6aa61`, grade: ACCEPTED 2/2, 6 statements

| # | label | lines | md5-8 | flags |
|---|---|---|---|---|
| 1 | LEMMA GENTOW-6.1 | 95–109 | `cb50ffdc` | — |
| 2 | COROLLARY GENTOW-6.1C | 210–236 | `1a047b21` | — |
| 3 | LEMMA GENTOW-6.2 | 249–259 | `e1eb6807` | — |
| 4 | COROLLARY GENTOW-6.2C | 270–293 | `1ebcf7f0` | — |
| 5 | THEOREM GENTOW-6.3 | 378–434 | `05fc3881` | — |
| 6 | LEMMA GENTOW-6.4 | 879–950 | `832e21a2` | — |

## S2. Extraction rule (S0-v1, verbatim from the instrument)

Capture starts at column 0 only, three forms: (A) `**KW ...` and
`> **KW ...`; (B) `> * **KW ...` (quote-bullet; sole corpus instance
THEOREM W-12.C); (C) `**(i) [KW ...` / `> **(i) [KW ...` (W12 verdict
items). KW in {THEOREM, LEMMA, COROLLARY, COR, PROPOSITION, PROP,
DEFINITION, DEF}. Span ends at the FIRST of: next statement start; a
line opening `*Proof`/`**Proof` (optionally quoted); [plain] a heading
or `---` rule; [quoted] end of the `>` block, a `> **(ii) ` roman item
marker, or `> **GRADE`; 120-line cap (cut to last blank line, flag T).
Labels: keyword + first token after it (trailing punctuation stripped);
unlabeled and duplicate labels numbered in document order.

## S3. Ambiguity & skip record (honest; enumerative, no universal claims)

1. **Over-capture is possible and accepted.** Spans may include
   trailing non-statement prose (inline `*Proof.*` inside a statement's
   own paragraph, notation brackets, correction brackets) up to the next
   terminator — e.g. LIFTCORNER's unlabeled THEOREM span carries its
   inline proof and the [r4, F4-5] notation bracket. Conservative for a
   tripwire: edits there also fire. Line ranges let a human adjudicate.
2. **Skipped class — plain-bullet keyword recaps** (consumption/
   hypothesis-set lists, not statement displays), enumerated:
   - GRTJB_PROOF_2026-08-08.md:506 `* **LEMMA JB-EPS — UNCONDITIONAL at every m ≥ 1** (row 19), and its`
   - W11_PROOF_2026-08-08.md:594 `* **THEOREM W-10(2,1,1)** — PROVED at the instance, two-commit seal`
   - W11_PROOF_2026-08-08.md:599 `* **LEMMA J-D0** — PROVED on its perimeter, seal 1642275/**9387eb1**;`
   - W12_PROOF_2026-08-08.md:1115 `* **THEOREM W-11(n = 2)** — the complete menu + exact drainage + the`
   - W12_PROOF_2026-08-08.md:1118 `* **THEOREM W-10(2,1,1)** — the digit-calculus template (S2.2 is its`
   - W12_PROOF_2026-08-08.md:1121 `* **LEMMA J-D0** — the shape-keying/count-gauge-blindness FRAME: what`
   - W12_PROOF_2026-08-08.md:1489 `* **THEOREM W-11(n = 2)** — PROVED at attempt grade (arc: seal 7020ceb`
   - W12_PROOF_2026-08-08.md:1496 `* **THEOREM W-10(2,1,1)** — PROVED, seal 2e6fdd8 / verdict 9506a55;`
   - W12_PROOF_2026-08-08.md:1499 `* **LEMMA J-D0** — PROVED on its perimeter, seal 1642275 / verdict`
   - HMENU3_PROOF_2026-08-08.md:682 `* **THEOREM W-12.D** @ w12 seal f669cb0 / verdict c16c717 /`
   - HMENU3_PROOF_2026-08-08.md:699 `* **THEOREM W-12.A (order-1 laws) + S2.4 depth-0 completeness +`
   - HMENU3_PROOF_2026-08-08.md:703 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / verdict cb05127 / r2 HEAD`
   - HMENU3_PROOF_2026-08-08.md:717 `* **LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame`
   - HEX3_PROOF_2026-08-08.md:710 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / verdict cb05127 / r2 HEAD`
   - HEX3_PROOF_2026-08-08.md:720 `* **LEMMA J-D0** @ 1642275/9387eb1 — the gauge-blindness frame behind`
   - GENIND_PROOF_2026-08-08.md:1466 `* **THEOREM W-12.D + W-12.A + S2.4/S2.5 + W12-L0/L1** @ w12 seal`
   - GENIND_PROOF_2026-08-08.md:1483 `* **THEOREM W-11(n = 2)** @ seal 7020ceb / r2 31506b3 / PE3 CLEAN`
   - GENIND_PROOF_2026-08-08.md:1518 `* **LEMMA J-D0** @ 1642275/9387eb1 — the count-gauge-blindness frame`
3. **Skipped class — bold NAMED displays without a keyword opener**
   (outside S-0's THEOREM/LEMMA/COR/DEF scope by the blueprint's own
   definition): e.g. `> **W-12 (the general-n assembly).**`,
   `> **(J-D1) THE FAITHFULNESS HANDOFF.**`, GRTW2's `> **(CLAUSE 1..3)`
   blocks, SIGMALAW's `**(Σ-DEF)`/`**(U-REC)` definitional displays, and
   per-clause `**(a)**...` markers. Audit count of `**(`-opening bold
   lines not captured, per note (size of this residue class):
   LIFTCORNER 8, GRTW2 6, GRTJA 1, GRTJB 16, GRTJC 18, WELDMASTER 7, JD0 7, SIGMALAW 3, W12 2, GENIND 10, GENH4 1, HE3 1, HE7 19, HE6R1 5.
   These are pinned only when inside a captured span; a statement whose
   ONLY display is such a form has no ledger row.
4. **Headings are not rows.** Section headings that restate labels
   (`## S4. THEOREM GENTOW2-A ...`) are not captured; the bold block
   below them is.
5. **Baseline matching is by (note, label), not line numbers** — dated
   appends that shift line numbers do NOT fire the tripwire; only text
   changes inside a span do. If an append INSERTS a same-labeled
   statement before an existing one, deterministic numbering shifts and
   the tripwire fires — conservative, adjudicate by hand.
6. **Parenthetical name-parts are cut from labels** (the token stops at
   `(`): observed instances at baseline — `THEOREM W-11` (displayed as
   `W-11(n = 2)`), `LEMMA GENHN-T #2` (displayed `GENHN-T(b)′`, GENHN
   L1127), `LEMMA HE6R1-2 #2` (displayed `HE6R1-2(b)(c)`, HE7 L1337).
   The md5 pins the FULL display text either way.
7. **Quoted keyword-opening RECAPS are captured as rows** (conservative
   over-inclusion; they pin cross-note quotes, which S5.3's record rule
   wants stable anyway): observed at baseline — HE7 L294 (`> **LEMMA
   HE6R1-2** when the block is PROPER ...`, a recap of HE6R1's export)
   and HE7 L307 vs L994 (`THEOREM HE7.D` summary display + full
   statement => rows HE7.D and HE7.D #2, both pinned).

## S4. Teeth record (instrument validated before seal, 2026-08-10)

Three momentary working-tree mutations, each restored via git checkout
immediately after the check (notes verified unmodified afterward):

1. Single-token change inside THEOREM W-12.D's span (W12 L267,
   `REDUCTION` -> `REDUCTIONX`): CHANGED reported with diff, **exit 1**.
2. Whitespace-only rewrap inside the same span (W12 L268-269 spacing):
   **exit 0**, GREEN — the declared whitespace-collapse tolerance.
3. Label rename (JD0 L49, `LEMMA J-D0.` -> `LEMMA J-D0X.`): DELETED
   (LEMMA J-D0) + ADDED-as-info (LEMMA J-D0X), **exit 1** — deletions
   fire, additions alone do not.

Verdict-of-record runs are appended below (S5) after the seal commit;
a --force rebuild regenerates S1-S4 only, so S5 appends must be
re-attached if the ledger is ever legitimately re-pinned.

## S5. BASELINE-GREEN RUN OF RECORD (commit 2 of 2)

Run at HEAD `f8bd49dd` (the seal commit), 2026-08-10:

```
CHECK: 166 baseline statements; 0 changed, 0 deleted, 0 added.
GREEN: every baseline statement byte-stable (normalized).
exit 0
```

The tripwire is ARMED from this commit: every S-unit consumption check
(blueprint S5.3 item 3) must show its absorbed statement md5-identical to
this ledger, and any CI/manual `--check` run that exits 1 is a
stop-the-line event for the simplification campaign.
warning: Codex could not find bubblewrap on PATH. Install bubblewrap with your OS package manager. See the sandbox prerequisites: https://developers.openai.com/codex/concepts/sandboxing#prerequisites. Codex will use the bundled bubblewrap in the meantime.
ERROR: Reconnecting... 2/5
2026-08-11T10:18:22.106627Z ERROR rmcp::transport::worker: worker quit with fatal: Transport channel closed, when Client(HttpRequest(HttpRequest("http/request failed: error sending request for url (https://chatgpt.com/backend-api/ps/mcp)")))
ERROR: Reconnecting... 3/5
ERROR: Reconnecting... 4/5
2026-08-11T10:18:52.058563Z ERROR rmcp::transport::worker: worker quit with fatal: Transport channel closed, when Client(HttpRequest(HttpRequest("http/request failed: error sending request for url (https://chatgpt.com/backend-api/ps/mcp)")))
ERROR: Reconnecting... 5/5
warning: Falling back from WebSockets to HTTPS transport. request timed out
2026-08-11T10:20:21.590837Z ERROR codex_models_manager::manager: failed to refresh available models: timeout waiting for child process to exit
codex
I’m checking the request against the pasted statement boundary first. The key constraint is your “do not weaken” rule: I’ll distinguish facts whose exact Lean shape is recoverable from the pasted files from labels whose mathematical statements are not actually present.
codex
## Stop-the-line result

The requested exact blueprint cannot be produced from the pasted material without inventing mathematics or weakening statements.

The statement ledger contains only labels, line ranges, hashes, and extraction metadata. It does **not** contain the statements of W-12.A/C/D, GENIND.*, GENHN.*, HE7.*, or the tower results. An MD5 hash cannot reconstruct the omitted proposition. Likewise, the pasted gate file contains regression theorems, not a definition of faithfulness tying a `CountingModel` to actual \(p\)-adic polynomials.

Producing Lean signatures, new definitions, or dependency edges for those labels would therefore violate both requirements:

- “do NOT weaken any statement”;
- “every mathematical choice pre-made.”

What follows is the exact adequacy audit, unit by unit, including what must be supplied before mechanical implementation is possible.

## Critical divergences

### D1. The ledger is not the informal corpus

For example, the complete information supplied for W-12.A is:

```text
THEOREM W-12.A
lines 197–231
md5 06b4e5d3
```

This reveals none of its binders, hypotheses, objects, quantifier order, or conclusion. The same is true for every Slice 2 result.

### D2. `RealInstanceV2Gates` does not define faithfulness

The gate file proves:

- particular exact values;
- non-vacuity;
- separation of particular factorization types;
- emptiness of an order-zero ramified menu;
- nontriviality at one tame prime.

None of these statements mentions:

- monic polynomials over `ℤ_p`;
- reduction modulo `p^N`;
- an actual factorization-type classifier;
- Haar measure;
- equality between `decidedCount` and the cardinality of a genuine polynomial locus.

Consequently, these gates cannot logically replace:

```lean
faithful : True
```

as a definition of “the model counts actual \(p\)-adic factorizations.” A fabricated model could agree at all the finitely many tested values and be arbitrary everywhere else.

### D3. The arbitrary-prime parameter is ambiguous

The anchor says “prime `q`” but assumes only:

```lean
1 < q
```

It does not assume:

```lean
Nat.Prime q
```

Meanwhile `DensityFoundation` describes `q` as a residue cardinality, potentially a prime power.

These lead to different formalizations:

```lean
-- Prime interpretation
(q : ℕ) [Fact q.Prime]
```

versus something like:

```lean
-- Prime-power / unramified-extension interpretation
(p f q : ℕ)
(hp : p.Prime)
(hf : 0 < f)
(hq : q = p ^ f)
```

A genuine `ℤ_p` model requires the underlying prime `p`; a residue cardinality `q = p^f` does not by itself specify the local field. This choice cannot be made silently.

### D4. The essential counting API is missing

`CountingModel.lean` was not pasted. Its field types are needed to state extensional realness conditions for:

```lean
decidedCount
undecidedCount
countingDensity
decidedMeasure
```

Similarly, `PadicMeasure.lean` and the concrete `RealInstanceV2` construction are absent.

---

# Slice 1

## Unit 1 — `RealInstanceAt` faithfulness gates

### (a) Lean statement/definition sketch

Only the outer replacement shape is presently determined:

```lean
structure RealInstanceAt (q n : ℕ) where
  model : CountingModel q n
  data : MontesDataV2 q n model
  foundation : DensityFoundation
  hbridge : ∀ σ : FactorizationType, ∀ q' : ℕ, 1 < q' →
    foundation.density n σ q' =
      ∑ T ∈ data.shapesOf σ, data.C T q'
  faithful :
    RealInstanceAtFaithful q n model data foundation
```

But the body of the following predicate is **not determined**:

```lean
structure RealInstanceAtFaithful
    (q n : ℕ)
    (M : CountingModel q n)
    (D : MontesDataV2 q n M)
    (F : DensityFoundation) : Prop where
  -- Exact fields unavailable from the pasted API.
```

An empty structure, a `True` field, or fields reproducing only G1/G2 would be a forbidden weakening.

At minimum, genuine faithfulness must eventually express all of the following semantic obligations:

1. The local-field parameter is valid: either `q.Prime`, or specified prime-power data.
2. A finite level-\(N\) coefficient space genuinely represents monic degree-\(n\) polynomials modulo the chosen uniformizer power.
3. A classifier assigns the correct `FactorizationType` to decided inputs.
4. `M.decidedCount σ N` is the cardinality of exactly that decided locus.
5. `M.undecidedCount N` is the cardinality of the complement still unresolved at depth `N`.
6. The decided and undecided loci partition the full coefficient box.
7. `M.countingDensity σ` is the limit/Haar volume of the genuine type-\(\sigma\) locus.
8. `D.shapesOf`, `D.stratumCount`, and `D.C` refer to genuine OM strata rather than an arbitrary abstract decomposition.
9. `F.density` is the genuine \(p\)-adic factorization density, not merely a function agreeing with the abstract menu sum.

Which of these belong in `RealInstanceAtFaithful`, `CountingModel`, `MontesDataV2`, or a separate bridge is a mathematical interface decision not fixed by the pasted files.

### Why the existing gates cannot be copied as fields

A literal field modeled on G1 would be specialized to `n = 2` and `q = 2`, for example:

```lean
(RealInstanceV2.realM2 2 ...).countingDensity
  (Order0.unramType 2 (Nat.Partition.indiscrete 2)) = 1 / 4
```

That is not meaningful as a required property of `RealInstanceAt q n` for arbitrary `q` and `n`.

Likewise, requiring two distinct degree-\(n\) types is impossible at degrees where the requested pair does not exist. In particular, a universal σ-separation field patterned on the quadratic example cannot be imposed uniformly on all positive `n`.

The correct architecture should separate:

```lean
RealInstanceAtFaithful
```

which gives semantic identification with genuine \(p\)-adic counting, from optional regression theorems such as:

```lean
gate_degree2_inert_value
gate_degree2_sigma_separation
gate_degree2_ramified_vs_inert
gate_degree2_tame_nontrivial
```

The latter should be proved from a particular real family, not stored as fields of every instance.

### (b) New definitions forced

Exact definitions are needed for at least:

```lean
RealInstanceAtFaithful
ActualMonicPolynomial
FiniteLevelPolynomial
truncatePolynomial
ActualFactorizationType
ActualDecidedLocus
ActualUndecidedLocus
ActualStratumLocus
ActualFactorizationDensity
```

These names are only an obligation inventory, not implementable definitions: their domains depend on the unresolved prime/prime-power choice and the omitted counting API.

### (c) Dependencies

Required before Unit 1:

- resolution of the prime-versus-prime-power interpretation;
- complete `CountingModel` declaration;
- the concrete finite-level coefficient-box construction;
- the actual \(p\)-adic factorization-type classifier;
- the reduction/truncation maps;
- the OM stratum decoder;
- the relevant `PadicMeasure` definitions;
- the arbitrary-prime analogue of `RealInstanceV2`.

Downstream:

- construction of each `RealInstanceAt q n`;
- any theorem claiming the Stage 2 target concerns genuine \(p\)-adic densities;
- generalized non-vacuity and σ-separation regression tests.

### (d) Mathlib surface

Likely required areas:

- `NumberTheory.Padics.PadicIntegers`;
- `NumberTheory.Padics.PadicNumbers`;
- polynomial factorization and `Polynomial.IsMonic`;
- finite quotient rings and `ZMod`;
- `Fintype`/`Finset` cardinalities;
- `MeasureTheory.Measure.Haar`;
- topological rings and limits;
- finite extensions and residue fields;
- valuations and valuation rings;
- separability and irreducibility.

Likely gap: mathlib may not provide an off-the-shelf measurable classifier from monic \(p\)-adic polynomials to ramification/residue factorization types, nor the exact equality between its Haar volume and limits of finite residue-box counts. That bridge may require substantial new development or an explicitly cited interface axiom.

### (e) Difficulty

**[hard]**

The surrounding record assembly is mechanical; defining and proving the genuine counting correspondence is not.

### (f) Acceptance test

Unit 1 is accepted only if all of the following pass:

```lean
#check LeanUrat.Stage2.RealInstanceAtFaithful
#check LeanUrat.Stage2.RealInstanceAt
#print axioms LeanUrat.Stage2.RealInstanceAtFaithful
```

Additionally:

- `RealInstanceAt` contains no `True` placeholder.
- `RealInstanceAtFaithful` is neither empty nor propositionally trivial.
- A real arbitrary-prime construction supplies the predicate.
- Its count-identification fields mention actual polynomial loci.
- A deliberately fake `CountingModel` matching only the quadratic G1/G2 values cannot automatically instantiate it.
- No theorem uses `by trivial` to discharge realness.
- The Stage 2 statement file still compiles.
- Any final theorem intended to be trusted contains no `sorry`.

### (g) Translation specification

A mechanical implementer must:

1. Stop until the `q` interpretation is decided.
2. Import the complete counting and \(p\)-adic APIs.
3. Define the actual finite coefficient box.
4. Define monicity and exact degree in that box.
5. Define truncation from integral \(p\)-adic polynomials.
6. Define the actual type-\(\sigma\) locus.
7. Define decided and undecided predicates at depth `N`.
8. Define actual OM stratum loci.
9. State cardinality equalities for `decidedCount`, `undecidedCount`, and `stratumCount`.
10. State the limit/Haar-volume identification.
11. Bundle those fields in `RealInstanceAtFaithful`.
12. Replace `faithful : True` by the bundled predicate.
13. Keep G1/G2 as separate theorems about a concrete family.
14. Run the acceptance checks above.

No lesser model can fill in steps 3–10 without the missing definitions and mathematical choices.

---

# Slice 2 — Statement fan-out

I selected the following fifteen chain heads based solely on the labels requested and the ledger’s theorem-level hierarchy. Their exact propositions remain absent.

For every unit below, the same decisive fact applies: line ranges and hashes provide no recoverable Lean type.

## Unit 2 — THEOREM W-12.A

Source identity: `W12_PROOF_2026-08-08.md`, lines 197–231, MD5 `06b4e5d3`.

- **(a) Lean statement:** unavailable; the proposition text is absent.
- **(b) New definitions:** unknowable until the statement span and its notation are supplied.
- **(c) Dependencies:** unknowable; labels do not encode referenced results.
- **(d) Mathlib surface:** unknowable from the ledger.
- **(e) Difficulty:** unclassifiable.
- **(f) Acceptance:** exact quantifiers and conclusion must be audited against the full 35-line span; then a fenced `by sorry` statement may be syntax-checked before proof work.
- **(g) Translation spec:** paste lines 197–231 plus every local definition/notation used there. Translate binders left-to-right without merging hypotheses or replacing structured objects by propositions.

## Unit 3 — THEOREM W-12.C

Source identity: lines 250–266, MD5 `afe5b2c0`.

- **(a)** Exact Lean type unavailable.
- **(b)** Forced definitions unavailable.
- **(c)** Dependency edges unavailable.
- **(d)** Mathlib surface unavailable.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires preservation of the quote-bullet statement captured by the ledger’s special extraction rule.
- **(g)** Paste the complete span and its notation context; preserve every side condition and quantifier domain verbatim.

## Unit 4 — THEOREM W-12.D

Source identity: lines 267–315, MD5 `70bc878f`.

- **(a)** Exact Lean type unavailable.
- **(b)** Forced definitions unavailable.
- **(c)** Dependency edges unavailable.
- **(d)** Mathlib surface unavailable.
- **(e)** Unclassifiable.
- **(f)** The source span must remain MD5-stable under the ledger check; Lean review must separately verify semantic equivalence.
- **(g)** Paste all 49 lines and definitions referenced by its displayed “reduction” clauses. Do not collapse an equivalence into a one-way implication.

## Unit 5 — THEOREM GENIND.A

Source identity: `GENIND_PROOF_2026-08-08.md`, lines 127–178, MD5 `52f2b4a4`.

- **(a)** Exact statement absent.
- **(b)** Cannot inventory recursive/inductive definitions without the span.
- **(c)** Cannot determine its relation to W-12 statements from chronology alone.
- **(d)** Unknown.
- **(e)** Unclassifiable; the label suggests induction but does not determine complexity.
- **(f)** Acceptance requires exact preservation of induction parameters, base range, and induction measure.
- **(g)** Supply the full statement and all preceding definitions it references; encode its induction measure as data rather than guessing `Nat.rec`.

## Unit 6 — THEOREM GENIND.B

Source identity: lines 186–224, MD5 `02dc45ce`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Even an edge `GENIND.A → GENIND.B` cannot be asserted merely from ordering.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Compile the exact statement first; compare every premise with the source display.
- **(g)** Paste the complete statement and explicit proof-consumption paragraph if dependencies are to be recorded without inference.

## Unit 7 — THEOREM GENHN.CLASS

Source identity: `GENHN_PROOF_2026-08-08.md`, lines 127–154, MD5 `1b6bdada`.

- **(a)** Exact classification proposition absent.
- **(b)** Any class, equivalence relation, or normal-form definition is unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance must test both coverage and exclusivity if those are present in the source; neither may be inferred from the word `CLASS`.
- **(g)** Paste the complete span and definitions of every class appearing in it.

## Unit 8 — THEOREM GENHN.A

Source identity: lines 156–211, MD5 `eb606039`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** No safe edge from `GENHN.CLASS` can be declared without the text.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires a binder-by-binder source/Lean concordance table.
- **(g)** Supply all 56 lines and referenced notation.

## Unit 9 — THEOREM GENHN.C

Source identity: lines 259–273, MD5 `c8c98e43`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Syntax-check only after the complete proposition is available.
- **(g)** Do not infer that `.C` depends on `.A`; obtain dependencies from explicit citations or the proof.

## Unit 10 — THEOREM GENHN.B

Source identity: lines 303–373, MD5 `4ef55318`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown, including the apparent nonalphabetical source ordering.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires preserving every clause in the 71-line ledger span.
- **(g)** Paste the entire span; split conjunctions into named predicates only if definitional unfolding reproduces the original statement exactly.

## Unit 11 — THEOREM HE7.A

Source identity: `HE7_PROOF_2026-08-08.md`, lines 197–251, MD5 `0a90b21f`.

- **(a)** Exact statement absent.
- **(b)** `DEFINITION HE7-1`, lines 93–109, is likely relevant by proximity but this is not a provable dependency. Its full text is also missing.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires first formalizing any referenced HE7 definitions without changing their semantics.
- **(g)** Paste `DEFINITION HE7-1`, the complete HE7.A statement, and all imported notation.

## Unit 12 — THEOREM HE7.A′

Source identity: lines 1224–1231, MD5 `c934a492`.

- **(a)** Exact statement absent.
- **(b)** Unknown; the prime mark does not establish whether this is a strengthening, reformulation, or distinct theorem.
- **(c)** No edge from HE7.A may be asserted solely from the name.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires the source’s exact relation, if any, to HE7.A to appear as a proved theorem rather than an assumed equivalence.
- **(g)** Paste the full span and the paragraphs explaining the prime notation.

## Unit 13 — THEOREM HETOW.A

Source identity: `HETOW_RECON_2026-08-09.md`, lines 286–327, MD5 `6b4a7dc4`.

- **(a)** Exact tower statement absent.
- **(b)** Likely forces tower/index/transition definitions, but their forms cannot be inferred.
- **(c)** The preceding HETOW lemmas are candidates, not established dependencies.
- **(d)** Potentially algebra towers, finite fields, valuations, and polynomial extensions; this is only a topic forecast, not a surface specification.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires exact preservation of tower orientation, indexing, and compatibility conditions.
- **(g)** Paste HETOW-1/2/3 and HETOW.A together with tower notation definitions.

## Unit 14 — THEOREM GENTOW2-A

Source identity: `GENTOW2_PROOF_2026-08-09.md`, lines 187–219, MD5 `5d1ae5f0`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** A dependency on GENTOW1 cannot be inferred from filenames alone.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires explicit checks of all index bounds and transition-map equalities.
- **(g)** Supply the full theorem and the GENTOW1 exported statements it explicitly cites.

## Unit 15 — THEOREM GENTOW-3

Source identity: `GENTOW3_PROOF_2026-08-09.md`, lines 186–216, MD5 `a6d97dfe`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** The statement file must compile with all implicit types made explicit during review.
- **(g)** Paste the span and every named object introduced before line 186.

## Unit 16 — THEOREM GENTOW-4.A

Source identity: `GENTOW4_PROOF_2026-08-09.md`, lines 253–324, MD5 `f77a8145`.

- **(a)** Exact 72-line statement absent.
- **(b)** Unknown.
- **(c)** No dependency on GENTOW-3 may be recorded without an explicit citation or use.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires clause-by-clause coverage of the entire captured span; no subsidiary conclusion may be dropped.
- **(g)** Paste `GENTOW-4.1`, GENTOW-4.A, all local definitions, and its explicit hypothesis-consumption list.

## Dependency edges presently justified

Only structural/API edges visible in the pasted Lean files can be asserted:

```text
CountingModel ───────┐
                     ├─ MontesDataV2
Interface objects ───┘

CountingModel + MontesDataV2
        ├─ countingDensity_eq_sum_coeff
        └─ countingDensity_isRational

countingDensity_eq_sum_coeff
+ countingDensity_isRational
+ hbridge
+ TameFunctionalEquation
        └─ goal_theorem_montes
             └─ goal_theorem_via_montes

RealInstanceAt
  ├─ CountingModel
  ├─ MontesDataV2
  ├─ DensityFoundation
  ├─ hbridge
  └─ RealInstanceAtFaithful   [missing semantic definition]
```

There are **no justified dependency edges among Units 2–16** in the supplied material. Document order and matching label prefixes are insufficient evidence.

## Exact additional material required

To make the requested blueprint mechanical, supply:

1. `CountingModel.lean` in full.
2. Relevant portions of `PadicMeasure.lean`.
3. `OM/RealInstanceV2.lean`.
4. `OM/OMCountV2.lean` and relevant order-zero definitions.
5. A decision whether `q` means a prime or a prime-power residue cardinality.
6. The complete captured statement spans for Units 2–16.
7. Every definition/notation referenced by those spans.
8. The explicit consumption/dependency paragraphs from their proofs, if the dependency DAG must be fixed without reading proof bodies.

## Dependency-ordered implementation queue

1. Decide the local-field parameterization: prime `p` versus residue cardinality `q = p^f`.
2. Expose the actual finite-level polynomial and counting APIs.
3. Define actual factorization-type, decided, undecided, and stratum loci.
4. Define and validate `RealInstanceAtFaithful`.
5. Replace `faithful : True`.
6. Construct arbitrary-prime real instances.
7. Reprove G1/G2-style facts separately as regression theorems where mathematically applicable.
8. Paste and freeze the fifteen informal statement spans.
9. Translate all definitions referenced by those spans.
10. Compile statement-only Lean declarations and perform binder-by-binder review.
11. Extract the real dependency DAG from referenced constants and explicit citations.
12. Topologically sort and prove the units.
13. Run `#print axioms`, the zero-sorry check, and the statement-ledger tripwire.
14. Only then consume the resulting units in `uniformity_target` and `uniformity_target_exhaustive`.

UNITS: 16
tokens used
39,102
## Stop-the-line result

The requested exact blueprint cannot be produced from the pasted material without inventing mathematics or weakening statements.

The statement ledger contains only labels, line ranges, hashes, and extraction metadata. It does **not** contain the statements of W-12.A/C/D, GENIND.*, GENHN.*, HE7.*, or the tower results. An MD5 hash cannot reconstruct the omitted proposition. Likewise, the pasted gate file contains regression theorems, not a definition of faithfulness tying a `CountingModel` to actual \(p\)-adic polynomials.

Producing Lean signatures, new definitions, or dependency edges for those labels would therefore violate both requirements:

- “do NOT weaken any statement”;
- “every mathematical choice pre-made.”

What follows is the exact adequacy audit, unit by unit, including what must be supplied before mechanical implementation is possible.

## Critical divergences

### D1. The ledger is not the informal corpus

For example, the complete information supplied for W-12.A is:

```text
THEOREM W-12.A
lines 197–231
md5 06b4e5d3
```

This reveals none of its binders, hypotheses, objects, quantifier order, or conclusion. The same is true for every Slice 2 result.

### D2. `RealInstanceV2Gates` does not define faithfulness

The gate file proves:

- particular exact values;
- non-vacuity;
- separation of particular factorization types;
- emptiness of an order-zero ramified menu;
- nontriviality at one tame prime.

None of these statements mentions:

- monic polynomials over `ℤ_p`;
- reduction modulo `p^N`;
- an actual factorization-type classifier;
- Haar measure;
- equality between `decidedCount` and the cardinality of a genuine polynomial locus.

Consequently, these gates cannot logically replace:

```lean
faithful : True
```

as a definition of “the model counts actual \(p\)-adic factorizations.” A fabricated model could agree at all the finitely many tested values and be arbitrary everywhere else.

### D3. The arbitrary-prime parameter is ambiguous

The anchor says “prime `q`” but assumes only:

```lean
1 < q
```

It does not assume:

```lean
Nat.Prime q
```

Meanwhile `DensityFoundation` describes `q` as a residue cardinality, potentially a prime power.

These lead to different formalizations:

```lean
-- Prime interpretation
(q : ℕ) [Fact q.Prime]
```

versus something like:

```lean
-- Prime-power / unramified-extension interpretation
(p f q : ℕ)
(hp : p.Prime)
(hf : 0 < f)
(hq : q = p ^ f)
```

A genuine `ℤ_p` model requires the underlying prime `p`; a residue cardinality `q = p^f` does not by itself specify the local field. This choice cannot be made silently.

### D4. The essential counting API is missing

`CountingModel.lean` was not pasted. Its field types are needed to state extensional realness conditions for:

```lean
decidedCount
undecidedCount
countingDensity
decidedMeasure
```

Similarly, `PadicMeasure.lean` and the concrete `RealInstanceV2` construction are absent.

---

# Slice 1

## Unit 1 — `RealInstanceAt` faithfulness gates

### (a) Lean statement/definition sketch

Only the outer replacement shape is presently determined:

```lean
structure RealInstanceAt (q n : ℕ) where
  model : CountingModel q n
  data : MontesDataV2 q n model
  foundation : DensityFoundation
  hbridge : ∀ σ : FactorizationType, ∀ q' : ℕ, 1 < q' →
    foundation.density n σ q' =
      ∑ T ∈ data.shapesOf σ, data.C T q'
  faithful :
    RealInstanceAtFaithful q n model data foundation
```

But the body of the following predicate is **not determined**:

```lean
structure RealInstanceAtFaithful
    (q n : ℕ)
    (M : CountingModel q n)
    (D : MontesDataV2 q n M)
    (F : DensityFoundation) : Prop where
  -- Exact fields unavailable from the pasted API.
```

An empty structure, a `True` field, or fields reproducing only G1/G2 would be a forbidden weakening.

At minimum, genuine faithfulness must eventually express all of the following semantic obligations:

1. The local-field parameter is valid: either `q.Prime`, or specified prime-power data.
2. A finite level-\(N\) coefficient space genuinely represents monic degree-\(n\) polynomials modulo the chosen uniformizer power.
3. A classifier assigns the correct `FactorizationType` to decided inputs.
4. `M.decidedCount σ N` is the cardinality of exactly that decided locus.
5. `M.undecidedCount N` is the cardinality of the complement still unresolved at depth `N`.
6. The decided and undecided loci partition the full coefficient box.
7. `M.countingDensity σ` is the limit/Haar volume of the genuine type-\(\sigma\) locus.
8. `D.shapesOf`, `D.stratumCount`, and `D.C` refer to genuine OM strata rather than an arbitrary abstract decomposition.
9. `F.density` is the genuine \(p\)-adic factorization density, not merely a function agreeing with the abstract menu sum.

Which of these belong in `RealInstanceAtFaithful`, `CountingModel`, `MontesDataV2`, or a separate bridge is a mathematical interface decision not fixed by the pasted files.

### Why the existing gates cannot be copied as fields

A literal field modeled on G1 would be specialized to `n = 2` and `q = 2`, for example:

```lean
(RealInstanceV2.realM2 2 ...).countingDensity
  (Order0.unramType 2 (Nat.Partition.indiscrete 2)) = 1 / 4
```

That is not meaningful as a required property of `RealInstanceAt q n` for arbitrary `q` and `n`.

Likewise, requiring two distinct degree-\(n\) types is impossible at degrees where the requested pair does not exist. In particular, a universal σ-separation field patterned on the quadratic example cannot be imposed uniformly on all positive `n`.

The correct architecture should separate:

```lean
RealInstanceAtFaithful
```

which gives semantic identification with genuine \(p\)-adic counting, from optional regression theorems such as:

```lean
gate_degree2_inert_value
gate_degree2_sigma_separation
gate_degree2_ramified_vs_inert
gate_degree2_tame_nontrivial
```

The latter should be proved from a particular real family, not stored as fields of every instance.

### (b) New definitions forced

Exact definitions are needed for at least:

```lean
RealInstanceAtFaithful
ActualMonicPolynomial
FiniteLevelPolynomial
truncatePolynomial
ActualFactorizationType
ActualDecidedLocus
ActualUndecidedLocus
ActualStratumLocus
ActualFactorizationDensity
```

These names are only an obligation inventory, not implementable definitions: their domains depend on the unresolved prime/prime-power choice and the omitted counting API.

### (c) Dependencies

Required before Unit 1:

- resolution of the prime-versus-prime-power interpretation;
- complete `CountingModel` declaration;
- the concrete finite-level coefficient-box construction;
- the actual \(p\)-adic factorization-type classifier;
- the reduction/truncation maps;
- the OM stratum decoder;
- the relevant `PadicMeasure` definitions;
- the arbitrary-prime analogue of `RealInstanceV2`.

Downstream:

- construction of each `RealInstanceAt q n`;
- any theorem claiming the Stage 2 target concerns genuine \(p\)-adic densities;
- generalized non-vacuity and σ-separation regression tests.

### (d) Mathlib surface

Likely required areas:

- `NumberTheory.Padics.PadicIntegers`;
- `NumberTheory.Padics.PadicNumbers`;
- polynomial factorization and `Polynomial.IsMonic`;
- finite quotient rings and `ZMod`;
- `Fintype`/`Finset` cardinalities;
- `MeasureTheory.Measure.Haar`;
- topological rings and limits;
- finite extensions and residue fields;
- valuations and valuation rings;
- separability and irreducibility.

Likely gap: mathlib may not provide an off-the-shelf measurable classifier from monic \(p\)-adic polynomials to ramification/residue factorization types, nor the exact equality between its Haar volume and limits of finite residue-box counts. That bridge may require substantial new development or an explicitly cited interface axiom.

### (e) Difficulty

**[hard]**

The surrounding record assembly is mechanical; defining and proving the genuine counting correspondence is not.

### (f) Acceptance test

Unit 1 is accepted only if all of the following pass:

```lean
#check LeanUrat.Stage2.RealInstanceAtFaithful
#check LeanUrat.Stage2.RealInstanceAt
#print axioms LeanUrat.Stage2.RealInstanceAtFaithful
```

Additionally:

- `RealInstanceAt` contains no `True` placeholder.
- `RealInstanceAtFaithful` is neither empty nor propositionally trivial.
- A real arbitrary-prime construction supplies the predicate.
- Its count-identification fields mention actual polynomial loci.
- A deliberately fake `CountingModel` matching only the quadratic G1/G2 values cannot automatically instantiate it.
- No theorem uses `by trivial` to discharge realness.
- The Stage 2 statement file still compiles.
- Any final theorem intended to be trusted contains no `sorry`.

### (g) Translation specification

A mechanical implementer must:

1. Stop until the `q` interpretation is decided.
2. Import the complete counting and \(p\)-adic APIs.
3. Define the actual finite coefficient box.
4. Define monicity and exact degree in that box.
5. Define truncation from integral \(p\)-adic polynomials.
6. Define the actual type-\(\sigma\) locus.
7. Define decided and undecided predicates at depth `N`.
8. Define actual OM stratum loci.
9. State cardinality equalities for `decidedCount`, `undecidedCount`, and `stratumCount`.
10. State the limit/Haar-volume identification.
11. Bundle those fields in `RealInstanceAtFaithful`.
12. Replace `faithful : True` by the bundled predicate.
13. Keep G1/G2 as separate theorems about a concrete family.
14. Run the acceptance checks above.

No lesser model can fill in steps 3–10 without the missing definitions and mathematical choices.

---

# Slice 2 — Statement fan-out

I selected the following fifteen chain heads based solely on the labels requested and the ledger’s theorem-level hierarchy. Their exact propositions remain absent.

For every unit below, the same decisive fact applies: line ranges and hashes provide no recoverable Lean type.

## Unit 2 — THEOREM W-12.A

Source identity: `W12_PROOF_2026-08-08.md`, lines 197–231, MD5 `06b4e5d3`.

- **(a) Lean statement:** unavailable; the proposition text is absent.
- **(b) New definitions:** unknowable until the statement span and its notation are supplied.
- **(c) Dependencies:** unknowable; labels do not encode referenced results.
- **(d) Mathlib surface:** unknowable from the ledger.
- **(e) Difficulty:** unclassifiable.
- **(f) Acceptance:** exact quantifiers and conclusion must be audited against the full 35-line span; then a fenced `by sorry` statement may be syntax-checked before proof work.
- **(g) Translation spec:** paste lines 197–231 plus every local definition/notation used there. Translate binders left-to-right without merging hypotheses or replacing structured objects by propositions.

## Unit 3 — THEOREM W-12.C

Source identity: lines 250–266, MD5 `afe5b2c0`.

- **(a)** Exact Lean type unavailable.
- **(b)** Forced definitions unavailable.
- **(c)** Dependency edges unavailable.
- **(d)** Mathlib surface unavailable.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires preservation of the quote-bullet statement captured by the ledger’s special extraction rule.
- **(g)** Paste the complete span and its notation context; preserve every side condition and quantifier domain verbatim.

## Unit 4 — THEOREM W-12.D

Source identity: lines 267–315, MD5 `70bc878f`.

- **(a)** Exact Lean type unavailable.
- **(b)** Forced definitions unavailable.
- **(c)** Dependency edges unavailable.
- **(d)** Mathlib surface unavailable.
- **(e)** Unclassifiable.
- **(f)** The source span must remain MD5-stable under the ledger check; Lean review must separately verify semantic equivalence.
- **(g)** Paste all 49 lines and definitions referenced by its displayed “reduction” clauses. Do not collapse an equivalence into a one-way implication.

## Unit 5 — THEOREM GENIND.A

Source identity: `GENIND_PROOF_2026-08-08.md`, lines 127–178, MD5 `52f2b4a4`.

- **(a)** Exact statement absent.
- **(b)** Cannot inventory recursive/inductive definitions without the span.
- **(c)** Cannot determine its relation to W-12 statements from chronology alone.
- **(d)** Unknown.
- **(e)** Unclassifiable; the label suggests induction but does not determine complexity.
- **(f)** Acceptance requires exact preservation of induction parameters, base range, and induction measure.
- **(g)** Supply the full statement and all preceding definitions it references; encode its induction measure as data rather than guessing `Nat.rec`.

## Unit 6 — THEOREM GENIND.B

Source identity: lines 186–224, MD5 `02dc45ce`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Even an edge `GENIND.A → GENIND.B` cannot be asserted merely from ordering.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Compile the exact statement first; compare every premise with the source display.
- **(g)** Paste the complete statement and explicit proof-consumption paragraph if dependencies are to be recorded without inference.

## Unit 7 — THEOREM GENHN.CLASS

Source identity: `GENHN_PROOF_2026-08-08.md`, lines 127–154, MD5 `1b6bdada`.

- **(a)** Exact classification proposition absent.
- **(b)** Any class, equivalence relation, or normal-form definition is unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance must test both coverage and exclusivity if those are present in the source; neither may be inferred from the word `CLASS`.
- **(g)** Paste the complete span and definitions of every class appearing in it.

## Unit 8 — THEOREM GENHN.A

Source identity: lines 156–211, MD5 `eb606039`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** No safe edge from `GENHN.CLASS` can be declared without the text.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires a binder-by-binder source/Lean concordance table.
- **(g)** Supply all 56 lines and referenced notation.

## Unit 9 — THEOREM GENHN.C

Source identity: lines 259–273, MD5 `c8c98e43`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Syntax-check only after the complete proposition is available.
- **(g)** Do not infer that `.C` depends on `.A`; obtain dependencies from explicit citations or the proof.

## Unit 10 — THEOREM GENHN.B

Source identity: lines 303–373, MD5 `4ef55318`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown, including the apparent nonalphabetical source ordering.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires preserving every clause in the 71-line ledger span.
- **(g)** Paste the entire span; split conjunctions into named predicates only if definitional unfolding reproduces the original statement exactly.

## Unit 11 — THEOREM HE7.A

Source identity: `HE7_PROOF_2026-08-08.md`, lines 197–251, MD5 `0a90b21f`.

- **(a)** Exact statement absent.
- **(b)** `DEFINITION HE7-1`, lines 93–109, is likely relevant by proximity but this is not a provable dependency. Its full text is also missing.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires first formalizing any referenced HE7 definitions without changing their semantics.
- **(g)** Paste `DEFINITION HE7-1`, the complete HE7.A statement, and all imported notation.

## Unit 12 — THEOREM HE7.A′

Source identity: lines 1224–1231, MD5 `c934a492`.

- **(a)** Exact statement absent.
- **(b)** Unknown; the prime mark does not establish whether this is a strengthening, reformulation, or distinct theorem.
- **(c)** No edge from HE7.A may be asserted solely from the name.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires the source’s exact relation, if any, to HE7.A to appear as a proved theorem rather than an assumed equivalence.
- **(g)** Paste the full span and the paragraphs explaining the prime notation.

## Unit 13 — THEOREM HETOW.A

Source identity: `HETOW_RECON_2026-08-09.md`, lines 286–327, MD5 `6b4a7dc4`.

- **(a)** Exact tower statement absent.
- **(b)** Likely forces tower/index/transition definitions, but their forms cannot be inferred.
- **(c)** The preceding HETOW lemmas are candidates, not established dependencies.
- **(d)** Potentially algebra towers, finite fields, valuations, and polynomial extensions; this is only a topic forecast, not a surface specification.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires exact preservation of tower orientation, indexing, and compatibility conditions.
- **(g)** Paste HETOW-1/2/3 and HETOW.A together with tower notation definitions.

## Unit 14 — THEOREM GENTOW2-A

Source identity: `GENTOW2_PROOF_2026-08-09.md`, lines 187–219, MD5 `5d1ae5f0`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** A dependency on GENTOW1 cannot be inferred from filenames alone.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires explicit checks of all index bounds and transition-map equalities.
- **(g)** Supply the full theorem and the GENTOW1 exported statements it explicitly cites.

## Unit 15 — THEOREM GENTOW-3

Source identity: `GENTOW3_PROOF_2026-08-09.md`, lines 186–216, MD5 `a6d97dfe`.

- **(a)** Exact statement absent.
- **(b)** Unknown.
- **(c)** Unknown.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** The statement file must compile with all implicit types made explicit during review.
- **(g)** Paste the span and every named object introduced before line 186.

## Unit 16 — THEOREM GENTOW-4.A

Source identity: `GENTOW4_PROOF_2026-08-09.md`, lines 253–324, MD5 `f77a8145`.

- **(a)** Exact 72-line statement absent.
- **(b)** Unknown.
- **(c)** No dependency on GENTOW-3 may be recorded without an explicit citation or use.
- **(d)** Unknown.
- **(e)** Unclassifiable.
- **(f)** Acceptance requires clause-by-clause coverage of the entire captured span; no subsidiary conclusion may be dropped.
- **(g)** Paste `GENTOW-4.1`, GENTOW-4.A, all local definitions, and its explicit hypothesis-consumption list.

## Dependency edges presently justified

Only structural/API edges visible in the pasted Lean files can be asserted:

```text
CountingModel ───────┐
                     ├─ MontesDataV2
Interface objects ───┘

CountingModel + MontesDataV2
        ├─ countingDensity_eq_sum_coeff
        └─ countingDensity_isRational

countingDensity_eq_sum_coeff
+ countingDensity_isRational
+ hbridge
+ TameFunctionalEquation
        └─ goal_theorem_montes
             └─ goal_theorem_via_montes

RealInstanceAt
  ├─ CountingModel
  ├─ MontesDataV2
  ├─ DensityFoundation
  ├─ hbridge
  └─ RealInstanceAtFaithful   [missing semantic definition]
```

There are **no justified dependency edges among Units 2–16** in the supplied material. Document order and matching label prefixes are insufficient evidence.

## Exact additional material required

To make the requested blueprint mechanical, supply:

1. `CountingModel.lean` in full.
2. Relevant portions of `PadicMeasure.lean`.
3. `OM/RealInstanceV2.lean`.
4. `OM/OMCountV2.lean` and relevant order-zero definitions.
5. A decision whether `q` means a prime or a prime-power residue cardinality.
6. The complete captured statement spans for Units 2–16.
7. Every definition/notation referenced by those spans.
8. The explicit consumption/dependency paragraphs from their proofs, if the dependency DAG must be fixed without reading proof bodies.

## Dependency-ordered implementation queue

1. Decide the local-field parameterization: prime `p` versus residue cardinality `q = p^f`.
2. Expose the actual finite-level polynomial and counting APIs.
3. Define actual factorization-type, decided, undecided, and stratum loci.
4. Define and validate `RealInstanceAtFaithful`.
5. Replace `faithful : True`.
6. Construct arbitrary-prime real instances.
7. Reprove G1/G2-style facts separately as regression theorems where mathematically applicable.
8. Paste and freeze the fifteen informal statement spans.
9. Translate all definitions referenced by those spans.
10. Compile statement-only Lean declarations and perform binder-by-binder review.
11. Extract the real dependency DAG from referenced constants and explicit citations.
12. Topologically sort and prove the units.
13. Run `#print axioms`, the zero-sorry check, and the statement-ledger tripwire.
14. Only then consume the resulting units in `uniformity_target` and `uniformity_target_exhaustive`.

UNITS: 16
