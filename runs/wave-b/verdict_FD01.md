# Verdict — unit FD01 (nodes FD-0 + FD-1): the records ASSEMBLED

Date: 2026-08-25 · One new file `leanfinal/Uniformity/ChapC/C130fd0.lean` (45 declarations).
`lake env lean` exit 0, zero errors/warnings, zero `sorry`; all 45 `#print axioms` rows
EXACTLY `[propext, Classical.choice, Quot.sound]` (no cite inheritance anywhere — checked
row-by-row by script). `lake build Uniformity.ChapC.C130fd0` green. No other file touched;
no commit.

## The FD-0 finding (load-bearing, machine-certified)

The briefed laws record `FGMNSourceLaws (s2DepthTwo h2 hq) K 2 1 5` is **UNSATISFIABLE at
the landed operator readings, for EVERY key chain K** — ★
`s2SourceLaws_depthTwo_unsatisfiable` (+ instance corollary `s2SourceLaws_impossible`):
`carried_key_is_key` forces `keyAt 2 ∈ KP(μ₂)`, `carried_key_residual` forces
`R₃(keyAt 2) = 1`, and KP-9's landed degree dictionary (`s2KeyPoly_normRes_natDegree`:
`deg R₃ = deg/4` on keys) collides with the chain's own `deg(keyAt 2) = 4`. Cause: the
abstract structure reuses the tower depth `r` as the FGMN key index, but the landed
operators realize the `μ₁ → μ₂` augmentation whose key is `keyAt 1 = Φ′` — the `r = 1`
anchoring already RECORDED by RP-0's docstring, RP-11's course correction, and KP-3's
anchoring note. Same genre as U13's `no_s2_node_source`: typing refuted, nothing weakened.
(Conditional on the landed reads `normalizedResidual = s2NormRes`, `keyPolynomial =
S2KeyPoly`; a future genuinely-μ₃-level depth-two record — plan §5.2's original intent,
nowhere landed — is NOT refuted.)

**Consequence for SG-0:** C130s17's split `S2SourceFrontier` types its `fgmn`/`fgmnLaws` at
exactly this depth-two typing, so the frontier as currently typed is uninhabitable at the
landed operators for the same reason; the corrected frontier row should consume the `r = 1`
records below (or retype the fgmn legs).

## FD-0 deliverables

At the **briefed depth-two typing**: ★ `s2SourceData : FGMNSourceData (s2DepthTwo h2 hq)
(s2DepthTwoKeyChain h2 hq) 2 1 5` (all seven operator fields, each read pinned `rfl`); all
five banked pins FIRE with `rfl` discharges; ten of the thirteen field-facts hold with
named theorems (see table, column "at r=2"); two are machine-REFUTED as printed
(`s2_carried_key_residual_depthTwo_refuted`: `R₃(composedKey) = X+1 ≠ 1`;
`s2_key_criterion_depthTwo_shape_refuted`: the new degree-eight witness `g₈ = (Φ′²+4x)·Φ′²`
has irreducible degree-1 residual `X+1` but is no key); `normalized_recipe`'s depth-two
shape is a STOP field (not landed, not claimed — RP-11's factor-of-`e'` grade
miscalibration applies at this anchoring too).

At the **recorded r = 1 anchoring** (`s2DepthOne := (s2Witness …).trunc 1`; carrier
definitionally the SAME stage field, pinned by `s2DepthOne_fld_eq : rfl`): ★★ BOTH records
constructed — `s2SourceDataOne` (same seven operators, reads pinned `rfl`) and
`s2SourceLawsOne` with **all thirteen projections discharged by named landed theorems**:

| # | `FGMNSourceLaws` field | named theorem (r = 1 record) | at the briefed r = 2 typing |
|---|---|---|---|
| 1 | `graded_zero_of_above` | `C130rp1.s2GradedRes_zero_of_above` | HOLDS (`s2SourceData_graded_zero_of_above`) |
| 2 | `graded_add` | `C130rp2.s2GradedRes_add` | HOLDS (`s2SourceData_graded_add`) |
| 3 | `graded_mul` | `C130rp6.s2_graded_mul` (A-C.13 `PrevGrade` premise) | HOLDS — pin `s2_graded_mul_fills` fired (`s2SourceData_graded_mul`) |
| 4 | `graded_scalar_nonzero` | `C130rp8.s2GradedRes_coeff_zero_ne_zero_of_exact` (fence `deg keyAt 1 = 2 ≤ 4`) | HOLDS — pin `s2_graded_scalar_nonzero_fills` fired (fence `deg keyAt 2 = 4`, sharp) |
| 5 | `normalized_mul` | `C130rp9.s2NormRes_mul` (universal) | HOLDS — pin `s2_normalized_mul_fills` fired |
| 6 | `normalized_recipe` | discharged **VACUOUSLY** — `C130rp11.s2_recipe_naive_numeral_vacuous`, re-exposed as `tooth_recipe_printed_numerals_vacuous`; honest non-vacuous law: `C130rp11.s2_normalized_recipe` at the `e'`-corrected grade 10 (OPEN-DICT-2) | **STOP** — not landed, not claimed (non-vacuous at fence 4 and believed false; unverified analysis, not a theorem) |
| 7 | `normalized_exists` | `C130rp11.s2_normalized_exists` (degree 4) | HOLDS via NEW degree-eight adapter `s2_gEight_monic/_natDegree/_normRes` (`s2SourceData_normalized_exists`) |
| 8 | `key_criterion` | `C130kp3.s2_key_criterion` (recipe degree `2·1·deg keyAt 1 = 4`) | printed `keyAt 2` shape **REFUTED** (`s2_key_criterion_depthTwo_shape_refuted`); the keyAt-1-anchored shape HOLDS (pin `s2_key_criterion_fills` fired) |
| 9 | `key_irreducible` | **NEW** `C130fd0.s2_key_irreducible` — direct proof at KP-0's predicates (`S2MuDvd_self` + μ₂-primality + μ₂-minimality + monic leading-coefficient units); closes KP-5's re-scoped universal field with NO cite | HOLDS (`s2SourceData_key_irreducible`, same theorem) |
| 10 | `carried_key_is_key` | `C130kp1.s2KeyPoly_key` (`Φ′ ∈ KP(μ₂)`) | HOLDS (`C130kp5.s2KeyPoly_composedKey` at `keyAt 2 = composedKey`) |
| 11 | `carried_key_residual` | `C130rp8.s2NormRes_key` (`R₃(Φ′) = 1`, eq (11)) | **REFUTED** (`s2_carried_key_residual_depthTwo_refuted`: KP-6's `R₃(composedKey) = X+1`) |
| 12 | `initial_iff_residual` | `C130kp7.s2_initial_iff_residual` (Prop 5.6(2)⇔(3)) | HOLDS — pin `s2_initial_iff_residual_fills` fired |
| 13 | `letter_ne_zero` | `C130np6.s2Letter_ne_zero` (live range narrowed 1 ≤ i ≤ 1) | HOLDS (`s2SourceData_letter_ne_zero`, exact NP-6 shape) |

Fields 10+11 at r=2 hold/fail INDIVIDUALLY as marked but are JOINTLY unsatisfiable for any
chain (the ★ finding) — hence no r=2 laws record despite 10/13 individual field-facts.

## FD-1 deliverables (OPEN-DICT-2/4, split-frontier field shapes)

The un-split `ChainRealization` is uninhabitable at S2 (U13), so both compats land in
C130s17's split `S2SourceFrontier` field shapes, at `fgmn := s2SourceData`:

* ★ `s2_grade_compat : ∀ x : S2NPPoint, s2NPPt 2 x → ∀ g, (s2SourceData …).nextValue g =
  s2NPPointHgt 2 x g` — definitional after NP-0's normalization pin `s2NPPointHgt_two`
  (one `.symm`), exactly the plan row's "definitional after explicit normalization pins".
* ★ `s2_letter_compat (L) [Field L] [Algebra (fld 2) L] : ∀ i, StageLive 2 i →
  algebraMap … ((s2RepositoryRealization …).receiver.topEquiv ((s2SourceData …).letter i)) =
  (s2AmbientLetter L i : L)` — definitional from `map_one` (NP-6's letters forced to 1 on
  both sides).

## Flagged for human review (trust boundary — new statements)

`s2_key_irreducible` (new universal law + its honest-predicate proof), the `g₈` adapter
statements, both depth-two refutation statements, `s2SourceLaws_depthTwo_unsatisfiable`,
the `s2DepthOne` truncation typing (+ `s2DepthOne_fld_eq`), the vacuous discharge of field 6
at r=1 (certified vacuous, loudly documented), and the two FD-1 statements.
