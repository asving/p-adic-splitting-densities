## Semantic-faithfulness audit

The central round-5 façade is substantially repaired: `gr_w(A)`, its pieces, multiplication, initial forms, and localization source are no longer defined from `σ.R`. However, the manifest still does not encode the genuine degree-zero coefficient localization or the intrinsic grading of the localization, and several downstream units claim more than their hypotheses supply.

### A. `MovesGr/Defs.lean`

#### Genuine associated graded ring

This part is semantically genuine.

- `ge γ` and `gt γ` are the actual filtration submodules defined from `S.w`.
- `grPiece γ = ge γ / gt γ`.
- `Gr` is the direct sum of those quotients.
- `mulToGe` is induced directly by multiplication in `Polynomial ℤ_[p]`.
- `pmul` descends `mulToGe` through both quotients using `LinearMap.liftQ₂`.
- Neither `mulToGe` nor `pmul` mentions `Stage`, `σ.R`, `σ.grRes`, or the formal Laurent presentation.
- `initialForm f` is the genuine quotient class placed in degree `S.deg f`.

Therefore the original definitional-façade objection does not apply to `SideVal.Gr`, `pmul`, or `initialForm`.

`GradedRingStr` also prevents substituting an unrelated ring multiplication: `mul_of` requires its multiplication on homogeneous elements to equal `pmul`. Bundling the ring structure is acceptable provided its constructors are genuinely proved.

#### `GenuineStageModel.discharge`

The discharge equation is the right provenance demand:

```lean
Θ (algebraMap S.Gr Lo (S.initialForm f)) = σ.grRes f
```

It says the existing round-5 `grRes` is the image of the genuine initial form under a localization map and ring isomorphism. It does not reconstruct the source from `σ.R`.

That is a genuine repair of audit #5 §1 and §7.

There are nevertheless two important omissions:

1. `Tunit` is not intrinsically proved homogeneous of degree one. No grading on `Lo` is represented, and `Θ` is only a ring isomorphism, not a graded isomorphism. `hT` identifies it with the outer Laurent variable only after transport to the presentation.

2. The documentation claims an explicit `hL0` field, but the structure contains no such field. The target is simply hard-coded as:

   ```lean
   Lo ≃+* LTwo ↥σ.K
   ```

   Thus the identification of the genuine localization’s degree-zero subring with `↥σ.K[z±¹]` is not separately stated or checked.

So `GenuineStageModel` honestly certifies source provenance, but it is not yet the full D.1(e)/S4 graded-localization package described in its documentation.

#### L3–L4 normalization chain

The following chain is semantically sound:

```text
genuine initial form
  → algebraMap into genuine localization
  → Θ
  → σ.grRes f
  → multiply by T^(−σ.w f)
  → C (σ.R f)
```

Accordingly:

- `L4_grRes_eq_genuine` is the exact discharge equation.
- `L3_rank1_residual` genuinely converts round-5 `grRes` into the transported initial form and then normalizes it to `σ.R`.
- `L3_residual_mul` can genuinely derive residual multiplicativity from genuine initial-form multiplicativity, valuation additivity, and Laurent normalization.

But this chain does **not** by itself supply `StageCoreL`. In particular it does not establish:

- that `coeffLocSR` is the image of the genuine coefficient sublocalization;
- its degree-zero field equality;
- its exponent-group statement;
- that `σ`’s stored T-vector represents `M.Tunit`;
- `TvecUnitLaw σ`.

Therefore `L4_genuine_imp_stageCoreL` overreaches.

---

## B. Classification of the 26 statements

| # | Unit | Classification | Reason |
|---:|---|---|---|
| 1 | `L0_gt_le_ge` | FLAGGED-OK | Correct filtration inclusion. |
| 2 | `L0_ge_antitone` | FLAGGED-OK | Correct antitonicity of the filtration. |
| 3 | `L0_pmul_mk` | FLAGGED-OK | Genuine quotient multiplication computation. |
| 4 | `L0_initialForm_zero` | FLAGGED-OK | Harmless total extension of `[·]` to zero. |
| 5 | `L0_initialForm_ne_zero` | FLAGGED-OK | Correct nonvanishing of a genuine initial form. |
| 6 | `L0_deg_add` | FLAGGED-OK | Correct conditional conversion of valuation equality to degree equality. |
| 7 | `L1_pmul_assoc` | FLAGGED-OK | Correct compatibility consequence of `mul_of` and ring associativity. |
| 8 | `L1_initialForm_mul` | FLAGGED-OK | Exact D.1(c) statement. |
| 9 | `L1_initialForm_add_lt` | FLAGGED-OK | Exact strict-weight case of D.1(b). |
| 10 | `L1_gradedRingStr_exists` | FLAGGED-OK | Faithful construction target under genuine valuation multiplicativity. |
| 11 | `L1_gr_domain_iff_val` | FLAGGED-OK | Faithful D.1(c) equivalence, assuming the bundled ring is constructed through `pmul`. |
| 12 | `L2_loc_exists` | IMPRECISE | Generic localization existence; omits D.1(d)’s nonzero homogeneous-set and faithful graded-embedding content. Safe only as a generic algebra lemma. |
| 13 | `L2_degZero_subring` | FLAGGED-OK | Correct degree-zero subring of `Gr`; it is not yet the localized `L₀`. |
| 14 | `L2_homMon_homogeneous` | FLAGGED-OK | Correct homogeneity claim for the generated submonoid, subject to the representative nonzero conditions elsewhere. |
| 15 | `L2_coeffLoc` | FAITHLESS | `GenuineStageModel` contains no genuine coefficient sublocalization or S4 identification from which `CoeffLocLaw` follows. |
| 16 | `L3_Tunit_deg1` | IMPRECISE | It proves only `hT`; no intrinsic degree-one predicate exists on `Lo`. |
| 17 | `L3_iso_exists` | FLAGGED-OK | Honest but merely repackages the assumed `Θ`; it proves no new D.1(e) construction. |
| 18 | `L3_residual_mul` | FLAGGED-OK | Faithful consequence of genuine initial forms plus the discharge chain. |
| 19 | `L4_grRes_eq_genuine` | FLAGGED-OK | Exact provenance identification demanded by audit #5. |
| 20 | `L3_rank1_residual` | FLAGGED-OK | Correct normalization of the transported genuine initial form. |
| 21 | `L4_genuine_imp_stageCoreL` | FAITHLESS | `StageCoreL` includes coefficient-localization/T-vector content absent from `M`. |
| 22 | `L4_baseStage_exists` | FAITHLESS | `σ.wPrev = 0` does not characterize the D.2 base stage or supply its field, key, residual, S4, and T data. |
| 23 | `L4_base_nonvacuity_gate` | FAITHLESS | Does not state that the witness is the D.2 base construction; it can certify an unrelated existential stage. |
| 24 | `L4_TRANSvi` | FAITHLESS | `M'` repairs initial-form provenance but not the missing coefficient-sublocalization and transported-T-vector premises. |
| 25 | `L4_TRANSstage` | FAITHLESS | Omits the standard-lift, irreducible `ψ ≠ z`, positivity/coprimality, I-aug, DIV, and child-construction hypotheses required by D.3/D.7. |
| 26 | `L5_recTRANSRS` | FAITHLESS | `IsRecentering` plus a parent model does not provide a localization/graded-ring transport establishing a child model or full `StageCoreL`. |

### Counts

- **7 FAITHLESS**
- **2 IMPRECISE**
- **17 FLAGGED-OK**

“FLAGGED-OK” means faithful at the unit’s stated local or conditional scope; it does not mean the full stage package has been constructed.

---

## C. The two declared honest gaps

### G-L0: codomain-typed `L₀`

Acceptable only with a qualification.

It is legitimate to make the identification with `K[z±¹]` part of the model demanded from stage constructors. But the current structure does not contain the documented `hL0`; it folds that demand into the existence of an ungraded ring isomorphism to `LTwo`.

That is explicit enough to prevent the original backwards definition, but insufficient to certify:

- which subring of `Lo` is its degree-zero part;
- that this subring is the genuine coefficient-localization degree-zero field;
- the S4 exponent group;
- grading preservation by `Θ`.

### G-Rg: bundled localization/ring structure

Acceptable as scoped.

`Rg` is constrained by `mul_of`, and `isLoc` is a genuine `IsLocalization homMon Lo`. These are honest bundled proof obligations, not residual-defined façades. A constructor must actually produce them.

### Units consuming more than those gaps

Yes. The following require additional mathematical input beyond G-L0 and G-Rg:

- `L2_coeffLoc`
- `L4_genuine_imp_stageCoreL`
- `L4_baseStage_exists`
- `L4_base_nonvacuity_gate`
- `L4_TRANSvi`
- `L4_TRANSstage`
- `L5_recTRANSRS`

Additionally, `L3_Tunit_deg1` needs an intrinsic localization grading or a graded isomorphism if its name is to retain the “degree 1” claim.

---

## D. The five formerly deferred units

They do **not** all become faithful B2-DEF certifications merely by adding `GenuineStageModel` dependencies.

- `L4_baseStage_exists`: provenance is repaired, but the base-stage hypotheses are drastically insufficient.
- `L4_base_nonvacuity_gate`: a genuine model witness is better than a formal `StageCoreL` witness, but the statement does not pin the D.2 base stage.
- `L4_TRANSvi`: child provenance is repaired, but genuine S4 coefficient-localization and transported-vector compatibility remain absent.
- `L4_TRANSstage`: still lacks essentially the whole D.3–D.7 construction interface.
- `L5_recTRANSRS`: still lacks a genuine graded/localization transport through recentering.

None of these five is safe for fan-out in its current form.

## Units unsafe to prove under their advertised meanings

```text
L2_coeffLoc
L3_Tunit_deg1
L4_genuine_imp_stageCoreL
L4_baseStage_exists
L4_base_nonvacuity_gate
L4_TRANSvi
L4_TRANSstage
L5_recTRANSRS
```

`L2_loc_exists` is safe only if retained as a generic localization-existence lemma and not cited as the full D.1(d) homogeneous faithful-localization theorem.

## Verdict

**STOP THE LINE.**

The initial-form provenance defect is genuinely repaired, but the campaign has not yet connected the genuine source coefficient localization and transported T-vector to `CoeffLocLaw`, `TvecUnitLaw`, or `StageCoreL`.
