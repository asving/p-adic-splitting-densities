# Verdict REX — producer-side recenter-step export

**Date:** 2026-08-28  
**Unit:** REX

## Item 2 adjudication first

**Funnel refutable via `mp1`: YES.**

This is machine-proved at the current landed bytes, including the rebound
`CapstoneHypotheses`, not inferred merely from MP1R's unrelated abstract pair.

`IFC5.LadderSupplyLive.mp1` is still exactly the unrestricted
`Ladder.MP1Carrier` (`leanfinal/Uniformity/ChapI/I10LadderLive.lean:88`).  The rebound
`CapstoneHypotheses.ladder` returns `LadderSupplyLive` whenever
`CanonicalLadderConfig` holds (`I10_I15_I18.lean:164-171`).  The new probe uses the landed
degree-four S2 configuration and proves:

```lean
s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2
s2_ladderSupplyLive_false : ¬ IFC5.LadderSupplyLive C2 B2 ... 4
s2_canonical_ladder_config : CanonicalLadderConfig C2 B2 ... 4
capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4
```

The S2 producer itself sets `B2.μ = 1` and
`B2.F = B2.Φ + 1` (`C130s17.s2InputPolynomial`/`s2InputData`).  Take `Λ = -1` and the legal
block `B2'` whose key is `B2.F`.  Then
`B2'.Φ = B2.Φ - Λ` and `B2'.Φ ∣ B2.F`.  If unrestricted MP1 supplied a
`MidPeelEmission`, its quotient block would have degree at least `D`, while `hmass` at the
length-one parent would force `deg quot.F + D = deg B2.F = D`; this contradicts `D > 0`.

The same landed S2 realization supplies `CanonicalLadderConfig` through
`C130sg.s2Frontier_ladder_socket`.  Applying `CapstoneHypotheses.ladder` at that socket and
projecting `.mp1` yields the final refutation.  The counterexample block `B2'` is not asserted
to arise from S2; the current unrestricted field is exactly what permits it.

**Consequence:** amendment **A-I.7 is forced**.  It must replace only the `mp1` field of a
new superseding supply record by the same-realization `MP1CarrierLive`, preserve A-I.6's live
`vartheta` field and the existing `package`/`lb1` fields, and rebind
`CapstoneHypotheses.ladder` to that new record.  This unit does not enact the amendment.
The probe-grade construction plan is:

1. land `RecenterStep` beside the realization views and make each arising recentering produce
   it under its own `core/A/X` witness;
2. land `LadderMP1SupplierLive`/the combined live supply record, with an old-unrestricted to
   new-live adapter;
3. rebind the capstone ladder result and update the MP1 consumer to pass the step export;
4. retain E.40 and the current supply records as the refuted tension record.

## Exact source hypothesis list

The source is Guàrdia--Nart, *Genetics of polynomials over local fields*, Contemporary
Mathematics 637 (2015), Theorem 2.3.  Its exact hypothesis list is: `μ` is an “inductive
valuation equipped with a MacLane chain”; `φ ∈ KP(μ)`; `φ ≁_μ φ_r`; and `g` is a “monic
polynomial g ∈ O_v[x]”.

The factor indices and irreducible-leaf condition complete the relevant list: `-λ` runs over
the slopes of `N^-_{r+1}(g)`; `ψ` runs over the prime factors of
`R_{r+1,λ}(g)`; and `ord_ψ(R_{r+1,λ}(g)) = 1` implies that the selected
`g_{λ,ψ}` is irreducible in `O_v[x]`.  Checked primary copy:
`https://upcommons.upc.edu/bitstream/handle/2117/28206/GeneticsCM.pdf`.

Thus `B'.Φ ∣ B.F` is not the multiplicity-one premise, and even all theorem hypotheses would
prove irreducibility of `g_{λ,ψ}`, not of `B'.Φ`, without an exact identification.

## Export design

The probe elaborates three non-circular layers.

* `GNCitePayload A g phi kRes` carries the one-to-one GN data:
  `source/sourceLaws` for the inductive valuation and chain; `keyPolynomial`;
  `tangentClass`; `monicInput`; the selected `slope`; a monic irreducible `psi`; the
  residual factorization and multiplicity-one quotient; and the selected `leaf` with
  `exactLeaf : leaf = phi`.
* `RecenterStep C B B' ... Λ` existentially owns one `core/A/X/eK/eG` witnessing the same
  slot, block, and gauge-family views as the external socket.  Under that same witness it
  carries the nonzero/degree guard, `B'.Φ = B.Φ - Λ`, divisibility, the GN payload for the
  exact `B'.Φ`, and the peel core.
* `MP1StepCore B B'` contains only `MidPeelEmission` items 2--4: quotient, exact key, peel and
  mass identities, threshold, and quotient interface.  It contains neither `hirr` nor
  `hef`.

Residual multiplicity one is represented as

```lean
residual = psi * residualQuot
¬ psi ∣ residualQuot
```

together with `Irreducible psi`.  This avoids pretending that ordinary input divisibility is
residual order one.

The precise live carrier is:

```lean
def MP1CarrierLive ... : Prop :=
  ∀ Λ, Λ ≠ 0 → Λ.natDegree < C.D →
    ∀ B', B'.Φ = B.Φ - Λ → B'.Φ ∣ B.F →
      RecenterStep C B B' G Kt L N v rho q n Λ →
      Nonempty (Ladder.MidPeelEmission B B')
```

This follows the A-I.6 pattern: the old trigger and conclusion are unchanged, but the
conclusion is demanded only for a successor exported by the realization witnessing the same
socket.  Old unrestricted MP1 implies the live statement by ignoring the new premise; no
converse is claimed.

## Cite mapping table

| Source hypothesis/index | Export field | Landed S2 producer datum | Verdict |
|---|---|---|---|
| inductive `μ` with length-`r` MacLane chain | same `core.T`, `A.keys`, `source`, `sourceLaws` | `s2ArisingCore`, `s2DepthTwoKeyChain`, `s2SourceDataTwo`, `s2SourceLawsTwo_of` with landed `s2Mu3_hex`/`s2Mu3_hconv` | Lean prefix **PROVED**; analytic dictionary GAP |
| exact `φ ∈ KP(μ)` | `keyPolynomial` at `B'.Φ` | `s2Mu3KeyPoly_Φ2` only for carried `Φ2` | recentered successor **GAP** |
| `φ` not μ-equivalent to `φ_r` | `tangentClass` | none; `s2LandedPrefix_tangentClass_impossible` proves the carried `Φ2 = keyAt 2` cannot satisfy it | current exact key **FAILS** |
| monic `g ∈ O_v[x]` | `monicInput` | `s2InputPolynomial_monic`; generically `(B.natDegree_F).2` | monic **PROVED**; completion dictionary GAP |
| `-λ` selected slope | `slope`, `slope_pos`, exact slope-residual interpretation | none in `ArisingCore`/`ChainRealization`/`RealizedInput`/S2 frontier | **GAP** |
| prime factor `ψ` of `R_{r+1,λ}(g)` | `psi_monic`, `psi_irreducible`, `residual_factorization` | residual operators landed, no selected factor for this input | **GAP** |
| `ord_ψ(...) = 1` | `residual_multiplicity_one` | none | **GAP** |
| selected `g_{λ,ψ}` is exact `B'.Φ` | `leaf`, `leaf_dvd_input`, `exactLeaf` | none | **GAP, mandatory** |
| actual same-chain recentering | outer equality under the same existential witness | C.110 has generic shift algebra, no S2 successor export | **GAP** |
| peel items 2--4 | `MP1StepCore` | no S2 successor quotient/interface export | **GAP** |

The probe's `S2LandedPrefix` is the maximum current construction: depth-two chain, full
μ3 source laws, the exact carried `Φ2`, its key-polynomialhood, and monicity.  It does not
fabricate any missing row.

GMN, *Higher Newton polygons in the computation of discriminants and prime ideal
decomposition in number fields*, Trans. AMS 364 (2012), Theorem 2.11
(`docs/references/HigherNewton.tex`, label `phir`) constructs a particular monic `φ_r` of an
already specified type with prescribed residual polynomial and proves that construction
irreducible.  It still requires a refined-type/residual export and equality of the constructed
representative with `B'.Φ`; neither is landed.

## Probe status

Required command executed:

```bash
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/REX_probe.lean
```

**Exit 0.**  Zero `sorry`; every printed declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.

Files delivered:

* `leanfinal/scratch/REX_probe.lean` (new probe only)
* `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` (`[REX 2026-08-28]` appended)
* `runs/wave-c/verdict_REX.md` (this verdict)

No landed `.lean`, leanspec file, or existing scratch file was edited.  No git commit was
made.  No owner's-paper citation was used.
