# DWC — the depth-four arising-witness campaign blueprint

> **[DWR 2026-08-28] REVISION NOTICE.** Sections 1–10 preserve the original DWC proposal
> as an audit trail.  DWV refuted its `leaf^2` MP1 input.  The binding revision in §11
> supersedes every conflicting input, gate, node-grade, count, risk, and exit claim below;
> `[DWR]` rows inserted in the original node tables are deliberate visible edits, not
> claims that the old rows remain valid.

Date: 2026-08-28  
Scope: construct one honest depth-four arising witness over the S2 frame, its depth-three
and depth-four FGMN calculi, a mass-two realized input, and the four live consumer exports.
This document proposes work; it changes no landed Lean statement.

Machine authority for the arithmetic is `verification/dwc_tower_cert.py`, run from the
repository root with `python3 verification/dwc_tower_cert.py`.  It exits 0.  The certificate
checks the tower floors, cumulative degrees, normalizer exponent solves, live-index count,
and the formal mass-two recentering identity.  It deliberately does not claim the future
FGMN operators or the Guàrdia--Nart analytic dictionary.

## 1. Executive verdict

**GO on the S2 tower, but not on the naive all-proper μ5 branch.**  Keep the landed S2
chain, install `g8` as the depth-three key, extend the proper tower once more with

```text
depth-3 calculus / stage 4:  (e',f',u') = (2,1,85),  D3 = 8,  D4 = 16,
```

and use its degree-16 normalized-existence key as `keyAt 4`.  At the resulting depth-four
tower, use the refinement calculus

```text
depth-4 calculus / μ5 refinement: (e',f',u') = (1,1,171).
```

This last triple is operator data, not a fifth `DeepTower` stage: C.83 expressly excludes
`e'f'=1` refinements from `DeepTower.hproper`, while `FGMNSourceData`, `FGMNSourceLaws`, and
`FGMNCalculus` themselves impose no properness field.  Source-faithfulness of using the
refinement at the GN occurrence is nevertheless a stop-line gate (G4 below), not an
assumption hidden in construction.

The reason for the split is structural.  The documented proper continuation at depth four
would be `(2,1,341)`.  It constructs a degree-32 proper successor, not a degree-16 recentering
leaf, and `341 % 2 = 1` repeats the preceding-group obstruction already machine-exposed at
`21`.  By contrast `(1,1,171)` has the tight floor `170 < 171`, makes every cleared grade a
preceding-group grade, and makes `FGMNSourceLaws.normalized_exists` return a monic leaf of
degree `1*1*16 = 16`.  That is the degree needed for
`B'.Φ = B.Φ - Λ` at the depth-four socket.

Choose the input polynomial to be `leaf^2`.  Then the full parent has
`μ = 2`, degree `32 = 2*D4`; the quotient has mass one; `leaf ∣ leaf^2`; and the intended
correction is

```text
Λ = keyAt 4 - leaf = chainNormBelow 4 171,
```

whose certified exponent row is `(1,1,[1,1,1])` and whose degree is
`1 + 2 + 4 + 8 = 15 < 16`.  The equality with the normalizer, its nonzero proof, and the
actual residual computation are Lean nodes, not conclusions of the Python certificate.

There is exactly one deep live site: `DeepLive 4 3`.  It is simultaneously the first live
vartheta site (`LVS`), the first nonvacuous WLE site (`WLE`), and the site at which the wired
deep-twist conjunct must be assembled.

**Campaign size: 69 nodes**, each scoped for a 30–60 minute transcription unit.  The single
highest-risk node is **C4, the GN analytic binding**: it must prove that the chosen positive
slope is actually a principal Newton-polygon slope, that `residual` is the corresponding
slope residual, and that the selected completed factor descends to the exact `leaf`.

## 2. Authority and landed boundary

The design uses these landed facts, not memories of the mathematics.

* `DeepTower`, `DeepTower.Dcum`, `DeepTower.Econst`, `DeepTower.towerNorm`, and
  `DeepTower.trunc` are in `C83.lean`.  `DeepTower.hproper` is required only for stages
  actually inside the tower.
* `s2Witness` is already a depth-three `DeepTower` with stages
  `(2,1,1),(2,1,5),(2,1,21)`; `s2Witness_values` pins the upper numerals and
  `towerNorm 1 21`.  Its module record explicitly identifies the worked continuation
  `5,21,85,341`.
* `C132rp10b.g8`, `C132rp10.s2Mu3_gEight_monic`,
  `C132rp10.s2Mu3_gEight_natDegree`, and `C132rp10b.s2Mu3NormRes_g8` give the proper
  degree-eight candidate.  `C132kp3.s2Mu3_key_criterion` turns those facts into its key
  proof; SRX's scratch proof is a rehearsal, not a landed dependency.
* The depth-two calculus is genuinely packaged by `C132sg2.s2Mu3Calculus` and
  `C132sg2.s2_mu3_calculus_discharge`; the cleared consumer is
  `C132sg3.s2Mu3_gentow5w_two`.
* `FGMNSourceData` has seven fields and `FGMNSourceLaws` has thirteen; packaging is exactly
  `fgmnCalculusOf` / `fgmn_model_calculus_nonempty`.  No `ChainRealization` field can be
  cited as a calculus.
* The owner carriers are `ChainRealization`, `RealizedInput`, `SlotViewEq`, `BlockViewEq`,
  and `GaugeFamilyViewEq`.  IFC4's `s2SplitNodeWired` → `s2FrontierWired` →
  `s2FrontierWiredRealizedInput` is the construction pattern, including its one-field
  `towerRead` audit.
* TAU's compiling statement authority is `TAUProbe.CanonicalGeneratorDescent`,
  `TAUProbe.CanonicalTauLetterSource`, and `TAUProbe.CanonicalTauLiveSource`.  Only the
  conversion mechanism is proved; the source supplier is not.
* WLE's compiling statement authority is `WLEProbe.WleClearedLevelExport`,
  `WLEProbe.WleClearedPerLevelExporter`, `WLEProbe.ThetaCompatibleAt`,
  `WLEProbe.PeelCompatibleAt`, and `WLEProbe.RangeCompleteAt`.  These are scratch
  declarations and must be superseded before production use: the current level package
  still asks for one fixed `(e',f',u')` calculus family at every `i≤core.r`.  That cannot
  honestly combine this campaign's depth-three `(2,1,85)` and depth-four `(1,1,171)`
  calculi, even though its `cleared` field only consumes the top `j=3` member.
* The current MP1 surface is exactly `IFC5.GNCitePayload`, `IFC5.RecenterStep`, and
  `IFC5.MP1StepCore`.  SRX proved that the present payload is not source-bound and that the
  landed mass-one occurrence makes every `MP1StepCore` empty.

No owner's paper is an authority for this blueprint.  Any source-identification node below
must discharge its statement against the cited formal interface or the non-owner primary
source already scoped by the SRX verdict.

## 3. Tower adjudication and certified numerics

### 3.1 Proper depth-four extension

For the proper S2 tower, keep `e_i=2`, `f_i=1` through stage four and use the documented
tight-floor recurrence `u_{i+1}=e_{i+1}E_i+1`.  Only the first three stages are landed as a
Lean witness; the stage-four extension is an **examples-first conjecture until T3 lands**.

| stage `i` | `(e_i,f_i,u_i)` | `E_i=e_i f_i u_i` | `Dcum i` | floor entering stage |
|---:|---:|---:|---:|---:|
| 1 | `(2,1,1)` | 2 | 2 | — |
| 2 | `(2,1,5)` | 10 | 4 | `2*2=4<5` |
| 3 | `(2,1,21)` | 42 | 8 | `2*10=20<21` |
| 4 | `(2,1,85)` | 170 | 16 | `2*42=84<85` |

At depth three, the operator triple is `(2,1,85)`.  Its recipe degree is
`2*1*8=16`, and

```text
towerNorm 2 85 = (8,0,[0,1]),
chainNormBelow 3 85 = 2^8 * keyAt 2,
degree = 4 < 8 = degree(keyAt 3).
```

The proposed degree-16 output is `keyAt 4`.  The carried depth-three key is
`keyAt 3 = g8`, with degree eight.

### 3.2 Why the all-proper μ5 continuation is rejected for MP1

The next worked proper row is `(2,1,341)` because `2*170=340<341`.  It is a valid candidate
for a future **proper depth-five** tower, but it is the wrong object for the present
depth-four recentering:

* normalized existence has degree `2*1*16=32`, whereas `B'.Φ=B.Φ-Λ` with
  `deg Λ<16` forces `deg B'.Φ=16`;
* `341` is not in the previous cleared group (`2 ∤ 341`), the same arithmetic warning as
  `2 ∤ 21` at the landed S2 occurrence;
* merely choosing a mass-two input does not repair this degree/tangent mismatch.

The second bullet is a structural extrapolation from the landed μ3 theorem genre and is
therefore labeled **conjectural until G4**.  The first bullet is unconditional degree
arithmetic and already rejects `g32` as the exact recentering leaf.

### 3.3 Chosen depth-four refinement and genuine recentering plan

Use `(e',f',u')=(1,1,171)` at the already-built depth-four tower.  It satisfies

```text
1*E4 = 170 < 171,      gcd(171,1)=1,
e'f'D4 = 16,           1 divides every cleared grade.
```

The normalizer calculation is

```text
towerNorm 3 171 = (1,1,[1,1,1]),
chainNormBelow 4 171 = 2 * X * keyAt 1 * keyAt 2 * keyAt 3,
degree = 1+2+4+8 = 15 < 16.
```

Here `μ` is the block mass, not a tower ramification parameter.  Its occurrence audit is:

| occurrence | block mass `μ` | `μ≥2`? | role |
|---|---:|---:|---|
| landed depth-two S2 input | 1 | no | SRX's universal `MP1StepCore` obstruction |
| depth-three proper operator | no input occurrence | — | constructs `keyAt 4` |
| chosen depth-four input `leaf^2` | 2 | **yes** | first genuine MP1 candidate |

Let the refinement normalized operator be `R5`.  The intended construction is:

1. prove `R5(keyAt 4)=1` from `FGMNSourceLaws.carried_key_residual`;
2. apply normalized existence to `ψ=X+1` to get a monic degree-16 `leaf` with
   `R5 leaf=X+1`, and then `KP leaf` by the key criterion;
3. prove the recipe output is literally
   `leaf = keyAt 4 - chainNormBelow 4 171`;
4. set `Λ=chainNormBelow 4 171`; residual inequality proves `Λ≠0`, and the normalizer row
   proves `deg Λ<16`;
5. set `F0=leaf^2`, `μ=2`, `B'.Φ=leaf`, and `quot.F=leaf`.

Then `leaf ∣ F0`, `16+16=32`, and the parent/quotient masses are two/one.  The certificate
checks this algebraic shape with a sparse formal model.  It does **not** certify steps 1–3,
the key-free condition against `keyAt 4`, the rung interface, or the GN selected-factor
theorem; those are R8, C4, and C5.

### 3.4 Counts printed by the certificate

```text
proper_stages=4
live_deep_levels=1, namely [3]
full_input_mass=2
input_degree=32
leaf_degree=16
quotient_mass=1
```

A fresh `q=3` tower is rejected at this stage: it would discard the entire landed C132
operator bank and the proved `g8` successor without removing the GN surface defect.  It is
the fallback only if G5 proves that the `(1,1,171)` refinement is not a source-faithful
input to the GN occurrence.

## 4. Stop-line gates — all green before the fleet fires

1. **G0–G2, GN surface first.**  Amend the statement surface before constructing a payload.
   A positive rational is not a slope-membership proof; an arbitrary polynomial is not
   `R_{r+1,λ}(g)`; and an arbitrary divisor is not `g_{λ,ψ}`.  The completion/base-change
   datum must occur under the same owner as the slope, residual, and selected leaf.
2. **G3, repair WLE's quantifiers.**  Replace the fixed-triple total family in the scratch
   `WleClearedLevelExport` by an actual site package: one `(e',f',u')`, one calculus on
   `core.T.trunc j`, and one top `GENTOW5WCleared` law.  If a cumulative carrier is retained,
   its parameters and calculus must be indexed by the level.  No off-site calculus may be
   demanded merely to inhabit the `j=3` export.  Retype `ThetaCompatibleAt`,
   `PeelCompatibleAt`, `RangeCompleteAt`, and `wiredDemand_of_level_export` against that
   site package in the same amendment.
3. **G4, one shared owner record.**  Promote a single `DeepLevelExport X j hj` containing
   the corrected WLE calculus/wiring package, TAU's `CanonicalGeneratorDescent`, and the
   equality tying
   the calculus letters (after the same receiver/embedding) to the canonical generator
   values.  Do not land separate TAU and WLE dictionaries and merge them later.  The
   tau-word spanning theorem remains a theorem field/output outside this dictionary; the
   WLE theta/peel/range proofs remain consumer laws.
4. **G5, refinement admissibility.**  Confirm that `(1,1,171)` is an honest refinement
   calculus at μ5 and that GN's inductive-valuation input accepts it.  Confirm also that no
   `DeepTower.hproper` proof is being forged: the refinement is not stage five.
5. **G6, anti-cook compile gate.**  Compile the new carriers with three falsifiers:
   unconstrained `towerRead=0` cannot produce `GC13Wiring`; a freely chosen analytic
   residual cannot inhabit the refined GN payload; and a depth-four calculus cannot be
   projected from bare `ChainRealization`.
6. **T0/T2 arithmetic gate.**  Re-run `verification/dwc_tower_cert.py`, then land Lean
   numeral pins for `84<85`, `towerNorm 2 85`, `170<171`, and `towerNorm 3 171` before any
   operator node consumes the numbers.
7. **R8 input gate.**  Prove `IsCoprime (leaf^2) (keyAt 4)` after fraction-field mapping,
   rather than selecting the input polynomial by degree alone.  Prove `μ=2` from the literal
   degree equation.
8. **GCW-6 gate.**  The depth-four witness must be born wired.  Its `towerRead`, canonical
   generator dictionary, and per-level calculus export are construction data/proved laws
   before either socket theorem lands.  There must be no intermediate public zero-read
   depth-four `RealizedInput`.

## 5. Reuse boundary and naming discipline

The C132 stack is the template, not a theorem that deeper operators exist.  In the tables
below, every `landed:` item is an exact current declaration.  A `campaign:` item is the
contractual output name of an earlier row and is never represented as landed.  Proposed
names may be adjusted to the repository namespace, but a transcription unit may not replace
a named landed input with an analogous remembered lemma.

Depth three is the genuinely difficult level: coefficients are developed in `g8`, and the
survival/convolution proof must read the landed μ3 normalized operator.  Depth four's
`e'=f'=1` refinement removes carry and degree-growth complications, but it still needs an
honest μ4 operator and exact recipe evaluation.  Packaging remains trivial at both levels.

## 6. Node DAG — 69 nodes, 30–60 minutes each

### 6.1 Gates and tower/key carrier (13 nodes)

| node | min | statement sketch / exit condition | inputs | blocker |
|---|---:|---|---|---|
| G0 GN principal-side operators | 60 | Land actual principal Newton-polygon slope membership and slope-residual operators on one completed valued input; no free `Set ℚ` or free residual field. | landed: `IFC5.GNCitePayload`, `IFC5.GNCitePayload.slope_pos`, `IFC5.GNCitePayload.residual`, `FGMNSourceData` | analytic formalization |
| G1 GN selected-factor carrier | 60 | Define the completed selected factor by the one-sided-slope/prime-residual characterization and its base-change relation to an `O[x]` leaf. | landed: `IFC5.GNCitePayload`; campaign: G0 | completion descent |
| G2 payload/recenter amendment | 45 | Revised payload adds `slope_mem`, `residual_eq`, completed selected-leaf relation, and base-change equality; revised `RecenterStep` consumes it under the same existential owner. | landed: `IFC5.GNCitePayload`, `IFC5.RecenterStep`, `IFC5.MP1CarrierLive`; campaign: G0/G1 | signing/review |
| G3 WLE per-level amendment | 45 | Supersede the fixed-triple total calculus family by a true site package with one top calculus and `GENTOW5WCleared`; retype theta/peel/range/wired assembly; define an indexed cumulative wrapper if still needed. | landed: `WleCleared`, `GENTOW5WCleared`; scratch authority: `WLEProbe.WleClearedLevelExport`, `WLEProbe.ThetaCompatibleAt`, `WLEProbe.PeelCompatibleAt`, `WLEProbe.RangeCompleteAt`, `WLEProbe.wiredDemand_of_level_export` | signing/review |
| G4 shared deep-level export | 60 | Promote `DeepLevelExport X j hj`: corrected G3 calculus/wiring package + `CanonicalGeneratorDescent` + receiver/letter equality; derive WLE and TAU dictionary projections. | landed: `ChainRealization`, `RealizedInput`; scratch authority: `TAUProbe.CanonicalGeneratorDescent`; campaign: G3 | statement review |
| G5 μ5 refinement admissibility | 60 | Prove/document that `(1,1,171)` is a source-faithful refinement calculus and GN inductive valuation, while not a fifth proper tower stage. | landed: `DeepTower.hproper`, `FGMNSourceData`, `FGMNSourceLaws`, `FGMNCalculus` | **stop if false** |
| G6 carrier falsifiers | 45 | Compile zero-read, arbitrary-residual, bare-carrier calculus, and off-site fixed-triple non-derivability teeth. | landed: `IFC3.s2_wiring_refuted_at_landed_exports`, `C130s18.embeddedValue_not_uniform`; campaign: G2/G3/G4 | none after statements |
| **[DWR] G7 quotient key-free gate** | research gate, 1–3 days | Before an MP1 core exists, prove `BlockData.hkeyfree` for the literal quotient polynomial against `B'.Φ`; the `leaf²` control must fail here. | campaign: revised R8r/C5r; cert | **stop if false** |
| **[DWR] G8 residual order-one gate** | research gate, 2–5 days | Compute the actual selected slope residual and prove `ord_ψ(R_λ(F0))=1`; the `leaf²` control must report order two. | campaign: G0/G1/G9/C4r; cert is only the algebraic control | **stop if false** |
| **[DWR] G9 GN valuation/index gate** | **STOP-LINE: RED** | Identify the valuation, chain index, recenter key, principal side, and `R_{r+1,λ}` used by GN with the exact landed operator.  The current payload forces selected factor `=φ=B'.Φ` while also requiring `φ∣g`; this is the separate `φ`-power factor, not a finite-slope `g_{λ,ψ}`. | landed payload + GN factor indexing; campaign: G0/G1/G2/G5/D4-18 | **A-I.8 review; do not enact here** |
| **[DWR] G10 occurrence→universal gate** | theorem family, 2–4 days after producers | Prove a per-witness exporter quantified over every live level and every same-witness exported recenter step; one `j=3`/one-`Λ` occurrence is only its nonvacuity tooth. | campaign: G3/G4/C0–C5r | universal supplier boundary |
| T0 numeric certificate | 30 | Keep `verification/dwc_tower_cert.py` green; output all table rows and counts in §3. | landed: `DeepTower.towerNorm` definition | **DONE** |
| T1 depth-three chain alias | 45 | Define depth-three S2 occurrence from `s2Witness`; set `keyAt 3=g8`; pin degrees 2/4/8 and monicity. | landed: `s2Witness`, `C132rp10b.g8`, `C132rp10.s2Mu3_gEight_monic`, `C132rp10.s2Mu3_gEight_natDegree` | key proof next row |
| T2 `g8` key proof and `KeyChain` | 60 | Prove `S2Mu3KeyPoly g8` from the landed criterion/residual facts; construct depth-three `KeyChain`. | landed: `C132kp3.s2Mu3_key_criterion`, `C132rp10b.s2Mu3NormRes_g8`, `C132rp10.s2Mu3_X_add_one_irreducible`; campaign: T1 | none |
| T3 depth-four tower datum | 60 | Extend `s2Witness` with stage `(2,1,85)`, `ψ3=X-1`, constant residue field, and pins `84<85`, `Dcum4=16`. | landed: `DeepTower`, `s2Witness`, `Polynomial.quotientSpanXSubCAlgEquiv`; cert T0 | conjectural extension becomes theorem here |
| T4 depth-three normalizer pins | 45 | Land `towerNorm 2 85=(8,0,[0,1])`, degree `4<8`, and cleared exact-grade target `170`. | landed: `DeepTower.towerNorm`, `FGMNCalculus.chainNormBelow`; campaign: T2/T3 | exact-grade waits D3 |
| T5 depth-four normalizer pins | 45 | Land `towerNorm 3 171=(1,1,[1,1,1])`, polynomial formula, degree `15<16`, nonzero. | landed: `DeepTower.towerNorm`, `FGMNCalculus.chainNormBelow`; campaign: T3 and later D3-19 key chain | polynomial pin waits keyAt4 |

T5's final polynomial equality is completed after D3-19 constructs `keyAt 4`; its pure
exponent theorem can land immediately.  This is the only intentional two-part row.

### 6.2 Depth-three / μ4 operator stack at `(2,1,85)` (20 nodes)

| node | min | statement sketch / exit condition | inputs | blocker |
|---|---:|---|---|---|
| D3-00 support shell | 60 | Define the `g8`-development support and prove zero/ne-top/add/negation laws. | landed: `C132nv0.dv2Supp_zero_eq_top`, `C132nv0.dv2Supp_add_eq`, `C132rp10b.g8`; campaign: T2 | new development layer |
| D3-01 μ4 value | 45 | Define `s2Hgt4` with outer `(u,e)=(85,2)`; pin zero/add and `s2Hgt4 g8=85`. | landed: `C132nv1.s2Hgt₃`, `C132nv1.s2Hgt₃_Φ₂`; campaign: D3-00/T4 | none |
| D3-02 endpoint/minimizer | 60 | Port side-set, endpoint uniqueness, and support bounds. | landed: `C132nv2.Dv2OnSide`, `C132nv2.dv2OnSide_mul_endpoint`; campaign: D3-00/01 | none |
| D3-03 μ3 survival core | 60 | Reduction modulo `g8` preserves the μ3 endpoint residual product for coefficients of degree `<8`. | landed: `C132rp8.s2Mu3NormRes_mul`, `C132kp6b.s2Mu3KeyPoly_normRes_natDegree`; campaign: T2/D3-02 | genuine new core |
| D3-04 value product | 60 | Assemble unconditional `s2Hgt4_mul`; retain zero cases and side minimizers. | landed: `C132nv4.s2Hgt₃_mul`, `C132nv6.s2Hgt₃_mul_all`; campaign: D3-02/03 | survival |
| D3-05 valuation/grades | 45 | Package `AddValuation`; define exact/above grades and uniqueness/product laws. | landed: `C132nv6.s2AddVal₃`, `C132rp0.S2Mu3ExactGrade`; campaign: D3-04 | none |
| D3-06 grade-line/epsilon | 60 | Define μ4 gate `2*μ3(A_s)+85s=β`; derive Def-3.12 coordinates and the terminal-field epsilon collapse. | landed: `C132rp1.S2Mu3SlotOnGrade`, `C132rp1.s2Mu3EpsOf_eq_one`; campaign: D3-05 | inherited μ3 read faithfulness |
| D3-07 recursive coefficient | 60 | Define the μ4 coefficient by the landed μ3 graded/normalized read; prove gate, zero, and letter-display pins. | landed: `C132rp1.s2Mu3Coeff`, `C132rp1.s2Mu3Coeff_eq_eval_normRes`; campaign: D3-06 | exact transport |
| D3-08 total graded operator/add | 60 | Assemble polynomial-valued graded residual; prove finite support, zero-above, and exact-grade additivity. | landed: `C132rp2.s2Mu3GradedRes`, `C132rp3.s2Mu3GradedRes_add`; campaign: D3-07 | none |
| D3-09 carry arithmetic | 45 | Prove parity/carry and endpoint addition for `(85,2)`. | landed: `C132rp4.s2Mu3Carry_parity`, `C132rp4.s2Mu3_def312_add`; campaign: D3-06 | numeral-only |
| D3-10 convolution | 60 | Prove μ4 coefficient convolution through μ3 residual multiplicativity. | landed: `C132rp5.s2Mu3Coeff_mul`, `C132rp8.s2Mu3NormRes_mul`; campaign: D3-03/07/09 | genuine new core |
| **[DWR] L2E shared engine** | **research program, 8–15 working days** | **Supersedes D3-03/D3-10 as isolated transcription rows.** Build the generic level-2 Theorem-M twin once; instantiate it both at `(g8,85,2)` and for F1.4–F1.6. Exact node list and acceptance tests: §11.7. | landed: `C133mh1`, `C133mh3`, `C134dv2g`, `C132nv2`; campaign: T2/D3-02 | new multiplicative-operator root |
| D3-11 graded product/scalar | 60 | Assemble twisted/plain product laws, `PrevGrade := 2∣β`, and coefficient-zero nonvanishing below degree 8. | landed: `C132rp6.s2Mu3_graded_mul`, `C132rp7.s2Mu3_graded_scalar_nonzero`; campaign: D3-08/10 | none |
| D3-12 normalized operator | 60 | Strip the initial `X` power; prove universal multiplication, key reads, and nonzero constant. | landed: `C132rp8.s2Mu3NormRes`, `C132rp8.s2Mu3NormRes_mul`; campaign: D3-11 | none |
| D3-13 recipe/B-1 | 60 | Prove corrected recipe and `chainNormBelow 3 85` exact grade `170`, degree, and nonzero supplies. | landed: `C132rp9.s2Mu3_chainNormBelow_two_twenty_one`, `C132sg3.s2Mu3_B1_exact_grade_supply_cleared`; campaign: T4/D3-12 | none |
| D3-14 normalized existence | 60 | Evaluate the degree-16 recipe at `X+1`; produce monic `g16`, degree 16, residual `X+1`. | landed: `C132rp10b.s2Mu3_hex`, `C132rp10b.s2Mu3NormRes_g8`; campaign: D3-12/13 | exact non-recipe evaluation |
| D3-15 key predicates/divisibility | 60 | Define μ4 initial equivalence/divisibility/minimality/key predicates and normalized-residual divisibility iff. | landed: `C132kp0.S2Mu3KeyPoly`, `C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd`; campaign: D3-05/12 | none |
| D3-16 key criterion/irreducibility | 60 | Prove criterion, key irreducibility, and `g16` key theorem. | landed: `C132kp3.s2Mu3_key_criterion`, `C132kp5.s2Mu3_key_irreducible`; campaign: D3-14/15 | none |
| D3-17 carried key + initial iff | 60 | Prove `g8` is carried μ4 key with residual 1 and residual-equality iff initial equivalence. | landed: `C132kp4.s2Mu3KeyPoly_Φ₂`, `C132kp6b.s2Mu3_initial_iff_residual`; campaign: D3-12/15/16 | converse proof |
| D3-18 source records | 60 | Package all seven operators and all thirteen laws at depth three `(2,1,85)`; every projection gets a pin. | landed: `FGMNSourceData`, `FGMNSourceLaws`, `C132fd0.s2SourceDataTwo`; campaign: D3-01..17 | none |
| D3-19 calculus + keyAt4 | 45 | Package via `fgmnCalculusOf`; prove literal `Nonempty`; define `keyAt4=g16` and finish the depth-four `KeyChain`. | landed: `fgmnCalculusOf`, `fgmn_model_calculus_nonempty`; campaign: T3/D3-14/16/18 | none |

### 6.3 Depth-four / μ5 refinement stack at `(1,1,171)` (19 nodes)

| node | min | statement sketch / exit condition | inputs | blocker |
|---|---:|---|---|---|
| D4-00 support shell | 60 | Define the `keyAt4` development support with outer `(171,1)` and its basic laws. | landed: `C132nv0.dv2Supp_zero_eq_top`, `C132nv0.dv2Supp_add_eq`; campaign: D3-19 | new development layer |
| D4-01 μ5 value/product | 60 | Define `s2Hgt5`; prove zero/add/product and `s2Hgt5 keyAt4=171`. | landed: `C132nv6.s2Hgt₃_mul_all`; campaign: D4-00/D3-19 | survival folded into D4-02 |
| D4-02 μ4 survival | 60 | Prove endpoint survival modulo `keyAt4` using the μ4 normalized product. | landed pattern: `C132nv3b.s2_dvSupp_mul_modByComposedKey_eq`; campaign: D3-12/16/D4-00 | genuine new core |
| D4-03 valuation/grades | 45 | Package the μ5 valuation and exact/above grade bank. | landed: `C132nv6.s2AddVal₃`, `C132rp0.S2Mu3ExactGrade`; campaign: D4-01/02 | none |
| D4-04 grade-line coordinates | 45 | With `e'=1`, prove the unique slot residue is 0 and `PrevGrade` is all grades. | landed: `C132rp1.s2Mu3_def312_level3`, `C132rp6.S2Mu3PrevGrade`; campaign: G5/D4-03 | refinement gate |
| D4-05 recursive coefficient | 60 | Define μ5 coefficient via μ4 graded read; epsilon/carry collapse to 1/0. | landed: `C132rp1.s2Mu3Coeff`; campaign: D3-08/D4-04 | exact transport |
| D4-06 graded operator/add | 60 | Assemble total operator, zero-above, and additivity. | landed: `C132rp2.s2Mu3GradedRes`, `C132rp3.s2Mu3GradedRes_add`; campaign: D4-05 | none |
| D4-07 convolution/product | 60 | Prove coefficient convolution and untwisted graded multiplication (carry identically zero). | landed: `C132rp5.s2Mu3Coeff_mul`, `C132rp6.s2Mu3GradedRes_mul_of_prevGrade`; campaign: D4-02/05/06 | none |
| D4-08 scalar nonzero | 45 | Prove coefficient-zero nonvanishing below degree 16. | landed: `C132rp7.s2Mu3_graded_scalar_nonzero`; campaign: D4-03/06 | none |
| D4-09 normalized operator | 60 | Define μ5 normalized residual; prove multiplication, carried-key read 1, and key-power values. | landed: `C132rp8.s2Mu3NormRes`; campaign: D4-07/08 | none |
| D4-10 normalizer exact grade | 45 | Finish T5: `chainNormBelow 4 171` is exact grade 171, degree 15, nonzero. | landed: `FGMNCalculus.chainNormBelow`; campaign: T5/D4-03/09 | none |
| D4-11 literal refinement recipe | 60 | Prove the `f'=1,e'=1` recipe is `keyAt4 - chainNormBelow 4 171` and compute residual `X+1`. | landed: `C132rp9.s2Mu3_normalized_recipe`, `C132rp10b.mu3GradedRes_g8`; campaign: D4-09/10 | exact evaluation |
| D4-12 normalized existence leaf | 45 | Define `leaf`; pin monic, degree 16, residual `X+1`, and `leaf=keyAt4-Λ`. | landed: `C132rp10b.g8` construction pattern; campaign: D4-11 | none |
| D4-13 key predicates/divisibility | 60 | Define μ5 key predicates and residual-divisibility equivalence. | landed: `C132kp0.S2Mu3KeyPoly`, `C132kp0.S2Mu3InitialEquiv`, `C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd`; campaign: D4-03/09 | none |
| D4-14 criterion/leaf key | 60 | Prove criterion and `leaf` is a key polynomial; prove carried key is a key. | landed: `C132kp3.s2Mu3_key_criterion`, `C132kp4.s2Mu3KeyPoly_Φ₂`; campaign: D4-12/13 | none |
| D4-15 irreducibility/coprime | 60 | Prove both keys irreducible and distinct monic; derive fraction-map coprimality of `leaf^2` and `keyAt4`. | landed: `C132kp5.s2Mu3_key_irreducible`; campaign: D4-12/14 | input gate R8 |
| D4-16 initial iff/tangent | 60 | Prove residual equality iff initial equivalence; conclude `¬ initialEquiv leaf keyAt4` from `X+1≠1`. | landed: `C132kp6b.s2Mu3_initial_iff_residual`; campaign: D4-09/12/14 | none |
| D4-17 source records | 60 | Package seven operators and thirteen laws at `(1,1,171)`, with nonvacuous recipe/existence. | landed: `FGMNSourceData`, `FGMNSourceLaws`, `C132fd0.s2SourceLawsTwo_of`; campaign: D4-01..16 | none |
| D4-18 calculus packaging | 45 | Define μ5 refinement calculus and literal nonempty theorem solely through `fgmn_model_calculus_nonempty`. | landed: `fgmnCalculusOf`, `fgmn_model_calculus_nonempty`; campaign: D4-17 | none |

### 6.4 Realization and mass-two arising input (10 nodes)

| node | min | statement sketch / exit condition | inputs | blocker |
|---|---:|---|---|---|
| R0 terminal receiver/normalizer | 45 | Build depth-four `TerminalReceiver` and `LaurentNormalizer`; pin level maps and exact heights. | landed: `DeepTower.terminalReceiver`, `DeepTower.laurentNormalizer`; campaign: T3 | none |
| R1 stage-three slot tables | 60 | Extend `hgt/dig/Full/lift` to level 3, tied to the μ4 value/operator data. | landed pattern: `C130sg.s2NPFull`, `C130s17.S2RepositoryRealization`; campaign: D3-01/D3-05 | source tables |
| R2 stage-four slot tables | 60 | Build level-4 slot carrier and tie its point height to μ5 `nextValue`. | landed: `SplitNodePointSource.stageCarrier`; campaign: D4-01/D4-03 | source tables |
| R3 points/evaluation | 60 | Extend NP point, coefficient hom, coordinate, and valuation laws through both new live stages. | landed: `C130s17.s2EvalHom`, `C130sg.s2SplitNode`; campaign: R1/R2 | valuation realization |
| R4 thresholds/windows | 60 | Supply source-backed thresholds at levels 1–4 and prove strict windows; no invented numeral branch. | landed: `C130sg.S2LevelOneThreshold`, `C130sg.S2LevelOneThreshold.ofSplitNode`; campaign: R1/R2 | faithfulness datum |
| R5 letters/canonical dictionary | 60 | Define ambient letters/canonical reads and prove the shared receiver/letter equalities required by G4. | landed: `SplitNodePointSource.canonicalRead_generatorWord`; campaign: G4/R0/D3-19/D4-18 | OPEN-LETTERS core |
| R6 wired gauge fields | 45 | Define arena read, law-satisfying `towerRead`, and peel units at construction; prove live/junk pins. | landed: `IFC4.s2TowerReadWired`, `IFC4.s2SplitNodeWired_inherits`; campaign: R0/R5 | GCW-6 |
| R7 split node + chain realization | 60 | Assemble `SplitNodePointSource`, then `ChainRealization`; pin every stage table and the one-field read audit. | landed: `SplitNodePointSource`, `ChainRealization`, `C130s17.S2SourceFrontier.toCarrier`; campaign: R0..R6 | none |
| R8 mass-two `ArisingCore` | 60 | Set `F0=leaf^2`, `n=32`, `μ=2`, stage `i=r=4`; prove monic, degree block, and keyfree. | landed: `ArisingCore`, `C130s17.S2InputData.toArisingCore`; campaign: D4-12/15/R7 | coprime gate |
| **[DWR] R8r distinct-factor formal candidate** | research construction, 2–4 days | **Supersedes R8 as the algebraic control, not as an honest GN occurrence.** Set `h=keyAt4+1`, `F0=leaf*h`, `μ=2`; prove parent/quotient key-freeness and literal development records.  G9 is RED under the current payload. | campaign: D4-09/12/14/15, G7, R7 | blocked from GN by G9 |
| R9 `RealizedInput` + sockets | 60 | Select legal point, package `RealizedInput`, and expose ladder/deep-twist sockets at literal depth 4 without a zero-read intermediate. | landed: `RealizedInput`, `C130s17.S2SourceFrontier.realizedInput`, `IFC4.s2FrontierWired_deepTwist_socket`; campaign: R7/R8 | none |

### 6.5 Four consumer legs and final assembly (7 nodes)

| node | min | statement sketch / exit condition | inputs | blocker |
|---|---:|---|---|---|
| C0 shared export inhabitant | 60 | At the exact `X` from R9 and `j=3`, inhabit G4's `DeepLevelExport`; project the depth-three calculus, receiver, wiring, and generator dictionary. | landed: `GaugeFamilyViewEq`, `IFC3.GC13Wiring`; campaign: G3/G4/D3-19/R5/R9 | shared dictionary |
| C1 WLE cleared data | 60 | Prove the corrected per-level top `GENTOW5WCleared` law at `j=3` from the depth-three `(2,1,85)` calculus and B-1 normalizer supplies. | landed: `GENTOW5WCleared`, `C132sg3.gentow5w_two_cleared`; campaign: G3/D3-13/D3-19/C0 | single-w law |
| C2 WLE dictionaries | 60 | Prove `ThetaCompatibleAt`, `PeelCompatibleAt`, and `RangeCompleteAt`; port the proof of `WLEProbe.wiredDemand_of_level_export` to G3's corrected site package. | landed: `IFC1.gentowWWindow_of_cleared_law`, `IFC1.gentowW_iff_zero_window_tail`; scratch authority: `WLEProbe.ThetaCompatibleAt`, `WLEProbe.PeelCompatibleAt`, `WLEProbe.RangeCompleteAt`, `WLEProbe.wiredDemand_of_level_export`; campaign: G3/C0/C1/R6 | GCW-4/5, peel tie |
| C3 canonical tau/vartheta | 60 | Prove the general generator-word instance at `j=3`, use C0's descent dictionary, build `CanonicalTauLetterSource`, and derive `VarthetaRes`. | landed: `SplitNodePointSource.canonicalRead_generatorWord`, `Gauge.hvarthetaRes_of_tau_letters`; scratch: `TAUProbe.canonical_tau_mem`, `TAUProbe.varthetaRes_of_canonicalTauLetterSource`; campaign: C0 | tau triangular spanning |
| C4 GN analytic binding | 60 | For `g=leaf^2`, prove actual principal slope membership, actual slope residual with `X+1` multiplicity one, and completed selected factor/base-change equality to `leaf`. | campaign: G0/G1/G2/D4-12/14/16/R8 | **HIGHEST RISK** |
| C5 genuine recenter/MP1 | 60 | Set `Λ=chainNormBelow 4 171`, build successor block and quotient; prove `RecenterStep`, `MP1StepCore`, then `MidPeelEmission`. | landed: `IFC5.MP1StepCore`; campaign: revised G2 surface, D4-10/12/C4/R8/R9 | rung interface |
| C6 deepTwist tooth | 60 | At the unique `DeepLive 4 3`, pair C3's `VarthetaRes` with C2's wired `GentowW`; expose the `DeepTwistConjunctLive` arising-witness theorem and the ladder record with C5's live MP1 leg. | landed: `Ladder.DeepTwistConjunctLive`, `IFC5.LadderSupplyLive₂`, `IFC0.deepTwistField_of_suppliers`; campaign: C2/C3/C5/R9 | capstone binding remains separate |
| **[DWR] C4r honest GN binding** | **REFUTED under current payload** | Old C4 is refuted by multiplicity two.  The distinct-factor replacement clears the formal order control but cannot identify `leaf=φ` with finite-slope `g_{λ,ψ}`: the literal divisor `φ` is in the separate key-power term. | G9; current `GNCitePayload.exactLeaf`/`leaf_dvd_input` | **A-I.8-grade shape issue** |
| **[DWR] C5r provenance-bound recenter/MP1** | **BLOCKED by C4r/G9** | Conditional post-review construction: `B'.F=keyAt4+1`, `B'.T=B.T`, `quot.F=B'.F`; prove both key-free fields before `MP1StepCore`. | revised G2, G7, R8r/R9 | no honest current payload |
| **[DWR] C6r occurrence tooth only** | 1–3 days after consumers | **Narrows C6.** Expose the same-`X`, `j=3` deep tooth and the one recenter occurrence as nonvacuity results; do not claim `LadderSupplyLive₂` until G10's universal exporter, HE7A, and LB1 are supplied. | campaign: C2/C3/C5r/R9 | universal fields remain separate |

## 7. Dependency graph and fleet order

```text
G0 → G1 → G2
          └──────────────→ C4 → C5 ─┐
G3 → G4 → G6 → C0 → C1 → C2 ───────┤
      │          └────→ C3 ─────────┤
G5 ─────────────────→ D4 stack      │
T0 → T1 → T2 → D3 stack → D3-19 → T5 → D4 stack
T0 → T3 ────────────────────────────┘
D3-19 + D4-18 + R0..R9 → C0
C2 + C3 + C5 → C6
```

Fleet rule: G0–G6, T0, and the signed/reviewed statement changes complete first.  T1–T4 and
D3 may then run.  D4 begins only after G5 and D3-19.  R7/R9 may not publish an unwired
depth-four witness.  C4 can start once G2, D4-16, and R8 exist; it is not allowed to fill
the payload with a synthetic factorization.

## 8. Exact consumer exits

The campaign is not complete merely because the two calculi package.

1. **Depth-three calculus:** literal
   `Nonempty (FGMNCalculus depthThree 2 1 85)`, proved through
   `fgmn_model_calculus_nonempty`.
2. **Depth-four refinement calculus:** literal
   `Nonempty (FGMNCalculus depthFour 1 1 171)`, by the same packaging theorem.
3. **Arising witness:** a `RealizedInput` whose `core.r=4`, `core.i=4`, `core.μ=2`,
   `core.F₀=leaf^2`, and whose read is wired at construction.
4. **WLE:** a nonempty owner export at the literal site `j=3`, with positive `f'=1`, plus
   theta/peel/range dictionaries and `WiredGentowDemand` at its own exports.
5. **Vartheta:** a `CanonicalTauLetterSource` for that same `X`, view, and `j=3`, converted
   to the exact `VarthetaRes` demanded by the live ladder/deep-twist records.
6. **MP1:** a nonempty `RecenterStep` with literal `Λ≠0`, `deg Λ<16`,
   `B'.Φ=keyAt4-Λ=leaf`, `leaf∣leaf^2`, an honestly bound revised GN payload, and a
   nonempty `MP1StepCore` with mass equation `16+16=32`.
7. **Deep tooth:** the unique `DeepLive 4 3` branch of `DeepTwistConjunctLive`, pairing the
   exact vartheta and wired W conclusions from the same arising witness.

The final capstone-wide universal supplier is outside this occurrence campaign.  C6 is the
first honest deep inhabitant and the construction theorem needed to bind such suppliers; it
does not assert that every arbitrary `CanonicalDeepTwistConfig` is this witness.

## 9. Falsifiers and fallback

* If the depth-four witness exists before its wiring/dictionary records, GCW-6 is violated.
* If C4 can be filled after replacing the slope or residual arbitrarily, G0/G2 failed.
* If `Λ=0` is not refuted from `X+1≠1`, the recentering is not genuine.
* If the input is `keyAt4+1` or has `μ=1`, SRX's universal `MP1StepCore` obstruction returns.
* If a proof uses `(2,1,341)` to produce the exact degree-16 leaf, it has a degree error.
* If a proof calls the `(1,1,171)` refinement a fifth `DeepTower` level, it violates
  `DeepTower.hproper` and the campaign's own adjudication.

If G5 rejects the refinement as a GN input, stop.  The fallback is a fresh tower whose
**full-depth next valuation has `e'=1`** and supports a same-degree selected leaf; merely
switching from `q=2` to `q=3` without that property does not solve the recentering problem.

## 10. Campaign exit gates

1. `python3 verification/dwc_tower_cert.py` exits 0 with the exact §3 rows.
2. All 69 node outputs elaborate per file with no `sorry`; never use bare `lake build` as
   the validator.
3. Both source records name seven data projections and thirteen law projections, with
   anti-drift pins to their concrete operators.
4. Both calculus nonempty theorems use only `fgmn_model_calculus_nonempty` after records.
5. The realized input is mass two and keyfree, and no zero-read depth-four public witness
   exists on the path.
6. The revised GN payload contains actual slope membership, actual slope-residual equality,
   selected completed-factor identification, and base-change descent to `leaf`.
7. The exact same `X` and `j=3` inhabit C0, C2, C3, C5, and C6; no view or owner is swapped.
8. C6 proves both halves of the unique deep tooth and records that `DeepLive 4 j` forces
   `j=3`.

## 11. [DWR 2026-08-28] binding revision after DWV REJECT

This section is numerically downstream of the extended
`verification/dwc_tower_cert.py`.  It supersedes DWC §§1, 3.3–3.4, 4, 6–10 wherever they
refer to `leaf²`, call C4 viable, omit the four new gates, price research as transcription,
or infer a universal supply record from one occurrence.  The tower numerics remain unchanged.

### 11.1 Numerical adjudication of the replacement candidate (MP1 remains stopped)

`MP1StepCore.hmass` literally requires

```text
natDegree(quot.F) + C.D = natDegree(B.F).
```

Every `BlockData` has mass at least one and therefore polynomial degree at least `C.D`.
Consequently a mass-one input of degree `D=16` is impossible: its quotient would have degree
at least 16, while `hmass` would say `16+16=16`.  The `leaf·h` idea therefore works only when
`h` also has degree 16 and the parent still has mass two.

Use the literal second factor

```text
k := keyAt 4
Λ := chainNormBelow 4 171
leaf := k - Λ
h := k + 1
F0 := leaf * h
B'.Φ := leaf
B'.F := h
quot.Φ := leaf
quot.F := h.
```

This is a two-distinct-factor input, not a second normalized-existence key.  At the intended
two-element terminal residue field, `FGMNSourceLaws.normalized_exists` requires a monic
irreducible degree-one residual with nonzero constant coefficient, so its only admissible
residual is `X+1`; it cannot manufacture a second degree-16 leaf with residual coprime to
`X+1`.  The carried-key perturbation avoids that dead end.

The proof obligations for `h` are concrete:

1. `h` is monic of degree 16 by lower-term addition to monic `k`.
2. `k` and `h=k+1` are coprime by the explicit Bézout difference `h-k=1`.
3. `k` and `leaf` are distinct monic irreducibles of the same degree (`Λ≠0`), hence coprime
   after fraction-field mapping.
4. `leaf` and `h` are coprime: `leaf` is irreducible and cannot divide the same-degree monic
   `h` unless they are equal; equality would give `Λ=-1`, impossible because `deg Λ=15`.
5. Therefore `F0` is key-free against parent key `k`, and the quotient block `h` is key-free
   against peeled key `leaf`.
6. In the formal residual control, assigning the cofactor a nonzero scalar residual gives
   `R(F0)=(X+1)c`, hence order exactly one.  This repairs DWV's multiplicity defect but does
   not identify `leaf` with GN's finite-slope selected factor.

The certificate's sparse model uses `c=1` as the residual-unit control.  It proves only the
formal algebra; G8/G9/C4r own the analytic identification.  Its fresh output is:

```text
counts: proper_stages=4, live_deep_levels=1, full_input_mass=2,
        input_degree=32, leaf_degree=16, cofactor_degree=16, quotient_mass=1
accepted input: F0=leaf*(keyAt4+1), Lambda != 0, deg Lambda=15<16
  exact_quotient=keyAt4+1, parent_keyfree=True, quotient_keyfree=True
  hmass=16+16=32, ord_psi(residual)=1
rejected controls: leaf^2 parent_keyfree=True but quotient_keyfree=False
  exact_quotient=leaf, ord_psi(residual)=2
  mass-one leaf input hmass=False
```

Thus a key-free, multiplicity-one *formal candidate* exists numerically.  It is not an honest
GN occurrence under the current statement.  `GNCitePayload` is instantiated with
`phi=B'.Φ`; `exactLeaf` identifies the theorem-selected factor with that same `phi`; and
`leaf_dvd_input`/`RecenterStep` require `phi∣g`.  In GN's factor indexing a literal `phi`
factor is the separate key-power term.  It has no finite principal side and is not one of the
`g_{λ,ψ}` selected by a slope residual.  Replacing `leaf²` by `leaf*h` changes the power from
two to one but does not move that copy into a finite-slope selected factor.

Therefore **no source-faithful occurrence exists in this tower under the current payload
shape** (indeed, the obstruction is shape-level, not numeric).  This is the required
stop-the-line finding about the intended inhabitability of `MP1CarrierLive`: re-examine the
payload's identification of the GN test key with the emitted factor, or use the already
identified direct key-irreducibility route, only under A-I.8 authority.  This revision flags
that question and does not enact either change.

### 11.2 The three missing DWV gates and the input control gate

The four `[DWR]` rows G7–G10 inserted in §6.1 are part of the DAG.  For clarity, the three
mathematical gates DWV found missing are:

| gate | exact acceptance condition | falsifier |
|---|---|---|
| **G7 quotient `BlockData` key-free** | Construct the literal quotient block with `quot.F=h`, `quot.Φ=leaf`, and prove its fraction-field `IsCoprime`; construct `B'` with the same `F/Φ` pair. | Replacing `h` by `leaf` must fail. |
| **G8 residual multiplicity one** | Formal candidate target: for a genuine selected slope, prove `R_λ(F0)=ψ*c`, `c≠0`, and `¬ψ∣C c`; equivalently `ord_ψ=1`. | `leaf²` computes `ψ²` and order two.  Passing this alone does not pass G9. |
| **G9 GN valuation/key-index alignment — RED** | The current surface requires `selected g_{λ,ψ}=leaf=φ` and `φ∣F0`.  GN indexes literal `φ` divisors in the separate key-power term, so no finite principal slope/residual can select that same factor. | The distinct-factor candidate still contains one literal `φ`; changing its cofactor cannot repair the index mismatch. |

Parent input key-freeness remains an independent R8r acceptance condition.  Passing it does
not imply G7: parent key `k` and peeled key `leaf` are different polynomials.

### 11.3 Provenance-bound `RecenterStep`

G2 must be re-signed only after review.  Besides SRX's slope/residual/selected-factor fields,
the producer must bind the successor block's otherwise free data.  The minimum honest
transition payload is:

```text
step.quot.Φ = B'.Φ
step.quot.F = B'.F
B'.T = B.T
step.quot.T = B.T
B.F = B'.Φ * B'.F
natDegree(B'.F) + C.D = natDegree(B.F),
```

with the quotient `RungInterface` attached to this same `step.quot`.  At the chosen
occurrence these specialize to `B'.F=keyAt4+1` and `B'.T=B.T`.  An equality merely fixing
`B'.Φ` is insufficient.  Conversely, `B'.F=B.F` is impossible and must not be proposed:
`B'.Φ∣B.F` would contradict `B'.hkeyfree`.  The peeled block is the quotient block.

The analytic fields must remain under the same `core/A/X` owner and add all of:

```text
slope_mem_principal
residual_eq_slopeResidual
selectedFactor_spec
selectedFactor_baseChange_eq
leaf_eq_recentered_key.
```

The exact base-change relation, rather than a free equality between two `O[x]` names, is the
provenance link to GN's completed factor.

### 11.4 Occurrence is not universal supply

The honest result of C0–C5r is two nonvacuity theorems for one explicit witness `X`:

```text
Nonempty (DeepLevelExport X 3 deepLive_four_three)
∃ Λ B', RecenterStepFor X B B' Λ.
```

Neither theorem inhabits `LadderSupplyLive₂`.  Its `package` and `lb1` are separate HE7A/LB1
campaigns; `mp1` quantifies over every legal `Λ`, `B'`, and same-realization step; `vartheta`
quantifies over every `i≥3` at which `CanonicalLadderLiveAt` holds.

G10 therefore lands a per-witness exporter, in the same quantifier discipline as WLE:

```text
DeepLevelPerWitnessExporter X :=
  ∀ j, (hj : DeepLive core.r j) → Nonempty (DeepLevelExport X j hj)

MP1EmissionPerWitnessExporter X :=
  ∀ Λ B', RecenterStepFor X B B' Λ →
    Nonempty (MidPeelEmission B B').
```

`RecenterStepFor X` is the owner-exposed form of the revised existential producer.  The
generic compiler `midPeelEmission_of_recenterStepFor` may prove the second statement by
unpacking the source-bound GN conclusion plus the provenance-bound `MP1StepCore`; that is
still a universally quantified theorem, not evidence from one chosen `Λ`.  At `r=4`, the
first exporter reduces to the constructed `j=3` case only after proving
`DeepLive 4 j → j=3`.  A later supply assembly may project `mp1` and `vartheta` from these
exporters, but only after separately supplying `package` and `lb1`.

### 11.5 Honest re-grading and campaign count

All untouched arithmetic and record-packaging rows retain their 30–60 minute transcription
grade.  The following rows do not:

| node/group | [DWR] honest grade | reason / exit |
|---|---:|---|
| G0 principal polygon/slope residual | **research, 5–15 working days** | No landed analytic principal-polygon operator or slope-membership predicate. |
| G1 selected completed factor/descent | **research, 5–15 working days** | Completion factor carrier, prime-factor characterization, and descent dictionary are absent. |
| G2 statement amendment/provenance | **design + review, 2–5 days after G0/G1 shapes** | Trust-boundary re-signing; must compile anti-cook falsifiers. |
| D3-03 + D3-10 | **replaced by L2E, 8–15 working days** | They are consumers of one new generic coefficientwise multiplicative core, not local ports. |
| C3 canonical tau/vartheta | **research, 5–12 working days** | General-depth triangular spanning remains open; one generator-word identity is insufficient. |
| R3 valuation realization | **research, 3–8 working days** | Two new live stages and evaluation/value laws. |
| R4 thresholds/windows | **research, 3–7 working days** | Source-backed faithfulness thresholds, not numeral selection. |
| R5 letters/canonical dictionary | **research, 5–12 working days** | OPEN-LETTERS and same-receiver descent. |
| C4r GN occurrence | **REFUTED / A-I.8 review** | The current payload equates the finite-slope selected factor with the literal GN test-key divisor. |
| G10 universal exporters | **theorem family, 2–4 working days after occurrence producers** | Universal quantifiers and owner identity must be explicit. |

The conditional post-A-I.8 redesign has **83 planned nodes**: the original 69-node
accounting, with D3-03/D3-10
replaced by the twelve-node L2E program (net `+10`) and G7–G10 added (`+4`).  R8r, C4r,
C5r, and C6r replace their refuted/overstated predecessors and do not add to the count.
This is an accounting device, not a promise of 83 equal-sized units.  The MP1 branch is
currently stopped at G9; the independent tower and L2E work may proceed only if separately
authorized and useful without claiming the blocked occurrence.

### 11.6 Revised dependency spine

```text
MP1 analytic: G0 → G1 → G2 → G9 = RED ─╳→ C4r → C5r
formal control:             R8r → G7 + G8
shared algebra: T0 → T1 → T2 → L2E → D3 stack → D3-19 → D4
deep consumers: G3 → G4 → G6 → C0 → {C1 → C2, C3}
realization: R0..R7 + R8r → R9
universal supply (post-repair only): occurrence teeth → G10
  G10 + separately landed HE7A/LB1 → LadderSupplyLive₂
```

Fleet order changes accordingly: do not start the old D3-03/D3-10 ports independently;
start L2E after its statement shapes are reviewed.  **Do not construct C4r/C5r under the
current payload: G9 is already red.**  Do not advertise C6r as a ladder record before a
future authorized repair, G10, and HE7A/LB1.

### 11.7 Shared level-2 multiplicative engine (D3 + F1.4–F1.6)

This is one engine rooted at `LevelDatum`, not a D3-special theorem followed by a second F1
lift.  Its template is `C133mh1`/`C133mh3` Part 10's full-read, key-root vanishing,
coefficientwise convolution, then Theorem M clauses 2/3.  `C134dv2g` supplies the landed
level-2 support/no-interaction shell; it does not supply residue multiplication or the reverse
minimizer inequality.

| node | landed-vocabulary statement / exit | direct consumers |
|---|---|---|
| **L2E-00 shape lock** | Define reviewed `Dv2SlotCarryLawStatement` and `Dv2TwistProductLawStatement` over `L : LevelDatum`, level-2 key `Ψ`, outer `(u₂,ℓ₂)`, `IsMuKey L Ψ`, key-grade pin and outer floor.  Conclusions use `dv2Res L`, `dev Ψ`, `AdjoinRoot.root L.r`, and `L.cocycle`; no S2 numerals. | all |
| **L2E-01 full level-2 read** | Define the full coefficient read underlying `dv2Res` before the side-window truncation; prove additivity and vanishing below the inner pin from landed `dvResPoly`/`AdjoinRoot.mk`. | root |
| **L2E-02 level-2 key-root law** | Prove the residual symbol of `Ψ` dies at `AdjoinRoot.root L.r`, the one-level-up twin of `C133mh3.fullRead_key`; pin the exact key height used in the carry exponent. | root |
| **L2E-03 digit survival + nonzero read** | Strengthen `Dv2ResSurv`'s height-only slots 0/1 to residue nonvanishing for reduced products of `Ψ`-digits. | D3-03, min/max |
| **L2E-04 slot carry/twist root** | Prove `dv2Res L ((a*b)%ₘΨ)` equals the product of the two digit reads times the exact `AdjoinRoot.root L.r ^ L.cocycle ...` factor.  State all height and degree fences explicitly. | F1.4, convolution |
| **L2E-05 pair convolution pricing** | Port `pair_line_le/lt` and endpoint uniqueness to `dv2Pin` using `C134dv2g.dvSupp_le_dev_add` and L2E-03/04. | clauses 1/2 |
| **L2E-06 level-2 support product** | Prove generic `dv2Supp_mul` equality for nonzero factors, subsuming the conditional endpoint equality path in `C132nv2`. | D3 value product, F1 |
| **L2E-07 level-2 min/max equality** | Prove `dv2SideMin_mul` and `dv2SideMax_mul` equalities by the C133mh3 strict no-pair contradiction route; derive `dv2SideDeg_mul`.  This includes the reverse inequality F13A identifies as missing. | F1.6, D3 side laws |
| **L2E-08 pin-height addition** | At product side minima, prove finite `dv2Pin` heights add with the exact carry accounting needed by `dv2Res`. | residual law |
| **L2E-09 coefficientwise residual product** | Expand `dv2ResPoly` coefficientwise, use the `dev Ψ` convolution split and L2E-04, and prove the generic level-2 product law in `Polynomial (AdjoinRoot L.r)` with its landed cocycle/scalar normalization. | F1.4, D3-10 |
| **L2E-10 complement specialization** | Combine `C134dv2g.dv2Pin_mul_complement`, singleton side `{0}` for the complement, and L2E-07/09 to derive the exact `γg * root^cocycle` scalar translation. | F1.4/F1.6 |
| **L2E-11 adapters + acceptance** | Instantiate at the `(g8,85,2)` D3 datum to close D3-03/D3-10, then discharge the three signed acceptance tests below without restating them. | D3, F1 |

Acceptance tests are the exact signed conclusions, not nearby helper lemmas:

1. **F1.4 / C.39** `dv2ResPoly_scalar`: byte-for-byte scalar identity with
   `γg L f * root ^ L.cocycle (pinHeight ...) (complementConst ...)`.
2. **F1.6 / C.64** `mult₂_readable`: equality of both `dv2SideMin` and `dv2SideDeg` between
   `f` and `blockFactor L f` under the signed test-key/context/floor hypotheses.
3. **F1.5 / C.38** `dv2ResPoly_radical_eq`: equal degree and the iff of divisibility by every
   monic irreducible `q`, derived from F1.4's nonzero scalar plus F1.6's degree equality.
4. **D3-03** reduced coefficient products modulo `g8` preserve the μ3 endpoint read, not
   merely its height.
5. **D3-10** the μ4 coefficient convolution at `(u₂,ℓ₂)=(85,2)` is an instance of L2E-09,
   with parity/carry supplied by D3-09.

No F1 row may consume a D3-special axiom, and no D3 row may clone the L2E coefficientwise
proof.  The shared engine is complete only when all five acceptance tests elaborate.

### 11.8 Revised highest risk and exit rule

The single highest-risk node is now **G9, GN valuation/key-index alignment**, and it is
already **RED**: the current payload asks a finite-slope selected factor to be the literal
test-key divisor that GN places in the separate key-power term.  G0 remains a major absent
analytic engine, but building it cannot repair this identification.  C4's `leaf²` form is
refuted by order two; C4r is refuted by G9.  L2E is the largest independent algebraic
program, but it has the landed coefficientwise C133mh3 route as a template.

There is no MP1 campaign exit under the present statement.  The certificate, G7, and G8's
formal control are useful falsifiers, not an occurrence proof.  Resume C4r/C5r only after an
A-I.8-authorized surface decision separates the GN test key from the selected emitted factor
or replaces the GN leg by the direct key-irreducibility route.  After such a repair, the
remaining exits are provenance binding, all five L2E acceptance tests, and G10's universal
theorem families.  One occurrence without G10 would still not be a `LadderSupplyLive₂` result.

### 11.9 [G5F 2026-08-28] μ5 refinement admissibility — PASS, operator only

**Adjudication: PASS for G5's stated admissibility/layer question; the stop-if-false line is
not triggered.**  The triple `(e',f',u')=(1,1,171)` is a source-faithful numerical shape for
an equal-key-degree ordinary augmentation/refinement over the already constructed depth-four
valuation.  It is not, and must never be encoded as, a fifth proper `DeepTower` stage.

The primary-source clauses are decisive:

* Fernández--Guàrdia--Montes--Nart, *Residual ideals of MacLane valuations*, author PDF
  `docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`: Definition 1.6 (PDF p. 5)
  constructs `[μ;(φ,ν)]` from `φ ∈ KP(μ)` and `ν>0`; it imposes no key-degree-growth
  condition.  Section 3 (PDF p. 11) says exactly: *“A valuation μ ∈ V is called inductive
  if it is attained after a finite number of augmentation steps starting with μ₀.”*
  Section 3.1 (PDF p. 11) distinguishes a MacLane chain from an **optimal** MacLane chain:
  strict key-degree growth belongs to optimality, not to augmentation or inductivity.
  Lemma 3.4 (PDF p. 12) treats two consecutive augmentations whose keys have equal degree
  and proves that they collapse to the single augmentation
  `[μ;(φ',ν+ν')]`.  Finally, §3.2 equation (7) (PDF p. 14) gives
  `m_i=e_{i-1}f_{i-1}m_{i-1}`.  Thus `e'=f'=1` gives `m_new=m_old`; it is the
  equal-degree case the source permits and compresses, not a new optimal rung.  Theorem 5.7
  and its proof (PDF p. 23) likewise construct a key with degree `e_r (deg ψ) m_r`; with
  `e_r=1` and linear `ψ`, this degree is `m_r`.
* Alberich-Carramiñana--Guàrdia--Nart--Poteaux--Roé--Weimann, *Polynomial Factorization
  Over Henselian Fields*, `docs/references/s10208-024-09646-x.pdf`: §3.1 (PDF p. 14,
  journal p. 644) defines the ordinary augmentation `[μ;φ,γ]` under the clause
  `μ(φ)<γ` and states `deg(ν)=deg(φ)`.  Definition 3.2 (PDF p. 15, journal p. 645)
  requires `deg(μ_n)<deg(μ_{n+1})` for an ordinary step that is retained in an MLV chain.
  The worked refinement discussion (PDF p. 25, journal p. 655) says that the equal-degree
  chain is not an MLV chain, calls the non-growing case a refinement step, and replaces the
  old type/key rather than appending a depth.  Definition 5.5 (PDF p. 35, journal p. 665)
  states: *“A refinement step ... yields a unique new type ... with moreover
  `deg(ϕ)=deg(φ)`.”*  Its immediately following characterization is a one-sided principal
  Newton polygon with `e_rel(μ_λ)=1` and residual `(y-ζ)^ℓ`, `ζ≠0`; hence the new residual
  factor is linear, so the refinement invariants have `e'=1`, `f'=deg(y-ζ)=1`.

For this row, the old cleared key value is `170` and the proposed new absolute value is
`171`, so `170<171` is precisely the positive-increment clause `μ(φ)<γ`; also
`gcd(171,1)=1`.  The FGMN degree formula gives
`1·1·D₄=1·1·16=16`, so the key degree does not grow.  These checks establish that the
numeric row is admissible as the next/refined valuation's **operator parameters**.

The Lean carrier boundary agrees exactly.  `C130pk.lean:110-111` indexes
`FGMNCalculus W e' f' u'` by a pre-existing `W : DeepTower ... r`; the parameters do not
change `r`.  Conversely, `C83.lean:148-150` requires
`DeepTower.hproper : 2 ≤ e i * f i` at every stage `i≥2`.  A hypothetical fifth row with
`e 5=f 5=1` would require `2≤1`, and the cumulative degree would stay `16`, violating the
strict-growth invariant.  The machine proof is `leanfinal/scratch/G5F_probe.lean`; it proves
the general `unit_row_not_a_proper_stage`, its stage-five specialization, and the two degree
arithmetic teeth.  Therefore the `(1,1,171)` row **MUST remain operator-level data over the
depth-four tower**.  Forging a stage-five `DeepTower` is impossible, not merely undesirable.

Scope fence: the triple alone does **not** prove that a particular polynomial execution is
an OM refinement step.  Definition 5.5 additionally demands the unique-new-type,
one-sided-principal-polygon, and residual pure-power clauses.  G5 passes only the
source-admissibility and carrier-layer questions; G0/G1/G8/G9 (or §12's superseding direct
route) own occurrence/provenance.  Treating this G5 result as an occurrence witness would be
the exact overclaim, but it is not part of the adjudicated claim.

## 12. [A8D 2026-08-28] binding A-I.8 adjudication: direct key route

This section supersedes §11 wherever that section keeps the MP1 branch stopped at G9 or
retains GN-only nodes.  The adjudication record is `runs/wave-c/verdict_A8D.md`; the exact
statement shape compiles in `leanfinal/scratch/A8D_probe.lean`.  No landed Lean/leanspec
statement is changed by this blueprint amendment.

**[AI8E 2026-08-28] §12.3 IS ENACTED** (`runs/wave-c/verdict_AI8E.md`): the five direct
declarations are production at `leanfinal/Uniformity/ChapI/I10RecenterDirect.lean`
(namespace `Uniformity.Density.IFC5`; declaration bytes identical to the probe, one
docstring word `draft`→`live`), the superseding record `IFC5.LadderSupplyLive₃` (ONLY
`mp1` → `MP1CarrierLiveDirect`) is the capstone `ladder` field's result record in both
twins (leanspec A-I.8 STATE UPDATE; gate item (3) retargeted), `GNCitePayload` and the
whole A-I.7 GN surface stay byte-frozen in `I10RecenterLive.lean` as the tension record,
and the generic MP1 compiler `mp1CarrierLiveDirect_of_steps` DISCHARGES the `mp1` leg
outright — the spine row "A8D-S0 → generic MP1 compiler → MP1CarrierLive" is landed; the
remaining MP1 work is exactly C4d/C5d on the D3/D4 key tails.  Pre-enactment state
archived at commit `3d545e6e`.

### 12.1 Decision and exact consumer reduction

Choose fork **(β)**: remove `GNCitePayload` from the live recenter producer and use the
direct key-irreducibility route.  E.40's conclusion needs no selected completed factor:

| E.40 field group | supplier after A-I.8 |
|---|---|
| `quot`, `hkey`, `hpeel`, `hmass`, `hthr`, `iface` | `MP1StepCore` |
| `hirr` | direct keyhood of `B'.Φ` → ordinary irreducibility → monic Gauss transport |
| `hef` | `B'.hΦdeg.trans C.hef` |

Route (α) would retain principal-side, completion-factor, descent, and multiplicity
machinery whose outputs the consumer discards.  Route (β) instead consumes the deep key
predicate and irreducibility law already required by D3-15/16 and D4-13--15.  It is not
blocked, but it is not yet landed at absolute μ₄/μ₅.

`C134p1d.isMuKey_of_isTestKey` is generic over a `KeyFrame` plus one `LevelDatum`; its
actual terms are still `dvSupp F · L.u L.ℓ` and `dvResPoly F ... · L.u L.ℓ`.
Consequently it does not definitionally instantiate at the recursive `g8`-development μ₄
or `keyAt4`-development μ₅ operators.  Its architecture does generalize.  The required
operator twins are the same deep key-tail work already present in this campaign.

### 12.2 Generalization matrix

| direct-key leg | one `LevelDatum` | μ₄ `(2,1,85)` | μ₅ `(1,1,171)` |
|---|---|---|---|
| monic/positive recipe degree | **landed**: `IsTestKey` clause 1 + `natDegree_pos_of_isTestKey` | **twin needed**: D3-14--D3-16, degree 16 | **twin needed**: D4-12/D4-14, degree 16 |
| μ-minimality degree contradiction | **landed**: `not_residual_dvd_of_natDegree_lt` + `muMinimal_of_isTestKey`; C.26 exact degree/nonzero | **twin needed**: D3-08/12/15; the below-16 two-slot residual must be a nonzero constant/unit | **twin needed**: D4-08/09/13; a below-16 remainder has only slot 0 |
| μ-primality head | **landed**: `residual_dvd_or_of_muDvd_mul` from Theorem M clause 3 | **twin needed**: L2E-09 → D3-12 product law | **twin needed**: D4-07/09 recursive product law |
| residual lift | **landed**: `muDvd_of_residual_dvd`, quotient/remainder + line-read tie transfer | **twin needed, unblocked**: D3-15; use the concrete two-slot `C132kp1` pattern | **twin needed, unblocked**: D4-13; the one-slot remainder is simpler |
| assemble keyhood | **landed**: `isMuKey_of_isTestKey` | **twin needed**: D3-15/16 | **twin needed**: D4-13/14 |
| keyhood → `Irreducible O[x]` | generic proof shape validated in A8D probe; concrete lower twins landed in `C130fd0`/`C132kp5` | algebra-only twin in D3-16 | same twin in D4-15 |
| Gauss to E.40 `hirr` | **landed** | **landed after key proof** | **landed after leaf key proof** |

No cell is blocked.  Theorem M is frame-generic at the exact P1D interface; L2E-09 is its
μ₄ operator twin and D4-07/09 its μ₅ recursive instance.  C.26 and the remainder
mechanism likewise need operator-facing twins rather than new mathematics.

### 12.3 A-I.8 statement draft

Retire `GNCitePayload` from the live dependency surface and add:

```lean
structure DirectKeyPayload ... (A : ChainRealization ...) (phi : Polynomial O) where
  e' f' u' : ℕ
  source : FGMNSourceData core.T A.keys e' f' u'
  keyPolynomial : source.keyPolynomial phi
  key_irreducible : ∀ g, source.keyPolynomial g → g.Monic → Irreducible g
```

At every concrete supplier, `key_irreducible` must be filled by the direct deep-key proof;
the payload deliberately omits the other twelve `FGMNSourceLaws` fields and authorizes no
citation or axiom.  Amend the tail of
`RecenterStep` exactly as follows:

```diff
- (∃ (kRes : Type) (_fRes : Field kRes),
-   Nonempty (GNCitePayload (Kt := Kt) (L := L) A B.F B'.Φ kRes)) ∧
- Nonempty (MP1StepCore B B')
+ Nonempty (DirectKeyPayload A B'.Φ)
+ ∃ step : MP1StepCore B B',
+   step.quot.F = B'.F ∧
+   B'.T = B.T ∧
+   step.quot.T = B.T ∧
+   B.F = B'.Φ * B'.F
```

Keep the same `core/A/X/eK/eG` existential owner, all slot/block/gauge views, the nonzero
and degree conditions on `Lambda`, the recenter equality, and `B'.Φ ∣ B.F`.
`MP1CarrierLive` changes only to consume this amended step; its quantifier prefix and
`Nonempty (MidPeelEmission B B')` conclusion remain unchanged.  Add the direct compiler
which projects the core, applies the payload's `key_irreducible`, applies monic Gauss, and
fills `hef` definitionally.

### 12.4 Consumer/supplier obligations

| boundary | producer must supply | consumer obtains |
|---|---|---|
| same-realization provenance | one `core/A/X`, the three views, exact `Lambda`, successor and quotient bindings | no owner/view splicing |
| μ₄ prerequisite | L2E, D3-12, D3-14--D3-19; direct `key_irreducible` fills D3-18 source laws | carried degree-16 `keyAt4` and honest μ₄ calculus |
| μ₅ direct leaf | D4-09, D4-12--D4-15; direct `leaf` keyhood and irreducibility | `DirectKeyPayload A leaf` |
| quotient gate | `quot.F=B'.F=keyAt4+1`, quotient `hkeyfree`, threshold and peel bindings | full `MP1StepCore` and E.40 items 2--4 |
| occurrence | C4d/C5d for the exact `X`, `Lambda`, and `B'` | one nonvacuous `MidPeelEmission` |
| universal MP1 carrier | generic direct-step compiler, validated as `mp1CarrierLiveDirect_of_steps` | `LadderSupplyLive₂.mp1` without extrapolating from one occurrence |
| remaining full-supply fields | re-scoped G10 deep-level/vartheta exporter plus separate HE7A `package` and `lb1` | the non-MP1 fields of `LadderSupplyLive₂`; one occurrence alone remains insufficient |

### 12.5 Node additions, deletions, and revised spine

Delete GN-only G0, G1, G8, and G9 and all their edges.  Residual multiplicity of the
input `F0` is no longer an MP1 gate; direct keyhood concerns `B'.Φ` itself.  Replace in
place:

| old row | binding replacement |
|---|---|
| G2 payload/provenance amendment | **A8D-S0** direct payload, amended recenter step, generic key→irreducible bridge, compiler, and anti-cook review |
| G5 GN refinement admissibility | direct μ₅ refinement/operator admissibility only |
| C4r honest GN binding | **C4d direct key binding** from D4-12--D4-17 under the same `A.keys` |
| C5r provenance-bound recenter/MP1 | **C5d direct recenter/MP1 occurrence tooth**, retaining G7 and every DWR binding |

Strengthen D3-15/16 and D4-13--15 with the exact matrix obligations above; D3-18 and
D4-17 independently reuse the direct theorem for their full source-law records.  These are
not new count rows because their existing descriptions already promise residual-divisibility
equivalence, criterion, and irreducibility.  Re-scope G10 by deleting its
`MP1EmissionPerWitnessExporter` half: the generic direct compiler supersedes it.  Retain
G10's deep-level/vartheta universal half, G7, L2E, R8r, and the remaining full-supply fences.

Under §11's counting convention the campaign changes from 83 to **79 conditional nodes**:
four GN-only nodes are deleted; G2/G5/C4r/C5r are replaced in place.  The revised spine is

```text
L2E → D3-12 → D3-15/16 → D3-18/19
                         ↓
        D4-09 → D4-12 → D4-13/14/15 → D4-17
                                             ↓
A8D-S0 → generic MP1 compiler → MP1CarrierLive
G7 + R8r/R9 + D4-17 ─────────────────→ C4d → C5d  (nonvacuity)
deep-level/vartheta producers ───────────────→ G10      (other field)
```

The MP1 stop-line is no longer GN indexing.  The remaining exit is internal and exact:
land both deep key tails without an axiom, pass G7, construct the provenance-bound direct
step as a nonvacuity tooth, and finish the independent G10-vartheta/HE7A/LB1 obligations
before claiming a ladder supply record.  MP1's universal implication itself is discharged
by the generic compiler, not by extrapolation from C5d.
