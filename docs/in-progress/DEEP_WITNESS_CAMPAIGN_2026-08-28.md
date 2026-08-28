# DWC — the depth-four arising-witness campaign blueprint

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
