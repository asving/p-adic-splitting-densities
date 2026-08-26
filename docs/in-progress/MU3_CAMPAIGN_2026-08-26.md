# DEC3R — the μ₃ / Route-B campaign blueprint

Date: 2026-08-26  
Scope: construct
`FGMNSourceData (s2DepthTwo h2 hq) (s2DepthTwoKeyChain h2 hq) 2 1 21`
and its `FGMNSourceLaws`, package it through the landed Route-B endpoint, and repair only the
consumer premises that machine computation proves impossible.  This document proposes work;
it changes no corpus or signed statement.

Machine authority: `leanfinal/scratch/DEC3_probe.lean`, checked from `leanfinal/` by
`lake env lean scratch/DEC3_probe.lean` (exit 0, no `sorry`, no declaration of an axiom; all
printed footprints are Lean core).

## 1. Executive decision

The μ₃ model target is exactly `(r,e',f',u') = (2,2,1,21)`.  The witness stores
`(e₃,f₃,u₃) = (2,1,21)` and the floor `2·10 < 21`
(`leanfinal/Uniformity/ChapC/C97.lean:321-345`; machine pins
`stage_three_numerals`, `depth_two_floor`).  The old `u'=5` target fails the same floor
(`leanfinal/Uniformity/ChapC/C130s2.lean:165-167`; probe
`depth_two_floor_rejects_five`).  The carried chain is already the required depth-two chain:
`keyAt 2 = composedKey`, of degree `Dcum 2 = 4`
(`leanfinal/Uniformity/ChapC/C130s2.lean:171-206`).  The new recipe/key degree is
`2·1·4 = 8`, agreeing with the full witness's `Dcum 3 = 8` (probe
`stage_three_Dcum`).

Route B needs no carrier or packaging work.  `fgmnCalculusOf` projects the key chain and all
source-data/source-law fields into `FGMNCalculus`, and
`fgmn_model_calculus_nonempty` wraps that term in `Nonempty`
(`leanfinal/Uniformity/ChapC/C130pk.lean:207-258`).  The final model-discharge row is therefore
one application of that theorem.

Two consumer amendments are prerequisites to the advertised “GENTOW conclusions fire” end
state:

1. the source-correct `PrevGrade` remains evenness, so `PrevGrade 21` is false; at `f'=1`
   the ratio conclusion is instead provable without the multiplication induction;
2. independently, the current `chainNorm 2 21` is the carried `keyAt 2` itself, so the current
   strict supply `(chainNorm 2 21).natDegree < (keyAt 2).natDegree` is false.  The source B-1
   normalizer below the current key is `chainNorm 1 21 = 16·keyAt 1`, whose degree is `2 < 4`.

Both findings are machine-pinned in `DEC3_probe.lean`.  Thus the model campaign is finite and
well-scoped, but the current consumer signatures cannot fire merely by constructing the model.

## 2. OPEN-DICT-2 clearing decision

### 2.1 Decision

Use the paper's **full-current-group integer coordinate**:

```text
grade_i(α) = e(μ_i) · α,        α ∈ Γ_i = e(μ_i)⁻¹ Z.
```

At the μ₃ operator (`i=3`, repo depth `r=2`), define `nextValue` in this coordinate.  In
implementation terms its outer line has `(u,ℓ)=(21,2)` over the landed μ₂ value, i.e. the
level-up analogue of the landed `(5,2)` definition.  Do **not** replace this by the proposed
“preceding-group clearing” `e(μ₂)·α`.

### 2.2 Print-read evidence

The author PDF fixes
`Γ_i = e(μ_i)⁻¹ Z` and `e_i = e(μ_i)/e(μ_{i-1})`
(`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`, p. 14, §3.2, display before (6)).
Definition 3.12 then defines the grade-line integers by

```text
u_i(α)e_i + s_i(α)h_i = e(μ_i)α,   0 ≤ s_i(α) < e_i
```

(ibid., p. 16).  Therefore, for `β ∈ Γ_{i-1}`,

```text
e(μ_i)β = e_i · (e(μ_{i-1})β),
```

so preceding-group membership in the integer coordinate is exactly `e_i ∣ grade_i(β)`.
Conversely every multiple `e_i m` represents `m/e(μ_{i-1}) ∈ Γ_{i-1}`.  Published
Corollary 4.12(2) assumes precisely `β ∈ Γ_{i-1}`, and its proof uses `s_i(β)=0`
(ibid., p. 20).  This is also the print-read conclusion already recorded in
`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md:98-119,239-290`.

At S2, `e₃=2`, hence the μ₃ realization is

```lean
def S2Mu3PrevGrade (β : ℕ) : Prop := 2 ∣ β
```

and not an all-grades predicate.  The probe proves the evenness normal form and
`Nat.Coprime 21 2 ∧ ¬ S2Mu3PrevGrade 21`.  This agrees with the landed μ₂ realization
`S2PrevGrade := 2 ∣ β` (`leanfinal/Uniformity/ChapC/C130rp6.lean:192-212`) and with the
source carrier's required interpretation (`leanfinal/Uniformity/ChapC/C130fg.lean:144-152`).

### 2.3 Why `e(μ₂)·α` is rejected

Multiplication by `e(μ₂)` sends the preceding group `Γ₂` to all integers, but it does not
integerize all of `Γ₃`: since `e(μ₃)=2e(μ₂)`, a general μ₃ grade becomes half-integral in that
coordinate.  It also ceases to be Definition 3.12's right-hand side.  Using it only for the
consumer would make `PrevGrade 21` appear automatic by changing coordinates without changing
the `u'=21` recipe indices.  That is a dictionary mismatch, not a discharge.

This decision fixes the new `nextValue`: it must be the μ₃ valuation cleared by `e(μ₃)`, with
outer coefficients valued by the landed μ₂ operator and outer weights `2·μ₂(A_j)+21j`.
The existing generic support definition displays exactly that recursive shape one level lower
(`leanfinal/Uniformity/ChapC/C06.lean:93-100`); the level-up carrier is `dv2Supp`
(`leanfinal/Uniformity/ChapC/C11.lean:128-144`).

## 3. The `hprev` / `hcop` disposition

The conflict is genuine arithmetic, not an operator-construction gap:

```text
hcop  : Nat.Coprime 21 2             true
hprev : S2Mu3PrevGrade 21 = (2 ∣ 21) false.
```

Consequently no source-faithful full-current-clearing μ₃ calculus can supply the current
`hprev : I.PrevGrade u'` binder.  The probe theorem `mu3_coprime_and_not_previous` certifies
both halves in the same context.

The repair is the narrow fence suggested by the packaging adjudication: replace the consumer
supply by

```lean
hprev : 2 ≤ f' → I.PrevGrade u'
```

(equivalently, split the theorem into an `f'=1` base theorem with no `hprev` and a `2 ≤ f'`
theorem retaining it).  For `f'=1`, every `t<f'` is `t=0` and `f'-t=1`; the desired ratio is
only `a·(a·a⁻¹)=a`.  It uses `Rgr_ne_zero` for cancellation and never calls `Rgr_mul`.
`DEC3Probe.ratio_power_one` proves the literal ratio conclusion at arbitrary depth and arbitrary
`u'`, from the three normalizer supplies but without `PrevGrade`.

Consumer audit for this amendment:

| locus | current use | required change |
|---|---|---|
| `C99r.gentow2_Bpp` | power induction calls `Rgr_mul ... hprev` at every successor step (`leanfinal/Uniformity/ChapC/C99r.lean:118-165`) | split on `f'=1` versus `2 ≤ f'`; use the probe base proof in the first branch and the existing induction in the second |
| private `ratio_power_law` | same induction (`leanfinal/Uniformity/ChapC/C107ac14.lean:110-160`) | identical split/fenced binder |
| `gentow5w_two` | merely forwards `hprev` to C.99 (`leanfinal/Uniformity/ChapC/C107ac14.lean:168-183`) | cascade the fenced binder |
| `gentow5w_one_shape_of_letter_tie` | forwards `hprev` to `ratio_power_law` (`leanfinal/Uniformity/ChapC/C107ac14.lean:196-213`) | cascade the fenced binder; OPEN-LETTERS remains separate |
| `FGMNSourceLaws.Rgr_pow` | genuinely iterates graded multiplication (`leanfinal/Uniformity/ChapC/C130la.lean:217-247`) | **no change**; its `PrevGrade` premise is source-correct |

A repository-wide `hprev` search finds no further theorem-body consumer.  The corresponding
signed binders are the C.99 and C.89 declarations
(`leanspec/Leanspec/ChapC.lean:2488-2517,3785-3832`); both must receive the recorded amendment
before their leanfinal twins change.

## 4. Independent consumer blocker: the normalizer index

`FGMNCalculus.chainNorm I i k` uses `towerNorm i k` and the keys indexed by `Fin i`
(`leanfinal/Uniformity/ChapC/C130pk.lean:177-194`).  `towerNorm i k` is documented as the
level-`(i+1)` normalizer and its exponent vector contains `i` carried keys
(`leanfinal/Uniformity/ChapC/C83.lean:182-194`).  Therefore, at depth 2 and grade 21, it uses
the exponent solve against the off-range next-stage datum `u₃=21` and includes the last key.

The probes calculate:

```text
towerNorm 2 21 = (0,0,[0,1])
raw chainNorm 2 21 = keyAt 2
¬ degree(raw chainNorm 2 21) < degree(keyAt 2).
```

Thus the current `hnormdeg` family in C.99/C.89 is impossible already at `d=1`; this is
independent of `PrevGrade` and remains impossible after the fence.  By contrast the witness
already pins

```text
towerNorm 1 21 = (4,0,[1]),
raw chainNorm 1 21 = C(16)·keyAt 1,
degree(raw chainNorm 1 21) = 2 < 4 = degree(keyAt 2)
```

(`leanfinal/Uniformity/ChapC/C97.lean:352-379`; probes
`towerNorm_one_twenty_one`, `rawChainNorm_one_degree_lt`).

The required source-index print-read is now complete.  The landed definition explicitly says
`towerNorm 1` is `n-hat_2` verbatim (`leanfinal/Uniformity/ChapC/C83.lean:182-187`), while the
GENTOW B-double-prime proof takes `N := n-hat_2(u_3)` and `M := n-hat_2(u_3 d)`, both of degree
strictly below `m_3` (`lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:705-713,729-752`).  Hence
the B-1 supply at depth `r>0` must read the normalizer strictly below the current key: introduce
`chainNormBelow I r k` from `towerNorm (r-1) k` and keys `1,...,r-1` (with a separately specified
base case), then change `thetaRatio` and all three supply families together.  Repairing only the
degree premise would leave the ratio on the wrong normalizers.  **OPEN-NORM-INDEX is DECIDED:**
at repo depth 2 the source normalizer is index 1, not index 2.

## 5. Reuse boundary

Here `REUSE-WITH-NUMERALS` means that the node still lands new μ₃ declarations, but its proof
is an instantiation or a syntactic level-up of a named landed engine; it must not reopen that
engine's mathematics.  `GENUINELY-NEW` means a new structural lemma is required at the μ₂ /
`composedKey` interface.

NP-0's discovery is real but has a precise limit.  The outer endpoint theorem is generic once
one supplies survival (`leanfinal/Uniformity/ChapC/C130nv3.lean:153-185`), and the final product
assembly only consumes that endpoint theorem (`leanfinal/Uniformity/ChapC/C130nv3.lean:531-555`).
The old survival proof itself is specific to degree-`≤1` coefficients modulo `x²-2`
(`leanfinal/Uniformity/ChapC/C130nv3.lean:275-316`).  At μ₃, the corresponding coefficients
have degree `<4` modulo `composedKey`; survival must be proved from the landed μ₂ normalized
residual product, not copied from the parity proof.  Likewise the polynomial bookkeeping of
graded convolution is reusable, but the recursive coefficient read through the landed μ₂
operator is new.  These two interfaces are the campaign's mathematical cores.

The landed depth-1 chain that may be reused is:

```text
value: C130s6/C130nv/C130nv2/C130nv3/C130nv5
  → grades: C130rp0
  → graded operator: C130rp1/C130rp2/C130rp4/C130rp6
  → normalized operator: C130rp8/C130rp9/C130rp11
  → KP: C130kp0/C130kp1/C130kp3/C130kp5/C130kp7
  → records: C130fd0
  → packaging: C130pk/C130sg.
```

The concrete evidence for this dependency shape is the import spine
`C130fd0.lean:6-9`, `C130kp5.lean:6-8`, `C130kp7.lean:6-7`,
`C130kp0.lean:6`, `C130rp8.lean:6`, `C130rp6.lean:6-7`,
`C130rp4.lean:6`, `C130rp2.lean:6`, `C130rp1.lean:6-7`,
`C130rp0.lean:6`, and `C130nv5.lean:6-8`.

## 6. Node plan — 29 nodes, each 30–60 minutes

Every row has a separately checkable output.  The plan stays within U15's 20–30-node estimate.
The two amendment rows precede implementation because the final consumer target is otherwise
provably unsatisfiable.

| node | min | statement sketch / exit condition | named landed inputs | class |
|---|---:|---|---|---|
| M3-A0 `PrevGrade` fence | 45 | Recorded amendment: C.99/C.89 take `2 ≤ f' → PrevGrade u'`; leanfinal ratio engine splits `f'=1`/`2≤f'`; the base branch matches `DEC3Probe.ratio_power_one`. | `C99r.gentow2_Bpp` (`C99r.lean:118-170`), `C107ac14.ratio_power_law` (`C107ac14.lean:110-160`) | **GENUINELY-NEW** |
| M3-A1 normalizer re-index | 60 | Land the print-read-decided `chainNormBelow`; re-sign `thetaRatio`, C.99 and C.89 supplies consistently; teeth at depth 2 are `16Φ′`, degree `2<4`. | `DeepTower.towerNorm` (`C83.lean:182-194`), `FGMNCalculus.chainNorm/thetaRatio` (`C130pk.lean:177-194`), `C97.s2Witness_values` (`C97.lean:352-379`) | **GENUINELY-NEW** |
| M3-NV0 support shell | 60 | Generalize the basic `dvSupp` zero/finiteness/add/negation bank to `dv2Supp L Ψ`; no S2 numeral in the theorem statements. | `dvSupp_zero_eq_top` through `dvSupp_add_eq` (`C130s6.lean:169-293`), `dv2Supp` (`C11.lean:128-144`) | **GENUINELY-NEW** |
| M3-NV1 μ₃ value definition | 45 | Define `s2Hgt₃ g := toZ (dv2Supp L Φ₂ g 21 2)`; pin zero, ne-top, add inequality/equality, `Φ₂` value 21, and field shape. | M3-NV0, `toZ` (`C130s6.lean:113-167`), `s2DepthTwoKeyAt_two` (`C130s2.lean:181-182`) | **REUSE-WITH-NUMERALS** |
| M3-NV2 outer endpoints | 60 | Port the parameter-free endpoint/minimizer and convolution-pricing bank from `dvSupp` to `dv2Supp`, leaving one explicit μ₂-residual survival hypothesis. | generic endpoint theorem (`C130nv3.lean:153-210`), generic dev/product bank (`C130nv2.lean:475-784`) | **REUSE-WITH-NUMERALS** |
| M3-NV3 μ₂ survival core | 60 | For coefficients of degree `<4`, prove that reduction modulo `Φ₂` preserves the product endpoint value; derive it from nonzero μ₂ normalized residuals and `s2NormRes_mul`. | `s2NormRes_mul` (`C130rp9.lean:258-302`), coefficient-zero nonvanishing (`C130rp8.lean:241-276`), `composedKey_monic`/degree (`C130s2.lean:181-206`) | **GENUINELY-NEW** |
| M3-NV4 μ₃ product | 45 | Assemble `s2Hgt₃ (gh)=s2Hgt₃ g+s2Hgt₃ h`, including zero cases and endpoint minimizer corollaries. | M3-NV2/3, old assembly shape (`C130nv3.lean:531-572`) | **REUSE-WITH-NUMERALS** |
| M3-NV5 valuation package | 45 | Package `s2Hgt₃` as `AddValuation`; extend to `FractionRing (Polynomial O)` only if a later point consumer needs it; pin restriction. | `s2AddVal₂` and localization extension (`C130nv5.lean:124-235`) | **REUSE-WITH-NUMERALS** |
| M3-RP0 grades | 30 | Define `S2Mu3ExactGrade/AboveGrade` from `s2Hgt₃`; prove existence, uniqueness, product, zero, and addVal normal forms. | `S2ExactGrade` bank (`C130rp0.lean:115-248`), M3-NV4/5 | **REUSE-WITH-NUMERALS** |
| M3-RP1 recursive coefficients | 60 | Define the grade-line gate `2·μ₂(A_s)+21s=β` and the μ₃ coefficient via the landed μ₂ graded/normalized read and the FGMN ε-factor; pin proof independence. | Def. 3.12–3.13 print-read; old gate/operator shape (`C130rp1.lean:124-225`); landed `s2GradedRes/s2NormRes` | **GENUINELY-NEW** |
| M3-RP2 total graded operator | 45 | Assemble `s2Mu3GradedRes`; prove coefficient master law, range independence, finite support, zero-above. | M3-RP1; polynomial assembly pattern (`C130rp1.lean:279-345`) | **REUSE-WITH-NUMERALS** |
| M3-RP3 graded add/zero | 45 | Prove `graded_zero_of_above` and exact-grade additivity for arbitrary polynomials. | generic `twistRead` zero/add laws (`C130rp2.lean:246-290`), old add assembly (`C130rp2.lean:466-506`) | **REUSE-WITH-NUMERALS** |
| M3-RP4 endpoint/carry arithmetic | 45 | Prove on-line slots have parity `β%2`, endpoint sums, and the carry exponent `(β%2)(β'%2)`. | M3-NV4, old arithmetic (`C130rp1.lean:157-183`), U14 carry formula | **REUSE-WITH-NUMERALS** |
| M3-RP5 recursive convolution | 60 | Prove every μ₃ graded coefficient of a product is the convolution of μ₃ coefficients, using μ₂ residual multiplicativity in the coefficient calculation. | M3-RP1/4; `s2NormRes_mul` (`C130rp9.lean:258-302`); old coefficient target shape (`C130rp4.lean:626-709`) | **GENUINELY-NEW** |
| M3-RP6 graded products | 45 | Assemble the arbitrary-grade twisted identity and its `S2Mu3PrevGrade` plain specialization; package exact-grade conjunct. | M3-RP4/5; old polynomial ext assembly (`C130rp4.lean:711-753`), `S2PrevGrade` pattern (`C130rp6.lean:214-253`) | **REUSE-WITH-NUMERALS** |
| M3-RP7 scalar nonzero | 45 | At exact grade and degree `<deg Φ₂=4`, prove coefficient zero nonzero; provide the exact `graded_scalar_nonzero` field shape. | old slot/scalar bank (`C130rp8.lean:213-296`), `s2KeyChain_keyAt_two_natDegree` (`C130rp8.lean:263-265`) | **REUSE-WITH-NUMERALS** |
| M3-RP8 normalized operator | 60 | Define μ₃ grade-of and strip the initial `X`-power; prove nonzero constant, key-power values, and universal normalized multiplication. | old normalization (`C130rp8.lean:333-510`), old product/order proof (`C130rp9.lean:131-302`), M3-RP6 | **REUSE-WITH-NUMERALS** |
| M3-RP9 recipe | 60 | Prove the literal `f'=1,u'=21,keyAt 2=Φ₂` `normalized_recipe` for arbitrary `khat 0` of exact grade 21 and degree `<4`; non-vacuity tooth uses corrected `chainNormBelow 2 21=16Φ′`. | old symbolic recipe pattern (`C130rp11.lean:239-347`), M3-A1, M3-RP3/6/8 | **REUSE-WITH-NUMERALS** |
| M3-RP10 residual existence | 60 | Collapse the monic irreducible degree-one residual to `X+1`; build a monic degree-8 recipe lift and prove its μ₃ residual. | two-element-field collapse (`C130rp11.lean:356-379`), old lift pattern (`C130rp11.lean:399-448`), M3-RP9 | **REUSE-WITH-NUMERALS** |
| M3-KP0 predicates | 45 | Define μ₃ `initialEquiv`, μ-divisibility, minimality, irreducibility, and `S2Mu3KeyPoly`; prove equivalence-relation and grade transport basics. | μ₂ definitions/basic laws (`C130kp0.lean:158-399`), M3-NV/RP | **REUSE-WITH-NUMERALS** |
| M3-KP1 residual divisibility | 60 | Prove both directions between μ₃-divisibility and divisibility of the μ₃ normalized residual in the required monic scopes. | μ₂ theorem shapes (`C130kp1.lean:161-368`), M3-RP8 | **GENUINELY-NEW** |
| M3-KP2 primality/minimality | 60 | Derive μ₃-irreducibility from irreducible residual and μ₃-minimality from nonunit/irreducible residual. | μ₂ algebra (`C130kp1.lean:368-602`, `C130kp3.lean:182-247`), M3-KP1 | **REUSE-WITH-NUMERALS** |
| M3-KP3 key criterion | 45 | Assemble the literal degree-8 `key_criterion` field from monicity, residual irreducibility/degree/nonzero scalar. | μ₂ assembly (`C130kp3.lean:315-387`), M3-KP2, M3-RP10 | **REUSE-WITH-NUMERALS** |
| M3-KP4 carried key | 45 | Prove `Φ₂ ∈ KP(μ₃)` and `R₃(Φ₂)=1`; add a tooth separating this from the landed μ₂ read `R₂(Φ₂)=X+1`. | `keyAt 2=Φ₂` (`C130s2.lean:181-206`), landed contrasting value (`C130kp5.lean:340-365`), M3-KP0/RP8 | **REUSE-WITH-NUMERALS** |
| M3-KP5 key irreducibility | 45 | Prove every μ₃ key polynomial is irreducible over `O`; specialize to `Φ₂`; use the landed monic Gauss transport rather than a new cite. | μ₂ transport theorem (`C130fd0.lean:162-203`), M3-KP0/2 | **REUSE-WITH-NUMERALS** |
| M3-KP6 initial/residual iff | 60 | Prove the degree dictionary for μ₃ keys and assemble both directions of `initialEquiv ↔ normalizedResidual equality`. | μ₂ degree/iff architecture (`C130kp7.lean:504-645`), M3-KP1-5 | **REUSE-WITH-NUMERALS** |
| M3-FD0 source records | 60 | Construct `s2Mu3SourceData` with the seven pinned operators and `s2Mu3SourceLaws` with all thirteen projections named; no vacuous recipe field. | structures (`C130fg.lean:130-275`), depth-1 assembly pattern (`C130fd0.lean:522-603`), M3-RP/KP, `s2Letter_ne_zero` (`C130np6.lean:178-194`) | **REUSE-WITH-NUMERALS** |
| M3-FD1 B-1 supply | 45 | For `d>0,d≤1`, reduce to `d=1`; prove exact grade 21, degree `2<4`, and nonzero for `chainNormBelow 2 21=16Φ′`. | M3-A1/NV/RP0; probe lower-normalizer pins; `C97.s2Witness_values` (`C97.lean:352-379`) | **REUSE-WITH-NUMERALS** |
| M3-SG final wiring | 45 | Package the μ₃ calculus; expose a scoped/local instance; apply amended `gentow5w_two` with `2,1,21`, floor/coprime/fenced-prev and M3-FD1; also expose `gentow2_A_supply` as soon as its independent `c/hliftdeg/hadm` inputs are supplied. | `fgmn_model_calculus_nonempty` (`C130pk.lean:253-258`), consumer (`C107ac14.lean:168-183`), `gentow2_A_supply` (`C99r.lean:287-320`) | **REUSE-WITH-NUMERALS** |

Critical path: `A0/A1 → NV0 → NV1 → NV2 → NV3 → NV4 → RP0 → RP1 → RP2 → RP3 →
RP4 → RP5 → RP6 → RP8 → RP9 → RP10 → KP0 → KP1 → KP2 → KP3 → KP4/KP5 → KP6 →
FD0 → FD1 → SG`.  RP7 can run after RP2; KP4 and KP5 can run in parallel after their inputs.

## 7. Final wiring row

The Route-B endpoint is deliberately boring:

```lean
@[implicit_reducible] def s2Mu3Calculus :
    FGMNCalculus (s2DepthTwo h2 hq) 2 1 21 :=
  fgmnCalculusOf (s2DepthTwoKeyChain h2 hq)
    (s2Mu3SourceData h2 hq) (s2Mu3SourceLaws h2 hq)

theorem s2_mu3_calculus_discharge :
    Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  fgmn_model_calculus_nonempty (s2DepthTwoKeyChain h2 hq)
    (s2Mu3SourceData h2 hq) (s2Mu3SourceLaws h2 hq)
```

This is the exact target architecture already landed in C130pk; no `ChainRealization`, socket,
point, evaluation, or new packaging layer occurs.  Compare the depth-1 star discharge
(`leanfinal/Uniformity/ChapC/C130sg.lean:493-503`).  A local `letI := s2Mu3Calculus ...` then
feeds the amended `gentow5w_two`.  `gentow2_A_supply` also consumes this instance, but its
`c`, `hliftdeg`, and `hadm` antecedents remain explicit and are not manufactured by packaging
(`leanfinal/Uniformity/ChapC/C99r.lean:287-320`).

The probe theorem `route_b_packaging_signature` elaborates this exact `(2,1,21)` application,
and `rawChainNorm_eq_chainNorm` checks that the class-free normalizer computations above match
the landed `FGMNCalculus.chainNorm` definition whenever packaging supplies the same key chain.

## 8. OPEN ledger

The two questions that had to be decided before fixing `nextValue` are **not open**:
OPEN-DICT-2 uses full-current clearing (§2), and OPEN-NORM-INDEX uses `towerNorm 1` at repo
depth 2 (§4).  The remaining named obligations are:

| name | status / effect on this campaign | exact source passage or landed boundary needed |
|---|---|---|
| `OPEN-RP1-TRANSPORT` | **blocking M3-RP1's source-faithfulness, owned by M3-RP1.**  Do not assert that the landed μ₂ normalized read already contains precisely the paper's epsilon factor.  Prove the coefficient formula before fixing the μ₃ graded operator. | FGMN Definition 3.10 (epsilon), Definitions 3.12–3.13 (the `epsilon_(i-1)(alpha_j) R_(i-1,alpha_j)(a_s)(z_(i-1))` coefficient), and Theorem 4.1; author PDF pp. 15–18.  The local print transcription states the same two-read issue at `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:489-523`. |
| `OPEN-DICT-3-MU3` | **faithfulness open, not a packaging open.**  Route B can define and prove the concrete operators directly in `W.fld 2`; identifying them as transports of the published `F_3` operators still needs an explicit field equivalence and scalar-coordinate theorem. | FGMN Proposition 1.15 and the §3.2 identification of `F_i` with the key-root residue field (author PDF pp. 7, 15), plus Definitions 3.13/3.15 and Corollary 4.9.  The missing general transport is recorded at `docs/in-progress/FGMNCALCULUS_FIELDLIST_2026-08-24.md:511-513`. |
| `OPEN-DICT-4` / `OPEN-LETTERS` | **not on the depth-2 `gentow5w_two` path.**  M3-FD0 only needs nonvanishing of the chosen concrete letter; the landed S2 choice is constant `1` with its nonzero theorem (`leanfinal/Uniformity/ChapC/C130np6.lean:178-194`).  The stronger normalizer/letter identification remains open for the separate depth-1 shape consumer. | FGMN §3.3 after Lemma 3.11 (`gamma_i`, `y_i`, `z_i`) and the evaluation transport of Proposition 1.15/Theorem 4.3; the live conditional binder is documented at `leanfinal/Uniformity/ChapC/C107ac14.lean:185-213`. |
| `OPEN-A-SUPPLY` | **outside model construction.**  The μ₃ instance enables C.103 but does not choose its digit string or prove `hliftdeg`/`hadm`; those remain explicit inputs (`leanfinal/Uniformity/ChapC/C99r.lean:287-320`). | No further FGMN print-read is prescribed here; the caller must provide the three signed antecedent families. |
| `OPEN-C90-FAMILY` | **outside this endpoint.**  C.90's one-fixed-triple truncation family cannot represent both S2 levels and needs its own per-level re-sign; it is not used by `gentow5w_two`. | The mismatch and required per-level family are recorded at `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md:187-192`; any future proof must reread the level-indexing in FGMN Theorem 6.3 and Corollary 6.4. |

`OPEN-RP1-TRANSPORT` is the only open above that stops a node in the 29-node Route-B chain.
It is not permission to choose a convenient coefficient: the node exits only with the displayed
Definition-3.13 coefficient proved equal to its Lean implementation.  `OPEN-DICT-3-MU3` is the
remaining paper-to-repo faithfulness theorem; it does not justify a new carrier or packaging
layer.

## 9. Campaign exit gates

The campaign is complete only when all of the following are green:

1. M3-A0 and M3-A1 are recorded in leanspec and their leanfinal twins; the old impossible
   `PrevGrade 21` and `chainNorm 2 21` degree supplies no longer occur on the C.89 path.
2. The 27 construction nodes after A0/A1 elaborate with no `sorry`, and M3-FD0 names all seven
   `FGMNSourceData` projections and all thirteen `FGMNSourceLaws` obligations (the landed record
   arities are at `leanfinal/Uniformity/ChapC/C130fg.lean:130-162,194-275`).
3. The final theorem has the literal type
   `Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21)` and is proved solely through
   `fgmn_model_calculus_nonempty` (`leanfinal/Uniformity/ChapC/C130pk.lean:253-258`).
4. A local instance fires the amended `gentow5w_two` at `2,1,21`, using machine-checked
   `20<21`, coprimality, the fenced base branch, and the lower-normalizer supply; the consumer's
   current input/output shape is at `leanfinal/Uniformity/ChapC/C107ac14.lean:164-183`.
