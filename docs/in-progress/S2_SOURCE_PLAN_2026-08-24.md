# U13 — the S2 source-frontier funnel

Date: 2026-08-24  
Status: **DECIDED — `S2SourceFrontier` is uninhabitable as currently typed**

## 1. Decision

Do **not** start a field-filling campaign against the present `S2SourceFrontier`.
There is no inhabitant, concrete or general.  Its `node` field already implies `False` before
any `FGMNSourceData`, `FGMNSourceLaws`, `grade_compat`, or `letter_compat` field is considered.

The contradiction is a coefficient-field mismatch in `NodePointSource`:

```text
Kt = (s2DepthTwo h2 hq).fld 2,       |Kt| = 2
[Algebra Kt L]                       hence 2 = 0 in L
coeffHom : O →+* L                   hence coeffHom 2 = 0
pointHgt_eval at C 2                 hence pointHgt i x (C 2) = ⊤
slot_value + hgt_ne_top at i = 2     hence pointHgt i x (C 2) ≠ ⊤.
```

Here `(2 : O) ≠ 0` follows from `h2 : Irreducible (2 : O)`, and
`natDegree (C 2) = 0 < Dcum 2 = 4`.  Thus the clash is on a required live slot, not on junk
indices or a degenerate polynomial.  It does not use `hgt_two`; nevertheless the landed fixed
table independently proves `s2Hgt₂ (C 2) ≠ ⊤`.

The checked certificate is

```lean
theorem no_s2_node_source ... :
  IsEmpty (NodePointSource (L := L) (s2DepthTwo h2 hq)
    (s2RepositoryRealization h2 hq).receiver
    (s2RepositoryRealization h2 hq).keys)

theorem no_s2_source_frontier ... :
  IsEmpty (S2SourceFrontier h2 hq L)
```

in `leanfinal/scratch/U13_probe.lean`.  It checks with no `sorry`, no axiom declaration, and
the usual Lean-core footprint `[propext, Classical.choice, Quot.sound]`.

Consequently the end-to-end criterion answers the question **NO for the present signature**.
Finite S2 development computations cannot repair a contradictory ambient type.  The next
campaign must first split the valued evaluation ambient from the terminal residue-field ambient;
only then is a concrete depth-two source construction a meaningful goal.

## 2. The false dictionary and the required correction

`NodePointSource` uses the same field `L` for two unrelated roles.

1. `coeffHom`, `coord`, `valueOn`, and `pointHgt_eval` make `L` the target of a valued
   evaluation of polynomials over the DVR `O`.  A faithful evaluation must not kill a nonzero
   DVR constant.
2. `ambientLetter`, `psi_root`, `canonicalRead`, and `letter_compat` make `L` an algebra over
   the terminal residue field `Kt`.  At S2, `Kt` has two elements, so every such `L` has
   characteristic two.

These roles cannot be combined in residue characteristic two.  This is adjacent to, but
stronger than, U12's false-dictionary fence.  U12 says CC's node ambient is not the completed
root ambient `K̄_v` used by FGMN Corollary 6.3.  U13 shows that the present node interface cannot
even support its own advertised `O`-polynomial evaluation laws.

The conservative repair is to add a separate valued evaluation field `E`:

```lean
E : Type uE
[Field E]
coeffHom : O →+* E
coord : Point → E
valueOn : ℕ → E → WithTop ℤ
pointHgt_eval : pointHgt i x A = valueOn i (eval₂ coeffHom (coord x) A)

L : Type uL
[Field L] [Algebra Kt L]
ambientLetter : ℕ → Lˣ
canonicalRead : ker (...) →* Lˣ
```

No map `E → L`, no identification of node points with FGMN roots, and no
`canonicalRead = algebraMap ∘ arenaRead` should be added.  The existing `letter_compat` remains
an equation in `L`; `grade_compat` remains an equation of value reads and needs no field map
between `E` and `L`.

Removing `pointHgt_eval` would also avoid the contradiction, but it would restore the free-table
problem that CC-1 deliberately prevented.  Truncating the coefficient map or declaring `C 2`
out of scope is likewise inadmissible: `slot_value` quantifies over every nonzero polynomial of
degree below `Dcum i`.

## 3. What mathlib and the landed corpus actually supply

The search covered `leanfinal/.lake/packages/mathlib/Mathlib`, especially
`RingTheory/Valuation`, `RingTheory/Polynomial/GaussNorm`, `FieldTheory/RatFunc`,
`AdjoinRoot`, and every occurrence of valuation/polynomial/Newton/MacLane/residual terminology.

### 3.1 Mathlib

| requested ingredient | found | consequence |
|---|---|---|
| Multiplicative Gauss norm | `Polynomial.gaussNorm_mul`, for a nonarchimedean real-valued absolute value and positive radius | Useful model for the base Gauss step, but it is not the cleared `WithTop ℤ` S2 augmentation and has no key-development API. |
| Valuation on a localization | `Valuation.extendToLocalization` | Can pass a valuation from a domain to a fraction/localization once the input valuation exists.  It does not construct an augmented valuation on `K[x]`. |
| Extension relation | `Valuation.HasExtension` | A class saying two already-given valuations are equivalent after pullback.  `Extension.lean` does not prove existence on an arbitrary algebraic closure or `AdjoinRoot`. |
| Rational-function valuations | the `X`-adic and infinity valuations in `FieldTheory/RatFunc` | Special valuations, chiefly trivial on constants; not Gauss extensions of the DVR valuation with S2 weights. |
| `AdjoinRoot` | the ordinary quotient-ring and localization APIs | No constructor found which extends a DVR valuation to `AdjoinRoot`, and no MacLane augmentation theorem. |
| Newton polygons / MacLane chains / FGMN residual operators | no relevant API found | The word “Newton” occurrences are unrelated identities/dynamics.  There is no reusable inductive-valuation or residual-polynomial formalization. |

The first three positive findings are pinned by `#check` commands in `U13_probe.lean`.  They
reduce infrastructure work; they do not discharge a frontier field.

### 3.2 Landed development and residue machinery

The repository is substantially closer than mathlib:

* B.02--B.06 provide the canonical monic-key development `dev`, reconstruction, uniqueness,
  addition, and key-power computations.
* B.07--B.09 provide the coefficient Gauss value and its universal product law.
* B39a provides a universal, purity-free order-one product law for `suppVal` and `resPoly`,
  proved by an induction/convolution argument.
* C.06/C.11 and C130s6 provide the concrete S2 depth-two value
  `s2Hgt₂ = toZ (dvSupp (s2Frame ...) · 5 2)`, its zero/finiteness/ultrametric laws, and the
  forced two-element digit table.
* C.22/C.25 provide `twistRead` and the parameterized `dvResPoly`; C.127/C131k provide
  structural development normal forms.
* C.66/C.66b cite exact residual multiplication only on fenced pure, monic, positive-degree
  inputs.  Their types are too narrow to prove `FGMNSourceLaws.normalized_mul`, which quantifies
  over all `g h : Polynomial O`.

What is absent is exactly the total depth-two layer needed here: a total normalized residual
operator independent of side/nonemptiness/height proof arguments; the polynomial-valued
graded operator at every cleared grade; and their universal additive and multiplicative laws.
The finite computations for `g₀`, `f₅`, recipe keys, and `dev` teeth verify examples, not these
universal statements.

## 4. Why depth two does not turn the universal laws into finite computation

FGMN §§1--4 define a valuation on all of `K[x]`, then recursively define residual operators
from every coefficient in the last-key development.  “Depth two” fixes the recursion depth; it
does not bound polynomial degree or the number of development coefficients.

For the repository/FGMN dictionary the relevant terminal step is

```text
repo keyAt 1 ↔ φ₂,       repo keyAt 2 ↔ φ₃,
μ₂ --(φ₃, ν₃ with e'=2, f'=1, u'=5)--> μ₃.
```

The earlier `μ₀ → μ₁` step is not stored in these two repo slots.  `FGMNSourceData` describes
`μ₃`, `R_(3,β)`, and `R₃`.  Definition 1.6 gives `μ₃(g)` as
a minimum over the complete `keyAt 2` development of an arbitrary `g`.  Definition 3.13 gives
every coefficient of `R_(3,β)(g)` recursively from the preceding residual operator.  Definition
3.15 removes the initial power of `y` to define `R₃`.  Lemma 3.14 and Corollary 4.12 then prove
the laws by induction through these definitions.

Thus computation can close numeral/index facts, the `f' = 1` recipe specialization, and explicit
test polynomials.  It cannot close `normalized_mul : ∀ g h, ...`, `graded_mul : ∀ β β' g h,
...`, or the key/equivalence criteria.  The missing core is a structural induction on arbitrary
key developments and convolution of their coefficients, followed by proof-independence and
normalization arguments.  B39a is the order-one precedent and an honest size guide: the
depth-two analogue is a multi-node development, not a 30-minute table fill.

## 5. `S2SourceFrontier` field-by-field verdict

| frontier field | present verdict | honest route after the ambient split |
|---|---|---|
| `node` | **REFUTED / impossible.** `no_s2_node_source` proves its type empty. | Construct the two concrete polynomial valuations on a valued field `E`, keep letters/reads in the residue ambient `L`, and fill the level-one plus level-two source family. |
| `hgt_two` | Unreachable because `node` is empty.  The right-hand table is landed and lawful. | Definitionally choose level-two height to be `s2Hgt₂`; no new mathematics after the corrected node constructor. |
| `dig_two` | Unreachable because `node` is empty.  The right-hand table is landed and forced by `|K₂|=2`. | Definitionally choose `s2Dig₂`. |
| `full_two` | Unreachable because `node` is empty.  `S2Full₂` and `s2Lift₂` are landed. | Definitionally choose `S2Full₂`. |
| `fgmn` | Not reached; no total `μ₃`, `R_(3,β)`, or `R₃` is landed. | Reuse the corrected terminal point valuation for `nextValue`; totalize the recursive dev/twist residual operators. |
| `fgmnLaws` | Not reached; several fields are universal polynomial theorems. | Prove the recursive depth-two law bank.  Explicit computations are regression tests, not proofs. |
| `grade_compat` | Not reached. | Make `fgmn.nextValue` and terminal `pointHgt` the same definition; expected `rfl` after normalization conventions are fixed. |
| `letter_compat` | Not reached. | Choose one transported terminal letter and use it for both records; expected `rfl`/`simp` after OPEN-DICT-4 is constructed. |

### 5.1 `NodePointSource`

| field | present status | corrected-construction assessment |
|---|---|---|
| `Point` | Part of the contradiction only through `point_exists`. | `Unit` or a small stage-tagged type suffices if a point represents a chosen valuation/evaluation pair; no finite-coordinate enumeration is needed. |
| `Pt` | Same. | Stage legality can be the proposition that the chosen valuation has the required key value.  Do not use unproved `True`; package the value equations in the point. |
| `point_exists` | Supplies the live level-two point used in the contradiction. | Requires concrete valuations at both levels.  This is a theorem, not a computation over `K₂`. |
| `coeffHom` | **Contradictory codomain.** Every such map kills `2`. | Retype to `O →+* E`, with `E` of the DVR/fraction-field characteristic. |
| `coord` | **Contradictory codomain.** | Put it in `E`; the rational-function variable is the simplest injective evaluation coordinate. |
| `valueOn` | **Contradictory codomain.** | Two additive valuations on `E`, obtained by first proving the polynomial value laws and then using localization. |
| `value_zero` | Forces the top side of the `C 2` contradiction. | Immediate from an `AddValuation`. |
| `value_mul` | Presently impossible with the slot tie. | **Inductive core N-VALUE:** universal product theorem for the concrete weighted-development value, then localization.  Estimate 3--5 nodes. |
| `value_add_ge`, `value_add_eq` | Presently impossible with the slot tie. | Inequality/off-tie equality are largely landed for `dvSupp`; transport through localization is additional work.  Estimate 1--2 nodes. |
| `hgt` | No total two-level family; only level two is landed. | Level two is `s2Hgt₂`; define and prove the analogous level-one table.  Estimate 1 node. |
| `dig` | Same. | Level two is `s2Dig₂`; construct the actual level-one residue digit, not an arbitrary nonzero indicator unless the same `q=2` forcing proof applies.  Estimate 1--2 nodes. |
| `pointHgt` | Inconsistent through `pointHgt_eval`. | Define by valued evaluation in `E`. |
| `pointDig` | Not contradictory by itself. | Define from the matching initial/residual form; a copy of `dig` is acceptable only after the point-value dictionary is proved. |
| `pointHgt_eval` | **The equation exposing the false dictionary.** | Retain unchanged in meaning with codomain `E`; do not weaken it. |
| `slot_value` | Gives the finite side of the contradiction with `hgt_ne_top`. | Dictionary theorem that the two valued evaluations agree with the landed tables below `Dcum i`.  Estimate 2--3 nodes after N-VALUE. |
| `slot_digit` | Open. | Matching residual/digit dictionary below `Dcum i`.  Estimate 2 nodes after the residual core. |
| `hgt_zero`, `hgt_ne_top`, `hgt_add_ge`, `hgt_add_eq` | Level two landed; level one missing. | One level-one law-bank node; the terminal instances then dispatch by `fin_cases i`. |
| `dig_zero`, `dig_ne_zero`, `dig_add` | Level two landed; level one missing. | One or two level-one digit-law nodes. |
| `Full`, `lift` | Level two landed; level one missing. | Define level-one fullness by realizability, as at level two, then the lift is mostly packaging.  Estimate 1--2 nodes. |
| `thresholdZ`, `thresholdNat`, `threshold_nonneg` | No named inherited S2 threshold is landed. | **Independent source input.** First locate/derive the actual S2 inherited threshold; choosing `0` because it satisfies a later inequality would be circular.  Estimate unknown until the source occurrence is identified, then 1 node. |
| `window` | Missing at both live stages. | With exact key values, reduces to inequalities against the inherited thresholds plus terminal key finiteness.  Estimate 1--2 nodes after threshold and valuation construction. |
| `ambientLetter`, `psi_root` | Residue-side data, not involved in the contradiction. | Degree-one `ψ` and the terminal receiver make this plausibly concrete.  Estimate 1 node, with an explicit root computation. |
| `key_value` | Missing at gauge-live level `i=1`. | A defining computation of the first corrected valuation on `keyAt 1`; part of N-VALUE, not a separate assumption. |
| `canonicalRead` | Merely typed; no landed constructor. | Construct from the Laurent normalizer and residue letters.  Estimate 1--2 nodes; keep it `L`-valued. |
| `arenaRead`, `towerRead`, `peelUnit` | Merely typed; no landed constructor. | Separate `Kt`-valued construction, 1--2 nodes.  No agreement with `canonicalRead`. |

The contradiction uses only `point_exists`, `coeffHom`, `value_zero`, `pointHgt_eval`,
`slot_value`, and `hgt_ne_top`.  Therefore filling or weakening any other node field cannot make
the current structure inhabited.

### 5.2 `FGMNSourceData`

| field | concrete depth-two definition | missing proof core |
|---|---|---|
| `nextValue` | The corrected terminal point value, equivalently the cleared S2 weighted-development value `toZ (dvSupp ... · 5 2)`. | Universal multiplication and localization must be proved before this is known to be an actual valuation rather than a lawful additive table. |
| `gradedResidual` | The Definition 3.13 recursion, using `dev (keyAt 2)`, the preceding residual operator, `twistRead`, and the S2 cleared grade arithmetic. | Totality, finite support, grade-line indexing, independence of chosen witnesses, and codomain transport to `W.fld 2`.  Estimate 3--5 nodes. |
| `normalizedResidual` | Strip the initial `y`-power from the graded residual at `nextValue g`, as in Definition 3.15; set the zero case to zero. | Endpoint existence, exact divisibility by the initial power, proof-independence, and zero case.  Estimate 2--3 nodes. |
| `keyPolynomial` | Honest `KP(μ₃)`: monic, `μ₃`-minimal, and initial-form prime. | Needs an explicit initial-form/divisibility relation or an equivalent proved residual criterion.  Defining it as ordinary irreducibility would falsify the source dictionary.  Estimate 2--4 interface nodes before the laws below. |
| `initialEquiv` | FGMN Definition 1.2's explicit value criterion, as already prototyped by U12's `MuEquiv`. | Small definition plus zero-case lemmas; 1 node. |
| `letter` | Transport the explicit S2 residue letters through the terminal receiver. | OPEN-DICT-4 and nonzero/root computations; 1 node. |

### 5.3 `FGMNSourceLaws`

| law field | finite S2 collapse? | honest cost |
|---|---|---|
| `graded_zero_of_above` | No: `g` and `β` are arbitrary. | Induction through Definition 3.13, exactly FGMN Lemma 3.14.  2--3 nodes. |
| `graded_add` | No: three exact-grade hypotheses still quantify over arbitrary polynomials. | `dev` additivity plus recursive residual additivity and grade-line bookkeeping.  2--3 nodes. |
| `graded_mul` | **No; load-bearing universal core.** | Convolution of arbitrary key developments, addition of minimizing endpoints, preceding-grade membership/clearing, and recursive residual multiplication.  This is the depth-two analogue of B39a, not a computation.  4--6 nodes. |
| `graded_scalar_nonzero` | Degree `< 4` bounds the development length, but coefficients range over the infinite DVR and `β` is arbitrary. | Exact-grade coefficient nonvanishing and residue-map kernel theorem.  1--2 nodes after `gradedResidual`. |
| `normalized_mul` | **No; load-bearing universal core.** Existing C.66/C.66b cites are too narrowly fenced. | Additivity of left endpoints/initial `y`-orders plus `graded_mul`; all zero cases.  3--4 nodes after the graded product core. |
| `normalized_recipe` | `f'=1`, `e'=2`, `u'=5` shortens the displayed sum to one coefficient, but `khat 0` is arbitrary under an exact-grade and degree fence. | Symbolic two-term development and twist normalization, not enumeration.  2 nodes. |
| `normalized_exists` | The two-element terminal field and `f'=1` reduce the residual input essentially to the monic linear polynomial with nonzero constant term. | Prove that collapse, construct the explicit degree-eight recipe polynomial, and prove its residual.  1--2 nodes after `normalized_recipe`. |
| `key_criterion` | No: it quantifies over every monic degree-eight `g` satisfying residual hypotheses. | Initial-form primality/minimality from irreducible residual, the substance of FGMN Lemma 5.2/Theorem 5.7.  3--5 nodes or a faithfully typed literature theorem after the source dictionary exists. |
| `key_irreducible` | No: `g` is arbitrary in `KP(μ₃)`. | FGMN Lemma 1.8 plus integrality and the landed monic Gauss transport.  2--3 nodes or a faithful cite transport. |
| `carried_key_is_key` | Concrete single polynomial. | Direct augmentation-key proof; still needs the honest KP/initial-form interface.  1--2 nodes. |
| `carried_key_residual` | Concrete single polynomial. | Equation (11) from the total normalized operator; 1 node. |
| `initial_iff_residual` | **No; load-bearing universal core.** It quantifies over arbitrary key polynomials. | Prove FGMN Proposition 5.6 for the concrete depth-two operators, including normalization and equal-value cases.  3--4 nodes or a faithful cite transport. |
| `letter_ne_zero` | Yes: only `i=1,2` are live and the terminal field is explicit. | `fin_cases` plus field/root computations; 1 node. |

The lower estimate after the signature repair is roughly **30--45 focused nodes** for an
all-Lean concrete source, dominated by three structural cores: N-VALUE, graded/normalized
residual multiplication, and the key-polynomial criterion/equivalence theory.  At 30--60 minutes
per node this is 20--35 engineer-hours after the interface repair, with substantial risk in the
product and initial-form cores.  A reviewed literature layer could replace some theorem proofs,
but not the definitions, dictionaries, or the present contradiction.

## 6. Node plan after U13

Every row is a 30--60 minute unit.  Rows marked **CORE** are serial groups whose combined size is
the honest cost of one universal theorem; they must not be collapsed into a nominal one-hour node.

| node | min | dependencies / named landed inputs | deliverable and exit condition |
|---|---:|---|---|
| SF-0 impossibility landing | 30 | `C130s17`, `C130s6.s2Fld₂_card` | Land the `no_s2_node_source`/`no_s2_source_frontier` theorem in an allowed diagnostic module; core axiom footprint only. |
| SF-1 ambient amendment | 45 | SF-0, U11 §4.2, U12 false-dictionary fence | Draft recorded amendment adding valued ambient `E` to `NodePointSource`; `L` remains the residue ambient.  No consumer conclusion or `E → L` map is added. |
| SF-2 signature elaboration | 60 | SF-1, `C130k`, `C130fg` | Scratch authority for corrected `NodePointSource`, `ChainRealization`, `S2SourceFrontier`; all projections elaborate. |
| SF-3 consumer ripple | 60 | SF-2, `C130st`, `C130pt`, `C130th`, `C130in`, `C130s17`, `C130s18` | Exact diff/consumer matrix; existing theorems restate with `E`, and letter/read statements stay in `L`. |
| SF-4 noncontradiction tooth | 30 | SF-2 | Exhibit a characteristic-zero `E` and injective coefficient evaluation at the rational-function variable; prove `eval₂ coeffHom X (C 2) ≠ 0`. |
| NV-0 polynomial-value shell | 45 | SF-2, `C130s6.toZ`, U12 `PolynomialValuation` prototype | Define the level-one and level-two cleared polynomial value functions and zero/addition laws. |
| NV-1 level-one product | 60 | NV-0, `B09.gaussVal_mul`, B39a `suppVal_mul_gen` | Universal product law for the first augmentation, including zero cases. |
| NV-2 outer endpoints (**CORE 1/4**) | 60 | NV-1, `B02--B06.dev`, `C130s6.dvSupp_*` | For nonzero `g,h`, choose minimizing outer-development slots and prove their sum is a product minimizer. |
| NV-3 outer convolution (**CORE 2/4**) | 60 | NV-2, B39a convolution pattern, `C131k` structural normal forms | Unique lowest convolution term survives; cancellation cases handled. |
| NV-4 level-two product (**CORE 3/4**) | 60 | NV-3 | `dvSupp (g*h) 5 2 = dvSupp g 5 2 + dvSupp h 5 2`, with no monic/pure/degree fences. |
| NV-5 additive valuation packaging (**CORE 4/4**) | 45 | NV-4, mathlib `AddValuation` | Package both polynomial values as additive valuations; `#print axioms` core only. |
| NV-6 fraction-field extension | 45 | NV-5, `AddValuation.toValuation`, `Valuation.extendToLocalization` | Convert, extend both valuations to a common `E = FractionRing (Polynomial O)` (or prove the precise localization equivalent), convert back, and pin polynomial restriction. |
| NP-0 points and evaluation | 45 | NV-6, SF-2 | Construct `Point`, `Pt`, `point_exists`, `coeffHom`, `coord`, `valueOn`, `pointHgt`, and the evaluation/value laws. |
| NP-1 level-one table | 60 | NV-1, `C35b`, `C130s2.s2DepthTwo_Dcum_one` | Define level-one `hgt/dig/Full`; prove the complete stage-law bank. |
| NP-2 slot value dictionary | 60 | NP-0, NP-1, `C130s6` | Prove `slot_value` at levels 1 and 2 and exact `key_value` at gauge level 1. |
| NP-3 slot digit dictionary | 60 | NP-1, RP-2 below, `twistRead` | Prove `slot_digit` and `dig_add` from actual residual reads, not a free copy. |
| NP-4 threshold source | 60 | source occurrence not yet named | Identify the inherited S2 thresholds and prove integer/natural equality. **Stop as BLOCKED if no source occurrence supplies them; do not choose a convenient numeral.** |
| NP-5 window | 45 | NP-2, NP-4 | Prove both live window inequalities and finiteness. |
| NP-6 letters | 45 | `s2Bridge_ψ`, terminal receiver, `s2Fld₂_card` | Construct `ambientLetter`, `psi_root`, and `letter_ne_zero` by live-index computation. |
| NP-7 canonical read | 60 | `C130cr`, Laurent normalizer, NP-6 | Construct the `L`-valued kernel read and its generator regressions. |
| NP-8 arena data | 60 | `C130ar`, terminal receiver | Construct `arenaRead`, `towerRead`, `peelUnit`; lint that no canonical/arena equality was introduced. |
| RP-0 grade arithmetic | 45 | NV-5, S2 numerals `(2,1,5)` | Cleared grade/value-group lemmas and exact/above membership normal forms. |
| RP-1 graded residual definition | 60 | RP-0, `dev`, `twistRead`, terminal receiver | Define total `R_(3,β)` with finite-support and proof-independence pins. |
| RP-2 zero/add laws | 60 | RP-1, `dev_add_of_monic`, twist-read additivity | Prove `graded_zero_of_above` and `graded_add`. |
| RP-3 graded product endpoints (**CORE 1/4**) | 60 | NV-2--NV-4, RP-1 | Relate exact-grade endpoints of `g`, `h`, and `g*h`. |
| RP-4 graded convolution (**CORE 2/4**) | 60 | RP-3, `C131k`, B39a pattern | Recursive coefficient convolution formula for the depth-two graded residual. |
| RP-5 preceding residual product (**CORE 3/4**) | 60 | RP-4, B39a `resPoly_mul_gen` | Discharge the inner residual product and twist normalization. |
| RP-6 `graded_mul` (**CORE 4/4**) | 45 | RP-5 | Assemble exact-grade product plus polynomial identity for arbitrary inputs. |
| RP-7 scalar nonzero | 45 | RP-1, `degree_dev_lt`, residue kernel API | Prove `graded_scalar_nonzero` under the exact `< 4` fence. |
| RP-8 normalized definition | 60 | RP-1, endpoint/side API | Define total `R₃`, prove constant-term nonzero for nonzero inputs, and compute key powers. |
| RP-9 normalized product order (**CORE 1/2**) | 60 | RP-6, RP-8 | Initial `y`-orders add under products, including all zero cases. |
| RP-10 `normalized_mul` (**CORE 2/2**) | 45 | RP-9 | Prove the universal normalized residual product law. |
| RP-11 recipe | 60 | RP-2, RP-6, RP-8, `dev_pow_self` | Prove the S2-specialized universal recipe (`f'=1`) symbolically. |
| RP-12 residual existence | 60 | RP-11, `s2Fld₂_card`, residue lifts | Collapse the residual input to the unique admissible linear polynomial and construct its degree-eight lift. |
| KP-0 initial-form predicates | 60 | NV-5, RP-8, U12 `MuEquiv`/`MuDivides` prototypes | Define honest `initialEquiv`, μ-divisibility, μ-minimality, and key-polynomialhood in the concrete model. |
| KP-1 residual divisibility (**CORE 1/4**) | 60 | KP-0, RP-10 | Translate μ-divisibility into divisibility of normalized residuals in the needed scopes. |
| KP-2 residual primality (**CORE 2/4**) | 60 | KP-1 | Irreducible residual with nonzero constant term gives prime initial form. |
| KP-3 degree minimality (**CORE 3/4**) | 60 | KP-1, `degree_dev_lt` | Prove μ-minimality at the recipe degree. |
| KP-4 `key_criterion` (**CORE 4/4**) | 45 | KP-2, KP-3 | Assemble the literal frontier field. |
| KP-5 key irreducibility | 60 | KP-4, mathlib monic Gauss transport | Prove `key_irreducible`; state any source-to-fraction-field bridge explicitly. |
| KP-6 carried key | 60 | KP-0, RP-8, `s2DepthTwoKeyAt_two` | Prove `carried_key_is_key` and `carried_key_residual`. |
| KP-7 residual classification (**CORE 1/3**) | 60 | KP-1, RP-8 | One direction of initial equivalence versus normalized residual equality. |
| KP-8 residual reconstruction (**CORE 2/3**) | 60 | KP-7, key minimality | Converse for arbitrary concrete key polynomials. |
| KP-9 `initial_iff_residual` (**CORE 3/3**) | 45 | KP-8 | Assemble Proposition-5.6 field with zero/equal-value cases. |
| FD-0 `FGMNSourceData/Laws` assembly | 60 | RP-0--RP-12, KP-0--KP-9, NP-6 | Construct both records; every one of the thirteen projections has a named theorem. |
| FD-1 OPEN-DICT-2/4 | 45 | FD-0, NP-0, NP-6 | `grade_compat` and `letter_compat`, preferably definitional after explicit normalization pins. |
| SG-0 corrected frontier | 60 | NP-0--NP-8, FD-1 | Construct the corrected S2 frontier; exact level-two table ties and core-only/cite-audited footprint. |
| SG-1 funnel fire | 45 | SG-0, `C130s17`, `C130s18` after amendment | Re-run `toChainRealization → calculusNonempty → s2RealizedInput →` both socket applications. |

The critical path is SF-0--SF-4, NV-0--NV-6, NP-0/NP-2/NP-4/NP-5,
RP-0--RP-12, KP-0--KP-9, FD-0/FD-1, SG-0/SG-1.  NP-6--NP-8 can run alongside the
residual cores after the signature repair.  NP-3 waits on RP-2.

## 7. Campaign rulings

1. **Current funnel:** refuted at `S2SourceFrontier.node`; its conditional downstream
   constructors remain correct but have an empty premise at S2.
2. **Concrete depth two:** potentially viable only after the ambient split, using weighted
   developments and localization.  U13 does not claim that corrected constructor exists.
3. **Computation boundary:** concrete numerals, live-index cases, and `f'=1` shrink several
   nodes.  They do not replace universal polynomial induction.
4. **First genuine inductive blocker:** `NodePointSource.value_mul`, equivalently the universal
   product law for the concrete level-two weighted-development value.  This is needed before
   `grade_compat` can honestly call `nextValue` a valuation read.
5. **FGMN inductive blockers:** `FGMNSourceLaws.graded_mul`, `normalized_mul`,
   `key_criterion`, and `initial_iff_residual`.  These are the largest cores and are sized as
   multi-node groups above.
6. **OPEN-DICT-2/4:** not the immediate obstruction.  With shared definitions they should be
   short after the two source models exist.
7. **OPEN-EVAL-ISO / OPEN-LETTERS:** the ambient repair clarifies their boundary.  Evaluation
   belongs to `E`; residue letters belong to `L`.  No future proof may identify them merely
   because both are fields.
8. **No edits enacted here:** `leanspec/`, `leanfinal/Uniformity/`, roll-ups, and project state
   remain untouched.  This unit supplies the diagnostic proof and the replacement plan only.
