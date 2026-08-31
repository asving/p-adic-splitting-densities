# AUD report — adversarial audit of the census master chain

## Executive verdict

**The internal census implication PASSES:** the five premises of
`IFCG55.decidedSliceAt_all_of_MASTER` genuinely imply the exact Lean proposition
`∀ n : ℕ, Uniformity.Density.DecidedSliceAt n` appearing in its conclusion.  The
reduction is not obtained by an empty binder, a mismatched remainder carrier, or a
changed limit predicate.

**The surrounding capstone claim does not receive an unqualified pass.**  There is one
CRITICAL semantic break in the `capstoneHypotheses_of_MASTER` branch, and there are three
JUSTIFICATION GAPs/statement-surface defects.  In particular, the formal result is about
the repository's unrestricted certified density, not the corpus's stated `disc ≠ 0`
locus.

## Classified findings

### CRITICAL C1 — `capstoneHypotheses_of_MASTER` is not the “whole proof's remaining surface”

The offending claim is:

> `leanfinal/Uniformity/ChapI/IFCG55.lean:342-345`
> ```lean
> /-- ★★★ **THE WHOLE PROOF'S REMAINING SURFACE, one Lean statement**:
> `CapstoneHypotheses n` from {the two live structural fronts (ladder, deepTwist)} +
> {the five census master premises (§4)}. -/
> theorem capstoneHypotheses_of_MASTER (n : ℕ)
> ```

But the result structure still contains content-free fields:

> `leanfinal/Uniformity/ChapI/I10_I15_I18.lean:209-215`
> ```lean
>   a0 : DecidedSliceAt n
>   a1 : MenuLawAt n
>   a2 : DrainageAt n
>   jd0 : True                            -- ⚠ LATE-BINDING F (I.08); defect I-D7
>   genhnBox2 : 6 ≤ n → True              -- ⚠ LATE-BINDING F (I.09); defects I-D7, I-D8
>   windowPinning : WindowPinningAt n
>   genhnHE : 6 ≤ n → GenhnHEAt n
>   genhnTow1 : 8 ≤ n → GenhnTow1At n
> ```

The last three named predicates are themselves `True`:

> `leanfinal/Uniformity/ChapI/I05.lean:90-94`
> ```lean
> ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the degree-`n` stage
> data (H.09's `StageInterface` instances) and asserts the `hwin` clause at every stage of every
> genre of degree `n`. FROZEN HERE: name, degree index, `Prop` kind. -/
> def WindowPinningAt (n : ℕ) : Prop :=
>   True
> ```
>
> `leanfinal/Uniformity/ChapI/I06.lean:96-99`
> ```lean
> ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): quantifies over degree-`n` stage leaves with
> `μ ≥ 3` (H's `StageLeaf`/`GenreDatum` layer) asserting the σ-decision clause. -/
> def GenhnHEAt (n : ℕ) : Prop :=
>   True
> ```
>
> `leanfinal/Uniformity/ChapI/I07.lean:90-93`
> ```lean
> ⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the census conjunction, typed against C.93's
> `#check`-suite names at the resolution pass. -/
> def GenhnTow1At (n : ℕ) : Prop :=
>   True
> ```

ID12 consequently fills them by `trivial` (`ID12.lean:83,90,96,142-146`).  IFCG55 does
disclose the “as signed” status at lines 336-338, so this is not a hidden Lean dependency;
it is nevertheless a semantic break in the advertised whole-proof reduction.  The theorem
proves the current placeholder-bearing `CapstoneHypotheses`, not the real window-pinning,
GENHN-HE, GENHN-TOW-1, JD0, or GENHN-BOX-2 obligations.

### JUSTIFICATION GAP J1 — `DecidedSliceAt` is re-keyed away from the stated `disc ≠ 0` locus

The file itself records the divergence:

> `leanfinal/Uniformity/ChapI/I02.lean:72-75`
> ```lean
> **(6) FAITHFULNESS DIVERGENCE, disclosed (honesty I-6, carried from the signed docstring).**
> The corpus states `(A0)` on the `disc ≠ 0` locus; `decidedDensity` counts the every-lift decided
> classes with **no** such restriction (GC-9), which is the strictly STRONGER read.
> ```

The actual carrier contains no discriminant condition:

> `leanfinal/Uniformity/ChapI/I02.lean:98-105`
> ```lean
> def DecidedSliceAt (n : ℕ) : Prop :=
>   ∀ σ : FactorizationType, σ.degree = n →
>     ∃ num den : Polynomial ℚ, den ≠ 0 ∧
>       ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
>         [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
>         den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
>           decidedDensity O n σ
>             = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
> ```

Rationality of the unrestricted certified density is not, by itself, a formal implication
of rationality after restricting to `disc ≠ 0`; that requires a comparison/null-locus
lemma which is absent from this spine.  Thus the master reaches `DecidedSliceAt` exactly as
defined, but the semantic identification of that proposition with the corpus's stated A0
remains unjustified.

### JUSTIFICATION GAP J2 — the all-`n` wrapper over-demands the zero-degree slice

The recorded defect is exact:

> `leanfinal/Uniformity/ChapI/I02.lean:60-68`
> ```lean
> **(5) THE RECORDED DEFECT — I-D10, hypothesis-side over-demand at `n = 0`.**  The landed target
> guards its body with `0 < n`; `DecidedSliceAt` does not carry that guard (correctly — the guard
> belongs to the ∀-`n` wrapper, and the first gate below proves the two fit together on the nose).
> The over-demand appears only at I.10's `a0 : DecidedSliceAt n` field, where `∀ n,
> CapstoneHypotheses n` would demand `DecidedSliceAt 0`, a law the capstone never asks for.
> **Class: harmless to soundness, dishonest to the open surface** (it makes the hypothesis block
> look one law bigger than Display A).  Left OPEN by amendment A-I.1; **not repairable from this
> node** — the fix is a field-level change at I.10, which is owner-gated (Part V gate (a)) and
> under the standing I.10 freeze.  Recorded here so I.02's consumer cannot inherit it silently.
> ```

The anti-drift pin confirms the difference:

> `leanfinal/Uniformity/ChapI/I02.lean:109-114`
> ```lean
> -- `∀ n, 0 < n → DecidedSliceAt n`, on the nose.
> example : UniformityStatementDecided ↔ ∀ n : ℕ, 0 < n → DecidedSliceAt n := Iff.rfl
> ```

IFCG55 concludes the stronger guard-free wrapper (`IFCG55.lean:323`).  This does not break
the implication because `DecidedSliceAt 0` is independently landed through IFCG0/IFCG14,
but it means the stated all-`n` surface is not byte-identical to the positive-degree target.

### JUSTIFICATION GAP J3 — IFCG71 globally strengthens the drain handoff

The local assembly only needs drain at decompositions of the current mass:

> `leanfinal/Uniformity/ChapI/IFCG71.lean:988-997`
> ```lean
> theorem visCensusLaw_of_clusterGeom_collisions {m : ℕ} (hm : 0 < m)
>     (σ : FactorizationType)
>     (hentry : ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
>       0 < n₁ → 0 < n₂ → n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
>         VisEntryClusterGeom g n₁ n₂ σ part)
>     (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ →
>       DeepStratumDrain n₁ n₂)
>     (hC : CollisionLaw m σ)
>     (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
>       (powerCollisionTotal O π m σ M : ℝ)
>         / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
> ```

The recomputed master instead asks for every pair at every mass:

> `leanfinal/Uniformity/ChapI/IFCG71.lean:1030`
> ```lean
>     (hDR : ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂)
> ```

The handoff visibly discards the available mass equation:

> `leanfinal/Uniformity/ChapI/IFCG71.lean:1055-1058`
> ```lean
>       visCensusLaw_of_clusterGeom_collisions (by omega) σ
>         (hCG e he hsm σ hσ hwit hram hcard)
>         (fun n₁ n₂ _ h₁ h₂ => hDR n₁ n₂ h₁ h₂)
> ```

This is a strict premise over-demand, so IFCG71's handoff is not “the same Props,
byte-level.”  IFCG71's prose does disclose that the drain is global, but that does not make
the Props identical.  The strengthening does not invalidate the implication, and IFCG73
later discharges exactly this global Prop by `deepStratumDrain_min_two`
(`IFCG73.lean:712-714`), so it does not break the final IFCG73 endpoint.

## Spine-link audit

| Link | Verdict | Reason |
|---|---|---|
| IFCG55 `decidedSliceAt_all_of_MASTER` → `coneRemainderLaw_all_of_master` + IFCG25 remainder/bridge front | **PASS** | The five master premises are passed with the same guards; `hBr` is supplied by IFCG32 with `1 ≤ δ` derived from the consumer's `2 ≤ δ`. |
| IFCG55 engine: masses 2/3/4 | **PASS** | IFCG25/26 close 2/3; mass 4 consumes exactly `hFC 2`. |
| IFCG55 engine: mass ≥ 5 | **PASS** | The witnessed/ramified branch consumes `hSD`, `hPD`, `hLeaf`; prime masses use the prime full-span law; nonprime mass ≥ 5 is shown unequal to 5 and hence ≥ 6 before consuming `hEis`; unramified and unwitnessed branches use IFCG33/IFCG55 zero laws. |
| IFCG33 unramified zero law → IFCG55 engine | **PASS** | The same `ConeRemainderLaw e σ` is produced; no carrier or normalization changes. |
| IFCG32 `unramifiedBlockBridge_all` → IFCG25 `hBr` | **PASS** | Consumer requires `δ,e ≥ 2`; producer requires only `δ ≥ 1` and is uniform in `e`. |
| IFCG25 remainder/bridge front → IFCG24 point/remainder front | **PASS** | The same remainder law supplies both `ZeroConeClause` and the linear point clauses. |
| IFCG24 remainder laws → IFCG21 `decidedSliceAt_all_of_cones` | **PASS** | `zeroConeClause_of_remainderLaw` uses the exact finite-level partition, and the centered law has the same normalization. |
| IFCG21 point cone → single-point aggregate | **PASS** | The `e = 1` factor is closed separately; all `e ≥ 2` calls respect the mass window and excluded self-call. |
| IFCG21 centered cone → IFCG20 fractional cell | **PASS** | The center partition multiplies the common limit by `q`, represented by numerator `X * n`; denominator and level normalization are unchanged. |
| IFCG20 fractional cell ↔ IFCG18 deep-linear kernel | **PASS** | `deepLinearClusterLaw_iff_fractionalCell` is an actual iff with identical premise binders. |
| IFCG18 kernels → IFCG16 census | **PASS** | The two kernel Props produce `UniformRationalNonloopCensus` without added hypotheses. |
| IFCG16 census → IFCG15 nonloop remainder | **PASS** | The per-mass interface is proved equivalent in both directions. |
| IFCG15 nonloop remainder → IFCG14 recursion socket | **PASS** | `ClusterRecursionAt m ↔ RationalNonloopRemainderAt m` is an iff, and the smaller-mass premise is unchanged. |
| IFCG14 recursion → `DecidedSliceAt` | **PASS** | Strong induction uses the independently landed degrees 0–3 and the socket only for `m ≥ 4`; `DecidedSliceAt` is definitionally the family of `DecidedValueLaw`s. |
| IFCG55 decided slice → ID12 `CapstoneHypotheses` | **FAIL (semantic)** | Formally type-correct, but C1 shows that the result record still contains five content-free real-obligation placeholders. |

## Definition spot-audit

| Definition/interface | Verdict |
|---|---|
| `DecidedSliceAt` vs `DecidedValueLaw` | **PASS internally**: `IFCG14.lean:93-96` gives `Iff.rfl`. **Semantic qualification:** J1 and J2. |
| `DecidedAt` | **PASS**: `GenuineDensity.lean:66-67` quantifies every lift of the class, and `proj_surjective` is used at lines 83-86 to prove each class has a lift; the universal is not empty. |
| `decidedCount` | **PASS**: it is `Nat.card (decidedSet ...)` at `GenuineDensity.lean:104-105`, over finite coefficient classes. |
| `gapSeq` | **PASS**: it is exactly `possibleSeq - decidedSeq` at `GenuineDensity.lean:330-331`; nonnegativity follows from the proved set inclusion, and `Drainage.lean:691-723` bounds it by the genuinely undecided proportion. |
| IFCG24 carrier vs IFCG35 `remainderCarrier` | **PASS, definitionally identical**: IFCG24 lines 1026-1031 counts the same intersection-minus-`pureFaceSet` that IFCG35 lines 654-660 names, and IFCG35 lines 665-666 prove the count equality by `rfl`. |
| `ZcURLim` | **PASS**: IFCG24 lines 129-140 place `∃ n d` before the DVR/uniformizer quantifiers, require both `d ≠ 0` and every actual `d(q) ≠ 0`, and demand the limit for every irreducible uniformizer. No denominator or uniformity binder is lost downstream. |

## IFCG71/72/73 recomputation audit

| File/master | Verdict |
|---|---|
| IFCG71 `decidedSliceAt_all_of_clusterGeom` and capstone twin | **FAIL on exact-premise audit** because of J3's global `hDR`; all other row Props (`hCG`, `hCL`, `hPCL`, `hPF`, `hLeafSub`, `hR4`, and the capstone's `hFC`/`hEis`) hand off with the same binders and guards. The Lean implication itself passes. |
| IFCG72 `decidedSliceAt_all_of_MASTER_CENSUS` | **PASS**: `hFC`, `hEis`, `hSD`, and `hPD` are byte-identical to the IFCG69 consumer. `hCensus` is consumed at the same `e,σ,p`, with the same non-singleton and `e ≠ e' d + 1` guards, to produce exactly `SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ`. The capstone twin repeats the same handoff. |
| IFCG73 drain-free masters | **PASS**: the surviving `hCG`, `hCL`, `hPCL`, and `hLeafSub` Props match IFCG71 byte-for-byte, while `deepStratumDrain_min_two` supplies exactly IFCG71's global `hDR`. No remaining premise is strengthened in the call. |

## Final answer to the brief's implication question

**YES — as stated in Lean.**  After unfolding the named interfaces, the premises of
`IFCG55.decidedSliceAt_all_of_MASTER` feed the remainder-law engine, the point/centered
cone reductions, the two kernel reductions, and IFCG14's strong induction without a type,
carrier, normalization, or guard mismatch.  Therefore they genuinely imply
`∀ n, DecidedSliceAt n` for the repository's exact definition.

**NO — if “as stated” is intended to mean the full external mathematical capstone without
qualification.**  J1 leaves the discriminant-locus re-keying unproved, J2 records the
zero-degree scope over-demand, and C1 means `capstoneHypotheses_of_MASTER` still proves a
placeholder-bearing record rather than all real capstone obligations.
