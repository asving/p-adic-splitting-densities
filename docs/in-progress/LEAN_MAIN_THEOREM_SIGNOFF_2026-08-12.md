# MAIN LEAN THEOREM — SIGN-OFF DECISION DOCUMENT (2026-08-12)

**For Asvin. The ask: fix the shape of the main Lean theorem (the stage-two
capstone generalizing `montes_unconditional` to all primes at once) and its
definition closure, so the LEANSIMP build (steps 2–18, parked per append #31)
can start.** Agent-drafted, pending orchestrator review.

This is a decision document; the evidence lives in three reference appendices
in `docs/in-progress/`: **Part 1** `LEAN_SCOPING_core_2026-08-12.md` (signed
statements, definition closure, findings F1–F4), **Part 2**
`LEAN_SCOPING_consumption_map_2026-08-12.md` (informal corpus → Lean nodes,
with grades), **Part 3** `LEAN_SCOPING_inventory_2026-08-12.md` (existing
1209-module corpus vs the five-node target).

Context (PROJECT_STATE appends #25–#31): the SOL certification campaign
**closed 29/29 today** — every cone note certified end to end, plus four
discovered-and-proved lemmas (W12-HT, GENHN-CAP-GEN, GENHN-COUNT-RERUN,
RM-1-TRANSPORT). The compression campaign is mid-arc: **T3 ACCEPTED 2/2**;
T1 live at r8, T2 v2 at r1, T4/T5 owe repairs. So the informal supplier corpus
is certified-stable, but its compressed T-unit form is stable only at T3.

---

## 1. THE DECISION ASKED

You are signing off (i) the statement of the main Lean theorem and (ii) the
exact definitions it consumes (§2). Everything downstream — the 18-step
migration, the five proof nodes, the gates unit — keys off this choice.

### 1.1 The finding that forces the decision (F1 — machine-checked)

**The current signed anchors are provable vacuously, today.** During scoping,
a scratch snippet (in-memory, no repo file touched) containing a byte-identical
copy of `RealCountingFamily` and full ~20-line proofs of BOTH
`uniformity_target` and `uniformity_target_exhaustive` compiled, with
`#print axioms` = exactly `[propext, Classical.choice, Quot.sound]`. The
linter confirms `hn : 0 < n` and `hσ : σ.degree = n` are unused and the
exhaustive variant's drainage hypothesis is discarded. Mechanism: any single
prime's `C_isRational` field transports across `coefficient_coherent` to make
the shared coefficient rational-in-q, and `countingDensity_eq_sum_coeff` ties
each prime's density to the shared menu-sum. Consequences:

1. The comment fence ("NO proof unit may target these until `faithfulAt` is
   real") is the **only** thing between the repo and a contentless discharge
   of both sorries. Discharging them today would prove nothing about ℤ_p.
2. The fence's stated mechanism is wrong: no "abstract family whose
   `coefficient` is not rational-in-q" can exist. Rev 2's failure mode is
   **trivial truth**, not falsity (rev 1's was falsity, via free instances).
3. All mathematical content of stage two therefore lives in **constructing
   the canonical real family** — genuine monic-ℤ_p-box counting (`faithfulAt`
   real), the canonical coefficient with rationality a theorem (D6), coherence
   from GMN p-independence.

### 1.2 Shape (a) — keep the fenced rev-2 anchors

The capstone stays `uniformity_target` / `uniformity_target_exhaustive` as
signed (∀ family, one law). Content arrives via three not-yet-landed pieces:

- **Unit 1** (gates): `faithfulAt : True` → the `GenuineZpCounting` predicate
  + same-prime uniqueness (general analogue of `OM/RealInstanceV2Gates.lean`).
- **D6** (`coefficient_uniform`): the canonical coefficient's rationality-in-q,
  one representative for ALL primes — what makes instantiating
  `RealCountingFamily` at the real semantics possible at all.
- **D9** (`fullDensity`): a genuine full-density object with a necessary
  drainage tie, so the exhaustive hypothesis stops being decorative.

*For (a):* signed statement bytes stay stable (D12 discipline; you already
signed rev 2); smallest immediate diff; the ∀-form is the cleanest quotable
final statement. *Against (a):* per F1 the theorem is provable now with a
Lean-core footprint, so its meaning rests on a comment fence the kernel cannot
see; even after Unit 1, the ∀-family form is only as contentful as the
*existence* of a genuine family, which would still live in side gates.

### 1.3 Shape (b) — capstone = the canonical real family + `uniformity_core`

Restate the capstone as a construction plus a law over it:

```lean
def canonicalFamily (n : ℕ) : RealCountingFamily n            -- gates real
theorem coefficient_uniform (n) (T : ClusterShape) :
    IsRationalFn (fun p => canonicalCoefficient n T p)        -- D6
theorem uniformity_core : ∃ num den, ...                      -- decided law
UndecidedVanishes M → fullDensity M σ = M.countingDensity σ   -- D9 tie
```

with `faithfulAt : ∀ p hp, GenuineZpCounting (modelAt p hp)` a real field, so
`canonicalFamily` cannot be built without exhibiting the genuine counting
semantics. The rev-2 anchors survive **byte-identical as corollaries** fired
through `canonicalFamily`. *For (b):* provability itself certifies content —
the F1 accident becomes structurally impossible. *Against (b):* a statement
re-designation needing this sign-off; the capstone lands only when D6 + menus
+ gates land; the headline is an instantiation, not a single ∀-sentence
(mitigated: the ∀-corollary is one line away).

### 1.4 Recommendation

Recommendation: shape (b). Four reasons. (1) F1 makes (a)'s risk concrete,
not hypothetical: the anchors are provable today in ~20 lines with a Lean-core
footprint, so under (a) the difference between a landmark and a no-op is a
comment fence — an invariant the kernel cannot see and one accidental proof
unit can erase. (2) Even after Unit 1 makes `faithfulAt` real, (a)'s ∀-family
statement is only as contentful as the existence of a genuine family, which
would still live in side gates; (b) makes that existence THE theorem, so
provability itself certifies content. (3) (b) is the repo's own proven
pattern: the M9 rebase resolved the identical vacuity crisis at the
single-prime capstone by re-keying it through the constructed real instance
(`realM2`/`realD2`/`realF2`), and that discipline has held since. (4) (b)
loses nothing signed: the rev-2 anchors survive byte-identical as corollaries
fired through the canonical family, so D12 ledger discipline and the
2026-08-11/12 sign-offs are preserved. The cost — the capstone lands only when
D6 + the menus + the gates land — is not a cost of (b): under (a) the content
lands at exactly the same moment; (a) merely lets the *theorem* land earlier
than its content, which is precisely the failure mode F1 exposes.

---

## 2. THE THEOREM AND EVERY DEFINITION

File: `lean/LeanUrat/Stage2/UniformityTarget.lean` (rev 2, commit `cb169b40`).
Exactly two `sorry`s in the repo's active scope = the two target bodies.

### 2.1 `uniformity_target` (verbatim)

```lean
theorem uniformity_target
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry
```

One rational law per (n, σ) and per family: the ∃ (num, den) stands OUTSIDE
∀ p — the uniformity claim, for the DECIDED (level-N certified, N→∞) density.
Per F1, `hn`/`hσ` currently do no work.

### 2.2 `uniformity_target_exhaustive` (verbatim)

```lean
theorem uniformity_target_exhaustive
    (n : ℕ) (hn : 0 < n) (σ : FactorizationType) (hσ : σ.degree = n)
    (F : RealCountingFamily n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p),
        Filter.Tendsto
          (fun N => (F.modelAt p hp).undecidedCount N / (p : ℚ) ^ (n * N))
          Filter.atTop (nhds 0) →
        den.eval (p : ℚ) ≠ 0 ∧
        (F.modelAt p hp).countingDensity σ = num.eval (p : ℚ) / den.eval (p : ℚ) := by
  sorry
```

Same law under a per-prime drainage hypothesis (= `UndecidedVanishes`
unfolded). D9's standing complaint, now machine-checked by F1: the conclusion
is the same `countingDensity` equality, so the hypothesis connects to nothing.

### 2.3 The definition closure — one line + defect status each

| Definition | Home | Meaning | Defect status |
|---|---|---|---|
| `RealCountingFamily` | `Stage2/UniformityTarget.lean:58` | one coherent prime-indexed bundle: shared menu + shared coefficient + per-prime models/data | D1 landed; `faithfulAt : True` = THE placeholder (Unit 1); fence-mechanism sentence wrong (F1) |
| `CountingModel` | `CountingModel.lean:95` | level-N decided/undecided box counting; density = decided limit | D7 (ℚ-valued `densityVal` carried as data) + D10 (ℚ-valued counts); REDESIGN behind a compatibility facade |
| `countingDensity`, `UndecidedVanishes` | `CountingModel.lean:235` | THE density := `densityVal` (pinned as genuine limit by `decided_tendsto`); drainage predicate | inherits D7; D9: drainage ties to no distinct full-density object |
| `MontesDataV2` | `MontesV2.lean:66` | abstract Montes layer: menu, stratum counts, partition, coefficient C | D11 (degenerate instances admitted by design); `C_isRational` as a FIELD = half of F1; TRUSTED-FROZEN |
| `FactorizationType` | `Interface.lean:152` | σ = multiset of (e,f) pairs, degree = Σ eᵢfᵢ | grain SIGNED 2026-08-11; no positivity constraint on entries |
| `ClusterShape`/`ShapeCell` | `Interface.lean:178` | the OM cluster-tree shape index T (count-native tree + faithful cells) | no defect; D5 destination `Core/ClusterShape.lean` |
| `L4.LatticePolygon` | `L4.lean:59` | integer Newton-polygon data (width, ⌈heights⌉, vertex flags); p-free | no defect; leaf |
| `IsRationalFn` | `RatFn.lean:32` | one rational fn represents f at every q > 1 — the ∃-outside-∀ engine | no defect; KEEP |
| mathlib/core leaves | — | `Polynomial ℚ`, `Nat.Prime`, `Filter.Tendsto`, `Finset`, `Multiset`, … | closure stops here |

Deliberately NOT in the closure (each a review decision): `RealInstanceAt`
(rev 1's free bundle, the falsity carrier — deleted), `DensityFoundation` +
`TameFunctionalEquation` (gone per D8), `IsPalindromic` (dropped 2026-08-10),
`OMBridge`/`PadicMeasure.*` (statement-free; module-import caveat F4/§4).

### 2.4 The load-bearing definitions, verbatim

```lean
structure RealCountingFamily (n : ℕ) where
  /-- The counting model at each prime (as `realM2` at the committed prime). -/
  modelAt : ∀ p : ℕ, Nat.Prime p → CountingModel p n
  /-- THE shared shape menu: the finite set of cluster shapes contributing to
  each type — one menu for all primes (p-independence is L5fix/GMN content). -/
  menu : FactorizationType → Finset ClusterShape
  /-- THE shared per-shape coefficient `C T (q)` as a function of the residue
  cardinality — one function for all primes. Its rationality-in-q is the
  cross-prime coefficient-uniformity theorem (review D6), NOT a field. -/
  coefficient : ClusterShape → ℕ → ℚ
  /-- The Montes data over each prime's model (as `realD2`). -/
  dataAt : ∀ p hp, MontesDataV2 p n (modelAt p hp)
  /-- Every prime's shape decomposition uses THE shared menu. -/
  shapes_coherent : ∀ p hp σ, (dataAt p hp).shapesOf σ = menu σ
  /-- Every prime's per-shape coefficients are THE shared coefficients. -/
  coefficient_coherent : ∀ p hp T, (dataAt p hp).C T = coefficient T
  /-- ⚠ PLACEHOLDER (Unit 1, the realness gates): the models count genuine
  monic degree-`n` ℤ_p-boxes. While this field is `True`, NO proof unit may
  target the theorems below (an abstract family with non-rational
  `coefficient` defeats them); the gates unit replaces this with the
  `GenuineZpCounting` predicate + the same-prime uniqueness theorem. -/
  faithfulAt : True
```

(Its last docstring sentence is the F1-refuted defeat mechanism — fix at
revision.)

`CountingModel` (13 fields verbatim in Part 1 §2.2: level-N decided/undecided
counts, `box_partition` placing q^(nN) as the partition TOTAL, monotone decided
measures converging to the density, `upper_tail`). The two defect-relevant
fields, plus the density and drainage definitions:

```lean
  decidedCount : FactorizationType → ℕ → ℚ   -- D10: counts should be ℕ
  densityVal : FactorizationType → ℚ         -- D7: limit carried as ℚ-data

noncomputable def countingDensity (σ : FactorizationType) : ℚ := M.densityVal σ

def UndecidedVanishes {q n : ℕ} (M : CountingModel q n) : Prop :=
  Filter.Tendsto M.undecided Filter.atTop (nhds 0)
```

```lean
structure MontesDataV2 (q n : ℕ) (M : CountingModel q n) where
  shapesOf : FactorizationType → Finset ClusterShape
  stratumCount : ClusterShape → ℕ → ℚ
  partition : ∀ (σ : FactorizationType) (N : ℕ),
    M.decidedCount σ N = ∑ T ∈ shapesOf σ, stratumCount T N
  C : ClusterShape → ℕ → ℚ
  C_isRational : ∀ T : ClusterShape, IsRationalFn (fun q' => C T q')
  stratum_tendsto_C : ∀ (σ : FactorizationType), ∀ T ∈ shapesOf σ,
    Filter.Tendsto (fun N => stratumCount T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (C T q))
```

```lean
structure FactorizationType where
  data : Multiset (ℕ × ℕ)

def FactorizationType.degree (σ : FactorizationType) : ℕ :=
  (σ.data.map (fun p => p.1 * p.2)).sum
```

```lean
def IsRationalFn (f : ℕ → ℚ) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧ f q = num.eval (q : ℚ) / den.eval (q : ℚ)
```

(`ClusterShape`/`ShapeCell`/`LatticePolygon` verbatim in Part 1 §§2.6–2.7 —
no defects, pure data.) The proved decomposition engine the anchors' rationale
invokes (Lean-core, sorry-free): `MontesDataV2.countingDensity_eq_sum_coeff`
(`M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.C T q` — the rev-2 header's
miscited theorem) and `countingDensity_isRational`.

---

## 3. WHAT SUPPLIES EACH PIECE

The certified corpus (29/29 as of append #31) per theorem piece / family field:

| Piece / field | Certified supplier(s) | Lean home |
|---|---|---|
| `coefficient` + `coefficient_coherent` → **D6** `coefficient_uniform` | **W-12.D corrected (A1)** — the cross-prime coefficient-uniformity result; order-1 coverage restored by **LEMMA W12-HT** (machine-certified: 1,196 keys, 0 mismatches) | `Assembly/CoefficientUniformity.lean`, `Reduction/W12.lean` |
| `menu` + `shapes_coherent` (p-independent menu) | **W-11 / HEX3 / HMENU3** (all CERTIFIED) + GENIND; finite-genre stage laws GENH4/GENHN | `Induction/*`, `StageLaws/*` |
| `faithfulAt` → **Unit 1** `GenuineZpCounting` gates | greenfield — general analogue of `OM/RealInstanceV2Gates.lean`; safety = non-vacuity witness, σ-separation, same-prime uniqueness, degenerate-model rejection | `Stage2/Real/Faithfulness.lean` |
| `dataAt` (partition + `stratum_tendsto_C`, the general `hNodeLimit` legs) | the five-node counting proof (Reduction / Induction / StageLaws / Ladder / Towers, per D3) | `Stage2/<Node>/*` |
| drainage (`hExhaust` / `UndecidedVanishes`) → **D9** | **HE3 / HE6 / HE7 / HE6R1 / HETOW** (all CERTIFIED at pinned HEADs), resting on M1 termination (`lem:countHaar`) | `Ladder/Exhaustiveness.lean`, `Counting/Drainage.lean`, `Assembly/FullUniformity.lean` |

The T-unit → node map with grades (the compression layer — the *form* the
suppliers will be consumed in, not new content; grades as of comp11 close):

| T-unit | Lean node | Grade today |
|---|---|---|
| T1 GAUGE-COCYCLE | `Gauge/{Defs,Cocycle,Transport}` | arc live at r8; 2 repairs delivered, unfolded |
| T2 v2 σ-LADDER MASTER | Ladder spine `{Base,FractionalKeys,StrictDescent,Exhaustiveness}` (S-5 carrier signature = the design; S-6 GO, red line: no complete-DVR-stage-quotient; `keyIrreducible` in no obligation) | 0/2, r1; 3 repairs unfolded |
| **T3 COCYCLE-TELESCOPE** | `Gauge/Cocycle` (+ `Transport` export) | **ACCEPTED 2/2** — the only accepted T-unit |
| T4 CERTIFICATE WITNESS | `Towers/{Windows,Cap}` | 0/2; P4 NOT CLEAN (1 CRITICAL: GT6 pin 4 reversed; 2 GAP) |
| T5 w-FRAME | `Gauge/Defs` + `Towers/TwistedTransport` | 0/2; P4 not clean (2 GAP) |

Campaign lemmas (all proved/certified inside accepted, byte-frozen hosts):
**W12-HT** → `Reduction/W12.lean`; **GENHN-CAP-GEN** + **GENHN-COUNT-RERUN** →
`StageLaws/{OrderOne,FiniteGenres}.lean`; **GENHN-LIFT** → `Gauge/Defs.lean`
(byte-for-byte T1's (C6)); **RM-1-TRANSPORT** → `Gauge/Transport.lean`.
Sequencing consequence: Gauge can start from certified sources now;
Ladder/Towers authoring waits on the T2/T4/T5 arcs or consumes the
uncompressed accepted notes directly.

---

## 4. THE BUILD PLAN SNAPSHOT

**Greenfield, not migration.** The five-node proof has **zero Lean
footprint**: the annex tags (W12, GENIND, HMENU3, HEX3, GENH4, GENHN,
HE3/6/7, HETOW, GENTOW1–6, LIFTCORNER, GRT*, WELDMASTER, SIGMALAW, W11)
appear in no `.lean` file. Steps 8–12 of the 18-step plan are authoring
against the certified notes; only step 1 (KEEP island — baseline frozen
`a95cc545`) and steps 3–4 (Core/Counting splits) are genuine migrations. The
existing corpus supplies *ingredients* only — finite-field counts, Newton
polygons, Witt base change, triangular solves, termination measures —
per-node source map in Part 3 §1.

**The single measure-cut edge.** Stage2 sits in the `PadicMeasure` closure
today only via `Stage2 → MontesV2 → Interface → PadicMeasure`, and the sole
direct importer of `PadicMeasure` in the repo is `Interface.lean:2`. Moving
`DensityFoundation`/`OMBridge`/`clusterVolume_rational` into
`Legacy/MeasureFoundation.lean` cuts it — rev 2 references none of them
(D2/D5, steps 3–4). 1063 of 1209 modules are already outside the measure
closure; the complete 21-file quarantine-or-rewire list is in Part 3 §4.

**Sorry-free ingredients.** All seven node-source dirs — `OM`, `MovesS`,
`MovesSp`, `MovesC`, `MovesGr`, `MovesRBase`, `Kernels` — carry **0 real
sorries**. Of the repo's 38 real sorries, 2 are the Stage2 targets themselves
and 36 live in RETIRE-verdict dirs.

**Three mandatory small fixes at next revision, regardless of shape:**

1. **The miscite (F2):** the rev-2 header cites `MontesV2.countingDensity_eq_sum_C`;
   no such declaration exists — actual name `MontesDataV2.countingDensity_eq_sum_coeff`
   (`MontesV2.lean:123`).
2. **The fence-mechanism sentence (F1):** "an abstract family whose
   `coefficient` is not rational-in-q still defeats the law" describes an
   impossible family (two sites: the header and the `faithfulAt` docstring);
   replace with the true hazard — trivial provability.
3. **The `OmLeafFaithful` quarantine note (step 2):** `OmLeafFaithful.om_leaf_faithful`
   is a genuine axiom carrying 45 AxChk rows on a chain the V2 capstone does
   not touch — it needs its own quarantine-manifest entry.

**The D9 model to copy:** `montes_unconditional_exhaustive`
(`OM/RealInstanceV2.lean`) genuinely consumes its drainage hypothesis (via
`hlim.add hExhaust`) — step 15's acceptance test verbatim: "the drainage
hypothesis occurs in a necessary value-tie theorem, not merely as an unused
argument." **Trust discipline:** the new Stage2 graph becomes trusted only
when sorry-free with a pinned Lean-core AxChk footprint; kept declarations
get D12 ledger hashes; footprint regression = stop-the-line.

---

## 5. OPEN QUESTIONS FOR THE SIGN-OFF

- **Q1 — Statement shape (a) vs (b).** *Recommendation: (b)* — capstone = the
  construction of `canonicalFamily` + `uniformity_core` over it; the rev-2
  anchors retained byte-identical as corollaries. Reasons in §1.4. If (a) is
  chosen instead, the three §4 fixes are still mandatory and Unit 1 becomes
  the hard critical path with the fence as sole interim protection.

- **Q2 — `FactorizationType` grain.** *Recommendation: re-confirm the
  2026-08-11 decision* — the bare (e,f)-multiset IS the target grain, finer
  invariants deferred. One note: the structure admits non-positive entries
  (e.g. (0,0)); recommend leaving the data-grain as signed (the real menu
  never emits them; degree-n-ness rides on `hσ`, which does real work once
  the family is genuine).

- **Q3 — Does palindromy stay dropped?** *Recommendation: yes, for stage
  two.* The completed informal proof derives uniform rationality without the
  tame FE, which was only ever palindromy's carrier (D8); the single-prime
  capstone keeps its conditional `htameFE` palindromy clause untouched.
  Cross-prime palindromy returns, if at all, as a post-capstone extension.

- **Q4 — Is the D9 `fullDensity` theorem in-scope for the capstone, or a
  corollary?** *Recommendation: in-scope.* The capstone package should be
  (i) `canonicalFamily`, (ii) `uniformity_core` (decided law), and (iii) the
  drainage-tied full-density theorem (`UndecidedVanishes M → fullDensity M σ
  = M.countingDensity σ`, then the law over `fullDensity`). F1 proved that a
  drainage hypothesis without a `fullDensity` conclusion is decorative; only
  (iii) makes the "full density" claim real. The signed exhaustive anchor
  stays as a compatibility corollary (the leansimp review's own split).

- **Q5 — LEANSIMP steps 2–18 execution order.** *Recommendation: key each
  node's start to ITS supplier's stability, not to the compression campaign's
  close* (math-first directive). Wave 1 (now, statement-level,
  arc-insensitive): the three §4 fixes + step 2 quarantine manifest (incl.
  `OmLeafFaithful`) + steps 3–4 splits (cuts the measure edge) + step 5
  Unit 1 gates — the critical path under either shape. Wave 2: the Gauge
  package (stablest sources: T3 accepted, GENHN-LIFT + RM-1-TRANSPORT
  proved). Wave 3: Reduction/Induction/StageLaws from the certified notes;
  Ladder/Towers gated on the T2/T4/T5 arcs (or on consuming the uncompressed
  notes). Wave 4: assembly steps 13–15 in order — `coefficient_uniform` (D6),
  `uniformity_core` + anchor discharge, `fullDensity` (D9).

---

*Sign-off record: decisions inline here or as a dated PROJECT_STATE append;
the anchors' revision (and, under (b), the capstone re-designation) executes
only after that record exists.*
