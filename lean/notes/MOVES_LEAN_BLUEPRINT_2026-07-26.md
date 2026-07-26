# MOVES §B2-DEF — Lean formalization blueprint (2026-07-26)

*Blueprint architect deliverable gating the ~60-agent formalization fan-out. Formalizes the
ACCEPTED `§B2-DEF` (the tower induction, passes 20+21 CLEAN) of `lean/notes/MOVES_2026-07-24.md`.
Read this together with `lean/LeanUrat/Moves/Defs.lean` (the shared vocabulary, COMPILES green)
and `lean/LeanUrat/Moves/MANIFEST.json` (the machine-readable unit list with verbatim Lean
statements). Statements were elaboration-tested against `Defs` — see §7.*

Discipline for this campaign (from the parent instructions): **NO new axioms at all**; anything
not (yet) provable stays `sorry`. `sorry`-free ≠ non-vacuous — non-vacuity is anchored by the
base-stage construction (`L1.baseStage_exists`) and its concrete gate (`L1.base_nonvacuity_gate`).
The statement-fence holds: **do not weaken any statement to make it provable.** Definitions and
statements are the trust boundary — every `Stage` axiom and every flagged design decision is for
human/semantic-guardian review.

---

## 1. Design decisions (the concrete model), with justification

**D1 — Ambient objects.** `A = ℤ_[p][X]` (`Polynomial ℤ_[p]`), parametric in `p` (a
`{p : ℕ} [Fact p.Prime]` section binder everywhere). The residue side is a **fixed ambient finite
field `F`** (a `{F : Type*} [Field F] [Fintype F]` binder), morally `𝔽_{p^{n!}}`. This is BOTH
`PROJECT_STATE.md` §4's decided "fixed ambient residue field → field-constant recursion"
architecture AND the decisive formalization simplification (below).

**D2 — The residual apparatus replaces the graded ring.** §B2-DEF's own structural decision is:
never flatten residuals into anchored digit polynomials; work through the residual map
`R(f) := [f]·T^{−w(f)}` living in `L₀ = F[z^{±1}]`, which is simultaneously linear on graded
pieces and globally multiplicative (D.1(e)). We take this literally and do **not** build
`gr_w(A)` as a mathlib `GradedRing`/`DirectSum`:

- `L₀ := LaurentPolynomial F` (mathlib `LaurentPolynomial`, `= AddMonoidAlgebra F ℤ`). The
  distinguished degree-0 unit `z` is the Laurent variable `LaurentPolynomial.T 1` (`zvar`).
- `R : A → LaurentPolynomial F` is bundled as `Stage` data with the D.1(e) laws as `Prop` fields
  (`hRmul`, `hRadd`, `hRlt`, `hRne`, `hR0`). This is faithful: D.3(e) states verbatim that the
  ledger consumes exactly R's per-piece additivity/injectivity + multiplicativity, which are
  these fields. The graded ring becomes derived/unnecessary.
- The residue digit `dig'(B) = R(B) mod ψ ∈ F'` is `evalUnit z̄ (R B)`, where
  `evalUnit z̄ := LaurentPolynomial.eval₂ (RingHom.id F) z̄ : L₀ →+* F` (the residue-evaluation
  ring hom at a unit `z̄ ∈ Fˣ`, a root of `ψ`). `LaurentPolynomial.eval₂` is exactly the map
  "`T ↦ z̄`" and exists in mathlib.

**D3 — Residue-field growth `F' = F[z]/(ψ)` is realized as a subfield `F(z̄) ⊆ F`.** Since `F` is
the FIXED ambient field, an increment's new residue field `F'` embeds in `F`; we take `z̄ ∈ Fˣ`
a root of `ψ` and model `F' = Algebra.adjoin F {z̄}` (`⊆ F`). The field arguments (DIV: product
of nonzero field elements nonzero) run in the ambient field `F`. Per-stage residue-unit tracking
is the `Stage` field `resUnits : Subgroup Fˣ` (grows through the tower; `⊇ O`).
**FLAG (faithfulness):** the ambient model requires `F` large enough to contain every residue
field of the run; `L1.baseStage_exists` carries this as the hypothesis
`p ^ φ.natDegree ∣ Fintype.card F`. See §4.1.

**D4 — Each stage carries its OWN residual map; cross-stage moves relate via evaluation.** A
recentering `Φ' = Φ̂ − t` changes the localization (`z ↦ z' = z − c̃`), which a single
`LaurentPolynomial F` cannot hold (both `z` and `z'` as variables). So the recentered stage `σ'`
is a **distinct `Stage`** with its own `R'` (its own `z' = T 1`), and the D.10 substitution
identity `R'(f)(z') = R(f)(z' + c̃)` is stated at the **evaluation level**:
`σ'.digPrime z̄' f = σ.digPrime z̄ f` whenever `(z̄ : F) = (z̄' : F) + (c̃ : F)`
(`L5.recSubst`). This is the faithful rendering of the "change of transcendental" in the concrete
model. Same for increments: `TRANS` (D.7) CONSTRUCTS a new `Stage σ'` with its own `R'`; the
parent↔child relations are the `L4.TRANS*` lemmas.

**D5 — Bespoke lightweight helpers, mathlib where lighter.** `IsDevelopment` (finite Φ-adic
development, polymorphic over any `CommRing` so "development commutes with reduction mod `p^N`",
Fact A, is statable over `ZMod (p^N)`), `SlotMinAttained` (the attained-min form of K1, dodging
`inf'` nonemptiness junk), `K1At`, `IsSlotMinWeight`, `IsStandardLift`, `IAug`, `OrdPsiEq`,
`HasAnchor`, `IsRecentering`, `inC`. Counting reuses mathlib `Nat.card` + `Equiv` transport
(the D.3(e)(ii) primitive is `Nat.card_congr (Equiv.subtypeEquiv Θ …)`, generalizing
`OM/DevBijection.card_caseE_original`). Weights are plain `ℤ`-valued functions with laws on
nonzero arguments (value SET bounded below, value GROUP `ℤ` via
`∃ f g ≠ 0, w f − w g = 1` — the pass-9-finding-1 correction).

**D6 — The stage `σ = (w, Φ, C, U, T, F, z)` as a Lean `structure`.** Read index `(e,h)` +
Bézout `(s,t)`; key `Φ` monic, `deg ≥ 1`; `w`, `R`; the D.1(e) laws; `hRΦ : R Φ = T s`
(the pinned key residual D.3(b)); `hK1` (S2); `hS5` (coefficient digits are monomial units at the
forced position `−t·w(B)`); `resUnits`, `O`, `thr`, `weightSet` and `hS6a`/`hS6b` (the S6 split,
rev-D⁵–D⁸ corrected). `T` is not carried as a separate object: its role (`R(f) = [f]·T^{−w f}`)
is baked into `R`, and its per-stage exponent-vector bookkeeping (P2) is a construction detail of
`baseStage`/`TRANS`. `z`, `U` are likewise implicit (`z = T 1`; `U`'s content is that dig' of the
representatives is a unit — `L4.TRANSiv`).

---

## 2. The `Stage` axioms ↔ §B2-DEF (S1)–(S6) correspondence

| Lean field(s) | §B2-DEF | note |
|---|---|---|
| `hwmul`, `hwult`, `hvalgrp`, `hwΦ` | (S1) valuation, value group ℤ, `w Φ = h` | `hvalgrp` = the pass-9-finding-1 fix (group, not surjective) |
| `hR0`, `hRne`, `hRmul`, `hRadd`, `hRlt` | D.1(e) residual apparatus laws | bundled because gr is not built (D2) |
| `hRΦ : R Φ = T s` | D.3(b) pinned key residual `R(Φ)=z^s` | literal monomial (rev-D⁶) |
| `hK1 : K1At w Φ (w Φ)` | (S2) Lemma K1 at own key | |
| `hS5` (monomial `c·z^{−t·w(B)}`, `c ∈ resUnits`) | (S5) monomial digits + stride position | (S4) `L₀ = F[z^{±1}]` and `(L^coeff)₀ = F` are the model choice D2 |
| `resUnits`, `O ≤ resUnits`, `hS6a` | (S6a) constant base-orbit `O = F_Qˣ` realizers | orbit group CONSTANT (rev-D⁶, pass-14) |
| `thr`, `weightSet`, `hWS`, `hS6b` | (S6b) full residue-field scalars above the clean threshold | the S6 split (pass-10); clean threshold (pass-12–13) |

(S3) slot decomposition is **derived** in the concrete model (distinct minimizing slots occupy
distinct `z`-positions by the stride ⟹ their monomials are independent — `L2.anchorCong` +
`L0.GRb`), so it is not a separate axiom.

---

## 3. The DAG (7 layers, 59 units)

Layer counts: **L0=9, L1=5, L2=10, L3=6, L4=10, L5=15, L6=4.** Difficulty: 10 easy / 30 medium /
19 hard. Each unit is one new file `lean/LeanUrat/Moves/<id>.lean`, importing `Defs` + its listed
deps. Full verbatim statements + per-unit proof sketches are in `MANIFEST.json`; below is the
skeleton and the load-bearing cross-layer edges.

**L0 — D.1 GR generalities + Facts A/B (pure `LaurentPolynomial`/development facts).**
`GRa` monomial·monomial; `GRb` distinct-exponent monomials independent (D.1(b) ties);
`GRc` `evalUnit` on a monomial; `GRd` dig' of a monomial ≠ 0; `GRe` `R(fⁿ)=(R f)ⁿ`;
`GRf` **distinct-ψ-order finite sum ≠ 0** (the K1 core, hard); `GRg` support-in-window ⟹ anchored
poly of degree < g; `FactA_exists`, `FactB_unique` (development exists/unique, polymorphic ring).

**L1 — the base stage (§A/§B1 re-expressed; the NON-VACUITY ANCHOR).**
`gaussVal` (introduces `def gaussVal`, Gauss's lemma over ℤ_[p]); `baseWeight` (introduces
`def baseWeight`, the min-formula valuation = B1.1); `baseResidual` (introduces `def baseResidual`
into `LaurentPolynomial F`, R multiplicative = A2/B1.2); **`baseStage_exists`** (assembles the
`Stage`, discharging all of S1–S6 — the anchor); `base_nonvacuity_gate` (a concrete
`GaloisField 2 2`, `φ = X²+X+1`, `p=2` witness mirroring `DevBijection.caseEPhi`).

**L2 — D.3 stride/width/P6 + D.4 (I-aug).**
`anchorCong` (D.3a); `keyResidualPow`; `strideRule` (D.3c); `widthBound` (D.3d);
`psiNotDvd` (D.3d, ψ ∤ R(B)); `P6i` (D.3(e)(i) additive+injective); `P6ii` (D.3(e)(ii) the
count-transport primitive); `iaugRoot`, `iaugStep` (D.4 convexity, hard), `iaugRecenter`.

**L3 — D.5 standard lift + K1, D.6 DIV.**
`liftExists` (Φ̂ exists via S6b realizers); `liftWeight` (w(Φ̂)=ehg); `liftResidual`
(`R(Φ̂)=z^{m̂}ψ(z)`); **`K1`** (Lemma K1(Φ̂/w), hard); `digPrime_nonzero`; **`DIV`** (D.6
multiplicativity + exact remainder weight, hard).

**L4 — D.7 Proposition TRANS (i)–(viii) + assembly.**
`TRANSi` (submult of w'); `TRANSii` (coefficient weight scaling `w'(B)=e'·w(B)`);
`TRANSiii` (w' a valuation, hard); `TRANSiv` (unit survival); `TRANSv` (dig' onto F', hard);
`TRANSviii_a` (𝒜' weight-set recursion, over parent data); `TRANSviii_b` (**the offset P-lift**,
over parent data, hard); `TRANSvi`, `TRANSvii` (z' pinning / S5' — extractions from the built σ');
**`TRANSstage`** (constructs the child `Stage`; the induction closes, hard).

**L5 — D.8 landing, D.9 REAL, D.10 recentering.**
D.8: `landBox`, `landVertex`, `landVertexDigit` (VERTEX with the explicit z̄^{−μm̂} unit —
pass-10 finding 2), `landTransport` (triangular determinacy — NOT term-by-term, pass-9 finding
10), `landTwoSided` (stratum ⟺ cylinder). D.9: `realRecursion`, `realCofin`, `realDomination`
(h_r>e_r f_r, hard), `realConclusion`. D.10: `recSpecies` (recentering ⟺ e=1), `recVV` (v=v'),
`recLiftIndep` (graded-scope lift independence — the Case-K-sharpened scope clause),
`recSubst` (the substitution identity, evaluation-level), `recRSland`, `recTRANSRS` (the
recentered stage is a full Stage).

**L6 — D.11 the per-move measure ledger.**
`moveReduceCommute` (development commutes with reduction mod p^M); `moveAffineBij` (the move is a
bijection); `ledgerCount` (#stratum = p^{nN}·vol, the one-unit-system count rev-D¹⁰);
`measureExact` (mass level-independent).

**Load-bearing cross-layer edges (the tower induction's genuine back-edges, acyclic — verified):**
`L2.iaugStep → L3.K1, L5.landBox` (I-aug-after-increment consumes the landing box — the induction
along the history, D.4); `L4.TRANSstage → L2.iaugStep` (TRANS consumes I-aug at D.7(ii));
`L5.realDomination → L2.iaugStep`; `L3.K1 → L2.psiNotDvd, L0.GRf`. No cycles (checked by DFS).
The mathematical induction is: base stage (L1) → [K1/DIV (L3) → TRANS (L4) → landing (L5) → next
stage's I-aug (L2)] repeated along the read history; the file DAG unrolls one level, and the
tower is closed by the parametric `Stage`/`TRANSstage`/`recTRANSRS` quantification (any `σ`).

---

## 4. Faithfulness gaps and flags (honest — these are blueprint gaps, not silent weakenings)

**4.1 The ambient-field model of residue growth (D3).** The note's `F' = F[z]/(ψ)` genuinely
GROWS the residue field; we realize it as `F(z̄) ⊆ F` for a fixed ambient `F`. This is faithful
IFF `F` is large enough (all residue fields of the run embed) — carried as the explicit
hypothesis `p^{deg φ} ∣ card F` in `baseStage_exists` and as `Algebra.adjoin F {z̄}` membership in
`TRANSv`/`TRANSviii_b`. **Flag for review:** the correspondence "`Algebra.adjoin F {z̄}` = the
note's F'" and the sufficiency of the ambient card hypothesis. An alternative faithful model
(per-stage bundled residue field `F' : Type`) is heavier and was rejected for compile-robustness;
the ambient model matches `PROJECT_STATE.md` §4.

**4.2 The `Stage` axiom set is a formalization choice.** (S1)–(S6) → the `Stage` `Prop` fields
(§2) is a translation; the exact quantification of `hS6a`/`hS6b` (constant orbit `O`, clean
threshold `thr`, `resUnits`) was the longest-fought point of the math campaign (passes 10–15).
**Flag:** semantic-guardian audit of every `Stage` field vs D.0/D.2, and that `baseStage_exists`
+ `base_nonvacuity_gate` genuinely inhabit it (else the whole tower is vacuous).

**4.3 `TRANS(vi)/(vii)` as post-construction extractions.** These verify the built child `σ'`
satisfies `hRΦ`/`hS5`; their mathematical content (z' pinning, T'-normalization) is discharged
inside `TRANSstage`. They depend on `TRANSstage` and are light extractions — the weight is in
`TRANSstage` + `TRANSviii_b` (offset P-lift) + `TRANSv`. **Flag:** ensure `TRANSstage` does not
become circular (it must build `σ'.hS6b` from the standalone `TRANSviii_b`, not from `σ'`).

**4.4 `L5.landTransport` states DETERMINACY, not the full bijection.** Per pass-9 finding 10,
term-by-term equality of slot residuals with ψ-adic digits is FALSE (ψ-level carries). The unit
states the deterministic direction (slot residuals determine `R(f)`); the invertibility is its
inverse. The full "triangular bijection with carries" as an explicit `Equiv` is **NOT** stated —
the ledger (D.10/D.11) consumes only determinacy + the count transport (`P6ii`). Flag if a later
unit needs the explicit carry recursion.

**4.5 L6 counting is stated abstractly.** `ledgerCount`/`measureExact` use an abstract
digit-coordinate `Equiv` (`{x // stratum x} ≃ (Fin (nN−k) → ZMod p)`) rather than instantiating
the repo's `QuotientBox`/`CellCard` box machinery. Fully grounding them reuses
`OM/DevBijection`/`RecenterBox` infrastructure (the deg-2 instances already exist). Flag: the
bridge from `Stage`-level strata to concrete `ZMod (p^N)` boxes is the least-developed layer.

**4.6 Items I could NOT fully faithfully state (explicit blueprint gaps).**
- **The convexity half of D.4 `iaugStep`** (lower-hull descent slopes increase leftward) is
  compressed into the chord inequality `ehg·(μ−j) < w(B_j) − w(B_μ)`; the "every continuing side
  is steeper" hull argument is in the sketch, not the statement. Faithful but the statement is the
  chord consequence, not the full hull lemma.
- **D.11's "vol = product of per-pinned-digit factors, transported digits on the same footing"**
  (rev-D¹⁰) is rendered as the single exponent `k` (number of unitriangular equations) via the
  digit-coordinate equiv; the note's finer per-equation bookkeeping is collapsed. Adequate for the
  measure-exactness conclusion, but does not expose each transported digit's factor separately.
- **§C composition along read histories** is deliberately OUT of scope (D.11 explicitly defers it,
  pass-8 gap 7). No unit claims the joint-history product theorem.

---

## 5. How the fan-out consumes this

**Preamble (every unit file):** `import Mathlib`, then `import LeanUrat.Moves.Defs`, then the unit
files listed in `deps`; then `open Polynomial LeanUrat.Moves` and `namespace LeanUrat.Moves`.
Set options as in the repo (`set_option linter.style.longLine false`,
`set_option linter.style.header false`, `set_option maxHeartbeats 400000`). End each file with a
`#print axioms <thm>` block (must be Lean-core only; any `sorry` shows as `sorryAx` — acceptable
this campaign, but flagged in the file docstring).

**Sorry policy:** proving is the goal; unprovable stays `sorry` (NO new axioms). Hard units
(`GRf`, `K1`, `DIV`, `TRANSiii/v/viii_b/stage`, `realDomination`, `iaugStep`, `landTransport`,
`landTwoSided`, `recLiftIndep`, `recRSland`, `recTRANSRS`, and the L1 base defs) are expected to
carry `sorry` initially. The def-introducing L1 units (`gaussVal`, `baseWeight`, `baseResidual`)
declare their `def` in-file; those defs must be `sorry`-free (junk defs are worse than open
theorems) — if a def needs a proof obligation, restructure per the repo rule.

**Search-before-prove (repo ladder):** local `rg`/`lean_local_search` → `exact?`/`apply?` →
Loogle → LeanSearch. Reuse `OM/Development.lean` (`develop`, `develop_unique`) for L0.FactA/B and
`OM/DevBijection.lean`/`OM/RecenterBox.lean` for the deg-2 concrete instances of L1/L6.

**Build/verify:** `cd lean && lake env lean LeanUrat/Moves/<file>.lean` per file (NOT `lake build`
— it can hang on NFS; per repo README). `Defs.lean` is already green.

---

## 6. `Defs.lean` inventory (COMPILES — `lake env lean LeanUrat/Moves/Defs.lean` exit 0)

`zvar`, `IsMonomialUnit`, `evalUnit`, `inC` (poly ring), `IsDevelopment` (poly ring),
`SlotMinAttained`, `K1At`, **`Stage`** (the structure, §2), `Stage.digPrime`, `Stage.mem`,
`IsStandardLift`, `IAug`, `IsSlotMinWeight`, `OrdPsiEq`, `HasAnchor`, `IsRecentering`. No `sorry`,
no axioms. If a fan-out unit needs a new shared def, add it to a `Defs2.lean` (do not edit
`Defs.lean` without re-running the elaboration sample in §7).

---

## 7. Elaboration-test record

`Defs.lean` compiles green. **31 sample statements across every layer** were elaboration-tested
(`:= sorry` in a scratch appending the `Defs` body; `lake env lean`, exit 0, only `sorry`
warnings): `L0.GRb, GRc, GRf, GRg, FactB_unique`; `L1.baseStage_exists` (+ a `Type*`/`GaloisField`
base gate); `L2.anchorCong-form, widthBound, psiNotDvd, strideRule, P6ii, iaugStep-form`;
`L3.K1, DIV`; `L4.TRANSi, TRANSii-form, TRANSv, TRANSvi-form, TRANSviii_a, TRANSviii_b,
TRANSstage`; `L5.landVertex, landVertexDigit, recSubst, recVV, recSpecies, recRSland,
recLiftIndep, realRecursion, realDomination, realConclusion-form`; `L6.moveReduceCommute,
ledgerCount, measureExact`. The `{F : Type*}` binder form used in `MANIFEST.json` was confirmed to
elaborate standalone. The DAG was verified acyclic (DFS) and all deps resolve.

---

# ROUND 2 (2026-07-26) — redesign after the semantic-faithfulness rejection

The round-1 `Defs.lean` + `MANIFEST.json` (§§1–7 above) were REJECTED by
`lean/notes/MOVES_LEAN_SEMAUDIT1_2026-07-26.md` (39 FAITHLESS / 2 IMPRECISE / 3 FLAGGED-OK / 15
faithful of 59 statements; 10 structural `DEF` defects + 1 IMPRECISE in `Defs`). This section
records the round-2 redesign that repairs it. **§§1–7 above are SUPERSEDED where they conflict
with this section** (notably D2/D3's fixed-ambient-`F` residual model and the `resUnits` tracker).
Round-2 `Defs.lean` and `MANIFEST.json` (61 units) are the current deliverables. Both were fully
elaboration-tested (below).

## R2.1 The one structural decision that fixes most defects

The round-1 root cause was modelling the residue side with a bare `resUnits : Subgroup Fˣ` over a
single fixed ambient `F`, with residue growth faked as `Algebra.adjoin F {z̄}` (= all of `F`, so
every degree-`g` descent collapsed to `g = 1`) and the residual map `R` landing in ambient
`F[z^{±1}]` (where an irreducible `ψ` over the *current* field splits, breaking K1). Round 2:

> **The stage carries the CURRENT residue field as a genuine `K : Subfield F`, and
> `R : A → LaurentPolynomial ↥K` lands in the CURRENT field's Laurent ring.**

Consequences: `ψ : Polynomial ↥σ.K` is genuinely prime in `↥K[z^{±1}]` (K1/width/ψ-order are
faithful); `F' = σ.nextField z̄ := Subfield.closure (↑K ∪ {z̄})` is a genuine degree-`g` extension
inside `F` (`σ.K ≤ σ'.K`, no collapse); the base field `σ.FQ : Subfield F` is fixed across the
tower (`TRANSstage` carries `σ'.FQ = σ.FQ`). The ambient `F` survives only as a big container
(`PROJECT_STATE.md` §4), now carrying `[Finite F]` (weaker than round-1 `[Fintype F]`, so the
concrete `GaloisField 2 2` gate elaborates).

## R2.2 The 10 `DEF` defects — one-line resolutions

| DEF | round-1 defect | round-2 resolution |
|---|---|---|
| DEF-1 | S3 (slot decomposition / Y-transcendence) absent | new **derived** unit `L2.slotDecomp`: graded-piece additivity from `strideRule`+`anchorCong`+`GRb` (distinct minimizing slots ⟹ distinct `z`-positions ⟹ no cancellation) |
| DEF-2 | S4 / current residue field absent; `adjoin F {z̄}` = all of `F` | `σ.K : Subfield F` current field; `R` over `↥K`; `F' = σ.nextField z̄ = K⟮z̄⟯`, genuine degree-`g` |
| DEF-3 | `U`, representatives, `V`, `T`-vector absent | `σ.reps : List (Polynomial ℤ_[p])` (the `U` list, all in `C` so current key adjoined separately) + `σ.Tvec : List (Polynomial ℤ_[p] × ℤ)` (exponent-vector pairs), `hTvec : Tvec.map Prod.fst = reps` |
| DEF-4 | S5 wrong scale (`−t·w(B)` for `−t·w_prev(B)`) | `σ.wPrev` (parent valuation) added; `hStretch : w B = e·wPrev B`; `hS5` position `−t·wPrev B`; base spot-check `dig(B)=ū·z^{−t·v(B)}` now comes out right |
| DEF-5 | `e=1` pinning missing | `he1t : e = 1 → t = 0` (P2), a `Stage` field |
| DEF-6 | S6a orbit group not constant | `σ.FQ : Subfield F` fixed base; `hS6a` scalar `c` ranges over `FQ`; `TRANSstage` preserves `FQ` |
| DEF-7 | S6b not "all current-field scalars" | `hS6b` scalar is any `a : (↥σ.K)ˣ` (current field units), no `resUnits=⊤` smuggling |
| DEF-8 | `thr` arbitrary | no free `thr`; `hS6b` threshold is literally `σ.wPrev σ.Φ` (the key's parent weight) |
| DEF-9 | `IsStandardLift` weaker than the displayed lift | `IsStandardLift` **is** the displayed formula `Φ^{eg}+Σ_{ψ_k≠0} t_k Φ^{ek}` with realizer conditions; monic/degree/weight/residual are the **theorems** `L3.liftMonic/liftWeight/liftResidual` |
| DEF-10 | `IsRecentering` assumes an unrelated stage | `IsRecentering` is a **field-by-field construction** relating `σ'` to `σ` (TRANS-RS items: `w'=w`, `wPrev'=wPrev`, `K'=K`, `FQ'=FQ`, `weightSet'=weightSet`, coefficient digits unchanged at the `digPrime` level) |
| DEF-11 | value group as `∃ f g, w f − w g = 1` | `hvalgrp : AddSubgroup.closure {n \| ∃ f g, … w f − w g = n} = ⊤` (generated subgroup) |
| IMPRECISE | `OrdPsiEq X` in Laurent (always false) | new `OrdPsiPoly` over `Polynomial K` + `HasAnchorK` (z-order via the anchored polynomial); no `ord_ψ` of a Laurent unit anywhere |

## R2.3 Per-unit FAITHLESS repairs (the 39 + the 3 vacuity collapses)

All keyed to the same `Stage` redesign. Highlights: `L1.baseStage_exists` now takes a genuine
`K0 : Subfield F` with `Nat.card ↥K0 = p^{deg φ}` (repairs the "`d ≤ [F:F_p]` insufficient"
finding — the caller supplies the subfield, so `d ∣ [F:F_p]` is its obligation). `L2.iaugRoot` is
restated **without a `Stage`** (the round-1 form forced `w Φ = 0` on a stage with `w Φ = h ≥ 1` —
vacuous); it is now the arithmetic ROOT base case over the trivial parent. `L3.liftExists` drops
`resUnits=⊤` and returns the displayed lift. `L4.TRANSv`/`TRANSviii_b` quantify `a ∈ σ.nextField z̄`
(genuine `F'`), not the vacuous self-adjoin. `L4.TRANSstage` produces `σ'` with `σ'.K = K⟮z̄⟯`,
`σ.K ≤ σ'.K` (genuine growth), `σ'.FQ = σ.FQ`. `L5.realCofin`/`realDomination`/`realConclusion` use
the parent-scale weight set + threshold `wPrev Φ` + position-0 pinning (no `fr`-trivialisation).
`L5.recRSland`'s RHS is the z'-anchor exponent `a' = μ` (not `OrdPsiEq X`). `L5.recVV`/`recLiftIndep`/
`recTRANSRS` consume the field-by-field `IsRecentering` (no longer circular).

## R2.4 Kept faithful-as-scoped (import/name adjustments only)

The audit's 15 faithful units are retained with the residue-tower type changes only: `L0.GRa–GRf`
(now generic over any field, applied at `↥K`), `L0.FactA_exists`, `L1.gaussVal`, `L2.keyResidualPow`,
`L2.strideRule`, `L4.TRANSii`, `L4.TRANSiv`, `L5.realRecursion`, `L6.moveReduceCommute`. The three
**FLAGGED-OK** scopings are kept and recorded as gaps below: `L2.iaugStep` (chord, not full hull),
`L5.landTransport` (determinacy, not the carry `Equiv`), `L6.ledgerCount` (single uniform `p^{−k}`).

## R2.5 Honest gaps (blueprint gaps — explicit, NOT silent weakenings)

- **G1 — `T` exponent-vector product identity.** `σ.Tvec`/`σ.reps` carry the `(representative, ℤ)`
  data and the "representatives are nonzero coefficients / current key adjoined separately" pins,
  but the graded-product identity `T = Π in(ũ_i)^{a_i}` and the transport `V' := Π in_{w'}(ũ)^{s b}·…`
  are **not** stated as `Stage` equations (the graded ring is deliberately not built, per §B2-DEF's
  structural decision). The load-bearing residual consequences ARE pinned (`hRΦ`, `hS5`); the raw
  exponent values are construction detail inside `TRANSstage`. **Flag for review.**
- **G2 — ambient-`F` sufficiency of the residue tower.** `F` must contain every residue field of
  a run; carried as `Nat.card ↥K0 = p^{deg φ}` in `baseStage_exists` and as `σ.nextField z̄ ⊆ F`
  (requires a root `z̄ ∈ F`). A per-stage bundled `F' : Type` model would avoid this but is heavier;
  the ambient model matches `PROJECT_STATE.md` §4. **Flag: correspondence `nextField z̄` = the
  note's `F'`, and that `F` is large enough.**
- **G3 — I-aug ROOT.** `L2.iaugRoot` is the arithmetic base case (trivial parent, `w = 0`); the
  full "§A initial cluster has positive slopes" is folded into `baseStage_exists`.
- **G4 — I-aug convexity.** `L2.iaugStep` states the chord inequality `ehg·(μ−j) < w(B_j)−w(B_μ)`;
  the "every continuing hull side is steeper" half is in the sketch, not the statement.
- **G5 — `TRANSvi/vii` as post-construction extractions** of `σ'.hRΦ`/`σ'.hS5`; the weight is in
  `TRANSstage`+`TRANSviii_b`+`TRANSv`. `TRANSstage` must build `σ'.hS6b` from the standalone
  `TRANSviii_b`, not from `σ'` (non-circularity flag).
- **G6 — `L5.landTransport` = determinacy**, not the carry `Equiv` (term-by-term ψ-digit equality
  is false, pass-9 finding 10). The ledger consumes determinacy + `P6ii` only.
- **G7 — lift-independence scope.** `L5.recLiftIndep` is graded/read-height only; digits below the
  read line are not lift-independent (Case-K-sharpened D.10 scope clause).
- **G8 — `L6.moveAffineBij`** states injectivity; the full affine-unitriangular bijection is
  `FactA` (surjectivity) + `moveReduceCommute` (reduction-compatibility) combined.
- **G9 — `L6.ledgerCount`/`measureExact`** use the single exponent `k` (uniform `p^{−k}`); the
  per-equation alphabet-factor bookkeeping (rev-D¹⁰) is collapsed, adequate for measure-exactness.
- **§C composition** remains out of scope (D.11 defers it, pass-8 gap 7).

## R2.6 Elaboration-test record (round 2)

`Defs.lean` compiles green (`lake env lean LeanUrat/Moves/Defs.lean`, exit 0, no `sorry`, no
axiom). **All 61 `MANIFEST.json` statements** were elaborated together against the `Defs` body
(`:= sorry`, `lake env lean`, exit 0, exactly 61 `sorry` warnings, zero errors), including the
`↥σ.K` residual type, `σ.nextField`, `OrdPsiPoly`/`HasAnchorK`, the field-by-field `IsRecentering`,
the displayed `IsStandardLift`, and the concrete `GaloisField 2 2` gate (with its
`Fact (Nat.Prime 2)` + `Fintype.ofFinite` instances). The def-introducing L1 units' signatures
(`gaussVal`, `baseWeight`, `baseResidual` into `↥K0[z^{±1}]`) were confirmed to elaborate. The DAG
was verified acyclic (DFS) with all 61 deps resolving; per-layer counts L0=9, L1=5, L2=11, L3=7,
L4=10, L5=15, L6=4.

---

# ROUND 3 (2026-07-26) — repair of the 29 rejected units after the round-2 STOP-THE-LINE

Round-2 was rejected by `lean/notes/MOVES_LEAN_SEMAUDIT2_2026-07-26.md` (29 FAITHLESS + 2 IMPRECISE
+ 4 FLAGGED-OK + 26 faithful; five structural defects still open: DEF-1, DEF-2 (S4 half), DEF-3,
DEF-8 (transition/history half), DEF-10, plus 5 fresh "pathological-stage vacuity" findings). This
section records the round-3 repair. **Hard concurrency constraint honored:** `Defs.lean` and
`MANIFEST.json` are UNCHANGED (the round-2 fan-out proving the 32 cleared units reads them). All
round-3 material lives in two NEW files — `lean/LeanUrat/Moves/DefsT.lean` (tower/transition
extensions, imports `Defs`, COMPILES green, no `sorry`/axiom) and
`lean/LeanUrat/Moves/MANIFEST_R3.json` (the 29 restated units). R3 unit files use the `_R3.lean`
suffix (no collision with any round-2 file).

## R3.1 `DefsT.lean` — the new vocabulary (imports `Defs`, edits nothing)

The audit's core finding is *pathological-stage vacuity*: a round-2 `Stage` can describe an abstract
residual calculus with no tower behind it. Since `Stage` cannot be edited, `DefsT` adds the missing
laws as predicates/structures LAYERED on `Stage`, and the restated units either CONCLUDE them
(`baseStage_exists`, `slotDecomp`, `TRANSstage`, `recTRANSRS`) or CONSUME them.

- **`SlotDecomp σ` (S3, DEF-1).** Two conjuncts: DECOMPOSITION (`R` additive across a graded piece —
  the round-2 substitute) *and* the half the audit demanded — INDEPENDENCE / `Y`-transcendence: a
  vanishing `Y`-combination `Σ_j R(B_j)·(RΦ)^j` all of whose nonzero slots live in ONE graded piece
  `γ` (so their `z`-positions are distinct by `anchorCong`+stride) is termwise zero.
- **`CoeffFieldLaw σ` (S4, DEF-2).** Three conjuncts: the degree-0 coefficient field `= K` (every
  `Kˣ` realized as a digit scalar — the "theorem-shaped law connecting `K` to the residual data");
  fixed-position (fixed-`Y`) lines are `K`-lines; the exponent group `= ℤ` generated by `z = T 1`.
- **`StageWF σ` (DEF-3 + the 5 fresh findings).** `wPrev` is a valuation (`wPrev_mul`/`wPrev_ult`);
  `reps` is nonempty and contains `p`; `reps_pinned` — representatives have CANONICAL (scalar-1)
  monomial residuals `z^{−t·wPrev(ũ)}` (the RESIDUAL CONSEQUENCE of the T-vector product identity
  `T = Π in(ũ)^a`, constraining `R` to the representatives so `R` is no longer "an abstract
  Laurent-valued operation"); `K_gen` — `K` is generated by the digit scalars (the localization
  theorem connecting `K` to `R`).
- **`TransitionData σ σ' Φhat e' h' zbar` (D.7, DEF-8 + G5).** The child laws as a bundle to be
  CONSTRUCTED: `child_wPrev` (the HISTORY invariant `σ'.wPrev = σ.w`), `threshold`
  (`σ'.wPrev Φ̂ = σ.w Φ̂` — the DEF-8 clean threshold), `child_slotmin`, genuine residue growth
  (`σ'.K = K⟮z̄⟩ ⊇ K`, `σ'.FQ = σ.FQ`), `child_reps` (grows by the outgoing key `Φ`).
- **`RecenterSubstLaw` / `IsRecenteringT` (D.10, DEF-10 + G7).** The common-localization
  substitution `z' = z − c̃` at the EVALUATION level, SCOPED to coefficient (read-height) data;
  `IsRecenteringT = IsRecentering ∧ RecenterSubstLaw` (round-2 `IsRecentering` related digits only
  at the SAME `z̄` — the change-of-transcendental was absent).
- **`DigitSystem n α` / `IsSolution` / `numPinned` (P6ii, D.11).** A `k`-equation unitriangular
  digit system (each pinned coordinate a function of strictly-earlier coordinates); the count law is
  `|α|^{n−k}`.

## R3.2 One-line resolution per audit demand

| Audit demand | Round-3 resolution |
|---|---|
| S3 genuine slot decomposition (reject residual additivity) | `SlotDecomp` (decomp **+** degreewise independence); `L2.slotDecomp` concludes it |
| S4 degree-0 field ↔ `K`, fixed-`Y` lines, exponent group | `CoeffFieldLaw` (3 clauses); produced by `baseStage_exists` and `TRANSvi` |
| T exponent-vector PRODUCT identity + transported `V'`, constraining `R` + history invariant | `StageWF.reps_pinned` (canonical residual consequence) + `StageWF.K_gen` + `TransitionData.child_wPrev`/`child_reps` (history: data came from the parent) |
| transition threshold `σ'.wPrev Φ̂ = σ.w Φ̂`, consumed by `TRANSviii_b` (weight `= ν`, `a=0`) | `TransitionData.threshold`; `TRANSviii_b` uses `σ.w Φhat < ν`, concludes `σ.w B = ν`, guards `a≠0 → B≠0` |
| `IsRecentering` + cross-stage substitution, scoped to read-height | `IsRecenteringT`/`RecenterSubstLaw`; `recSubst`/`recLiftIndep` scope `f` by `inC σ.Φ f` |
| `TRANSi` with DIV/standard-lift | added `hlift`, `hψ : Irreducible ψ`, root `zbar`/`hzbar` |
| `TRANSiii` with irreducibility/root | added `hψ`, `hψz`, `zbar`, `hzbar` (F' a field ⟹ DIV(iii) nonvanishing) |
| `TRANSv` without the `a=0` bug | conclusion `∃ B, inC ∧ digPrime = a ∧ (a≠0 → B≠0)` (B=0 realizes a=0) |
| `TRANSstage` constructs (not assumes) the laws | concludes `∃ σ', TransitionData σ σ' … ∧ StageWF σ'` |
| L5.real* trio = genuine D.9 recursion/domination | `realRecursion` ties to `hlift`; `realCofin` = the Bézout covering (no tail assumption); `realDomination` = the inductive step (I-aug + liftWeight) |
| `landTransport` with slot-weight equality | added `hslotw : ∀ j<N, w(B j) = w(B' j)` |
| `landTwoSided` with pinned vertex digit + transported pattern | RHS gains the `landVertexDigit` clause (`R f = ψ^μ·q`, `dig'(B_μ) = z̄^{μthg}·eval q`) |
| `moveReduceCommute` with monicity | added `hmon : Φhat.Monic` (degree preserved under reduction) |
| `measureExact` connected to a move | consumes `hmove` (moveAffineBij + FactA bijection) + `hcyl` (landTwoSided digit cylinder) + `ledgerCount`, not an assumed cardinal law |
| `psiNotDvd` with Monic | added `hmon : ψ.Monic` (excludes `cX`) |
| `P6i` with `F_Q`-linearity + image description | 4 conjuncts: inj, add, `F_Q`-linear scaling, monomial-image |
| `P6ii` as `k`-equation unitriangular count | over `DigitSystem`: `Nat.card {solutions} = |α|^{n−numPinned}` |
| base L1 units with key/read-index hyps | `baseWeight`/`baseResidual`/`baseStage_exists` gain `Monic`, `deg≥1`, `1≤e`, `1≤h`, `gcd=1`, `Irreducible φ̄`, `card K0 = p^{deg φ}`; `baseStage_exists`/`base_gate` conclude `StageWF ∧ SlotDecomp ∧ CoeffFieldLaw` |

## R3.3 What could NOT be fully satisfied (explicit round-3 gaps — carried forward)

- **G1′ — the raw graded T-vector product `T = Π in(ũ_i)^{a_i}` is still not an equation.** The
  graded ring stays unbuilt (§B2-DEF's structural decision). Its CONSUMABLE residual consequences
  ARE now laws (`StageWF.reps_pinned` = canonical scalar-1 representative residuals; `hRΦ`;
  `TransitionData` reps/threshold transport). The literal integer exponent vector and its
  factorwise transport `V' := Π in_{w'}(ũ)^{s·a}·in_{w'}(Φ)^{t}` remain a construction detail inside
  `TRANSstage`, not a `Stage`/`TransitionData` equation.
- **G5′ — `TRANSvi`/`TRANSvii` are post-construction verifications.** They now CONSUME
  `TransitionData` and conclude the genuine S4′/S5′ content (`CoeffFieldLaw σ'`, the transported
  monomial digit at `−σ'.t·σ'.wPrev` with `σ'.wPrev B = σ.w B`), so they are no longer bare
  projections of `σ'.hRΦ`/`σ'.hS5` — but the objects they verify are built inside `TRANSstage`
  (non-circularity flag: `σ'.hS6b` must come from the standalone `TRANSviii_b`).
- **G6′ — `landTransport` is DETERMINACY**, not the term-by-term carry `Equiv` (false, pass-9
  finding 10). Now honest with `hslotw`; the full carry recursion is still not stated.
- **G7′ — recentering lift-independence/substitution is READ-HEIGHT/COEFFICIENT-SCOPED.** Digits
  strictly below the read line are NOT lift-independent (D.10's Case-K-sharpened scope). `recSubst`
  and `recLiftIndep` quantify `f` only over `inC σ.Φ f`. For strict coefficients at `e=1` the
  substitution is trivially the identity (position-0 constants); its non-trivial `(z+c̃)^a` content
  lives in the anchor, stated at the anchored-polynomial level (`recRSland`), not below the line.
- **G9′ — L6 counting is still abstract over `DigitSystem`.** `measureExact` is now genuinely
  connected to a move (`hmove` + `hcyl` + `ledgerCount`), but the bridge from `Stage`-level strata
  to concrete `ZMod (p^N)` boxes — instantiating `hmove` from `OM/DevBijection` — is still the
  least-developed layer (the round-3 statement TAKES `hmove`/`hcyl`/`E` as hypotheses; a future unit
  must supply them from `moveAffineBij`+`FactA`+`landTwoSided`).
- **Not attempted:** the S4 "fixed-`Y` line" and "exponent group" clauses of `CoeffFieldLaw` are
  provable but partly automatic in the `LaurentPolynomial ↥K` model (each position is a `K`-line by
  construction); they are stated as genuine laws but their content is thinner than the abstract
  localization picture. §C composition remains out of scope (D.11 defers it).

## R3.4 Elaboration-test record (round 3)

`DefsT.lean` compiles green (`lake env lean LeanUrat/Moves/DefsT.lean`, exit 0, no `sorry`, no
axiom; olean built via per-file `lake env lean -o`, never `lake build`). **All 29 `MANIFEST_R3.json`
statements** were elaborated TWICE: first hand-written, then REGENERATED verbatim from the manifest
`statement` fields and re-elaborated (`:= sorry` against the `Defs`+`DefsT` preamble with stub
`gaussVal`/`baseWeight`/`baseResidual` defs and the `GaloisField 2 2` gate instances; `lake env
lean`, exit 0, exactly 29 `sorry` warnings, zero errors) — confirming no transcription drift. The
tested statements: `L1.{baseWeight, baseResidual, baseStage_exists, base_nonvacuity_gate}`,
`L2.{slotDecomp, psiNotDvd, P6i, P6ii}`, `L4.{TRANSi, TRANSiii, TRANSv, TRANSvi, TRANSvii,
TRANSviii_a, TRANSviii_b, TRANSstage}`, `L5.{landTransport, landTwoSided, realRecursion, realCofin,
realDomination, recSpecies, recVV, recLiftIndep, recSubst, recRSland, recTRANSRS}`,
`L6.{moveReduceCommute, measureExact}` — the exact 29 in the audit's "Units unsafe to prove as
stated" list.

---

# ROUND 4 (2026-07-26) — the design escalation: real objects for the 17-unit hard core

Round 3 was rejected by `lean/notes/MOVES_LEAN_SEMAUDIT3_2026-07-26.md` (17 FAITHLESS, 1
IMPRECISE, 11 FLAGGED-OK; G1′/G5′/G7′/G9′/S4-partial all unacceptable). Three audits converged
on the same conclusion: the residual-only model — `R : A → LaurentPolynomial ↥K` as abstract
data with Prop laws — **erased structure that four clusters of the accepted proof are
statements about**: (i) the S4 coefficient localization and its exponent group, (ii) the T
exponent-vector product law, (iii) the D.10 cross-stage common-localization substitution,
(iv) the D.8 landing cylinder's transported (triangular) pattern. This round is a design
decision, not a patch. Deliverables: `lean/LeanUrat/Moves/DefsCore.lean` (imports
`Defs`+`DefsT`, both UNCHANGED; compiles green, no `sorry`/axiom),
`lean/LeanUrat/Moves/MANIFEST_CORE.json` (the 17 units restated + 3 machine-checked
corrections; all 20 elaboration-tested), and this section.

## R4.0 The decision: **(C) hybrid — build the minimal real objects where structure was erased; keep faithful residual-level laws where it was not, bundled into a constructed-and-transported core**

One paragraph of rationale. Option (A)-pure (build `gr_w(A)`, its localization, and the
graded module isomorphisms as mathlib objects) was rejected because the four failures do not
need the full graded ring — each has a MINIMAL faithful object, three of them off-the-shelf —
and a bespoke graded-ring layer would move the trust boundary into a large pile of new
definitions (the thing this repo's discipline exists to avoid). Option (B)-pure (a fourth
residual-level re-encoding) was rejected because the audits are RIGHT that (i)–(iv) cannot be
expressed at that level: I verified the sharpest instance myself — the D.1(b) tie laws
(`w_strict`, `w_jump`, `R_neg`) are formally underivable from the round-2 `Stage` fields, so
round 3's unconditional `L2_slotDecomp` was not just unintegrated but UNPROVABLE, exactly as
audit #3 suspected. The hybrid: (1) the D.10 common localization is `RatFunc F` — a genuine
mathlib field of fractions containing both frames' Laurent rings, with the substitution law
stated at the TRANSCENDENTAL variable (injective on Laurent polynomials — kills the
finite-field-evaluation defect) for EVERY `f`; (2) the T product law is carried EXACTLY with
no graded ring by a two-element trick: `T = Π in(ũᵢ)^{aᵢ}·Y^t` ⟺ `R(P) = R(Q) ∧ w(P) = w(Q)+1`
for the literal elements `P = Π ũᵢ^{aᵢ⁺}·Φ^{t⁺}`, `Q = Π ũᵢ^{aᵢ⁻}·Φ^{t⁻}` of `A` (proof:
`R(P)·R(Q)⁻¹ = ([P]/[Q])·T^{−(wP−wQ)}`, so the equation pins `[P]/[Q] = T`); (3) S4 is
characterized on the localization's actual GENERATORS (coefficient-monomial products), where
the clauses are no longer automatic; (4) the D.8 transported pattern is an EXECUTABLE carry
recursion (`%ₘ`/`/ₘ` at monic ψ) and the stratum's pattern is the canonical ψ-adic
`IsDevelopment` — real data structures, not erased. Everything is then integrated by a single
architecture move the audits demanded three times: the well-formed package `StageCore` is
**CONSTRUCTED by the base, TRANSPORTED by both transitions, and CONSUMED by every unit
needing provenance** — no law is ever claimed for a bare `Stage`.

## R4.1 `DefsCore.lean` inventory (all new; `Defs`/`DefsT` untouched)

- `ratX F`, `ratXShift c` : units of `RatFunc F` (the variable `ζ` and `ζ + c`);
  `Stage.ratRes`, `Stage.ratResShift` : the residual embedded in `RatFunc F` via
  `LaurentPolynomial.eval₂` at those units; **`RecenterSubstCore σ σ' cc`** : `∀ f,
  σ'.ratRes f = σ.ratResShift c̃ f` — D.10's display `R'(f)(z') = R(f)(z' + c̃)` verbatim.
- `Stage.tvecNum`, `Stage.tvecDen`, **`TvecLaw`** : the T-vector product law (§R4.0(2)).
- `IsCoeffProd`, `IsUnitMonProd`, **`CoeffFieldLawCore`** : (a) every `Kˣ`-scalar realized at
  its forced position; (b) equal-weight coefficient-product residual ratios are `K`-CONSTANTS
  (`(L^coeff)₀ ⊆ K` — forces equal `z`-positions across products, NOT automatic); (c) the
  degree-0 exponent group — position differences of equal-weight `L`-monomial products —
  generates all of `ℤ` (`= ⟨class of z⟩`, `z` at position 1).
- `Stage.slotImages` : the slot-image set at weight γ (for P6i's image-as-span).
- **`StageCore`** : parent-valuation laws, genuine reps, the three D.1(b) tie laws
  `w_strict`/`w_jump`/`R_neg` (NEW — see R4.0), `TvecLaw`, **`prevIaug : e·wPrev(Φ) < h`**
  (machine-checked finding 1, below), `SlotDecomp`, `CoeffFieldLawCore`.
- **`TransitionCore`** : `TransitionData` + `child_Tvec` (the FACTORWISE vector transport
  `σ'.Tvec = map (s'·) σ.Tvec ++ [(Φ, s'·t)]` — D.7(vi)/(vii)'s `V' ↦ T' = V'^{s'}Y'^{t'}` as
  a literal list equation) + `child_dig` (the child residual BUILT from parent ψ-digits:
  scalar `dig'(B)·z̄^m`, position `−t'·σ.w B`).
- **`IsRecenteringCore`** : `IsRecentering` + `coeff_R` (coefficient residuals LITERALLY
  unchanged, cast-free via `ratRes`) + `reps_eq`/`Tvec_eq` (T coefficient-pure, untouched).
- `carryStep`/`carryRec`/**`carryDigit`** : the D.8 triangular carry recursion, executable;
  **`StratumData`** (anchor + canonical ψ-adic pattern via `IsDevelopment` at key ψ);
  **`LandingCylinder`** (BOX/VERTEX/side-line + the anchored slot terms reproducing the
  pattern under `carryDigit` — the transported pattern as data).

## R4.2 The three machine-checked prover findings (mandatory inputs, folded in)

1. **`L4.TRANSviii_b`'s true blocker is the previous-read (I-aug) law** (prover note in
   `L4_TRANSviii_b_R3.lean`): the offset-P-lift summand weights clear only `μ_k > h/e`; MOVES
   ~2299-2303 closes the (S6b) application via `h/e > w_prevprev(Φ_prev)` — i.e.
   `e·wPrev(Φ) < h` — which NO `Stage` field supplied (`wPrev Φ` was free, and enlarging it
   weakens `hS6b` without touching `w`/`R`/`digPrime`). The prover explicitly corrected audit
   #3's emphasis: S3/S4 was NOT the blocker there. **Resolution: `StageCore.prevIaug` is
   exactly this law** — it holds at the base (`wPrev(φ) = v(φ) = 0 < h`), is LITERALLY `IAug`
   for the increment child (`h' > e'·w(Φ̂) = e'·wPrev'(Φ̂)`), and transports through a
   recentering (`wPrev(Φ − t) = wPrev(Φ)` under the strict inequality + tie laws). The
   corrected `TRANSviii_b` adds the one hypothesis `hcore : StageCore σ`.
2. **`L5.landTransport` is FALSE as stated** (machine counterexample in
   `L5_landTransport_R3.lean`: base stage, `Φhat = 1 + X` untied to σ; equal slot residuals
   and weights, unequal totals via total residual cancellation of the minimal block).
   **Resolution: restated with the prover's prescribed tie** — `Φhat` a standard lift with
   `K1At σ.w Φhat (σ.w Φhat)` + `StageCore` (SlotDecomp): distinct ψ-orders make the
   cancellation impossible.
3. **`L6.moveReduceCommute` is FALSE at `M = 0`** (certified disproof
   `L6_moveReduceCommute_statement_false` in `L6_moveReduceCommute_R3.lean`).
   **Resolution: `1 ≤ M` added**; the corrected statement is the already-fully-proven
   `L6_moveReduceCommute_of_one_le` from that file, restated under the fenced name.

## R4.3 Audit #3, answered point by point (quote → answer; the next auditor starts here)

**Decisive defect 1.** *"`StageWF.reps_pinned` is not the residual consequence of a transported
`T`-vector and is generally false for outgoing keys."* — Conceded and REMOVED. `StageWF` is
retired from the core path (nothing in `MANIFEST_CORE` concludes or consumes it). The honest
residual consequence of `T = Π in(ũᵢ)^{aᵢ}·Y^t` is now the exact equation `TvecLaw`
(`R(tvecNum) = R(tvecDen)` at weight gap 1 — no scalar-1 pin on any representative; the
outgoing key's `c·z^k` monomiality is already `hS5`/D.3(b) and needs no new law). Transport is
`TransitionCore.child_Tvec`, factorwise and literal.

**Decisive defect 2.** *"`CoeffFieldLaw` does not characterize the coefficient localization or
its exponent group."* — Replaced by `CoeffFieldLawCore`, whose clauses quantify over the
localization's GENERATORS: clause (b) states `(L^coeff)₀ ⊆ K` on equal-weight
coefficient-monomial PRODUCTS (`IsCoeffProd`) — `R f = C d · R g` forces equal positions
across products, which is NOT automatic in the flattened codomain (it needs S5's forced
positions + `wPrev` additivity — precisely the `(L^coeff)₀ = F` content); clause (a) is `⊇`;
clause (c) restricts the exponent set to `IsUnitMonProd` pairs of equal weight (degree-0
monomials of `L` mod `Kˣ`) and states the group is `ℤ` — infinite cyclic on the generator `z`
(position 1). What is NOT built: the localization as a ring with a universal property
(honest-impossible list, R4.5).

**Decisive defect 3.** *"`TransitionData` contains no `Tvec`/`V'` transport and does not
ensure child S3/S4."* — `TransitionCore` adds the transport as data (`child_Tvec` — the
in_{w'}-image of T's vector over `reps' = reps ++ [Φ]` with the Bézout re-pinning `s'`, key
exponent `t' = σ'.t`; this IS D.7(vi)'s `V'` and D.7(vii)'s `T' = V'^{s'}Y'^{t'}` in vector
form) and the child-residual construction record (`child_dig`). Child S3/S4 are ENSURED by
`L4_TRANSstage`'s conclusion `StageCore σ'` (which contains `SlotDecomp σ'` and
`CoeffFieldLawCore σ'`), not by `TransitionData` alone — deliberately, so that
`TRANSvi`/`TRANSvii` verify recorded construction data instead of projecting a complete child
(the G5′ demand).

**Decisive defect 4.** *"The recentering law is restricted to old coefficients, whereas D.10's
read-height identity applies to every polynomial's graded residual."* — `RecenterSubstCore`
quantifies **every `f`** with no coefficient restriction. The read-height scope is honest by
construction, not by restriction: `σ'.R f` IS the graded (read-height) data of `f`; digits
strictly below the read line are not present in either side (Case-K clause satisfied without
any quantifier narrowing).

**Decisive defect 5.** *"`recRSland` consumes an arbitrary-`f` cross-frame identity that
`IsRecenteringT` does not provide."* — The identity is now PROVIDED: `L5_recTRANSRS`
constructs `RecenterSubstCore` for the actual move, `L5_recSubst` derives it from the
recorded Laurent-level coefficient data (`IsRecenteringCore.coeff_R`, K1(Φ'/v) from `recVV`,
child slot decomposition) — the D.10 proof itself: at `e = 1` coefficient residuals are
position-0 constants, hence substitution-invariant, and the two slotwise expansions assemble.
`recRSland` then legitimately consumes `hsub : RecenterSubstCore` and displays the anchored
transform `ζ^{a'}·Ranch'(ζ) = (ζ+c̃)^a·Ranch(ζ+c̃)` — the `(z+c̃)^a` anchor-monomial factor
explicit.

**Decisive defect 6.** *"`measureExact` still assumes the move equivalence and cylinder
identification instead of deriving them for an actual move."* — The move equivalence
(`hmove`) is GONE from the statement: it is derived inside the proof from `hcodeN`
(coordinate surjectivity) + `hstratN` (the abstract family pinned to the ACTUAL
`StratumData` locus) + `L5.landTwoSided` at each point's development (`L0.FactA_exists`) +
`hcylN` (the digit system pinned to the ACTUAL `LandingCylinder` through the development
coordinates). What remains hypothesis: the level-`N` coordinates themselves and the
D.3(e)(ii) DigitSystem presentation OF THE ACTUAL CYLINDER — named, locus-specific, and on
the honest-impossible list (R4.5), no longer free-floating counting data.

**Fresh-eyes 1 (pathological stages).** *"`σ.Tvec` … can remain decorative and unrelated to
`R`, `T`, `V`, or transition transport"; "`wPrev` … is not related globally to the current
valuation"; "`K_gen` is also not a localization theorem"; "genuine OM stages can fail
`StageWF`" (scalar-1).* — `TvecLaw` makes `Tvec` load-bearing (it pins `T` through `R`);
`wPrev` is a valuation in `StageCore` and globally tied at transitions (`child_wPrev`,
`threshold`, `prevIaug`); `K_gen` is dropped for `CoeffFieldLawCore` (the localization
characterization); scalar-1 is gone (defect 1). Additionally the round-4 analysis found and
closed a DEEPER pathology the audits circled: the D.1(b) tie laws (`w_strict` strict-triangle
equality, `w_jump` cancellation at a weight jump, `R_neg`) are underivable from `Stage` — they
are now `StageCore` fields, constructed at the base and re-proved for each child (where `w'`
is the definitional slot minimum).

**Fresh-eyes 2 (pathological children).** — See defect 3; additionally `TRANSstage` now
REQUIRES the full parent core (audit: "does not assume a well-formed parent").

**Fresh-eyes 3 (recentering scope).** *"For an `e = 1` coefficient, this is essentially the
trivial constant-digit part … It is also weaker than a polynomial/common-localization
identity because it only compares evaluations at unit points. Over a finite field, equality
on the available evaluation points need not identify Laurent polynomials."* — Both halves
answered by the `RatFunc` design: the identity is at the TRANSCENDENTAL point (evaluation
`LaurentPolynomial ↥K → RatFunc F` is injective: a nonzero Laurent polynomial times `ζ^n` is
a nonzero polynomial, and `RatFunc F` is its fraction field — so the stated equation carries
the full Laurent-polynomial identity), and it holds for every `f`, where the non-trivial
content (key slots, the `(z+c̃)^a` factor) lives — not only for constant coefficient digits.

**Fresh-eyes 4 (`DigitSystem` scope).** *"Those omissions are acceptable for `L2.P6ii`, but
not for `L6.measureExact` as a claimed D.11 endpoint."* — `P6ii` is untouched (FLAGGED-OK).
`measureExact` now consumes `DigitSystem` only through the locus-pinning hypotheses
(defect 6): the bridge OM-development → coordinates is the named jet-coordinate gap, R4.5.

**Per-unit answers (the 17).** `L1.baseResidual` — adds `1 ≤ e`, `1 ≤ h`, `gcd e h = 1`, and
replaces the cardinality proxy with the compatibility itself: `emb : AdjoinRoot φ̄ ≃+* ↥K0`
(the residue quotient identified with `K0` by a SPECIFIED isomorphism, used by the def).
`L1.baseStage_exists` / `L1.base_nonvacuity_gate` — conclude `StageCore` (not `StageWF`),
with the base T-vector pinned literally (`Tvec = [(C p, σ.s)]`). `L2.slotDecomp` — no longer
unconditional: carries the three tie laws as hypotheses (the audit's "no provenance" point
was correct — see R4.0; with them the derivation via forced positions + GRb closes, and
consumers get `SlotDecomp` from `StageCore` anyway). `L2.P6i` — restated per-piece at fixed
`γ`: injectivity ON GRADED CLASSES (`f − f' = 0 ∨ γ < w(f − f')`), per-piece additivity,
`F_Q`-scaling of EVERY piece element, and the image description in BOTH directions against
`AddSubgroup.closure (slotImages γ)` (the additive span of the slot images — the audit's
"per-piece `F_Q`-linear image-as-slot-span theorem"). `L4.TRANSvi` — concludes
`CoeffFieldLawCore σ' ∧ TvecLaw σ'` from the `TransitionCore` records (no `hRΦ` projection —
that is a `Stage` field already). `L4.TRANSvii` — concludes the CROSS-STAGE digit
construction (parent ψ-digit × explicit `z̄^m` frame unit at position `−t'·σ.w B`, plus the
history clause `σ'.wPrev B = σ.w B`). `L4.TRANSviii_a` — forced position `−t'·(γ+jh)`
INSTANTIATED, child scale `σ'.w B = e'·(γ+jh)` explicit, constant orbit `c ∈ FQ`, and the
"fixed z̄-monomial class" as `∃ m` BEFORE `∀ c`. `L4.TRANSstage` — consumes `StageCore σ`,
returns `TransitionCore ∧ StageCore σ'` (transport + child S3/S4/T'/prevIaug constructed).
`L5.landTwoSided` — the stratum carries its canonical ψ-adic PATTERN (`IsDevelopment` at ψ)
and the cylinder carries the TRANSPORTED pattern via the executable `carryDigit` recursion
(BOX/VERTEX with the pinned `T(μm̂−a)` unit + one unitriangular equation per transported
digit); this is D.8's triangular data as structure. `L5.recSpecies` — adds `1 ≤ g`,
monic/irreducible ψ, and the explicit REAL hypothesis `hreal` (the D.9(d) realization the
audit demanded). `L5.recVV` — NO `σ'` in the statement: both conclusions (`w(Φ−t) = w(Φ)`,
`K1At σ.w (Φ−t)`) are parent-frame statements derived by the g = 1 instance of D.5 —
non-circular by construction. `L5.recLiftIndep` — every `f`, at the residual level in the
common localization (defect 4). `L5.recSubst` — now a DERIVATION of the full
`RecenterSubstCore` (defect 5). `L5.recRSland` — see defect 5. `L5.recTRANSRS` — assumes
`StageCore σ`, constructs `IsRecenteringCore + RecenterSubstCore + StageCore σ'` (child
S3/S4 + the vector, reps, coefficient residuals recorded unchanged). `L6.measureExact` —
defect 6.

**Declared-gap verdicts.** *G1′ unacceptable* → resolved: the product law IS an equation
(`TvecLaw`) and the transport IS an equation (`child_Tvec`); `TRANSstage`/`TRANSvii`/
`recTRANSRS` now claim exactly what these interfaces construct. *G5′ unacceptable* →
resolved: `TransitionCore` records S4/T' construction data; `TRANSvi`/`TRANSvii` verify
against records produced by `TRANSstage`. *G6′ acceptable only for landTransport* → kept as
determinacy, but restated with the machine-checked tie (R4.2(2)); the carry `Equiv` content
now lives in `landTwoSided`'s `carryDigit` clauses. *G7′ unacceptable* → resolved: every-`f`
scope (defect 4). *G9′ unacceptable for the endpoint* → resolved for the move equivalence;
the jet-coordinate presentation remains a named hypothesis (R4.5). *S4 partial unacceptable*
→ resolved: `CoeffFieldLawCore` on monomial products (defect 2).

## R4.4 Elaboration-test record (round 4)

`DefsCore.lean` compiles green (`lake env lean LeanUrat/Moves/DefsCore.lean`, exit 0, no
`sorry`, no axiom; olean built via `lake env lean -o`, never `lake build`). **All 20
`MANIFEST_CORE.json` statements** (17 core + 3 corrections) were elaborated TWICE: first
hand-written, then REGENERATED verbatim from the manifest `statement` fields
(`:= sorry` against the `Defs`+`DefsT`+`DefsCore` preamble with the stub `baseResidual` def
and the `GaloisField 2 2` gate instances; `lake env lean`, exit 0, exactly 21 `sorry`
warnings = 1 stub + 20 statements, zero errors) — no transcription drift.

## R4.5 What remains honestly impossible without building the full graded ring (explicit)

1. **The graded module isomorphism `gr_γ(A) ≅ ⊕_j gr^C_{γ−jh}` as a mathlib iso of built
   modules.** We state its complete element-level content (`SlotDecomp` decomposition +
   independence, `P6i` per-piece injectivity/additivity/`F_Q`-scaling/image-as-span), which
   is everything D.3(e) says the ledger consumes — but the OBJECT `gr_γ(A)` (quotient
   `A_{≥γ}/A_{>γ}`) and the map itself are not constructed.
2. **The localizations `L`, `L^coeff` as rings with universal properties.** `TvecLaw` pins
   `T` and `CoeffFieldLawCore` pins the degree-0 field and exponent group ON GENERATORS;
   the abstract monoid of `⟨U ∪ {Y}⟩`-monomials and the statement "`L₀ = F[z^{±1}]`" as a
   ring isomorphism are not built (the model takes `L₀ := LaurentPolynomial ↥K` by fiat —
   the standing D2 flag since round 1).
3. **D.3(e)(ii)'s global jet-coordinate system** (Fact A applied down the WHOLE tower,
   giving literal digit coordinates on every coefficient space, in which strata/cylinders
   are digit cylinders). This needs the full read-history recursion (§C territory) and is
   consumed by exactly one unit (`L6.measureExact`) as the named locus-specific hypotheses
   `codeN`/`ΘN`/`EN`/`hcylN`. Everything else in D.11's chain is derived.
4. **The upward (inverse) direction of the carry transport as a function.** `carryDigit` is
   the downward recursion; uniqueness of inversion on actual loci is a theorem the
   `landTwoSided` iff encodes, but no inverse FUNCTION (pattern ↦ slot data) is defined —
   defining it well requires the graded pieces as types (item 1).
5. **§C composition along read histories** — deliberately out of scope (D.11 defers it;
   pass-8 gap 7); no round-4 unit claims it.

---

# ROUND 5 (2026-07-26, FINAL) — the four audit-4 demands, resolved by building the localization objects

Audit #4 (`lean/notes/MOVES_LEAN_SEMAUDIT4_2026-07-26.md`) left 8 FAITHLESS units
(`L1.baseStage_exists`, `L1.base_nonvacuity_gate`, `L2.P6i`, `L4.TRANSvi`, `L4.TRANSviii_a`,
`L4.TRANSstage`, `L5.landTwoSided`, `L5.recTRANSRS`) behind four concrete demands. The round-5
charge carried an explicit stopping rule: per demand, either (a) a compiling construction that
satisfies it (small localization objects now permitted for real), or (b) record the
graded-ring boundary as the honest terminal state — and no fifth defect-shifting
approximation. Deliverables: `lean/LeanUrat/Moves/DefsL.lean` (imports `Defs`+`DefsT`+`DefsCore`
UNCHANGED; compiles green via `lake env lean`, no `sorry`; its two lemmas' axiom footprint is
Lean core exactly), `lean/LeanUrat/Moves/MANIFEST_FINAL.json` (the 8 units restated;
elaboration record below), and this section.

## R5.0 The one construction that unlocks all four: `L = L₀[T^{±1}]`, concretely

D.1(e) — proved once inside the accepted §B2-DEF — states that the stage localization
`L = 𝒢[⟨U ∪ {Y}⟩⁻¹]` with its degree-1 unit `T` is CANONICALLY `L₀[T^{±1}]`, via
`x ↦ R(x)·T^{deg x}` on homogeneous elements. Under the standing round-1 codomain fiat
(`L₀ := LaurentPolynomial ↥σ.K` — the D2 flag, unchanged since round 1), the right-hand side
is a concrete mathlib ring: `LTwo ↥σ.K := LaurentPolynomial (LaurentPolynomial ↥σ.K)` (inner
variable `z`, outer variable `T`). `DefsL` therefore defines the initial-form map
`Stage.grRes f := C (σ.R f) · T (σ.w f)` and the ACTUAL unit `locT` (the outer variable), with
`R(f) = [f]·T^{−w(f)}` DEFINITIONAL (`grRes_mul_T_neg`). Faithfulness argument, stated once
and relied on throughout: the round-4 tie laws (`w_strict`/`w_jump`/`R_neg`, in `StageCore`)
make `R` injective on graded classes ("equal weight ∧ equal `R`" ⟺ "equal initial form" — the
`L2.P6i` clause-1 content, derivable from the tie laws); hence for any GENUINE stage,
identities among `grRes`-images, unit products, and subring memberships in `LTwo` hold iff the
corresponding identities hold among genuine initial forms in the genuine `L`. So laws stated
of `LTwo`-objects are equivalent to the graded-locus laws the audit demanded — the erased
structure (the element `T`, the localization ring, the Laurent transport locus, the graded
piece) now EXISTS, and nothing is re-encoded through flattened output comparisons. In
particular the audit-#4 §2.4 pathology (a `Tvec` satisfying two aggregate equations while no
transported product is the normalizing unit) is dead: the normalizing unit is an object, the
law is an equation about it. (The audit's §2.2 second defect — vector support untied to
`reps` — was already excluded by the `Stage.hTvec` field `Tvec.map Prod.fst = reps`, a round-2
Stage axiom; the genuine-history provenance of `reps` itself is by construction and transport:
the base pins `[C p]`, `child_reps` appends exactly the outgoing key. Recorded here so audit
#5 does not re-derive it.)

## R5.1 Per-demand decision: (a) / (b), with rationale

**Demand 1 — "tie the T-vector to genuine representatives and to an actual localized
normalizing unit, or an interface genuinely equivalent": route (a).** `TvecUnitLaw σ` states
`Π in(ũᵢ)^{aᵢ} · Y^t = T` as an identity of UNITS of `LTwo ↥σ.K`: each factor is pinned by
value to `grRes` of the literal `σ.Tvec` entry (support = `σ.reps`), `Y` to `grRes σ.Φ`,
exponents are the literal vector entries and the Bézout `σ.t`, and the right side is `locT` —
the element that normalizes `R` definitionally. Requiring the factors to BE units is itself
faithful (initial forms of representatives are invertible in `L`). Base check (now at the
actual objects): `(grRes(C p))^s·(grRes φ)^t = C(z^{−ts+st})·T^{es+ht} = T¹ = locT`.
Propositionally, given the Stage laws, `TvecUnitLaw` is equivalent to round 4's `TvecLaw` —
that is the point: the round-4 equation was extensionally right but stated at the wrong locus
(two evaluations); the demanded locus now exists and the law is stated there. No choice
functions: units are pinned by value (`IsGrUnit`), and unit inverses are unique.

**Demand 2 — "S4 must identify the coefficient LOCALIZATION, not its flattened residual
image": route (a).** `Stage.coeffLocSR : Subring (LTwo ↥σ.K)` IS the coefficient localization
`𝒞[⟨U⟩⁻¹]`: the subring generated by the coefficient initial forms `{grRes B : B ∈ C∖0}` and
the INVERSES of the representative units (no `Y`, per D.0/(S4)). `CoeffLocLaw` states (S4) of
that object: (i) every degree-0 element of the subring (an outer constant `C ℓ` — degree-0
elements of `L₀[T^{±1}]` are exactly these; sums, products, and fractions all included, not
pairs of flattened outputs) is a `K`-constant; (ii) every `K`-constant is in it; (iii) the
(P1) pinning — `z` is EXACTLY (scalar 1) the value of a degree-0 formal `U ∪ {Y}`-monomial
vector (`LVec`/`IsLVecVal`: genuine exponent vectors over the representative list, weights
computed from `σ.w` and `σ.h`, NOT through `R`) — the genuine `z = V^{−h}·Y^{e}` of
D.2/D.7(vi), strictly stronger than round 4's "position differences generate ℤ". On the
audit's "rank one already imposed by the codomain": rank-1-ness now genuinely TRANSFERS
rather than being imposed — if a genuine stage had two independent degree-0 exponent
directions, clearing denominators gives equal-weight element pairs on which graded injectivity
(tie laws) forces distinct `R`-images, contradicting a rank-≥2 lattice mapping injectively to
the position line; so the concrete model's rank 1 certifies the genuine rank 1. What is NOT
built: the localization as an abstract ring with a universal property — subsumed in the R5.3
boundary below, unchanged since round 1.

**Demand 3 — "D.8 transport must operate on LAURENT slot terms and record terminal
carry/no-overflow": route (a).** `IsCarryChainL ψ c Cdig carry` is the displayed D.8
triangular recursion as a RELATIONAL chain: `carry 0 = 0` and, at every level,
`c j + carry j = toLaurent (Cdig j) + toLaurent ψ · carry (j+1)` with `Cdig j` the canonical
`deg < g` polynomial digit — slot terms and carries LAURENT (negative `z`-powers may cancel
only across ψ-levels, exactly the locus round 4's polynomial `%ₘ`/`/ₘ` had changed — the
audit's FAITHLESS catch), digits canonical. `CarryTransportL` RECORDS the terminal
no-overflow clause `∀ j ≥ N, carry j = 0`. `LandingCylinderL` keeps round 4's
BOX/VERTEX/side-line clauses but carries the anchored minimizing-slot terms as the Laurent
elements `cL j = T(j·m̂ − a)·R(B j)` themselves — no `toLaurent` coercion of individual slot
terms — and requires `CarryTransportL` to the stratum's canonical pattern. The chain's
witness is unique given the slot terms (digit = the unique `deg < g` representative mod `ψ`
in `F[z^{±1}]`, where `z` is invertible mod `ψ` since `ψ ≠ z`; carry = the exact quotient):
the relational form IS the deterministic recursion, in both directions on actual loci, with
no executable Laurent division machinery to audit. Round 4's executable `carryRec` is retired
from the cylinder (it remains in `DefsCore` for the FLAGGED-OK consumers' polynomial shadow,
unconsumed by any R5 statement).

**Demand 4 — "P6i's scalar action must preserve the fixed graded piece": route (a),
statement-level.** The corrected `L2.P6i` clause 3 hypothesizes `σ.w û = 0` (the `F_Q`-lift is
a weight-0 unit, position 0 forced) and concludes `σ.w (û·f) = γ ∧ R(û·f) = C c·R f` — an
`F_Q`-linear endomorphism OF `gr_γ`, as D.3(e)(i) states. No new objects needed.

## R5.2 The 8 units, restated (all in `MANIFEST_FINAL.json`; all elaboration-tested)

`L1.baseStage_exists` / `L1.base_nonvacuity_gate` — conclude `StageCoreL` (= round-4
`StageCore` + `TvecUnitLaw` + `CoeffLocLaw`); the base pins are exact at the actual objects
(the manifest sketches display the computations, including the base `z`-vector
`(−h on C p; key exponent e)` with value `C(z)` at scalar 1). `L2.P6i` — demand-4 clause fix
only. `L4.TRANSvi` — concludes `CoeffLocLaw σ' ∧ TvecUnitLaw σ'` from the `TransitionCoreL`
records (post-construction verification, G5′ discipline preserved). `L4.TRANSviii_a` —
statement unchanged from R4 (the audit endorsed its shape); the missing per-index coherence
is now supplied upstream by `TransitionCoreL.child_dig_frame`, whose frame-unit exponent is a
function `mfun : ℤ → ℤ` of the PARENT WEIGHT alone, quantified BEFORE the elements — realizers
of one index share their parent weight, hence their frame unit, and the orbit scalar enters
linearly. `L4.TRANSstage` — consumes `StageCoreL σ`, returns `TransitionCoreL ∧ StageCoreL σ'`
(the inductive step at the genuine objects). `L5.landTwoSided` — `StratumData ↔
LandingCylinderL` (demand 3). `L5.recTRANSRS` — returns `StageCoreL σ'`; with `Tvec_eq`,
`reps_eq`, `coeff_R`, and `σ.t = 0` at `e = 1` (T coefficient-pure, no key factor), the child's
`TvecUnitLaw` product is LITERALLY the parent's — equality of the ACTUAL normalizing units,
certified at the object level (the audit-#4 defect: round 4 had no objects to equate).

NOT restated: `L6.measureExact` keeps its audit-4 ruling — provable only under the explicit
label "conditional on the supplied jet-coordinate presentations" (the D.3(e)(ii) global
jet-coordinate system remains the named R4.5 gap); the 12 FLAGGED-OK units continue at their
stated scopes.

## R5.3 The remaining boundary (unchanged, restated with its campaign spec)

No demand was resolved by route (b); the four demanded structures are now genuine objects.
What remains is the SINGLE standing boundary, unchanged since round 1 and carried through
every audit: the identification of the abstract data `(σ.w, σ.R)` with the residual calculus
of a genuine graded tower — the D2 codomain fiat plus the use of D.1(e)'s presentation as the
DEFINITION of `L` rather than a theorem about a constructed `gr_w(A)`. Everything in `DefsL`
is downstream of that identification; nothing else is assumed. A future graded-ring campaign
would discharge it by providing, in order: (1) `𝒢 := ⊕_γ A_{≥γ}/A_{>γ}` as a graded
`ℤ_p`-algebra with the initial-form map `[·] : A∖0 → 𝒢` (D.1(a)-(b)), and the proof that `𝒢`
is a domain iff `w` is a valuation (D.1(c)); (2) the localization `L := 𝒢[⟨U ∪ {Y}⟩⁻¹]` at
the homogeneous multiplicative set, as a graded ring with its universal property (D.1(d));
(3) D.1(e) as a THEOREM: a degree-1 unit `T ∈ L` induces a graded ring isomorphism
`Θ : L ≅ L₀[T^{±1}]`; (4) the fiat discharged: an isomorphism `L₀ ≅ LaurentPolynomial ↥σ.K`
under which `Θ([f]·T^{−w f}) = σ.R f` for every `f` — i.e., the `Stage` fields `(w, R)` ARE
`x ↦ ([x], deg)` composed with the constructed structure. Given (1)-(4), `Stage.grRes` equals
`Θ ∘ [·]` and every `DefsL` law becomes a statement about the abstract localization verbatim;
no other round-5 definition needs to change. That is the precise spec; it is a large,
self-contained formalization unit (graded quotient algebras + homogeneous localization are
not off-the-shelf in mathlib at this granularity), and it is NOT needed by any consumer in
the §B2-DEF ledger DAG, all of whose displays are (P4)-dictionary statements.

## R5.4 Elaboration-test record (round 5)

`DefsL.lean`: `lake env lean LeanUrat/Moves/DefsL.lean` exit 0, no output; no `sorry`, no
`axiom`; `#print axioms` on its two lemmas (`tUnit`, `Stage.grRes_mul_T_neg`) = `{propext,
Classical.choice, Quot.sound}` exactly; olean built via `lake env lean -o` (never
`lake build`). All 8 `MANIFEST_FINAL.json` statements elaborated TWICE: first hand-written,
then REGENERATED verbatim from the manifest `statement` fields (`:= sorry` against the
`Defs`+`DefsT`+`DefsCore`+`DefsL` preamble with the `Fact (Nat.Prime 2)` gate instance;
`lake env lean`, exit 0, exactly 8 `sorry` warnings, zero errors, both runs) — no
transcription drift. `Field`/`Finite` instances for `GaloisField 2 2` resolve from mathlib
(probe-checked; the R4 preamble's explicit `Fintype` instance is no longer needed).
