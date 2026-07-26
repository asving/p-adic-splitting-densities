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
