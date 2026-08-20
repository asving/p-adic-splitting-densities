# THE DV-GRADED ENGINE — the one proof behind the chapter-C frontier (assembly, 2026-08-20)

**Author: the orchestrator (Fable 5), math-first assembly per the standing directive.**
STATUS: **math assembly + formalization design — nothing signed, nothing landed.** Sources:
`EFF.GENTOW3.22–.26` (the weight ledger, verbatim steps), `EFF.GENTOW1.19` (Step 0's compile),
C.72's BLOCKED record (the mechanism notes), `C52_BLOCKED_2026-08-18.md` /
`C33_BLOCKED_2026-08-17.md` (the obstruction inventories this must clear).

## §0 Why this one document

FIVE blocked/open chapter-C sites are the SAME missing engine, not five problems:

| site | what it needs from the engine |
|---|---|
| C.72 `shadow_floor`/`shadow_faithful_band` | literally the ledger's clause (i)+(ii) |
| C.52 `dvAbove_boxMonomial` + Steps 1–3 | Step 0/1 pricing + the capped read-back |
| C.52/C.53 `towerLocus_iff_budget` (leg 1 — C.53's ONLY remaining input) | Steps 0–3 assembled |
| C.54 node floors | the division ledger (Step 1) at a member |
| C.34/C.35's dv-Hensel adjacency | the graded division calculus (partially; the dissection cites stay) |

The obstruction inventories name it precisely: "the dv-graded product law is absent …
no `dvSupp` multiplication theorem, no `IsDvPure` multiplication theorem" (C.52 obstruction 1).
The EFF notes carry the proof as a **weight-ledger branch census** — a two-variable monomial
calculus — NOT as a valuation-theoretic product law. That reframing is what makes it
formalizable: the census is combinatorics + one conversion annex, and the combinatorics
never mentions `towerLocus`.

## §1 The objects (all fixed for the whole document)

Frame `F = (e₁, f₁, h; Φ′)`, `D′ = e₁f₁`, tower datum `T = (e₂, f₂, u₂, ψ₂)`, `E₂ = e₂f₂u₂`,
`D₂ = D′e₂f₂`, `δ := u₂ − e₂D′h > 0` (the node floor `hfloor`, a structure field).
Work in `O[x][Y]` (Lean: `Polynomial (Polynomial O)`), `Y` the level-2 placeholder. The
**evaluation** `ev : O[x][Y] → O[x]` is `Y ↦ Φ′` (Lean: `Polynomial.eval₂` at `C` and `Φ′`,
or `aeval Φ′`).

**The weight.** For a monomial `π^v x^a Y^b`: `wt := e₁e₂·v + a·e₂h + b·u₂`. For
`P ∈ O[x][Y]`: `WT(P) := min` over the support of `e₁e₂·addVal(coeff) + a·e₂h + b·u₂`
(valued in `ℕ∞`; `WT 0 = ⊤`). This is C.50's `gridWeight` with `(v, a, b, j)`'s `j`-slot
generalized from `Φ₂`-powers to the free variable `Y` — the "unreduced weight (x-degrees kept
literal)" of `EFF.GENTOW3.23`.

**The two carries** (Step 0, `EFF.GENTOW3.22`, arithmetic audited there):

* **x-carry** `x^{D′} = Φ′ + tail` — in `O[x][Y]` the move: replace a factor `x^{D′}` by
  `Y + tail(x)` where `tail = x^{D′} − Φ′ ∈ O[x]`, `deg tail < D′` — wait: the SIDE form.
  Pricing: the `x^{D′}`-part carries weight `D′·e₂h`; the `Y`-part carries `u₂ = D′e₂h + δ`;
  every `tail` monomial `π^{v'} x^{a'}` sits at weight `≥ D′e₂h` (this is the frame's
  one-sidedness: `Φ′`'s coefficients below the top sit ON or ABOVE the slope-`h/e₁` side —
  `F.hpure` cleared to the `(u₂, e₂)` grid; **LEMMA L2 below, the one place `hpure` enters**).
  So: tail branches at weight ≥ parent (equality allowed — the key's own side), the
  `Y`-branch at parent `+ δ` EXACTLY.
* **Φ′-carry (recarry)** `Y^{e₂f₂} = Φ₂-marker + lifts` — replace `Y^{e₂f₂}` by the level-3
  marker plus the lift terms of `composedKey` (each lift `stageLiftO((f₂−t)u₂)(…)·Y^{e₂t}`
  at weight `(f₂−t)u₂·e₂-cleared + …` = `E₂` exactly — C.43's display; **LEMMA L3**,
  the exact-height clause of `stageLiftO`, landed at C.46's pins). Weight-preserving, the
  `Φ₂`-part at `E₂`.

## §2 The proof, assembled (steps restated with their justifications; each ★ is a Lean node)

**★ L1 (weight ultrametric, free).** `WT(P + Q) ≥ min (WT P) (WT Q)`; `WT(PQ) ≥ WT P + WT Q`
(!!— this product law is FREE in the two-variable ring: monomial weights ADD and there is no
carry in `O[x][Y]` itself; the whole difficulty of the "dv-graded product law" lives in the
REDUCTION, not the product). Pure support-arithmetic over `ℕ∞`.

**★ L2 (x-carry pricing).** `WT(x^{D′} − Φ′-as-tail…)`: for the frame key,
`WT(x^{D′} · M) ≤ WT(Y·M) − δ` and `WT(tail·M) ≥ WT(x^{D′}·M)` for every monomial `M`.
Consumes: `F.hpure` cleared to the `(u₂, e₂)`-grid (the clearing arithmetic: a level-1
coefficient `π^v x^a` of `Φ′` on/above the slope-`h/e₁` side has
`e₁·v + a·h ≥ D′h`, hence `e₁e₂·v + a·e₂h ≥ D′e₂h`) plus `δ`'s definition. `hfloor` enters
ONLY as `δ ≥ 1`.

**★ L3 (Φ′-carry pricing).** Every term of `composedKey`'s display sits at weight `E₂`
exactly in the `(v, a, b)`-grid: the lift at height `(f₂−t)u₂` contributes
`e₁e₂·v + a·e₂h = (f₂−t)u₂·e₂`… **[TO VERIFY at transcription: the cleared form; C.46's
`slotRes_stageLiftO`/exact-height pins are the landed supply]** — and `Y^{e₂t}` adds
`e₂t·u₂`, totalling `e₂f₂u₂ = E₂`. Consumes: C.43's display + C.46's pins. (This is
`EFF.GENTOW3.23`'s "every term of K2 has wt = E₂ exactly — side terms of the key".)

**★ L4 (the division ledger, Step 1).** Monic `Y`-division of `P` by
`K₂ := Y^{e₂f₂} − (lift sum)` is weight-monotone: if `WT P ≥ w` then every `Y`-division
quotient/remainder layer `Ĝ_j` has `WT(Ĝ_j) ≥ w − j·E₂`. Proof: induction down the
`Y`-degree; one division step replaces top·`Y^{top}` by top·(lift sum)·`Y^{top−e₂f₂}`-shape
— by L1 + L3 the substituted content sits at `≥ WT(top-part) − 0` … each `Φ₂`-extraction
"spends `E₂`". [The induction is LINEAR in `P` — `EFF.GENTOW3.23`'s remark — so it can be
stated per-monomial and summed by L1.]

**★ L5 (reduction termination + the census, Step 2).** The reduction system (x-carry
everywhere `a ≥ D′`, recarry everywhere `b ≥ e₂f₂`) terminates (measure: `Σ` over support of
`a + b·D′`, strictly decreasing per move — **[TO CHECK: the recarry rewrites `b`-content
upward in `j` with x-degrees from the lifts; the EFF note's "recarry moves content only
UPWARD in j (division uniqueness)" is the invariant; a cleaner Lean measure may be
lexicographic `(Σ a-overflow, Σ b-overflow)`]**), and the normal form has all `a < D′`,
`b < e₂f₂` per `Φ₂`-slot — i.e. IS the two-key development (uniqueness: C.73's landed
presentation lemma / C53b's dictionary). The census prices the discrepancy: every branch
that ever used a `Y`-producing move carries `≥ parent + δ`; every recarry into coordinate
`j+1` re-prices to `≥ (μ₂−j)E₂ + δ` (the `EFF.GENTOW3.24` audit chain,
`(μ₂−j′)E₂ + kδ − (j−j′)E₂ ≥ (μ₂−j)E₂ + δ` for `k ≥ 1`).

**Corollary A (= C.72's clause (i), `shadow_floor`).** `WT(shadowDev − dev) ≥ Θ_j =
(μ₂−j)E₂ + δ` — the unreduced digit and the true digit differ only by branches that paid δ.

**Corollary B (Step-1 face, = C.52's `dvAbove_boxMonomial`).** The box monomial's every
reduced branch sits `≥` its unreduced weight = `e₁e₂·v(c) + slotOffset(a,b) + j·E₂` — L1–L5
applied to a single monomial.

**Corollary C (= C.52 Steps 2–3, leg 1).** Membership `f ∈ 𝒯 ↔` digit floors: forward by
L4+L5 from the locus side-data; backward by the census + C53b's dictionary + C.118's capped
congruence (the record's own retirement route, now with every named ingredient landed or in
this document).

**★ L6 — THE ANNEX (GENHN-2′'s weight-to-height conversion).** "Each slot digit's dv2-value
is the slot-min exactly, and heights separate classes." This is the ONE step that is
genuinely valuation-theoretic rather than combinatorial: the two-variable weight of the
REDUCED form computes the `dv2Hgt` of the digit. At the reduced form (all `a < D′`,
`b < e₂f₂`) this should be close to definitional — `dv2Hgt` IS the cleared min over the
digit's slots (C.11) — but the annex's "heights separate classes (one K₂-digit per height)"
clause consumes the residue-field grading. **STATUS: accepted annex in the corpus, NOT a
Lean object, NOT printed as a full proof in the EFF notes. This is the cite-or-prove
decision point — the only one in the whole engine.** Recommendation: attempt the proof at
the reduced normal form first (where it may reduce to C.11 arithmetic + the landed
`stageHeight` battery); only if that stalls, raise the cite question to the owner
(gate (b)).

## §3 Honest gaps in this assembly (state before formalizing)

1. **L2's clearing** assumes `Φ′`'s side data converts to the `(u₂, e₂)`-grid bound stated;
   the conversion `e₁·v + a·h ≥ D′h ⟹ e₁e₂·v + a·e₂h ≥ D′e₂h` is multiplication by `e₂` —
   trivial — but the PREMISE (`Φ′`'s coefficients on/above its side) must come from
   `F.hpure` via the landed B-chain (`OnSide`/`suppVal` at the frame). Named lemma, not yet
   checked against the exact landed forms.
2. **L4's "spends E₂"** needs the lift terms' weight to be exactly `E₂` AND the division to
   never see a lift term BELOW `E₂` — L3's "exactly" matters only as `≥` for the floor
   direction; the `= E₂` sharpness is consumed only by C.54's `_sharp` leg.
3. **L5's termination measure** is sketched, not fixed; the EFF note relies on "division
   uniqueness" for upward-only recarry. The Lean design should avoid a rewriting SYSTEM
   entirely if possible: define the reduction as a single structural recursion (reduce
   x-overflow slot-by-slot from the top), which sidesteps confluence.
4. **L6 is the annex** — see above.
5. The `+1` vs `+δ` strictness bookkeeping (C.54 wants `+1`; the ledger gives `+δ`, `δ ≥ 1`)
   — fine, but must be threaded as `δ ≥ 1`, not re-derived.

## §4 Formalization plan (nodes, ≈30–60 min each; provisional IDs C.131a–h)

* **C.131a** `wt2`/`WT` on `Polynomial (Polynomial O)` + L1 (support arithmetic; no frame).
* **C.131b** L2 (x-carry pricing; consumes `F.hpure` + B-chain clearing).
* **C.131c** L3 (Φ′-carry pricing; consumes C.43 display + C.46 pins).
* **C.131d** L4 (division ledger; induction, linear-in-P form).
* **C.131e** the reduction recursion + termination (no confluence needed).
* **C.131f** the census (Corollary A = C.72's `shadow_floor` at general datum).
* **C.131g** Corollary B (discharges C.52's `dvAbove_boxMonomial` verbatim).
* **C.131h** L6 at the reduced normal form (attempt); on stall → owner cite question.
* Then C.52 Steps 2–3 and C.54 consume C.131f–h + C53b + C.118 per their records.

## §5 Verification protocol before any Lean work

Per the standing rules: (1) numeric certification FIRST — the ledger's pricing at the two
landed witnesses (`linTower`: δ = 1, E₂ = 6; `s2Witness` trunc: δ = 1, E₂ = 10) against a
brute-force two-variable reduction in Python (`verification/` twin, exact arithmetic);
(2) a Codex adversarial pass on THIS document (after the Sun Aug 23 budget reset, or on
owner-purchased credits); (3) only then C.131a.
