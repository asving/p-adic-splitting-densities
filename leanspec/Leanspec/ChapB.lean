import Uniformity

/-!
# Chapter B — THE LEAF / ORDER-1 LAYER: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-B_leaf_layer.md` (86 nodes, **135 signed declarations** + 5
RE-PLAN supplier declarations), landed in the isolated `leanspec` environment **before** the
chapter-B fleet fires, in the blueprint's §11 topological order (node order `B.01 … B.86`) with
§12 rule 2's one hard exception applied: the RE-PLAN suppliers **B.63a** (`typeOf_prod`) and
**B.66a** (`slopeFinset` / `resFactorFinset` + their membership lemmas) are signed **before**
B.63, B.66, B.71, B.79a/b and B.80.

**Wrapper choice, declared per GC-6.6:** wrapper: `LeanspecB` per CHAP-B §12/H-13; the ChapG
retire-to-examples route (PA-2) was considered and not taken — a wrapped namespace keeps the stubs
greppable by contract name. Collisions with `leanfinal` are therefore structurally zero (nothing
here is declared inside `Uniformity.*`), and the 0e type diff runs per declaration against the
fully-qualified `leanfinal` twin `Uniformity.Density.Leaf.<name>` once a node lands.

**What is real and what is a stub — the landed census.** 139 declarations:

| kind | count | note |
|---|---:|---|
| real bodies (`structure` 1 + `abbrev` 1 + `def` 20) | **22** | §12 rule 1's definitional layer |
| `axiom` stubs of theorem rows | **109** | of §12's 110 — B.51's first block is unsignable (B-D6) |
| `axiom`s standing in for body-less def-class rows | **3** | B-D2: `instFiniteResField`, `instLocalRingAdjoinRoot`, `residueFieldEquiv` |
| `axiom`s for the 5 RE-PLAN suppliers | **5** | B.63a (1) + B.66a (4), B-D4 |

So §12's predicted "25 real bodies / 110 axioms" lands as **22 real bodies / 117 axioms**; the 20
`def`s are the blueprint's 20 minus `residueFieldEquiv` plus `instFieldResField` (demoted from
`instance`, B-D3). B.62 is deliberately unsigned (§12 rule 3). `sorry` appears nowhere. The file
also elaborates clean under `-DautoImplicit=false`, i.e. no binder here is silently auto-bound.

**This file is never imported by `leanfinal` or `leancheck`.** It carries `axiom`s by design; it
is an interface contract, not mathematics. Nothing here is proved.

**Environments** (blueprint §0.1, checked per NODE per §12 rule 7). ENV-A is the section
`variable` block below; **ENV-A′ = ENV-A with `(hπ : Irreducible π)`**, which every node that
names `π` carries as an explicit hypothesis inside its own signature, so ENV-A and ENV-A′ share
one `variable` block; **ENV-B = ENV-A + `[IsAdicComplete (maximalIdeal O) O]`**; **ENV-C = ENV-B +
`[Finite (ResidueField O)]`**. ENV-B/ENV-C are entered by `section`+`variable` blocks marked
`-- ENV-B` / `-- ENV-C` below, so Lean's use-driven variable inclusion trims the instances a
statement does not need — exactly as the `leanfinal` twin's own environment block will. **ENV-D**
nodes (B.27, B.38, B.45, B.46) bind their own `{K : Type*} [Field K]` inline and mention no `O`.
The §10 gates bind nothing: they are concrete `ℤ_[2]` / `ℤ_[3]` instances.

## RE-SIGN LOG (post-0e, blueprint-authorized amendments)

* **A-F.6 (2026-08-15, wave-10 refutation adjudication).** B.35a/B.35b REFUTED as frozen
  (fleet counterexamples, re-verified); consumer audit refuted FOUR more frozen signatures.
  Re-signed here, matching the blueprint's `[repaired: A-F.6]` tags: B.35a/b (`hu`, `hfd`,
  `hgd`), B.39 (`hu`, `hgd`, `hhd`), B.41 (`hu`, `hfd`), B.42 (conclusion strengthened:
  `0 < p.1`, factor-degree divisibility), B.43 (STATEMENT-restoration: `hu`, four
  divisibilities, purity of `g'`,`h'`), B.48 (`hu`, `hfd`), B.57 (`hgd`). Full record with
  all six counterexamples: blueprint amendment A-F.6.
* **A-F.7 (2026-08-15, same adjudication).** B.59 REFUTED as frozen (compiled witness,
  `leanfinal/Uniformity/ChapB/B59_REFUTATION.lean.txt`); the conjectured general-`φ`
  extraction B.44′ REFUTED. B.59/B.60 re-signed at `φ = X`; the `hperim` displays' first
  disjunct narrowed to `(ℓ = 1 ∧ φ.natDegree = 1)` at B.63, B.71, B.79a, B.79b, B.80, B.81,
  B.82 (7 sites, matching the blueprint's §12 item 4 dictionary). Full record: blueprint
  amendment A-F.7 + CHAP-I dated addendum (OPEN-MATH routing of `ℓ = 1, m ≥ 2, d ≥ 2`).
* **A-F.8 (2026-08-16, wave-11 refutation adjudication).** B.39's A-F.6 re-sign REFUTED again
  (compiled witness `leanfinal/Uniformity/ChapB/B39_REFUTATION.lean.txt`: `g = 1` passes every
  hypothesis, `U.natDegree < 0` is `False`). Re-signed here with the conclusion bounds in
  `degree`/`WithBot ℕ` (R1 — B.38's and the landed templates' shape; R2, added positivity,
  rejected). Full record: blueprint amendment A-F.8.
* **A-F.9 (2026-08-16, same adjudication).** B.42's A-F.6 re-sign REFUTED (compiled witness
  `leanfinal/Uniformity/ChapB/B42_REFUTATION.lean.txt`: `f = φ`, `μ = 1`). Re-signed here with
  the classical standing hypothesis `(h0 : dev φ f 0 ≠ 0)` ([GN15] Thm 2.3's explicit
  `φ^{ord_φ(g)}` peel) and clause 3 strengthened (`dev φ (F p) 0 ≠ 0`, `0 < (F p).natDegree` —
  what B.48 needs at B.63). The same missing hypothesis found and repaired at B.71 (`hnz`,
  B.81's clause verbatim), B.72 (`h0`), B.79a (`h0`); B.41/B.48/B.79b/B.80/B.81/B.82 verified
  immune (`hH₀`/`hvis`/`hnz`); B.63's stub UNCHANGED (its blueprint route gains the `φ`-part
  peel step 0 instead). Full record: blueprint amendment A-F.9.

## THE DEFECT LIST (stage-0e gate, 2026-08-15)

Recorded here and in the 0e report; **NOT repaired in the blueprint** (§12 rule 5 / H §15 rule 5:
elaboration failures in a stub are blueprint defects, versioned in the blueprint by dated append,
never patched in `leanspec`). Every stub-side adjustment made to get the file to elaborate is
listed; nothing was adjusted silently.

* **B-D1 — B.25 `instFieldResField`, ELABORATION FAILURE (verbatim form).** The signed body is
  `AdjoinRoot.instField (hf := hφ.irred.ne_zero)`. At our pin (mathlib
  `Mathlib/RingTheory/AdjoinRoot.lean:516`) `AdjoinRoot.instField` takes **no** explicit argument
  and instead requires an instance `[Fact (Irreducible f)]`; there is no argument named `hf`, and
  `f ≠ 0` is not the hypothesis it needs. *Classification: elaboration error (wrong argument name
  + missing instance).* **Stub-side repair applied** (minimal and unambiguous — `IsKey.irred` is
  exactly the irreducibility the instance wants): supply
  `haveI : Fact (Irreducible (φ.map (IsLocalRing.residue O))) := ⟨hφ.irred⟩` and then
  `AdjoinRoot.instField`. The blueprint entry still needs its body corrected.
* **B-D2 — THREE def-class declarations have NO BODY: B.26 `instFiniteResField`, B.49
  `instLocalRingAdjoinRoot`, B.49 `residueFieldEquiv`.** §12 rule 1 mandates real bodies for all
  25 def-class rows, but these three SIGNATUREs stop at the type. Two are Prop-valued classes
  (`Finite (resField φ)`, `IsLocalRing (AdjoinRoot g)`) whose "body" is a proof — B.26 and B.49
  are `[lemma]` nodes, so this is a **kind mis-classification in §12's own census**, not a
  transcription slip; `residueFieldEquiv` is worse, being *data* (`≃+*`) that only a proof can
  construct. *Classification: def with no body (ChapG defect D2's class).* Landed as `axiom`s
  (the D2 precedent's `axiom`-typed placeholder), so §12's "25 real bodies / 110 axioms" split is
  in fact **21 real bodies / 114 axioms**.
* **B-D3 — B.25/B.26/B.49's three `instance`s cannot be declared as `instance`s at all: HARD
  ERROR.** Each carries an explicit non-class hypothesis (`hφ : IsKey φ`, plus `hg`/`hk`/`hres` at
  B.49), and at our pin Lean rejects the declaration outright: *"This instance has 1 argument that
  cannot be inferred using typeclass synthesis. Specifically argument 6: `(hφ : IsKey φ)`. These
  arguments are not instance-implicit and appear neither in another instance-implicit argument nor
  the return type."* Consequences: (i) `instFieldResField` is demoted to `@[reducible]
  noncomputable def` here; (ii) the other two are `axiom`s anyway (B-D2) and an `axiom` cannot
  carry `instance`; (iii) **B.49's `residueFieldEquiv` type therefore does not elaborate** — it
  needs `IsLocalRing (AdjoinRoot g)`, which nothing can supply by TC — so its type names the
  instance explicitly here:
  `@IsLocalRing.ResidueField (AdjoinRoot g) _ (instLocalRingAdjoinRoot hφ hg hk hres)`.
  *Classification: elaboration error + missing dependency.* The blueprint must make the three rows
  `[IsKey φ]`-class-based (i.e. make `IsKey` a class), demote them to plain `def`/`theorem`, or
  write the explicit application at every use site.
* **B-D4 — B.66a (`slopeFinset`, `resFactorFinset`, `mem_slopeFinset`, `mem_resFactorFinset`) is
  booked with no signature and no body.** The booking (B.79's ⚠ RE-PLAN item, A-§9.5) gives only
  the names and a partially elided membership statement `mem_slopeFinset ↔ (sideSet …).Nonempty ∧
  1 ≤ card ∧ …`. §12 nevertheless requires these four signed *before* B.63/B.66/B.71/B.79a. The
  two `Finset`-valued suppliers are **underdetermined** — B.42 produces its slope `Finset`
  existentially and any canonical body needs an abscissa bound the blueprint never states — so
  they land as `axiom`-typed opaque constants (ChapG D2 precedent). The two membership lemmas land
  with the elisions expanded to the determinate content of B.42's own characterisation clause
  (`0 < ℓ ∧ Coprime u ℓ ∧ 1 < card`) and B.45's factorisation, marked in place.
  *Classification: missing dependency + elision that rule 5 cannot expand.*
  Note the booking's first two conjuncts are redundant (`1 ≤ card ↔ Nonempty`).
* **B-D5 — B.65 clause 2 is an unexpandable elision: `(∀ u ℓ ψ, … multiplicity = 1)`.** Rule 5
  allows expansion only through §12 item 4 or the node's own STATEMENT, and B.65's STATEMENT says
  only "every `(slope, monic irreducible residual factor)` pair has multiplicity `1`" —
  "multiplicity" is B.45's existentially-produced exponent function `a ψ`, which a closed
  statement cannot name. *Classification: elision rule 5 cannot expand / suspected under-specified
  statement.* Signed below with an **interpretive** expansion (`¬ ψ ^ 2 ∣ resPoly …`, the
  multiplicity-free reading) explicitly marked NOT-CONTRACT; the blueprint owner must re-sign
  clause 2.
* **B-D6 — B.51 `residueDeg_dvd_sum_of_local` cannot be signed: its conclusion is literally
  `s ∣ (Nat.find (…) : ℕ)`.** The blueprint's own PROOF note says the contract is stated on
  `addVal (norm z)` directly and supplies a second block, "**Contract declaration (the one the
  fleet must land)**" = `residueDeg_dvd_addVal_norm`. Only the contract declaration is signed
  here. *Classification: elaboration error (placeholder term) in a declaration §12's mechanical
  count nevertheless includes among the 110.* Signed count consequence: 109 of the 110 theorem
  rows are signed.
* **B-D7 — B.54 `inertiaDegOf_dvd_key_mul_resDeg` has an unbalanced parenthesis.** Its `hres`
  hypothesis reads `(hres : g.map (…) = (φ.map (…)) ^ (ℓ * sideDeg φ g u ℓ hne) :` — the closing
  paren of the binder is missing, so the signed text is not parseable. *Classification: syntax
  error (typo).* **Stub-side repair applied** (unambiguous: B.55's byte-identical `hres` on the
  next node closes the binder).
* **B-D8 — B.55 `inertiaDegOf_eq_of_resDeg_one` is signed as `(… same hypotheses …)`.** Expanded
  from `inertiaDegOf_bracket`'s hypothesis list immediately above it (unambiguous; the STATEMENT
  says "Under the joint hypotheses of B.52 and B.54 … In particular if `d = 1`").
  *Classification: elision, expanded per rule 5 from the node's own text.*
* **B-D9 — B.35 `resPoly_mul_of_pure` binds three hypotheses with no types: `(hf' hg' hfg')`.**
  The gloss under the SIGNATURE says "the three `Nonempty` witnesses are named `hf' hg' hfg'` and
  are supplied by B.18", which fixes them: `hf' : (sideSet φ f u ℓ).Nonempty`,
  `hg' : (sideSet φ g u ℓ).Nonempty`, `hfg' : (sideSet φ (f * g) u ℓ).Nonempty`.
  *Classification: elision, expanded per rule 5 from the node's own text.* (Verbatim, Lean would
  read `(hf' hg' hfg')` as three anonymous `Sort`-valued binders and the statement would not
  mention them where B.29 needs them.)
* **B-D10 — B.71 / B.72 / B.79a / B.79b / B.80 / B.81 / B.82 / B.63 carry `hsep`/`hperim`
  elisions.** All are expanded from §12 item 4's shared-clause dictionary (`hperim` verbatim;
  per-block instantiation `(φ, f) := (φ i, g i)`) and from B.63's own written-out `hsep`
  (post-A-F.1, pinned at `sideMin`), which is what rule 4 mandates. **B.71 is signed in B.80's
  data form** per rule 4c (`g : ι → Polynomial O` with `hgprod`/`hgres`), not over B.67's
  existential. No adjudication was needed beyond rule 4; recorded because the expanded text is
  contract text that no node states in full.
* **B-D11 — ENV-C over-claims completeness at 12 nodes.** ENV-C is defined as "ENV-B plus
  finiteness", i.e. it *includes* `[IsAdicComplete (maximalIdeal O) O]`; but B.37, B.39, B.43,
  B.47, B.52–B.55, B.57, B.64, B.66, B.73 are tagged ENV-C while needing no Hensel lift, and
  B.80/B.81/B.82's "ENV-C **plus completeness**" is then a tautology. Harmless here (Lean's
  use-driven inclusion trims what a statement does not mention), but the tag is doing no work.
  *Classification: environment tag imprecision (documentation-level).*
* **B-D12 — the `hperim` display of §12 item 4 quantifies `∀ hne : … , ∀ H₀ : ℕ` after a
  `→`-chain.** Signed verbatim; it elaborates. Noted only because the display's `∀ hne` binder is
  *used* in `resPoly π φ gS u ℓ hne H₀`, so the clause is genuinely dependent and any consumer
  that instantiates it must supply the same witness — the `Nonempty`-argument fragility §12 rule 6
  flags at B.20/B.28/B.29 reappears here, inside a hypothesis.
* **B-D13 — B.50 `exists_smith_of_norm` uses the `⨁` big-operator, whose notation is
  `scoped[DirectSum]`.** ENV-A′ opens only `IsLocalRing Polynomial`, so the verbatim signature
  fails: `⨁` parses as a prefix operator with no binder and Lean reports
  `unknown identifier 'i'` (twice), then an application type mismatch. *Classification: missing
  dependency (missing `open`).* **Stub-side repair applied**: `open DirectSum in` on the
  declaration; the intended object is unambiguous.
* **B-D14 — B.86's census block names a constant that does not exist:
  `Uniformity.Density.FactorizationType`.** `FactorizationType` is declared in `Uniformity`
  (`LocalData.lean:43`), *before* `namespace Density` opens at `:58`; the correct name is
  `Uniformity.FactorizationType`. All six degree-conservation `#eval`s of B.86 part (ii) fail with
  `unknown identifier` as written. *Classification: elaboration error (wrong qualified name).*
  **Stub-side repair applied** (unambiguous) in the GC-11 block below. The same slip would break
  B.86 as a leanfinal file verbatim.
* **B-D15 — §0.1's ⚠ ENV-C premise is FALSE at our pin, so §12 rule 7's mechanical check has a
  void criterion.** §0.1 asserts: *"`Uniformity.Density.Res` … is declared inside a
  `variable (O) … [Finite (ResidueField O)]` section, so a stub that mentions `Res O N` without
  that instance does not elaborate."* Checked directly: none of `Res`, `Coeff`, `proj`,
  `residueCard`, `DecidedAt` carries `[Finite (ResidueField O)]` in its own signature — their
  bodies do not use it, so Lean trimmed it from them too (only genuinely counting theorems such as
  `card_res` keep it). Empirically, of the 139 declarations in this file **zero** end up carrying
  `[Finite (ResidueField O)]`, including `card_resField` (which names `residueCard O`) and all
  three `DecidedAt` certificates; `[IsAdicComplete (maximalIdeal O) O]` by contrast is included in
  25 of them, because it is genuinely mentioned nowhere else and Lean keeps it once a statement's
  elaboration needs it. *Classification: false premise in the environment spec (documentation +
  process defect).* Consequence: chapter B's claim to fix chapter G's defect D4 *"by
  construction"* does not hold — the D4 phenomenon simply reappears in `leanfinal`, where each
  node file's own `variable` block will drop the instance exactly as here. Harmless for the
  retirement-form 0e diff (ChapG's 0e-G unit verified that), but the ENV-C tag cannot be audited
  the way rule 7 describes.
* **B-D16 — B.17, B.19, B.20d, B.20e use `u` and `ℓ` with no binder, and ENV-A does not declare
  them.** They survive only through Lean's `autoImplicit`: under leanfinal's option set
  (`relaxedAutoImplicit = false`, `autoImplicit` left on) they auto-bind, in first-occurrence order
  `{ℓ u : ℕ}`; under `autoImplicit = false` all four fail with
  `unknown identifier 'ℓ'`. *Classification: missing binder (latent — signature depends on an
  option the project has not fixed).* **Stub-side repair applied**: the binders are written
  explicitly, in the same order Lean's auto-binding produces, so the elaborated types are
  identical to the verbatim ones under leanfinal's options (verified by `#check` against a
  verbatim copy). ENV-A should declare `{u ℓ : ℕ}`.

**What the stub gate CANNOT catch** (§12 rule 8's ⚠, restated): a wrong-but-well-typed statement.
The exposed class for this chapter is the §10 gate instances' hand-computed polygon data and the
`hperim` display; the executed arithmetic of B.86 (§ "GC-11 EXECUTION" below) is the mechanical
half of that defense, and §14 items 14–15 are the human half.

## GC-11 EXECUTION RECORD (§12 rule 8(c) / GC-11, run 2026-08-15 at this gate)

**Ran, and passed, at stub stage** (all `decide`/`#eval`, no `native_decide`; both primes):
1. all six degree-conservation checks of B.86 part (ii) — `⟨{(1,2)}⟩.degree = 2`,
   `⟨{(2,1)}⟩.degree = 2`, `⟨{(1,1),(2,1)}⟩.degree = 3`, `⟨{(1,1),(1,2)}⟩.degree = 3`,
   `⟨{(2,2)}⟩.degree = 4`, `⟨{(3,2)}⟩.degree = 6` — all `true`, matching the blueprint's
   `-- expect true` comments (after the B-D14 name repair);
2. D-3's bracket arithmetic at the B.85 `e > 1 ∧ f > 1` witnesses:
   `(gcd 2 4, gcd 2 6, gcd 1 2) = (2, 2, 1)`, matching the blueprint's `-- expect (2, 2, 1)`;
3. the split-gate multiset sum `{(1,1)} + {(1,2)} = {(1,1),(1,2)}` — `true`;
4. `residueCard ℤ_[2] = 2` and `residueCard ℤ_[3] = 3` discharged by the landed
   `residueCard_padicInt` (real proofs, not `#eval`);
5. B.86 part (iii): all ten gate signatures elaborate at their stated types, printed below.

**Must wait for real bodies:** B.86 part (i), the `#print axioms` footprints of the fourteen
capstone-path theorems and the ten gates. At stub stage each of those names is an `axiom` in this
file, so its footprint is itself — the check is vacuous until `leanfinal` carries the proofs.

**§14 item 14 (the gate instances' hand-computed data), recomputed independently at this gate — no
discrepancy found.** Not machine-checked (the chapter-B definitions have no lemmas yet), but
recomputed from scratch, by a different arm than the one that wrote §10, over `monicPoly a =
X ^ n + ∑ i, C (a i) * X ^ i`:

* `B.83(i)` `![3,1]` → `X² + X + 3`, reduction `X² + X + 1` irreducible over `𝔽₂` ⇒ `{(1,2)}`. ✓
* `B.83(ii)` `![2,2]` → `X² + 2X + 2`, Eisenstein at `2` ⇒ `{(2,1)}`. ✓
* `B.83(iii)` `![4,2,2]` → `X³ + 2X² + 2X + 4`, `φ = X` (`m = 1`), heights `(2,1,1,0)`.
  Slope `−1` side: `inf = 2`, argmin `{0,1}`, `sideMin = 0`, `sideDeg = 1`, residual `Y + 1`
  ⇒ `(ℓ, m·d) = (1,1)`. Slope `−1/2` side: `inf = 3`, argmin `{1,3}`, **`sideMin = 1 ≠ 0`**,
  `sideDeg = 1`, residual `Y + 1` ⇒ `(2,1)`. Total `{(1,1),(2,1)}`. ✓
  **This also verifies A-F.1's teeth claim / §14 item 13(iii) directly**: under the retired
  abscissa-`0` pin the second side reads `H₀ = 2` and its `k = 0` coefficient is
  `digAt π 2 (2) = 0` (since `4 ∤ 2`), so `resPoly` loses its constant term and is never
  separable; under the GC-1 `sideMin` pin `H₀ = 1` and both coefficients are units. The instance
  provably could not fire pre-repair, exactly as claimed.
* `B.83(iv)` `![2,3,3]` → `X³ + 3X² + 3X + 2`, reduction `X(X² + X + 1)` (squarefree, two distinct
  irreducibles) ⇒ order-0 peel gives `{(1,1)} + {(1,2)}`. ✓
* `B.84(i)` `![4,0]` → `X² + 4`, reduction `X² + 1` irreducible over `𝔽₃` ⇒ `{(1,2)}`. ✓
* `B.84(ii)` `![3,3]` → `X² + 3X + 3`, Eisenstein at `3` ⇒ `{(2,1)}`. ✓
* `B.84(iii)` `![9,3,3]` → `X³ + 3X² + 3X + 9`, heights `(2,1,1,0)` — the same polygon as B.83(iii),
  same two sides, `sideMin = 1` on the second ⇒ `{(1,1),(2,1)}`. ✓
* `B.84(iv)` `![3,1,3]` → `X³ + 3X² + X + 3`, reduction `X(X² + 1)` over `𝔽₃` ⇒ `{(1,1),(1,2)}`. ✓
* `B.85(i)` `![-1,2,3,2]` → `X⁴ + 2X³ + 3X² + 2X − 1 = φ² − 2` with `φ = X² + X + 1` (`m = 2`,
  `μ = 2`). Development `(dev 0, dev 1, dev 2) = (−2, 0, 1)`, heights `(1, ⊤, 0)`, one side of
  slope `−1/2`: `ℓ = 2`, `sideSet = {0,2}`, `d = 1` ⇒ `(ℓ, m·d) = (2,2)`. ✓ **`e > 1` AND `f > 1`
  simultaneously**, which is GC-11's mandated witness shape.
* `B.85(ii)` `![-1,3,6,7,6,3]` → `X⁶ + 3X⁵ + 6X⁴ + 7X³ + 6X² + 3X − 1 = φ³ − 2`, same `φ`;
  heights `(1,⊤,⊤,0)`, slope `−1/3`, `ℓ = 3`, `d = 1`, `m = 2` ⇒ `{(3,2)}`. ✓
* `B.85(iii)` `![-2,0,2,0]` → `X⁴ + 2X² − 2 = φ² − 3` with `φ = X² + 1` over `ℤ_[3]` ⇒ `{(2,2)}`. ✓
* `B.85(iv)` `![-2,0,3,0,3,0]` → `X⁶ + 3X⁴ + 3X² − 2 = φ³ − 3`, same `φ` ⇒ `{(3,2)}`. ✓

Every stated `N` is also sufficient on this recomputation (the two-slope gates need `N = 3` to fix
`v(a₀) = 2` exactly, and they ask for `3`; the `e·f` gates need `N = 2` to fix `v(dev 0) = 1`, and
they ask for `2`). What is NOT verified here: that these `N` are *minimal*, and the `Visible`-level
column of §10's tables, neither of which any signed statement claims.
-/

namespace LeanspecB

open IsLocalRing Polynomial Uniformity Uniformity.Density

/-! ## ENV-A — the polynomial arena (blueprint §0.1)

```lean
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
```
ENV-A′ is this block plus the explicit hypothesis `(hπ : Irreducible π)`, carried per signature.
-/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## §3 — the development, the heights, and the polygon representation (B.01–B.20) -/

/-- **B.01** [def] ENV-A. `IsKey φ` : `φ` is monic of positive degree with irreducible
reduction — an order-1 key. -/
structure IsKey (φ : Polynomial O) : Prop where
  monic : φ.Monic
  pos : 0 < φ.natDegree
  irred : Irreducible (φ.map (IsLocalRing.residue O))

/-- **B.02** [def] ENV-A. `dev φ f j` : the `j`-th coefficient of the `φ`-adic development
of `f`. -/
noncomputable def dev (φ : Polynomial O) : Polynomial O → ℕ → Polynomial O
  | f, 0 => f %ₘ φ
  | f, (j + 1) => dev φ (f /ₘ φ) j

/-- **B.03** [lemma] ENV-A. -/
axiom degree_dev_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), (dev φ f j).degree < φ.degree

/-- **B.04** [lemma] ENV-A. -/
axiom dev_eq_zero_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) :
    ∀ (f : Polynomial O) (j : ℕ), f.natDegree < j * φ.natDegree → dev φ f j = 0

/-- **B.05** [lemma] ENV-A. -/
axiom sum_dev_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : Polynomial O)
    {k : ℕ} (hk : f.natDegree < k * φ.natDegree) :
    ∑ j ∈ Finset.range k, dev φ f j * φ ^ j = f

/-- **B.06** [lemma] ENV-A. -/
axiom dev_unique {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} {a : ℕ → Polynomial O} {k : ℕ}
    (hdeg : ∀ j, (a j).degree < φ.degree)
    (hsum : ∑ j ∈ Finset.range k, a j * φ ^ j = f) :
    ∀ j < k, a j = dev φ f j

open IsDiscreteValuationRing in
/-- **B.07** [def] ENV-A. `gaussVal a` : the minimum `π`-valuation of the coefficients of `a`
(`⊤` iff `a = 0`). -/
noncomputable def gaussVal (a : Polynomial O) : ℕ∞ :=
  (Finset.range (a.natDegree + 1)).inf (fun i => addVal O (a.coeff i))

/-- **B.08a** [lemma] ENV-A′. -/
axiom le_gaussVal_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O} :
    (k : ℕ∞) ≤ gaussVal a ↔ ∀ i, π ^ k ∣ a.coeff i

/-- **B.08b** [lemma] ENV-A′. -/
axiom gaussVal_eq_top_iff {a : Polynomial O} : gaussVal a = ⊤ ↔ a = 0

/-- **B.08c** [lemma] ENV-A′. -/
axiom gaussVal_range (a : Polynomial O) {M : ℕ} (hM : a.natDegree < M) :
    gaussVal a = (Finset.range M).inf (fun i => IsDiscreteValuationRing.addVal O (a.coeff i))

/-- **B.09** [lemma] ENV-A′. -/
axiom gaussVal_mul (hπ : Irreducible π) (a b : Polynomial O) :
    gaussVal (a * b) = gaussVal a + gaussVal b

/-- **B.10** [lemma] ENV-A′. -/
axiom dev_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (h : ∀ i, π ^ N ∣ (f - f').coeff i) :
    ∀ j i, π ^ N ∣ (dev φ f j - dev φ f' j).coeff i

/-- **B.11** [def] ENV-A. `npHgt φ f j` : the height of the `φ`-adic Newton polygon's `j`-th
support point (`⊤` when the `j`-th development coefficient vanishes, i.e. when the abscissa `j`
carries no point). -/
noncomputable def npHgt (φ f : Polynomial O) (j : ℕ) : ℕ∞ := gaussVal (dev φ f j)

/-- **B.12a** [lemma] ENV-A. -/
axiom npHgt_eq_top_iff {φ f : Polynomial O} {j : ℕ} : npHgt φ f j = ⊤ ↔ dev φ f j = 0

/-- **B.12b** [lemma] ENV-A. -/
axiom npHgt_eq_top_of_lt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f : Polynomial O) {j : ℕ} (hj : f.natDegree < j) : npHgt φ f j = ⊤

/-- **B.13a** [lemma] ENV-A. -/
axiom dev_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : dev φ f μ = 1

/-- **B.13b** [lemma] ENV-A. -/
axiom npHgt_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) : npHgt φ f μ = 0

/-- **B.14** [def] ENV-A. `suppVal φ f u ℓ` : the cleared support value of `f`'s `φ`-adic polygon
at the slope `−u/ℓ`, i.e. `ℓ` times the corpus's `h_F(u/ℓ) = min_j (dv(A_j) + j·u/ℓ)`. -/
noncomputable def suppVal (φ f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • npHgt φ f j + (u * j : ℕ))

/-- **B.15a** [lemma] ENV-A′. -/
axiom dev_X (f : Polynomial O) (j : ℕ) : dev X f j = Polynomial.C (f.coeff j)

/-- **B.15b** [lemma] ENV-A′. -/
axiom npHgt_X (f : Polynomial O) (j : ℕ) :
    npHgt X f j = IsDiscreteValuationRing.addVal O (f.coeff j)

/-- **B.15c** [lemma] ENV-A′. -/
axiom suppVal_X_iff (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) (M : ℕ) :
    ((M * f.natDegree : ℕ) : ℕ∞) ≤ suppVal X f M 1 ↔
      ∀ i < f.natDegree, π ^ (M * (f.natDegree - i)) ∣ f.coeff i

/-- **B.16a** [def] ENV-A. `OnSide φ f u ℓ j` : the abscissa `j` lies on the side of
slope `−u/ℓ`. -/
def OnSide (φ f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  ℓ • npHgt φ f j + (u * j : ℕ) = suppVal φ f u ℓ

/-- **B.16b** [def] ENV-A. The on-side abscissae, as a `Finset`. -/
noncomputable def sideSet (φ f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (f.natDegree + 1)).filter (OnSide φ f u ℓ)

/-- **B.17** [lemma] ENV-A. -/
axiom onSide_modEq {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    {j j' : ℕ}
    (htop : suppVal φ f u ℓ ≠ ⊤) (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j') :
    j ≡ j' [MOD ℓ]

/-- **B.18a** [lemma] ENV-A. -/
axiom suppVal_ne_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    suppVal φ f u ℓ ≤ ((u * μ : ℕ) : ℕ∞)

/-- **B.18b** [lemma] ENV-A. -/
axiom sideSet_nonempty {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    (sideSet φ f u ℓ).Nonempty

/-- **B.19** [lemma] ENV-A. -/
axiom eq_of_onSide_onSide {ℓ ℓ' : ℕ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') {φ f : Polynomial O}
    {u u' j j' : ℕ}
    (hne : u * ℓ' ≠ u' * ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (htop' : suppVal φ f u' ℓ' ≠ ⊤)
    (hj : OnSide φ f u ℓ j) (hj' : OnSide φ f u ℓ j')
    (hk : OnSide φ f u' ℓ' j) (hk' : OnSide φ f u' ℓ' j') : j = j'

/-- **B.20a** [def] ENV-A. *(§12 rule 6 FRAGILE — dependent `Nonempty` argument in a `def`
type.)* -/
noncomputable def sideMin (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).min' h

/-- **B.20b** [def] ENV-A. *(§12 rule 6 FRAGILE.)* -/
noncomputable def sideMax (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideSet φ f u ℓ).max' h

/-- **B.20c** [def] ENV-A. *(§12 rule 6 FRAGILE.)* -/
noncomputable def sideDeg (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) : ℕ := (sideMax φ f u ℓ h - sideMin φ f u ℓ h) / ℓ

/-- **B.20d** [lemma] ENV-A. -/
axiom sideMax_eq {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) :
    sideMax φ f u ℓ h = sideMin φ f u ℓ h + ℓ * sideDeg φ f u ℓ h

/-- **B.20e** [lemma] ENV-A. -/
axiom onSide_eq_add_mul {ℓ u : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {φ f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {j : ℕ}
    (hj : j ∈ sideSet φ f u ℓ) :
    ∃ k ≤ sideDeg φ f u ℓ h, j = sideMin φ f u ℓ h + ℓ * k

/-! ## §4 — the order-1 residual field and the residual polynomial (B.21–B.30) -/

/-- **B.21** [def] ENV-A. `digAt π k x` : the residue of `x / π ^ k` when `π ^ k ∣ x`
(junk `0` otherwise) — the "digit of `x` at height `k`" of the corpus's digit calculus. -/
noncomputable def digAt (π : O) (k : ℕ) (x : O) : ResidueField O :=
  open Classical in if h : π ^ k ∣ x then IsLocalRing.residue O h.choose else 0

/-- **B.22a** [lemma] ENV-A′. -/
axiom digAt_eq (hπ : Irreducible π) {k : ℕ} {x y : O} (h : x = π ^ k * y) :
    digAt π k x = IsLocalRing.residue O y

/-- **B.22b** [lemma] ENV-A′. -/
axiom digAt_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {x : O} (h : π ^ k ∣ x) :
    digAt π k x = 0 ↔ π ^ (k + 1) ∣ x

/-- **B.22c** [lemma] ENV-A′. -/
axiom digAt_add (hπ : Irreducible π) {k : ℕ} {x x' : O} (h : π ^ k ∣ x) (h' : π ^ k ∣ x') :
    digAt π k (x + x') = digAt π k x + digAt π k x'

/-- **B.22d** [lemma] ENV-A′. -/
axiom digAt_zero (x : O) : digAt π 0 x = IsLocalRing.residue O x

/-- **B.23** [def] ENV-A. `digPoly π k a` : the coefficientwise digit of `a` at height `k`, as a
polynomial over the residue field. When `π ^ k` divides every coefficient of `a`, this is
`(a / π ^ k) mod π`. -/
noncomputable def digPoly (π : O) (k : ℕ) (a : Polynomial O) : Polynomial (ResidueField O) :=
  ∑ i ∈ Finset.range (a.natDegree + 1), Polynomial.C (digAt π k (a.coeff i)) * Polynomial.X ^ i

/-- **B.24a** [lemma] ENV-A′. -/
axiom digPoly_coeff (hπ : Irreducible π) (k i : ℕ) (a : Polynomial O) :
    (digPoly π k a).coeff i = digAt π k (a.coeff i)

/-- **B.24b** [lemma] ENV-A′. [repaired: A-F.5] `(hπ : Irreducible π)` added — the
unhypothesized form is equivalent to `∀ π k, digAt π k (0 : O) = 0`, independent at our pin
(the `Exists.choose` witness of `π ^ k ∣ 0` is unconstrained when `π ^ k = 0`); `hπ` forces
`π ^ k ≠ 0`, which suffices (blueprint amendment A-F.5). -/
axiom degree_digPoly_le (hπ : Irreducible π) (k : ℕ) (a : Polynomial O) :
    (digPoly π k a).degree ≤ a.degree

/-- **B.24c** [lemma] ENV-A′. -/
axiom digPoly_eq_map (hπ : Irreducible π) {k : ℕ} {a b : Polynomial O}
    (h : a = Polynomial.C (π ^ k) * b) : digPoly π k a = b.map (IsLocalRing.residue O)

/-- **B.24d** [lemma] ENV-A′. -/
axiom digPoly_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O}
    (h : (k : ℕ∞) ≤ gaussVal a) : digPoly π k a = 0 ↔ ((k + 1 : ℕ) : ℕ∞) ≤ gaussVal a

/-- **B.25a** [def] ENV-A. `resField φ = F[y]/(φ̄)` : the order-1 residual field of the key `φ`. -/
abbrev resField (φ : Polynomial O) : Type _ := AdjoinRoot (φ.map (IsLocalRing.residue O))

/-- **B.25b** [def] ENV-A. **DEFECT B-D1** — signed body
`AdjoinRoot.instField (hf := hφ.irred.ne_zero)` does not elaborate at our pin (`instField` takes
`[Fact (Irreducible f)]`, has no `hf`); the minimal repair below supplies the `Fact` from
`IsKey.irred`. **DEFECT B-D3** — declared `noncomputable instance` in the blueprint, which is a
HARD ERROR at our pin ("This instance has 1 argument that cannot be inferred using typeclass
synthesis … `(hφ : IsKey φ)`"); demoted to `noncomputable def` here, the minimal change that keeps
the signed type (`@[reducible]` is then forced by the linter for a class-typed `def`). -/
@[reducible] noncomputable def instFieldResField {φ : Polynomial O} (hφ : IsKey φ) :
    Field (resField φ) :=
  haveI : Fact (Irreducible (φ.map (IsLocalRing.residue O))) := ⟨hφ.irred⟩
  AdjoinRoot.instField

/-- **B.25c** [def] ENV-A. The residual reduction `O[X] → resField φ` at height `k`. -/
noncomputable def resMk (π : O) (φ : Polynomial O) (k : ℕ) (a : Polynomial O) : resField φ :=
  AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) (digPoly π k a)

section ENVC1
-- ENV-C (blueprint §0.1): ENV-A + completeness + residue finiteness.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.26a** [lemma] ENV-C. -/
axiom finrank_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Module.finrank (ResidueField O) (resField φ) = φ.natDegree

/-- **B.26b** [lemma] ENV-C. **DEFECT B-D2** — the SIGNATURE gives no body; `Finite (resField φ)`
is a proof obligation, so it lands as an `axiom`, not a real body. **DEFECT B-D3** — TC-unreachable
as an `instance` (explicit `hφ`). -/
axiom instFiniteResField {φ : Polynomial O} (hφ : IsKey φ) : Finite (resField φ)

/-- **B.26c** [lemma] ENV-C. -/
axiom card_resField {φ : Polynomial O} (hφ : IsKey φ) :
    Nat.card (resField φ) = residueCard O ^ φ.natDegree

end ENVC1

/-- **B.27a** [lemma] ENV-D + `[Finite K]`. -/
axiom irreducible_separable {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : Irreducible p) : p.Separable

/-- **B.27b** [lemma] ENV-D + `[Finite K]`. -/
axiom separable_iff_squarefree {K : Type*} [Field K] [Finite K] {p : Polynomial K}
    (hp : p ≠ 0) : p.Separable ↔ Squarefree p

/-- **B.28** [def] ENV-A. `resCoeff` : the `k`-th residual coefficient of the `(u,ℓ)`-side of
`f`'s `φ`-adic polygon. *(§12 rule 6 FRAGILE — dependent `Nonempty` argument plus the `H₀`
pin.)* -/
noncomputable def resCoeff (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ k : ℕ) : resField φ :=
  resMk π φ (H₀ - u * k) (dev φ f (sideMin φ f u ℓ h + ℓ * k))

/-- **B.29** [def] ENV-A. `resPoly π φ f u ℓ h H₀` : the residual polynomial
`R_{u/ℓ}(f) ∈ (resField φ)[Y]`. *(§12 rule 6 FRAGILE.)* -/
noncomputable def resPoly (π : O) (φ f : Polynomial O) (u ℓ : ℕ)
    (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ) : Polynomial (resField φ) :=
  ∑ k ∈ Finset.range (sideDeg φ f u ℓ h + 1),
    Polynomial.C (resCoeff π φ f u ℓ h H₀ k) * Polynomial.X ^ k

/-- **B.30a** [lemma] ENV-A′. -/
axiom resCoeff_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) {k : ℕ} (hk : k ≤ sideDeg φ f u ℓ h) :
    resCoeff π φ f u ℓ h H₀ k = 0 ↔ ¬ OnSide φ f u ℓ (sideMin φ f u ℓ h + ℓ * k)

/-- **B.30b** [lemma] ENV-A′. -/
axiom natDegree_resPoly (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) :
    (resPoly π φ f u ℓ h H₀).natDegree = sideDeg φ f u ℓ h ∧
      (resPoly π φ f u ℓ h H₀).coeff 0 ≠ 0

/-! ## §5 — the slot lemma and the product law (B.31–B.36) -/

/-- **B.31a** [lemma] ENV-A′. -/
axiom gaussVal_le_modByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a %ₘ φ)

/-- **B.31b** [lemma] ENV-A′. -/
axiom gaussVal_le_divByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a /ₘ φ)

/-- **B.31c** [lemma] ENV-A′. -/
axiom gaussVal_le_npHgt (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (f : Polynomial O) (j : ℕ) : gaussVal f ≤ npHgt φ f j

/-- **B.32** [lemma] ENV-A′. -/
axiom inf_weight_le_suppVal (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) {f : Polynomial O}
    {c : ℕ → Polynomial O} {K : ℕ} (hc : ∑ t ∈ Finset.range K, c t * φ ^ t = f) :
    (Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ)) ≤ suppVal φ f u ℓ

/-- **B.33** [lemma] ENV-A′. -/
axiom suppVal_add_le_suppVal_mul (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (f g : Polynomial O) :
    suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ

/-- **B.34** [def] ENV-A. `IsPure φ f u ℓ` : the `φ`-adic polygon of `f` is a single side of slope
`−u/ℓ` spanning the whole abscissa range `0 … f.natDegree / φ.natDegree`. -/
def IsPure (φ f : Polynomial O) (u ℓ : ℕ) : Prop :=
  OnSide φ f u ℓ 0 ∧ OnSide φ f u ℓ (f.natDegree / φ.natDegree)

section ENVFIN1
-- ENV-A′ + `[Finite (ResidueField O)]` (B.35's ENVIRONMENT: "via B.26, which B.30 consumes").
variable [Finite (ResidueField O)]

/-- **B.35a** [theorem] ENV-A′ + `[Finite (ResidueField O)]`. **[repaired: A-F.6]** —
`(hu : 0 < u)` and `(hfd) (hgd)` added; the frozen form is machine-REFUTED (blueprint amendment
A-F.6: `f = g = X` at `φ = X²+1` over `ℤ₃`, `u = ℓ = 1` — `IsPure`'s truncated right endpoint). -/
axiom suppVal_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic)
    (hfd : φ.natDegree ∣ f.natDegree) (hgd : φ.natDegree ∣ g.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) :
    suppVal φ (f * g) u ℓ = suppVal φ f u ℓ + suppVal φ g u ℓ ∧ IsPure φ (f * g) u ℓ

/-- **B.35b** [theorem] ENV-A′ + `[Finite (ResidueField O)]`. **DEFECT B-D9** — the signed
`(hf' hg' hfg')` binders carry no types; expanded per the node's own gloss ("the three `Nonempty`
witnesses … are supplied by B.18"). **[repaired: A-F.6]** — `(hu : 0 < u)` and `(hfd) (hgd)`
added; the frozen form is machine-REFUTED even with the divisibilities (amendment A-F.6:
`f = g = X²+X+1` at `u = 0`, `ℓ = 1` — the `φ`-carry sits at the same weight as the digit read). -/
axiom resPoly_mul_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f g : Polynomial O}
    (hf : f.Monic) (hg : g.Monic)
    (hfd : φ.natDegree ∣ f.natDegree) (hgd : φ.natDegree ∣ g.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ)
    {H₀f H₀g : ℕ} (hHf : npHgt φ f 0 = (H₀f : ℕ∞)) (hHg : npHgt φ g 0 = (H₀g : ℕ∞))
    (hf' : (sideSet φ f u ℓ).Nonempty) (hg' : (sideSet φ g u ℓ).Nonempty)
    (hfg' : (sideSet φ (f * g) u ℓ).Nonempty) :
    resPoly π φ (f * g) u ℓ hfg' (H₀f + H₀g)
      = resPoly π φ f u ℓ hf' H₀f * resPoly π φ g u ℓ hg' H₀g

end ENVFIN1

/-- **B.36a** [lemma] ENV-A′. -/
axiom mk_eq_zero_iff_of_degree_lt {φ : Polynomial O} (hφ : IsKey φ)
    {p : Polynomial (ResidueField O)} (hp : p.degree < (φ.natDegree : WithBot ℕ)) :
    AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) p = 0 ↔ p = 0

/-- **B.36b** [lemma] ENV-A′. -/
axiom resMk_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) :
    resMk π φ k a = 0 ↔ digPoly π k a = 0

/-- **B.36c** [lemma] ENV-A′. -/
axiom resMk_ne_zero (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {k : ℕ}
    {a : Polynomial O} (ha : a.degree < φ.degree) (ha0 : a ≠ 0)
    (hk : gaussVal a = (k : ℕ∞)) : resMk π φ k a ≠ 0

/-! ## §6 — the two dissections (B.37–B.48) -/

section ENVC2
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.37** [def] ENV-C. `GradedCoprime π φ u ℓ g h` : `g` and `h` are `(u,ℓ)`-pure with coprime
residual polynomials. -/
def GradedCoprime (π : O) (φ : Polynomial O) (u ℓ : ℕ) (g h : Polynomial O) : Prop :=
  ∃ (Hg Hh : ℕ) (hg' : (sideSet φ g u ℓ).Nonempty) (hh' : (sideSet φ h u ℓ).Nonempty),
    npHgt φ g 0 = (Hg : ℕ∞) ∧ npHgt φ h 0 = (Hh : ℕ∞) ∧
    IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧
    IsCoprime (resPoly π φ g u ℓ hg' Hg) (resPoly π φ h u ℓ hh' Hh)

/-- **B.38** [lemma] ENV-D. -/
axiom exists_solve_resField {K : Type*} [Field K] {G H : Polynomial K}
    (hG : G.Monic) (hH : H.Monic) (hcop : IsCoprime G H) {W : Polynomial K}
    (hW : W.degree < ((G.natDegree + H.natDegree : ℕ) : WithBot ℕ)) :
    ∃ U V : Polynomial K, U.degree < (G.natDegree : WithBot ℕ) ∧
      V.degree < (H.natDegree : WithBot ℕ) ∧ W = H * U + G * V

/-- **B.39** [lemma] ENV-C. **[repaired: A-F.6]** — `(hu : 0 < u)` and `(hgd) (hhd)` added; the
frozen form is machine-REFUTED (amendment A-F.6: `g = h = X`, `e = π^c` at `φ = X²+1` over `ℤ₃`,
`u = ℓ = 1` — `GradedCoprime` holds since `resPoly X` is a unit constant, and no `U, V` exist).
**[repaired: A-F.8]** — the two conclusion bounds re-stated in `degree` (`WithBot ℕ`): the
A-F.6 form is machine-REFUTED again (`B39_REFUTATION.lean.txt`: `g = 1`, `h = φ + C π`, `e = 0`,
`c = 0` at ANY DVR/key — `U.natDegree < 0` is `False` in `ℕ`). The `degree` form is B.38's own
shape and the landed template's; the degenerate divisor is served by `U = 0` (`degree ⊥`). -/
axiom exists_graded_solve (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h : Polynomial O}
    (hg : g.Monic) (hh : h.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (hhd : φ.natDegree ∣ h.natDegree)
    (hgh : GradedCoprime π φ u ℓ g h)
    {c : ℕ} {e : Polynomial O} (hdeg : e.natDegree < (g * h).natDegree)
    (he : ((c : ℕ) : ℕ∞) ≤ suppVal φ e u ℓ) :
    ∃ U V : Polynomial O, U.degree < g.degree ∧ V.degree < h.degree ∧
      ((c + 1 : ℕ) : ℕ∞) ≤ suppVal φ (e - (h * U + g * V)) u ℓ

end ENVC2

section ENVB1
-- ENV-B (blueprint §0.1): ENV-A + completeness.
variable [IsAdicComplete (maximalIdeal O) O]

/-- **B.40** [lemma] ENV-B. -/
axiom exists_graded_limit (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd0 : 0 < φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ) (d : ℕ) (p : ℕ → Polynomial O)
    (hdeg : ∀ k, (p k).natDegree < d)
    (hstep : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (p (k + 1) - p k) u ℓ) :
    ∃ P : Polynomial O, P.natDegree < d ∧ ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (P - p k) u ℓ

end ENVB1

section ENVC3
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.41** [theorem] ENV-C. **[repaired: A-F.6]** — `(hu : 0 < u)` and `(hfd)` added; the
frozen form is machine-REFUTED (amendment A-F.6: `f = X`, `G = H = 1` at `φ = X²+1` over `ℤ₃`,
`u = ℓ = 1` — `hprod` holds with `c = θ` and the conclusion forces `X = 1`). -/
axiom exists_graded_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O}
    (hf : f.Monic) (hfd : φ.natDegree ∣ f.natDegree)
    (hpure : IsPure φ f u ℓ) {H₀ : ℕ} (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞))
    (hne : (sideSet φ f u ℓ).Nonempty)
    {G H : Polynomial (resField φ)} (hG : G.Monic) (hH : H.Monic) (hGH : IsCoprime G H)
    (hprod : ∃ c : (resField φ)ˣ,
      resPoly π φ f u ℓ hne H₀ = Polynomial.C (c : resField φ) * (G * H)) :
    ∃ g h : Polynomial O, g.Monic ∧ h.Monic ∧ f = g * h ∧
      g.natDegree = ℓ * φ.natDegree * G.natDegree ∧
      h.natDegree = ℓ * φ.natDegree * H.natDegree ∧
      IsPure φ g u ℓ ∧ IsPure φ h u ℓ ∧ GradedCoprime π φ u ℓ g h

/-- **B.42** [theorem] ENV-C. **[repaired: A-F.6]** — conclusion STRENGTHENED (hypotheses
unchanged): clause 1 records `0 < p.1` (proof step 2 derives every slope positive from `hres`),
clause 3 records `φ.natDegree ∣ (F p).natDegree` (B.41's pinned factor degrees) — both are what
the repaired B.48 needs at B.63. **[repaired: A-F.9]** — `(h0 : dev φ f 0 ≠ 0)` added: the
A-F.6 form is machine-REFUTED (`B42_REFUTATION.lean.txt`: `f = φ`, `μ = 1` at ANY DVR/key —
`sideSet φ φ u ℓ = {1}`, the `↔`-clause forces `s = ∅`, clause 4 reads `φ = 1`). `h0` is the
classical `φ ∤ f` ([GN15] Thm 2.3 peels `φ^{ord_φ(g)}` explicitly). Clause 3 further records
`dev φ (F p) 0 ≠ 0` and `0 < (F p).natDegree` (proof-free: B.41's `GradedCoprime` output pins
the factors' left heights, and the peeled degrees are `ℓ·m·d`, `d ≥ 1`) — they discharge
B.48's `hH₀`/`hne`/`hd` at B.63. -/
axiom exists_slope_factorization (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O),
      (∀ p ∈ s, 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 * q.2 ≠ q.1 * p.2) ∧
      (∀ p ∈ s, (F p).Monic ∧ IsPure φ (F p) p.1 p.2 ∧
        φ.natDegree ∣ (F p).natDegree ∧
        dev φ (F p) 0 ≠ 0 ∧ 0 < (F p).natDegree) ∧
      f = ∏ p ∈ s, F p ∧
      (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
        (1 < (sideSet φ f u ℓ).card ↔ (u, ℓ) ∈ s))

/-- **B.43** [lemma] ENV-C. **[repaired: A-F.6]** — `(hu)`, the four divisibilities and the
purity of `g'`, `h'` added: the node's own STATEMENT ("under B.41's hypotheses"; "g, g' pure …
h, h' pure") was elided from the frozen signature (the A-F.4 class); no counterexample to the
weaker form is on record — fidelity restoration, see the A-F.6 audit table and route note. -/
axiom graded_factorization_unique (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (hhd : φ.natDegree ∣ h.natDegree)
    (hgd' : φ.natDegree ∣ g'.natDegree) (hhd' : φ.natDegree ∣ h'.natDegree)
    (hgp' : IsPure φ g' u ℓ) (hhp' : IsPure φ h' u ℓ)
    (hcopGH : GradedCoprime π φ u ℓ g h)
    (hgg' : ∀ hne hne' H₀, resPoly π φ g u ℓ hne H₀ = resPoly π φ g' u ℓ hne' H₀)
    (hhh' : ∀ hne hne' H₀, resPoly π φ h u ℓ hne H₀ = resPoly π φ h' u ℓ hne' H₀)
    (heq : g * h = g' * h') : g = g' ∧ h = h'

/-- **B.44** [lemma] ENV-C. -/
axiom exists_scaleRoots_of_pure_integral (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hn : 0 < f.natDegree) {u : ℕ} (hpure : IsPure X f u 1)
    (hsupp : suppVal X f u 1 = ((u * f.natDegree : ℕ) : ℕ∞)) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧
      f = G.scaleRoots (π ^ u) ∧ typeOf f = typeOf G ∧
      (∀ i, IsLocalRing.residue O (G.coeff i) = digAt π (u * (f.natDegree - i)) (f.coeff i))

end ENVC3

/-- **B.45** [lemma] ENV-D + `[Finite K]`. -/
axiom exists_residual_factorization {K : Type*} [Field K] [Finite K]
    {R : Polynomial K} (hR : R.Monic) (hd : 0 < R.natDegree) :
    ∃ (s : Finset (Polynomial K)) (a : Polynomial K → ℕ),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ) ∧ (∀ ψ ∈ s, 0 < a ψ) ∧
      (∀ ψ ∈ s, ∀ χ ∈ s, ψ ≠ χ → IsCoprime ψ χ) ∧
      R = ∏ ψ ∈ s, ψ ^ a ψ ∧
      (R.Separable ↔ ∀ ψ ∈ s, a ψ = 1)

/-- **B.46** [lemma] ENV-D. -/
axiom isCoprime_pow_of_not_dvd {K : Type*} [Field K] {ψ S : Polynomial K}
    (hψ : Irreducible ψ) {a : ℕ} (h : ¬ ψ ∣ S) : IsCoprime (ψ ^ a) S

/-- **B.47** [lemma] ENV-A. [repaired: A-F.4] `(hψ : ψ.Monic)` added — the original signed
form (no hypothesis on `ψ`) is machine-REFUTED (blueprint amendment A-F.4: `O = ℤ_[2]`,
`φ = X²`, `ψ = C (root φ̄) * X`, `a = 2`); the STATEMENT prose always asserted "ψ monic
irreducible", and monicity alone suffices via `Polynomial.Monic.natDegree_pow`. -/
axiom natDegree_of_residual_piece {φ : Polynomial O} {u ℓ : ℕ} {g : Polynomial O}
    {ψ : Polynomial (resField φ)} {a : ℕ} (hψ : ψ.Monic)
    (hg : g.natDegree = ℓ * φ.natDegree * (ψ ^ a).natDegree) :
    g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree

section ENVC4
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.48** [theorem] ENV-C. **[repaired: A-F.6]** — `(hu : 0 < u)` and `(hfd)` added; the
frozen form is machine-REFUTED (amendment A-F.6: `f = X³+4X+3` at `φ = X²+1` over `ℤ₃`,
`u = ℓ = 1` — pure with `sideDeg = 1 > 0`, yet every conclusion factor degree is even while
`deg f = 3`). Both free at B.63 via B.42's strengthened conclusion. -/
axiom exists_residual_dissection (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O}
    (hf : f.Monic) (hfd : φ.natDegree ∣ f.natDegree)
    (hpure : IsPure φ f u ℓ) (hne : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg φ f u ℓ hne) :
    ∃ (s : Finset (Polynomial (resField φ))) (a : Polynomial (resField φ) → ℕ)
      (F : Polynomial (resField φ) → Polynomial O),
      (∀ ψ ∈ s, ψ.Monic ∧ Irreducible ψ ∧ 0 < a ψ) ∧
      f = ∏ ψ ∈ s, F ψ ∧
      (∀ ψ ∈ s, (F ψ).Monic ∧ IsPure φ (F ψ) u ℓ ∧
        (F ψ).natDegree = ℓ * φ.natDegree * a ψ * ψ.natDegree) ∧
      (∀ ψ ∈ s, ∃ (hne' : (sideSet φ (F ψ) u ℓ).Nonempty) (H : ℕ) (c : (resField φ)ˣ),
        resPoly π φ (F ψ) u ℓ hne' H = Polynomial.C (c : resField φ) * ψ ^ a ψ)

/-! ## §7 — the `(e,f)` assignment and the leaf theorem (B.49–B.62) -/

/-- **B.49a** [lemma] ENV-C. **DEFECT B-D2** — no body in the SIGNATURE; `IsLocalRing (AdjoinRoot g)`
is a proof obligation, so it lands as an `axiom`. **DEFECT B-D3** — TC-unreachable as an
`instance`. -/
axiom instLocalRingAdjoinRoot {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    IsLocalRing (AdjoinRoot g)

/-- **B.49b** [lemma] ENV-C. **DEFECT B-D2** — no body in the SIGNATURE (and it is *data*, an
`≃+*`), so it lands as an `axiom`. **DEFECT B-D3** — the type does not elaborate without
`IsLocalRing (AdjoinRoot g)`, which B.49a cannot supply by TC; the instance is applied explicitly
below (minimal, unambiguous stub-side repair). -/
axiom residueFieldEquiv {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    @IsLocalRing.ResidueField (AdjoinRoot g) _ (instLocalRingAdjoinRoot hφ hg hk hres) ≃+*
      resField φ

end ENVC4

open DirectSum in
/-- **B.50** [lemma] ENV-A′. **DEFECT B-D13** — the signed type uses the `⨁` big-operator, whose
notation is `scoped[DirectSum]` at our pin; ENV-A′ opens only `IsLocalRing Polynomial`, so the
verbatim signature fails with `unknown identifier 'i'` (`⨁` parses as a prefix operator with no
binder). Repaired minimally and unambiguously with `open DirectSum in`. -/
axiom exists_smith_of_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] (hr : 0 < Module.finrank O A)
    {z : A} (hz : Algebra.norm O z ≠ 0) :
    ∃ e : Fin (Module.finrank O A) → ℕ,
      Nonempty ((A ⧸ (Ideal.span {z}).restrictScalars O) ≃ₗ[O]
        (⨁ i, O ⧸ (Ideal.span {π ^ e i}))) ∧
      IsDiscreteValuationRing.addVal O (Algebra.norm O z) = ((∑ i, e i : ℕ) : ℕ∞)

/-- **B.51** [lemma] ENV-A′. The **contract declaration** ("the one the fleet must land").
**DEFECT B-D6** — the node's first signed block, `residueDeg_dvd_sum_of_local`, ends in
`s ∣ (Nat.find (…) : ℕ)` and cannot be signed at all; it is NOT landed here. -/
axiom residueDeg_dvd_addVal_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [IsLocalRing A]
    [Algebra O A] [Module.Free O A] [Module.Finite O A] {s : ℕ}
    (hs : Module.finrank (ResidueField O) (IsLocalRing.ResidueField A) = s)
    {z : A} {k : ℕ} (hk : IsDiscreteValuationRing.addVal O (Algebra.norm O z) = (k : ℕ∞)) :
    s ∣ k

section ENVC5
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.52** [lemma] ENV-C. -/
axiom key_natDegree_dvd_inertiaDegOf (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    φ.natDegree ∣ inertiaDegOf g

/-- **B.53** [lemma] ENV-C. -/
axiom addVal_norm_key_eval (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) (h0 : dev φ g 0 ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (Polynomial.aeval (AdjoinRoot.root g) φ))
      = (φ.natDegree : ℕ∞) * gaussVal (dev φ g 0)

/-- **B.54** [lemma] ENV-C. **DEFECT B-D7** — the signed `hres` binder is missing its closing
parenthesis; closed here as B.55's byte-identical `hres` shows. -/
axiom inertiaDegOf_dvd_key_mul_resDeg (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)) :
    inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne

/-- **B.55a** [lemma] ENV-C. -/
axiom inertiaDegOf_bracket (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)) :
    φ.natDegree ∣ inertiaDegOf g ∧ inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne

/-- **B.55b** [lemma] ENV-C. **DEFECT B-D8** — signed as `(… same hypotheses …)`; expanded from
B.55a's list immediately above (the node's STATEMENT: "Under the joint hypotheses of B.52 and
B.54 … In particular if `d = 1`"). -/
axiom inertiaDegOf_eq_of_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    (h1 : sideDeg φ g u ℓ hne = 1) :
    inertiaDegOf g = φ.natDegree ∧ ramIndexOf g = ℓ

end ENVC5

/-- **B.56a** [lemma] ENV-A (arithmetic; no `O`). -/
axiom factorizationType_singleton {σ : FactorizationType} {n : ℕ} (hn : 0 < n)
    (hdeg : σ.degree = n) (hge : ∀ p ∈ σ.data, n ≤ p.1 * p.2) :
    ∃ p, σ.data = {p} ∧ p.1 * p.2 = n

/-- **B.56b** [lemma] ENV-A (arithmetic; no `O`). -/
axiom factorizationType_eq_of_dvd {σ : FactorizationType} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdeg : σ.degree = a * b) (hpos : ∀ p ∈ σ.data, 0 < p.1 ∧ 0 < p.2)
    (hA : ∀ p ∈ σ.data, a ∣ p.1) (hB : ∀ p ∈ σ.data, b ∣ p.2) :
    σ = ⟨{(a, b)}⟩

section ENVC6
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.57** [lemma] ENV-C. **[repaired: A-F.6]** — `(hgd)` added; the frozen form is
machine-REFUTED (amendment A-F.6: `g = X = X * 1` at `φ = X²+1` over `ℤ₃`, `u = ℓ = 1` — the
residue clause forces `X̄ = φ̄⁰ = 1`). -/
axiom isPure_of_monic_factor (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g g₁ g₂ : Polynomial O}
    (hg : g.Monic) (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (heq : g = g₁ * g₂)
    (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty) :
    ∃ (hne₁ : (sideSet φ g₁ u ℓ).Nonempty) (hne₂ : (sideSet φ g₂ u ℓ).Nonempty),
      IsPure φ g₁ u ℓ ∧ IsPure φ g₂ u ℓ ∧
      sideDeg φ g₁ u ℓ hne₁ + sideDeg φ g₂ u ℓ hne₂ = sideDeg φ g u ℓ hne ∧
      g₁.map (IsLocalRing.residue O)
        = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g₁ u ℓ hne₁)

/-- **B.58** [theorem] ENV-C. -/
axiom typeOf_leaf_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (h1 : sideDeg φ g u ℓ hne = 1)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ ℓ) :
    typeOf g = ⟨{(ℓ, φ.natDegree)}⟩

/-- **B.59** [lemma] ENV-C. **[repaired: A-F.7]** — re-signed at `φ = X` (`{φ} (hφ : IsKey φ)`
removed). The frozen general-key form is REFUTED by a compiled witness
(`leanfinal/Uniformity/ChapB/B59_REFUTATION.lean.txt`, kept as provenance): `hscale` is
`φ = X`-shaped, and at `2 ≤ φ.natDegree` it forces `sideDeg = 0`, so `resPoly` is a unit
constant (never irreducible) while `Ḡ` is free to be irreducible (`g = G = X` witnesses). -/
axiom irreducible_map_iff_irreducible_resPoly (hπ : Irreducible π)
    {u : ℕ} (hu : 0 < u) {g G : Polynomial O} (hg : g.Monic) (hG : G.Monic)
    (hGdeg : G.natDegree = g.natDegree) (hscale : g = G.scaleRoots (π ^ u))
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) :
    Irreducible (G.map (IsLocalRing.residue O)) ↔ Irreducible (resPoly π X g u 1 hne H₀)

/-- **B.60** [theorem] ENV-C. **[repaired: A-F.7]** — re-signed at `φ = X` with B.59 (the
`ℓ = 1, m ≥ 2, d ≥ 2` region now routes to B.61's `hBOX`; the conjectured general-`φ`
extraction B.44′ is REFUTED — blueprint amendment A-F.7). -/
axiom typeOf_leaf_integral_slope (hπ : Irreducible π)
    {u : ℕ} (hu : 0 < u) {g : Polynomial O} (hg : g.Monic)
    (hpure : IsPure X g u 1) (hne : (sideSet X g u 1).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt X g 0 = (H₀ : ℕ∞)) (hd : 0 < sideDeg X g u 1 hne)
    (hres : g.map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O)) ^ (sideDeg X g u 1 hne))
    (hirr : Irreducible (resPoly π X g u 1 hne H₀)) :
    typeOf g = ⟨{(1, (X : Polynomial O).natDegree * sideDeg X g u 1 hne)}⟩

/-- **B.61** [theorem] ENV-C. -/
axiom typeOf_leaf_of_resDeg_lower_bound (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (hd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    (hBOX : ∀ g' ∈ monicFactors g,
      φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g') :
    typeOf g = ⟨{(ℓ, φ.natDegree * sideDeg φ g u ℓ hne)}⟩

/-! **B.62 is NOT SIGNED** — §12 rule 3: its SIGNATURE field is explicitly *"not frozen — this
node is OPTIONAL … the orchestrator must re-sign it before it fires"* (the `G.23a` comment-out
precedent class). Signing it now would freeze an interface the mathlib spectral-norm route has not
validated. -/

/-! ### RE-PLAN SUPPLIERS (signed here per §12 rule 2, BEFORE B.63/B.66/B.71/B.79a/B.79b/B.80)

Five declarations booked in committed prose with no SIGNATURE block: **B.63a** `typeOf_prod`
(booked at B.63's SIZE field and in B.67's/B.80's DEPENDS) and **B.66a** `slopeFinset`,
`resFactorFinset`, `mem_slopeFinset`, `mem_resFactorFinset` (booked at B.79's ⚠ RE-PLAN item and
A-§9.5). See **DEFECT B-D4**: the two `Finset`-valued suppliers are underdetermined and land as
`axiom`-typed opaque constants; the membership lemmas' elisions are expanded to the determinate
content of B.42's characterisation clause and B.45's factorisation, and are NOT contract text. -/

/-- **B.63a** [RE-PLAN supplier] ENV-A. `typeOf_prod` — the `Finset`-indexed `typeOf_mul`
("a 20-line `Finset.prod_induction`"; landed `typeOf_mul` is binary). Signed from the booking:
the conclusion shape is fixed by B.67's own conclusion `(typeOf f).data = ∑ i ∈ s,
(typeOf (g i)).data`. -/
axiom typeOf_prod {ι : Type*} {s : Finset ι} {g : ι → Polynomial O}
    (hg : ∀ i ∈ s, (g i).Monic) :
    (typeOf (∏ i ∈ s, g i)).data = ∑ i ∈ s, (typeOf (g i)).data

/-- **B.66a-i** [RE-PLAN supplier] ENV-C. `slopeFinset π φ f` — the canonical slope `Finset` of
B.42, promoted from B.66's private helper. **DEFECT B-D4**: underdetermined (B.42 produces it
existentially; no abscissa bound is stated), so no real body is possible — `axiom`-typed opaque
constant per the ChapG D2 precedent. -/
axiom slopeFinset (π : O) (φ f : Polynomial O) : Finset (ℕ × ℕ)

/-- **B.66a-ii** [RE-PLAN supplier] ENV-C. `resFactorFinset π φ f p` — the canonical residual
factor `Finset` of B.45 at the slope `p`, promoted from B.66's private helper. **DEFECT B-D4**:
underdetermined, `axiom`-typed opaque constant. -/
axiom resFactorFinset (π : O) (φ f : Polynomial O) (p : ℕ × ℕ) : Finset (Polynomial (resField φ))

/-- **B.66a-iii** [RE-PLAN supplier] ENV-C. `mem_slopeFinset`. **DEFECT B-D4** — booked as
`mem_slopeFinset ↔ (sideSet …).Nonempty ∧ 1 ≤ card ∧ …`; the first two conjuncts are redundant
(`1 ≤ card ↔ Nonempty`) and the third is elided. Expanded to B.42's own characterisation clause,
which is the determinate content. NOT contract text. -/
axiom mem_slopeFinset {φ f : Polynomial O} {p : ℕ × ℕ} :
    p ∈ slopeFinset π φ f ↔
      (0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ 1 < (sideSet φ f p.1 p.2).card)

/-- **B.66a-iv** [RE-PLAN supplier] ENV-C. `mem_resFactorFinset`. **DEFECT B-D4** — booked as
`mem_resFactorFinset ↔ ψ ∈ (B.45 factorization)`, whose right-hand side is existential;
expanded to the determinate content (monic irreducible dividing the side's residual polynomial at
the GC-1 `sideMin` pin). NOT contract text. -/
axiom mem_resFactorFinset {φ f : Polynomial O} {p : ℕ × ℕ} {ψ : Polynomial (resField φ)} :
    ψ ∈ resFactorFinset π φ f p ↔
      (ψ.Monic ∧ Irreducible ψ ∧
        ∀ (h : (sideSet φ f p.1 p.2).Nonempty) (H₀ : ℕ),
          npHgt φ f (sideMin φ f p.1 p.2 h) = (H₀ : ℕ∞) →
            ψ ∣ resPoly π φ f p.1 p.2 h H₀)

/-! ## §8 — NS-6, the order-0 peel, and `typeOf` transport (B.63–B.74) -/

/-- **B.63** [theorem] ENV-C. **DEFECT B-D10** — `hperim` is elided in the SIGNATURE and is
expanded here from §12 item 4(a)'s shared-clause dictionary, verbatim (this file is the single
source for B.63, B.71, B.79a, B.79b, B.80, B.81, B.82). `hsep` is the node's own written-out
clause at the A-F.1/GC-1 `sideMin` pin. -/
axiom typeOf_of_separable_residuals (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
      1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
        (resPoly π φ f u ℓ h H₀).Separable)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ f → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    ∃ (T : Finset ((ℕ × ℕ) × Polynomial (resField φ))) (F : _ → Polynomial O),
      f = ∏ t ∈ T, F t ∧
      (typeOf f).data = (T.val.map (fun t => (t.1.2, φ.natDegree * t.2.natDegree)))

end ENVC6

/-- **B.64** [lemma] ENV-A. -/
axiom lt_natDegree_of_multiplicity_two {φ : Polynomial O} {u ℓ a : ℕ} (hℓ : 0 < ℓ)
    (hm : 0 < φ.natDegree) {ψ : Polynomial (resField φ)} (hψ : 0 < ψ.natDegree) (ha : 2 ≤ a)
    {g : Polynomial O} (hg : g.natDegree = ℓ * φ.natDegree * a * ψ.natDegree) :
    ℓ * φ.natDegree * ψ.natDegree < g.natDegree

section ENVC7
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.65** [theorem] ENV-C. **DEFECT B-D5 — NOT CONTRACT TEXT.** Clause 2 is signed
`(∀ u ℓ ψ, … multiplicity = 1)`; "multiplicity" is B.45's existentially-produced exponent `a ψ`,
which no closed statement can name, so rule 5 cannot expand the elision. The multiplicity-free
reading `¬ ψ ^ 2 ∣ resPoly …` is signed below as an INTERPRETIVE expansion, to keep the
elaboration gate; the blueprint owner must re-sign clause 2. -/
axiom ns6_biconditional (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ) :
    (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
        1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
          (resPoly π φ f u ℓ h H₀).Separable)
      ↔ (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ f u ℓ).Nonempty,
          1 < (sideSet φ f u ℓ).card → ∀ H₀ : ℕ, npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) →
            ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
              ¬ (ψ ^ 2 ∣ resPoly π φ f u ℓ h H₀))

/-- **B.66** [def] ENV-C. `order1Type π φ f` : the `FactorizationType` predicted by `f`'s order-1
polygon-and-residual data. `0` (the empty type) when the data are not separable — the junk branch
is never read. *(§12 rule 6 FRAGILE — `Classical` + `Multiset.bind` over the B.66a finsets.)* -/
noncomputable def order1Type (π : O) (φ f : Polynomial O) : FactorizationType :=
  open Classical in
  ⟨(slopeFinset π φ f).val.bind (fun p =>
      (resFactorFinset π φ f p).val.map (fun ψ => (p.2, φ.natDegree * ψ.natDegree)))⟩

/-- **B.67** [theorem] ENV-C. -/
axiom exists_order0_peel {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ₀ : ι → Polynomial (ResidueField O)}
    {a : ι → ℕ} (hmon : ∀ i ∈ s, (φ₀ i).Monic) (hirr : ∀ i ∈ s, Irreducible (φ₀ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → φ₀ i ≠ φ₀ j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, (φ₀ i) ^ (a i)) :
    ∃ g : ι → Polynomial O, (∀ i ∈ s, (g i).Monic) ∧ f = ∏ i ∈ s, g i ∧
      (∀ i ∈ s, (g i).map (IsLocalRing.residue O) = (φ₀ i) ^ (a i)) ∧
      (typeOf f).data = ∑ i ∈ s, (typeOf (g i)).data

/-- **B.68** [theorem] ENV-C. -/
axiom typeOf_of_separable_reduction {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {r : ι → Polynomial (ResidueField O)}
    (hmon : ∀ i ∈ s, (r i).Monic) (hirr : ∀ i ∈ s, Irreducible (r i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r i ≠ r j)
    (hres : f.map (IsLocalRing.residue O) = ∏ i ∈ s, r i) :
    typeOf f = ⟨∑ i ∈ s, {((1 : ℕ), (r i).natDegree)}⟩

end ENVC7

/-- **B.69a** [lemma] ENV-A′. -/
axiom dev_comp_shift (φ : Polynomial O) (c : O) (f : Polynomial O) (j : ℕ) :
    dev (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j
      = (dev φ f j).comp (X + Polynomial.C c)

/-- **B.69b** [lemma] ENV-A′. -/
axiom npHgt_comp_shift (hπ : Irreducible π) (φ : Polynomial O) (c : O) (f : Polynomial O)
    (j : ℕ) : npHgt (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j = npHgt φ f j

/-- **B.70a** [lemma] ENV-A′. -/
axiom npHgt_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (w j : ℕ)
    (hj : j ≤ f.natDegree) :
    npHgt X (f.scaleRoots (π ^ w)) j = npHgt X f j + ((w * (f.natDegree - j) : ℕ) : ℕ∞)

/-- **B.70b** [lemma] ENV-A′. -/
axiom sideSet_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (u w : ℕ) :
    sideSet X (f.scaleRoots (π ^ w)) (u + w) 1 = sideSet X f u 1

section ENVC8
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.71** [theorem] ENV-C. **DEFECT B-D10** — signed with `(hsep : ∀ i ∈ s, …)`,
`(hperim : ∀ i ∈ s, …)` and the conclusion's `(…the block factor…)`. Per §12 rule 4(c) the stub
signs B.71 in **B.80's data form** (`g : ι → Polynomial O` with `hgprod`/`hgres` as hypotheses),
NOT over B.67's existential — an `axiom` stub cannot bind an existential's witness. `hsep`/`hperim`
are §12 item 4's dictionary clauses at `(φ, f) := (φ i, g i)`.
**[repaired: A-F.9]** — `(hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)` added, byte-identical to
B.81's existing clause (the A-F.6-era form is refuted at the canonical B-D4 reading by the
singleton block `g i₀ = φ i₀`, `a i₀ = 1`; free at B.80's per-block `hvis` and B.81's `hnz`). -/
axiom typeOf_order1 (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {φ : ι → Polynomial O} {a : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    (hres : f.map (IsLocalRing.residue O)
      = ∏ i ∈ s, ((φ i).map (IsLocalRing.residue O)) ^ (a i))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic) (hgprod : f = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (a i))
    (hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)
    (hsep : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ h : (sideSet (φ i) (g i) u ℓ).Nonempty, 1 < (sideSet (φ i) (g i) u ℓ).card →
        ∀ H₀ : ℕ, npHgt (φ i) (g i) (sideMin (φ i) (g i) u ℓ h) = (H₀ : ℕ∞) →
          (resPoly π (φ i) (g i) u ℓ h H₀).Separable)
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g i → IsPure (φ i) gS u ℓ →
        ∀ hne : (sideSet (φ i) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt (φ i) gS (sideMin (φ i) gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField (φ i)), ψ.Monic → Irreducible ψ →
            (∃ c : (resField (φ i))ˣ, resPoly π (φ i) gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ (φ i).natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                (φ i).natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    (typeOf f).data = ∑ i ∈ s, (order1Type π (φ i) (g i)).data

/-- **B.72** [lemma] ENV-C. **DEFECT B-D10** — `(hsep : …)` expanded to B.63's `hsep` clause at
`(φ, g)`. **[repaired: A-F.9]** — `(h0 : dev φ g 0 ≠ 0)` added (the A-F.6-era form is refuted
at the canonical B-D4 reading by `g = φ`: `slopeFinset π φ φ = ∅` by the committed
`sideSet_key_self`, so the left side is `0 ≠ m`; step 3 is the `h0`-gated length identity
`Σ ℓ_S d_S = μ`). -/
axiom degree_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ g 0 ≠ 0)
    (hsep : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ∀ h : (sideSet φ g u ℓ).Nonempty,
      1 < (sideSet φ g u ℓ).card → ∀ H₀ : ℕ, npHgt φ g (sideMin φ g u ℓ h) = (H₀ : ℕ∞) →
        (resPoly π φ g u ℓ h H₀).Separable) :
    (order1Type π φ g).degree = g.natDegree

/-- **B.73** [def] ENV-C. `NeedsDescent π φ f` : some side's residual polynomial is not
separable — the order-1 read does not terminate. (Body carries the A-F.1/PA-1 `sideMin` pin.) -/
def NeedsDescent (π : O) (φ f : Polynomial O) : Prop :=
  ∃ (u ℓ : ℕ) (h : (sideSet φ f u ℓ).Nonempty) (H₀ : ℕ), 0 < ℓ ∧ Nat.Coprime u ℓ ∧
    1 < (sideSet φ f u ℓ).card ∧ npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞) ∧
    ¬ (resPoly π φ f u ℓ h H₀).Separable

end ENVC8

/-! ## §9 — level-`N` decidedness certificates in full generality (B.75–B.82)

Note the node order here: **B.75 (`Visible`) is a `def` that B.74's statement consumes**, so B.74
is signed after it (the blueprint's own gloss "(`Visible` is B.75.)"). -/

/-- **B.75** [def] ENV-A. `Visible π φ f N` : the order-1 read of `f` at the key `φ` is contained
in the height-`N` window — some digit of `dev φ f 0` sits strictly below height `N`. Equivalently
(given `Irreducible π`): `npHgt φ f 0 < N`. -/
def Visible (π : O) (φ f : Polynomial O) (N : ℕ) : Prop :=
  ∃ i, ¬ π ^ N ∣ (dev φ f 0).coeff i

section ENVC9
-- ENV-C.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.74** [lemma] ENV-C. Signed after B.75 because its statement consumes `Visible`. -/
axiom needsDescent_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i)
    (hvis : Visible π φ f N) : NeedsDescent π φ f ↔ NeedsDescent π φ f'

end ENVC9

/-- **B.76a** [lemma] ENV-A′. -/
axiom npHgt_min_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (j : ℕ) :
    min (npHgt φ f j) (N : ℕ∞) = min (npHgt φ f' j) (N : ℕ∞)

/-- **B.76b** [lemma] ENV-A′. -/
axiom visible_iff_npHgt_lt (hπ : Irreducible π) {φ f : Polynomial O} {N : ℕ} :
    Visible π φ f N ↔ npHgt φ f 0 < (N : ℕ∞)

/-- **B.76c** [lemma] ENV-A′. -/
axiom visible_mono {φ f : Polynomial O} {N M : ℕ} (hNM : N ≤ M) :
    Visible π φ f N → Visible π φ f M

/-- **B.76d** [lemma] ENV-A′. -/
axiom visible_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) :
    Visible π φ f N ↔ Visible π φ f' N

/-- **B.76e** [lemma] ENV-A′. -/
axiom exists_visible (hπ : Irreducible π) {φ f : Polynomial O} (h0 : dev φ f 0 ≠ 0) :
    ∃ N : ℕ, Visible π φ f N

/-- **B.77a** [lemma] ENV-A′. -/
axiom suppVal_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    suppVal φ f' u ℓ = suppVal φ f u ℓ

/-- **B.77b** [lemma] ENV-A′. -/
axiom sideSet_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    sideSet φ f' u ℓ = sideSet φ f u ℓ

/-- **B.77c** [lemma] ENV-A′. The signed statement's `Nonempty` witness is produced by rewriting
with B.77b, exactly as the blueprint writes it (`by rw [sideSet_congr …]; exact h`). -/
axiom resPoly_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) {u ℓ : ℕ} (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : H₀ < N) :
    resPoly π φ f' u ℓ (by rw [sideSet_congr hπ hφ hd hff' hdeg hvis]; exact h) H₀
      = resPoly π φ f u ℓ h H₀

/-- **B.78a** [lemma] ENV-A′. -/
axiom monicPoly_congr {n N : ℕ} {a b : Fin n → O}
    (hab : ∀ i, π ^ N ∣ (a i - b i)) (j : ℕ) :
    π ^ N ∣ (Uniformity.Density.monicPoly a - Uniformity.Density.monicPoly b).coeff j

/-- **B.78b** [lemma] ENV-A′. -/
axiom factor_congr_of_coprime (hπ : Irreducible π) {N : ℕ} {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    {g₀ h₀ : Polynomial (ResidueField O)} (hcop : IsCoprime g₀ h₀)
    (hgr : g.map (IsLocalRing.residue O) = g₀) (hhr : h.map (IsLocalRing.residue O) = h₀)
    (hgr' : g'.map (IsLocalRing.residue O) = g₀) (hhr' : h'.map (IsLocalRing.residue O) = h₀)
    (hff' : ∀ i, π ^ N ∣ (g * h - g' * h').coeff i) :
    (∀ i, π ^ N ∣ (g - g').coeff i) ∧ (∀ i, π ^ N ∣ (h - h').coeff i)

/-- **B.78c** [lemma] ENV-A′. -/
axiom peel_congr (hπ : Irreducible π) {N : ℕ} {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {g g' : ι → Polynomial O} {g₀ : ι → Polynomial (ResidueField O)}
    (hgmon : ∀ i ∈ s, (g i).Monic) (hgmon' : ∀ i ∈ s, (g' i).Monic)
    (h₀mon : ∀ i ∈ s, (g₀ i).Monic)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g₀ i) (g₀ j))
    (hgr : ∀ i ∈ s, (g i).map (IsLocalRing.residue O) = g₀ i)
    (hgr' : ∀ i ∈ s, (g' i).map (IsLocalRing.residue O) = g₀ i)
    (hff' : ∀ k, π ^ N ∣ ((∏ i ∈ s, g i) - (∏ i ∈ s, g' i)).coeff k) :
    ∀ i ∈ s, ∀ k, π ^ N ∣ ((g i) - (g' i)).coeff k

section ENVC10
-- ENV-C (+ completeness, already in ENV-C; see DEFECT B-D11).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.79a** [theorem] ENV-C. **DEFECT B-D10** — `hperim` expanded from §12 item 4(a),
byte-identical to B.63's. **[repaired: A-F.9]** — `(h0 : dev φ g 0 ≠ 0)` added (the A-F.6-era
form is refuted at the canonical B-D4 reading by `g = φ`: `hterm` holds, `hperim` is
dischargeable, and the conclusion forces `⟨{(1, m)}⟩ = ⟨0⟩`). B.79b below is IMMUNE — its
`hvis` gives `h0` via B.76(ii) — and supplies (a)'s `h0` at `g'` via B.76(iv). -/
axiom typeOf_eq_order1Type (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ g 0 ≠ 0)
    (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    typeOf g = order1Type π φ g

/-- **B.79b** [theorem] ENV-C. **DEFECT B-D10** — `hperim` as B.79a. -/
axiom typeOf_congr_of_certificate (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hterm : ¬ NeedsDescent π φ g)
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g → IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g'))
    {N : ℕ} (hvis : Visible π φ g N)
    {g' : Polynomial O} (hg' : g'.Monic) (hdeg : g'.natDegree = g.natDegree)
    (hgg' : ∀ i, π ^ N ∣ (g - g').coeff i) :
    typeOf g' = order1Type π φ g

/-- **B.80** [theorem] ENV-C + completeness. *(§12 rule 6 FRAGILE — indexed family:
`[DecidableEq ι]`, `Finset` products, per-block `hperim`.)* **DEFECT B-D10** — per-block `hperim`
at `(φ, f) := (φ i, g i)`. -/
axiom decidedAt_of_order1_certificate (hπ : Irreducible π) {n N : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hvis : ∀ i ∈ s, Visible π (φ i) (g i) N)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g i → IsPure (φ i) gS u ℓ →
        ∀ hne' : (sideSet (φ i) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt (φ i) gS (sideMin (φ i) gS u ℓ hne') = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField (φ i)), ψ.Monic → Irreducible ψ →
            (∃ c : (resField (φ i))ˣ, resPoly π (φ i) gS u ℓ hne' H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ (φ i).natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                (φ i).natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    Uniformity.Density.DecidedAt O n ⟨∑ i ∈ s, (order1Type π (φ i) (g i)).data⟩ N
      (Uniformity.Density.proj O n N a)

/-- **B.81** [lemma] ENV-C + completeness. **DEFECT B-D10** — per-block `hperim` as B.80. -/
axiom exists_decidedAt_of_terminating (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (a : Fin n → O) {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {φ : ι → Polynomial O} {e : ι → ℕ}
    (hkey : ∀ i ∈ s, IsKey (φ i)) (he : ∀ i ∈ s, 0 < e i)
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (φ i).map (IsLocalRing.residue O) ≠ (φ j).map (IsLocalRing.residue O))
    {g : ι → Polynomial O} (hgmon : ∀ i ∈ s, (g i).Monic)
    (hgprod : Uniformity.Density.monicPoly a = ∏ i ∈ s, g i)
    (hgres : ∀ i ∈ s, (g i).map (IsLocalRing.residue O)
      = ((φ i).map (IsLocalRing.residue O)) ^ (e i))
    (hnz : ∀ i ∈ s, dev (φ i) (g i) 0 ≠ 0)
    (hterm : ∀ i ∈ s, ¬ NeedsDescent π (φ i) (g i))
    (hperim : ∀ i ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ g i → IsPure (φ i) gS u ℓ →
        ∀ hne' : (sideSet (φ i) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt (φ i) gS (sideMin (φ i) gS u ℓ hne') = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField (φ i)), ψ.Monic → Irreducible ψ →
            (∃ c : (resField (φ i))ˣ, resPoly π (φ i) gS u ℓ hne' H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ (φ i).natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                (φ i).natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    ∃ N : ℕ, 0 < N ∧ Uniformity.Density.DecidedAt O n
      (typeOf (Uniformity.Density.monicPoly a)) N (Uniformity.Density.proj O n N a)

/-- **B.82** [theorem] ENV-C + completeness. **DEFECT B-D10** — `hperim` at
`(φ, f) := (φ, monicPoly a)`. -/
axiom decidedAt_of_leaf_certificate (hπ : Irreducible π) {n N : ℕ} (hn : 0 < n)
    (a : Fin n → O) {φ : Polynomial O} (hφ : IsKey φ) {μ : ℕ} (hμ : 0 < μ)
    (hres : (Uniformity.Density.monicPoly a).map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ μ)
    (hvis : Visible π φ (Uniformity.Density.monicPoly a) N)
    (hterm : ¬ NeedsDescent π φ (Uniformity.Density.monicPoly a))
    (hperim : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
      ∀ gS : Polynomial O, gS.Monic → gS ∣ Uniformity.Density.monicPoly a →
        IsPure φ gS u ℓ →
        ∀ hne : (sideSet φ gS u ℓ).Nonempty, ∀ H₀ : ℕ,
          npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞) →
          ∀ ψ : Polynomial (resField φ), ψ.Monic → Irreducible ψ →
            (∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ) →
            -- [repaired: A-F.7] first disjunct narrowed from `ℓ = 1`
            ((ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨
              ∀ g' ∈ monicFactors gS,
                φ.natDegree * ψ.natDegree ∣ inertiaDegOf g')) :
    Uniformity.Density.DecidedAt O n (order1Type π φ (Uniformity.Density.monicPoly a)) N
      (Uniformity.Density.proj O n N a)

end ENVC10

/-! ## §10 — gates: `q = 2` and `q = 3` firing instances (B.83–B.86)

Concrete bundles; no `variable` block. The ENV-C obligations are discharged by the landed
`LocalData.lean` §6 instances via TC. *(§12 rule 6 FRAGILE — `ℤ_[p]` literals + `![…]` vectors +
the `⟨{…}⟩` `FactorizationType` anonymous constructor meeting a multiset literal.)* -/

/-- **B.83 (i)** [gate] `q = 2`, inert. -/
axiom gate_inert_two :
    Uniformity.Density.DecidedAt ℤ_[2] 2 ⟨{(1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 2 2 ![3, 1])

/-- **B.83 (ii)** [gate] `q = 2`, ramified. -/
axiom gate_ram_two :
    Uniformity.Density.DecidedAt ℤ_[2] 2 ⟨{(2, 1)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 2 2 ![2, 2])

/-- **B.83 (iii)** [gate] `q = 2`, two-slope (linear × ramified) — the instance whose right side
has `sideMin ≠ 0`, i.e. the A-F.1 pin repair's teeth. -/
axiom gate_linram_two :
    Uniformity.Density.DecidedAt ℤ_[2] 3 ⟨{(1, 1), (2, 1)}⟩ 3
      (Uniformity.Density.proj ℤ_[2] 3 3 ![4, 2, 2])

/-- **B.83 (iv)** [gate] `q = 2`, split. -/
axiom gate_split_two :
    Uniformity.Density.DecidedAt ℤ_[2] 3 ⟨{(1, 1), (1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 3 2 ![2, 3, 3])

/-- **B.84 (i)** [gate] `q = 3`, inert. -/
axiom gate_inert_three :
    Uniformity.Density.DecidedAt ℤ_[3] 2 ⟨{(1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 2 2 ![4, 0])

/-- **B.84 (ii)** [gate] `q = 3`, ramified. -/
axiom gate_ram_three :
    Uniformity.Density.DecidedAt ℤ_[3] 2 ⟨{(2, 1)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 2 2 ![3, 3])

/-- **B.84 (iii)** [gate] `q = 3`, two-slope. -/
axiom gate_linram_three :
    Uniformity.Density.DecidedAt ℤ_[3] 3 ⟨{(1, 1), (2, 1)}⟩ 3
      (Uniformity.Density.proj ℤ_[3] 3 3 ![9, 3, 3])

/-- **B.84 (iv)** [gate] `q = 3`, split. -/
axiom gate_split_three :
    Uniformity.Density.DecidedAt ℤ_[3] 3 ⟨{(1, 1), (1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 3 2 ![3, 1, 3])

/-- **B.85 (i)+(ii)** [gate] `q = 2`, the `e > 1` AND `f > 1` witnesses (GC-11's shape). -/
axiom gate_ef_two :
    Uniformity.Density.DecidedAt ℤ_[2] 4 ⟨{(2, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 4 2 ![-1, 2, 3, 2])
    ∧ Uniformity.Density.DecidedAt ℤ_[2] 6 ⟨{(3, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[2] 6 2 ![-1, 3, 6, 7, 6, 3])

/-- **B.85 (iii)+(iv)** [gate] `q = 3`, the `e > 1` AND `f > 1` witnesses. -/
axiom gate_ef_three :
    Uniformity.Density.DecidedAt ℤ_[3] 4 ⟨{(2, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 4 2 ![-2, 0, 2, 0])
    ∧ Uniformity.Density.DecidedAt ℤ_[3] 6 ⟨{(3, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 6 2 ![-2, 0, 3, 0, 3, 0])

/-! ## B.86 — GC-11 EXECUTION AT STUB STAGE (§12 rule 8(c))

B.86 is a census block, not a declaration. Its part (i) — the `#print axioms` footprints of the
fourteen capstone-path theorems and the ten gates — **must wait for real bodies**: at stub stage
every one of those names is an `axiom` here, so its footprint is itself, which tests nothing.
Parts (ii) and (iii) run NOW and are executed below: pure arithmetic over the landed
`FactorizationType`/`residueCard`, at `q = 2` AND `q = 3`, all `decide`, no `native_decide`.
Every `#eval` is followed by the blueprint's own expected value. -/

section GC11
open Uniformity.Density

-- (ii) degree conservation of every gate value (GC-4's mandatory invariant, B.72's law
-- instantiated): Σ e·f over the multiset = the instance's degree n.
#eval decide ((⟨{(1,2)}⟩ : Uniformity.FactorizationType).degree = 2)      -- expect true
#eval decide ((⟨{(2,1)}⟩ : Uniformity.FactorizationType).degree = 2)      -- expect true
#eval decide ((⟨{(1,1),(2,1)}⟩ : Uniformity.FactorizationType).degree = 3) -- expect true
#eval decide ((⟨{(1,1),(1,2)}⟩ : Uniformity.FactorizationType).degree = 3) -- expect true
#eval decide ((⟨{(2,2)}⟩ : Uniformity.FactorizationType).degree = 4)      -- expect true
#eval decide ((⟨{(3,2)}⟩ : Uniformity.FactorizationType).degree = 6)      -- expect true

-- D-3's bracket arithmetic at the B.85 witnesses (m ∣ inertiaDeg ∣ m·d collapse site):
#eval (Nat.gcd (2*1*1) (2*2*1), Nat.gcd (2*1*1) (3*2*1), Nat.gcd (1*1*1) (2*1*1))
                                                          -- expect (2, 2, 1) = (m·d, m·d, m·d)

-- the two residue cardinalities the gates rely on (via landed `residueCard_padicInt`):
example : Uniformity.Density.residueCard ℤ_[2] = 2 := Uniformity.Density.residueCard_padicInt 2
example : Uniformity.Density.residueCard ℤ_[3] = 3 := Uniformity.Density.residueCard_padicInt 3

-- the split-gate multiset sum (B.80's Σ-shape at instance (iv)):
#eval decide (({(1,1)} + {(1,2)} : Multiset (ℕ × ℕ)) = {(1,1),(1,2)})             -- expect true

end GC11

-- (iii) non-vacuity: the ten gate theorems elaborate at their stated types.
#check @gate_inert_two
#check @gate_ram_two
#check @gate_linram_two
#check @gate_split_two
#check @gate_inert_three
#check @gate_ram_three
#check @gate_linram_three
#check @gate_split_three
#check @gate_ef_two
#check @gate_ef_three

end LeanspecB

/-
RESUME (stage-0e chapter-B stub gate)
=====================================
STATE: COMPLETE. 139 declarations landed: 22 real def-class bodies + 117 `axiom`s (109 of the 110
  theorem rows — B.51's `residueDeg_dvd_sum_of_local` is unsignable, defect B-D6 — plus the 3
bodyless def-class rows of B-D2 and the 5 RE-PLAN suppliers of B-D4/B.63a). Build green via
`lake build Leanspec.ChapB`; also clean under `-DautoImplicit=false`. 16 defects recorded
(B-D1 … B-D16).
B.62 deliberately unsigned (§12 rule 3). B.86 is a census block: parts (ii)+(iii) executed above,
part (i) (`#print axioms`) deferred to real bodies.
NEXT IF RESUMING: (1) `cd leanspec && lake build Leanspec.ChapB`; (2) re-read the DEFECT LIST in
the header before touching anything — every stub-side adjustment is logged there; (3) do NOT add
this file to `Leanspec.lean` (the orchestrator wires roll-up imports; a concurrent CHAP-H stub
agent owns `Leanspec/ChapH.lean`).
-/
