/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C127
import Uniformity.ChapC.C51
import Uniformity.ChapC.C47
import Uniformity.ChapC.C19
import Uniformity.ChapC.C16
import Uniformity.ChapB.B03
import Uniformity.ChapB.B05

/-!
# Uniformity.ChapC.C73 — x-free genres and GENTOW-3(iii): the shadow IS the composed read

**Chapter C, NODE C.73** [def+theorem] [fresh] [signed: A-C.1 — the PRIMARY clause is the
definition (every nonzero lift slot has `X`-degree `0`); the displayed `i(u₂(f₂−t)) = 0` test
lands as the `f₁ = 1`-ONLY companion `isXFree_iff_slot_of_f1`, per the `[GT3-r1]` scope bracket]
(`blueprint/CHAP-C_tower_grammar.md` §8, NODE C.73; twin `leanspec/Leanspec/ChapC.lean`, the
`### NODE C.73` block).  **ENV-C1**.  Three signed declarations.

Fix a frame `F` (C.01) pinned at `H₀` (C.14a's `F.Pin H₀`) and a tower datum `T` (C.42), and
write `Φ′ = F.key`, `D′ = e₁f₁ = deg Φ′`, `Φ₂ = composedKey T` (C.43), `m = e₂f₂` (so
`deg Φ₂ = D₂ = D′m`).  C.71 puts two `Φ₂`-adic reads of `f` side by side:

* the **composed (honest) read** `dev (composedKey T) f j` — B.02's development at `Φ₂`;
* the **stage-shadow read** `shadowDev T f j` — the same division tower run inside
  `(O[x]/Φ′)[Z]` (`biRead` + `devQ`) and lifted back by the canonical degree-`< D′`
  representative (`reass`).

C.72 bounds their disagreement below `Θ_j`.  This node identifies the genres at which there is
NO disagreement at all.

## The definition, and which clause is operative

`IsXFree T` is the **PRIMARY clause** of `EFF.GENTOW3.17`: every lift coefficient of the composed
key is an x-free monomial, i.e. `stageLiftO`'s output at each slot `t < f₂` with `ψ₂.coeff t ≠ 0`
has `X`-degree `0`.  The source's displayed test `i(u₂(f₂−t)) = 0` is NOT the definition: the
`[GT3-r1]` scope bracket says in terms that the "equivalently" holds **at `f₁ = 1` ONLY** and is
FALSE in general at `f₁ ≥ 2`.  So the test lands here as the companion
`isXFree_iff_slot_of_f1`, with `hf1 : F.f₁ = 1` explicit, and the PRIMARY clause is what
`shadow_exact_of_xfree` consumes — which is exactly why `.20` can say "(iii) needs no `f₁`
restriction".

## What the exactness theorem actually needs, and what it does not

`shadow_exact_of_xfree` is proved through the two-variable presentation, which is the honest
formalization of `EFF.GENTOW3.26`'s degree argument ("no x-overflow ever occurs, reduction mod
`Φ′` is the identity on every coefficient"):

1. `keyY T ∈ O[x][Z]` is the composed key read as a `Z`-polynomial — `Z^m` minus the lift terms
   at `Z^{e₂t}`.  It is monic of `Z`-degree `m` UNCONDITIONALLY (`keyY_monic`,
   `keyY_natDegree`), and `eval Φ′ (keyY T) = Φ₂` (`keyY_eval`).  **x-freeness enters exactly
   once**: it is what makes every coefficient of `keyY T` a CONSTANT (`X`-degree `0`), hence
   in-grid (`keyY_coeff_natDegree_le`).
2. `biRep F A` is the two-variable presentation of a single polynomial — its `Φ′`-digits against
   `Z`; in-grid by `degree_dev_lt`, and `eval Φ′ (biRep F A) = A` by B.05's `sum_dev_eq`.
3. `Ap := Σ_{j' < N} biRep F (dev Φ₂ f j') · (keyY T)^{j'}` presents `f` itself, and its
   coefficients are in-grid because the `keyY`-powers contribute `X`-degree `0` — this is the
   step that would FAIL at a non-x-free datum, and it is the only step that would.
4. `Ap` is by construction the `keyY`-adic development chain, so `devQ (keyY T) Ap j` is
   `biRep F (dev Φ₂ f j)` (`devQ_chain`), and the same computation runs verbatim after
   transport by `AdjoinRoot.mk Φ′` — the two-variable division is division in `Z`, which the
   reduction mod `Φ′` cannot disturb.
5. `reass` inverts `biRep ∘ map` on the in-grid locus (`reass_map_biRep`), so the shadow read
   returns `dev Φ₂ f j` on the nose.

**The signed binders `hh : 1 ≤ F.h`, `[Finite (ResidueField O)]`, `μ₂` and
`hf : f ∈ towerLocus T μ₂` are NOT consumed**: the proof establishes the equation for EVERY
`f : Polynomial O`.  They are kept because the statement is signed with them (statement fence),
and this is recorded rather than papered over — the honest reading is that (iii) is a degree
identity, not a locus statement, exactly as `.26` presents it.  `hπ` IS consumed: it discharges
the zero-slot branch (`stageLiftO_zero_iff` needs it) and, in the `f₁ = 1` companion, `η ≠ 0`.

## MANDATORY A-C.7 FIVE-INSTANCE BINDER-VACUITY AUDIT — verdict: **PASS with one disclosure**

Audited before any proving, against the A-C.7 registry's four prior A-C.1 failures plus the
A-C.8.4 additional row.  Hypotheses under audit — `shadow_exact_of_xfree`: `T`, `hπ`, `hh`,
`[Finite (ResidueField O)]`, `hx : IsXFree T`, `hf : f ∈ towerLocus T μ₂`;
`isXFree_iff_slot_of_f1`: `T`, `hπ`, `hh`, `hf1 : F.f₁ = 1`.

**Pattern 1 — C.111 `hnode`, an unpinned carrier field.**  No analogue.  `IsXFree` quantifies no
carrier: it is a condition on `T`'s OWN lift slots, every one of which is a `def`-level function
of `T.ψ₂`, `T.f₂`, `T.u₂` and the frame.  Nothing in either conclusion mentions an object that
the hypotheses leave free.

**Pattern 2 — C.94, a self-loop trivializing an infinite relation.**  No relation, history, or
reachability predicate.  `IsXFree` is a bounded `∀ t < T.f₂`.

**Pattern 3 — C.113 `hne`, a `Nonempty` hypothesis with no intended content.**  No `Nonempty`, no
existential side witness, no dependent-witness binder anywhere in the three declarations.

**Pattern 4 — C.118 `Visible₂`, an implication guard leaving a stratum unguarded.**  ⚠ **THIS
ONE BITES, and is CLOSED by a landed equivalence.**  `IsXFree`'s body is
`∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 → …`: the guard `ψ₂.coeff t ≠ 0` leaves the `ψ₂.coeff t = 0`
stratum unconstrained, which is structurally the C.118 shape.  It is harmless here, and that is a
THEOREM, not a hope: on the unguarded stratum the lift argument is `−0 · η^{W(t)} = 0` and
`stageLiftO M 0 = 0` (C.47's `stageLiftO_zero_iff` with C.14a's `resLift_zero`), whose `X`-degree
is `0` anyway.  The companion `isXFree_iff_forall` below states and proves exactly that: `IsXFree
T` is EQUIVALENT to the UNGUARDED `∀ t < T.f₂, (lift slot t).natDegree = 0`.  So no content
escapes through the guard, and the exactness proof consumes the unguarded form.

**Pattern 5 — C.66's low-degree purity collapse.**  No purity predicate is mentioned.  The one
degree degeneration available is `D′ = 1` (`F.key.natDegree = 1`), and it is benign: `natDegree
≤ 0 < 1 = D′` still holds, so the in-grid hypotheses of `shadowDev_of_ingrid` are satisfied and
the theorem is not weakened (in fact `F.natDegree_key_pos` is the only degree fact used).

**Is `hx : IsXFree T` satisfiable?**  Yes — and `isXFree_iff_slot_of_f1` is itself the
certificate, because at `f₁ = 1` it reduces x-freeness to the purely arithmetic
`∀ t < f₂ with ψ₂.coeff t ≠ 0, i((f₂−t)u₂) = 0`, which is manifestly satisfiable.  Worked
instance, on the LANDED frame `s2Frame` (C.97: `e₁ = 2`, `f₁ = 1`, `h = 1`, `Φ′ = X² − 2` over
`ℤ₂`, pin `H₀ = 1` inhabited by `s2Frame_pin`): there `i(k) = k mod 2`, so taking `e₂ = 1`,
`f₂ = 2`, `u₂ = 4` (legal: `hcop` is `Coprime 4 1`, `hcomp` is `2 ≤ 2`, the node floor is
`1·2·1 = 2 < 4`) makes `(f₂ − t)·u₂ ∈ {8, 4}` even for BOTH slots, hence `i = 0` at both, hence
x-free; and `ψ₂ = T² + T + 1` over the stage field `𝔽₂` supplies the residual (monic, irreducible,
`coeff 0 ≠ 0`, degree `f₂ = 2`).  **DISCLOSURE:** that instance is an argument, not a Lean object
— the corpus currently lands NO `TowerDatum` value at all (a chapter-wide gap, not this node's:
`s2Witness` is a `DeepTower`, C.83's carrier, not C.42's).  So `hx`'s inhabitation is certified
mathematically and reduced machine-checkably to arithmetic, not yet witnessed by a constructed
term.

**Could the theorem be vacuous through `hf`?**  No, in the strongest possible sense: the proof
never consumes `hf`, so the conclusion holds for every `f : Polynomial O` whether or not
`towerLocus T μ₂` is inhabited.  An empty locus cannot hide anything here.

**Verdict.** No fifth instance of the A-C.7 vacuity pattern.  The one registry-shaped guard
(pattern 4) is closed by the landed `isXFree_iff_forall` equivalence rather than argued away;
`hx` is satisfiable and its satisfiability is reduced to decidable arithmetic by the node's own
`f₁ = 1` companion; and the exactness conclusion is `hf`-independent, so locus emptiness is not a
vacuity channel.  *Self-refutation attempt (a drafted repair is itself a refutation target):* the
tempting "repair" of DROPPING the `ψ₂.coeff t ≠ 0` guard from the definition would be a
STATEMENT CHANGE and is refused; the tempting alternative of replacing the PRIMARY clause by the
displayed `i(u₂(f₂−t)) = 0` test is REFUTED by the source's own `[GT3-r1]` bracket at `f₁ ≥ 2`,
and is why the test is landed only as the `hf1`-guarded companion.

**DEPENDS.** C.43 (`composedKey`, `wrapExp`) · C.71 (`shadowDev`, `devQ`, `biRead`) · C.14a
(`stageLiftO`, `stageLiftIA`, `resLift_zero`, `sum_stageCoord`) · C.47
(`stageLiftO_zero_iff`, `composedKey_monic`, `composedKey_natDegree`) · C.19
(`stageLetter_ne_zero`) · C.16 (`slotIdx_spec`) · C.51 (`towerLocus`) · C.127 (the `devQ`/
`biRead`/`reass` API, `shadowDev_of_ingrid`, and the coefficient-degree toolkit) · B.03
(`degree_dev_lt`) · B.05 (`sum_dev_eq`) — all imported.  By committed node ID: C.52 (no
x-overflow ⟹ the mod-`Φ′` reduction is the identity — the informal content of step 3 above).

**PROOF.** (iii): no coefficient ever has `x`-degree `≥ D′`, so every reduction step is trivial
and the two division towers coincide term by term — formalized as the five-step two-variable
argument in the section above.

**SIZE.** 22 lines (blueprint estimate; the honest formalization is longer because the
"coincide term by term" step is a `devQ`-chain computation).

**SOURCE.** `EFF.GENTOW3.17` (the definition with the `[GT3-r1]` scope bracket — the PRIMARY
clause transcribed, the `f₁ = 1`-only equivalence recorded as a companion lemma with the `f₁ = 1`
hypothesis explicit, per the re-derivation at `.45`); `.20` ((iii), "so read needs no `f₁`
restriction"); `.26` (the proof); witness FAM-D (`Φ₂ = (x²−3)² + 27`, lift `−27` x-free).

**TEETH.** P-3 XFREE 3 + the 12-member FAM-D sweep (zero discrepancies, DRAIN self-shadow) →
retained; FAM-D is `q = 3` — §13 pairs it with a `q = 2` x-free instance.  The `example`s below
are the local unfolding checks.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## The signed definition -/

/-- **NODE C.73 — the PRIMARY x-free clause** (`EFF.GENTOW3.17`, the operative definition at
every `f₁`).  `IsXFree T` says every lift coefficient of the composed key `Φ₂` is an x-free
monomial `π^a`: at each slot `t < f₂` whose residual coefficient `ψ₂.coeff t` is nonzero,
C.14a's `stageLiftO` output has `X`-degree `0`.

This is NOT the source's displayed test `i(u₂(f₂−t)) = 0` — that is an `f₁ = 1` EVALUATION of
this clause and is FALSE in general at `f₁ ≥ 2` (the `[GT3-r1]` scope bracket); it lands as the
companion `isXFree_iff_slot_of_f1`.

The `ψ₂.coeff t ≠ 0` guard leaves the vanishing stratum unconstrained, which is the C.118 shape;
`isXFree_iff_forall` below proves that nothing escapes through it (the zero lift is zero, hence
x-free anyway). -/
def IsXFree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Prop :=
  ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 →
    (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
      (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))).natDegree = 0

/-! ## The audit's pattern-4 closure, and the `f₁ = 1` companion

`isXFree_iff_forall` is what makes the `ψ₂.coeff t ≠ 0` guard of `IsXFree` harmless: on the
vanishing stratum the lift ARGUMENT is `−0·η^{W(t)} = 0`, and C.47's `stageLiftO_zero_iff`
(with C.14a's `resLift_zero`) says the zero lift IS zero — whose `X`-degree is `0` anyway.  So the
guarded and unguarded readings coincide, and no content escapes the implication.  This is the
proved form the exactness theorem below consumes. -/

/-- **C.73 companion (the A-C.7 pattern-4 closure)** — the guard in `IsXFree` is vacuous:
x-freeness is EQUIVALENT to the unguarded "every lift slot below `f₂` has `X`-degree `0`", because
the zero lift is zero.  Consumed by `shadow_exact_of_xfree`, which needs the bound at every slot,
including the vanishing ones. -/
theorem isXFree_iff_forall {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    IsXFree T
      ↔ ∀ t, t < T.f₂ →
          (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))).natDegree = 0 := by
  constructor
  · intro hx t ht
    by_cases hc : T.ψ₂.coeff t = 0
    · have h0 : (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))
          = (0 : F.stageField H₀ hpin) := by rw [hc, neg_zero, zero_mul]
      rw [h0, (stageLiftO_zero_iff F hπ H₀ hpin _).2 resLift_zero, Polynomial.natDegree_zero]
    · exact hx t ht hc
  · intro h t ht _
    exact h t ht

/-! ### The `f₁ = 1` companion (`[GT3-r1]`): x-freeness IS the slot test, there and only there

`EFF.GENTOW3.17`'s displayed criterion `i(u₂(f₂−t)) = 0` is an EVALUATION of the primary clause
at `f₁ = 1`, where C.14a's `stageLiftIA` has a single summand and the lift is one monomial
`C(λ·π^a)·x^{i(M)}`; its `X`-degree is then `i(M)` exactly, PROVIDED the constant `λ·π^a` does not
vanish.  That proviso is where `hπ` is spent twice over: `π ≠ 0`, and `η ≠ 0` (C.19's
`stageLetter_ne_zero`) so that the lift ARGUMENT `−ψ₂.coeff t·η^{W(t)}` is nonzero, whence its
single letter-basis digit is nonzero (`stageCoord_ne_zero_of_f1`) and so is its `resLift`.

At `f₁ ≥ 2` the equivalence is FALSE in general (the source's own `[GT3-r1]` bracket), which is
why this is a companion carrying `hf1` and NOT the definition. -/

/-- **D9 (cured).**  The order-0 key `X` is an order-1 key; the private-copy pattern
(C.04/C.12/C.19/C.21/C.22/C.44/C.46/C.47/C.128 each carry one), because `private` does not
export. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- The `Field` structure on the stage field `K` — C.04's private copy (a `@[reducible]` `def`,
not an `instance`, for B.25(b)'s reason). -/
@[reducible] private noncomputable def fieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- At `f₁ = 1` every `stageLiftO` entry is a single monomial: C.14a's `stageLiftIA` sums `f₁`
terms, so one survives, at slot `i(M) = F.slotIdx M` and `π`-exponent `(M − i(M)h)/e₁`.  (Private
copy of C.128's Part 3(a): C.128 is a far later node and importing it here would invert the DAG.
The two proofs are the same two lines.) -/
private theorem stageLiftO_of_f1 (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (hf₁ : F.f₁ = 1)
    (M : ℕ) (c : F.stageField H₀ hpin) :
    F.stageLiftO H₀ hpin M c
      = Polynomial.C (resLift (F.stageCoord H₀ hpin c 0)
            * π ^ ((M - F.slotIdx M * F.h) / F.e₁))
        * Polynomial.X ^ F.slotIdx M := by
  rw [KeyFrame.stageLiftO, KeyFrame.stageLiftIA, hf₁, Finset.sum_range_one]
  simp

/-- At `f₁ = 1` the single letter-basis digit detects nonvanishing: `stageCoord c 0 = 0` would
make C.14a's reconstruction identity `sum_stageCoord` read `c = 0`.  (Private copy of C.128's
helper of the same name, for the DAG reason above.) -/
private theorem stageCoord_ne_zero_of_f1 (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (hf₁ : F.f₁ = 1) {c : F.stageField H₀ hpin} (hc : c ≠ 0) :
    F.stageCoord H₀ hpin c 0 ≠ 0 := by
  intro h0
  refine hc ?_
  have hsum := F.sum_stageCoord H₀ hpin c
  rw [hf₁, Finset.sum_range_one, h0] at hsum
  simpa using hsum.symm

-- `hh : 1 ≤ F.h` is an A-C.1-signed binder and is NOT consumed: the equivalence is a degree
-- computation on a single monomial, and the frame's slope numerator never enters.  Kept because
-- the signature is frozen (statement fence).
set_option linter.unusedVariables false in
/-- **NODE C.73 — the `f₁ = 1` COMPANION** (`EFF.GENTOW3.17`'s displayed test, scoped by
`[GT3-r1]`).  At `f₁ = 1`, x-freeness of the datum is exactly the arithmetic condition that every
NONZERO residual slot sits at the `x`-free slot index: `i((f₂−t)u₂) = 0`.

This is the criterion the corpus displays, and it is landed here with `hf1 : F.f₁ = 1` EXPLICIT,
because at `f₁ ≥ 2` it is false in general — the primary clause `IsXFree` is the operative
definition at every `f₁` and is what `shadow_exact_of_xfree` consumes.

It is also this node's satisfiability certificate for `IsXFree`: it reduces x-freeness to a
decidable statement about `slotIdx`, which at e.g. the landed `s2Frame` (`e₁ = 2`, `f₁ = 1`,
`h = 1`, so `i(k) = k mod 2`) holds for every even `u₂` — see the module docstring's audit. -/
theorem isXFree_iff_slot_of_f1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h) (hf1 : F.f₁ = 1) :
    IsXFree T
      ↔ ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 → F.slotIdx ((T.f₂ - t) * T.u₂) = 0 := by
  classical
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  constructor
  · intro hx t ht hc
    have hcne : (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hc)
        (pow_ne_zero _ (F.stageLetter_ne_zero hπ H₀ hpin))
    have hcoord := stageCoord_ne_zero_of_f1 F H₀ hpin hf1 hcne
    have hres : resLift (F.stageCoord H₀ hpin
        (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) 0) ≠ 0 := by
      intro h0
      have hspec := resLift_spec (F.stageCoord H₀ hpin
        (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) 0)
      rw [h0, map_zero] at hspec
      exact hcoord hspec.symm
    have hv : resLift (F.stageCoord H₀ hpin
          (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) 0)
        * π ^ (((T.f₂ - t) * T.u₂ - F.slotIdx ((T.f₂ - t) * T.u₂) * F.h) / F.e₁) ≠ 0 :=
      mul_ne_zero hres (pow_ne_zero _ hπ.ne_zero)
    have hlift := hx t ht hc
    rw [stageLiftO_of_f1 F H₀ hpin hf1, Polynomial.natDegree_C_mul_X_pow _ _ hv] at hlift
    exact hlift
  · intro h t ht hc
    rw [stageLiftO_of_f1 F H₀ hpin hf1, h t ht hc, pow_zero, mul_one, Polynomial.natDegree_C]

/-! ## The exactness theorem, part 1: the generic `devQ`-chain lemma

`EFF.GENTOW3.26`'s "the two division towers coincide term by term" is, formalized, the statement
that a polynomial PRESENTED as `Σ_{j' < N} E_{j'}·Ψ^{j'}` with every `E_{j'}` below `Ψ` in degree
IS its own `Ψ`-adic development.  C.127's `devQ` API gives the three pieces (`devQ_add`,
`devQ_mul_pow`, `devQ_mul_pow_of_lt`); these three lemmas assemble them over a general
`CommRing`, which is what lets the SAME computation run twice — once in `O[x][Z]` and once, after
transport by `AdjoinRoot.mk Φ′`, in `(O[x]/Φ′)[Z]`.  That double use is the whole mechanism of
(iii): the two-variable division happens in `Z`, and reduction mod `Φ′` cannot disturb it. -/

section Chain

variable {R : Type*} [CommRing R] [Nontrivial R] {Ψ : Polynomial R}

/-- `devQ` is additive over a `Finset.sum` (C.127's `devQ_add`, iterated). -/
theorem devQ_finsetSum {ι : Type*} (hΨ : Ψ.Monic) (s : Finset ι) (g : ι → Polynomial R) (j : ℕ) :
    devQ Ψ (∑ i ∈ s, g i) j = ∑ i ∈ s, devQ Ψ (g i) j := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [devQ_of_zero]
  · intro a s' ha ih
    rw [Finset.sum_insert ha, devQ_add hΨ, ih, Finset.sum_insert ha]

/-- One chain term: an in-grid `E` parked at `Ψ^{j'}` contributes `E` at coordinate `j'` and
nothing anywhere else.  (C.127's `devQ_pow_add_entry` is this statement bundled with a leading
pure power; here the term is isolated, which is what a general chain needs.) -/
theorem devQ_term (hΨ : Ψ.Monic) {E : Polynomial R} (hE : E.degree < Ψ.degree) (j' j : ℕ) :
    devQ Ψ (E * Ψ ^ j') j = if j = j' then E else 0 := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · rw [if_neg (by omega)]
    exact devQ_mul_pow_of_lt hΨ j' E j hlt
  · subst heq
    rw [if_pos rfl]
    have h := devQ_mul_pow hΨ j E 0
    rw [Nat.add_zero] at h
    rw [h]
    exact devQ_zero_of_degree_lt hΨ hE
  · rw [if_neg (by omega)]
    by_cases hE0 : E = 0
    · rw [hE0, zero_mul]; exact devQ_of_zero Ψ j
    obtain ⟨c, hc⟩ : ∃ c, j = j' + c := ⟨j - j', by omega⟩
    subst hc
    rw [devQ_mul_pow hΨ]
    refine devQ_eq_zero_of_lt hΨ E c ?_
    have hEd : E.natDegree < Ψ.natDegree := natDegree_lt_natDegree hE0 hE
    have hc1 : 1 ≤ c := by omega
    calc E.natDegree < Ψ.natDegree := hEd
      _ = 1 * Ψ.natDegree := by ring
      _ ≤ c * Ψ.natDegree := Nat.mul_le_mul_right _ hc1

/-- **THE CHAIN LEMMA.**  A polynomial presented as `Σ_{j' < N} E_{j'}·Ψ^{j'}` with every
`E_{j'}` of degree `< deg Ψ` IS its own `Ψ`-adic development: `devQ` reads the presentation back
coordinate by coordinate.  (This is `dev_unique` (B.06) in the shape the shadow read needs, over
an arbitrary `CommRing` rather than over the DVR.) -/
theorem devQ_chain (hΨ : Ψ.Monic) (E : ℕ → Polynomial R)
    (hE : ∀ j', (E j').degree < Ψ.degree) {N j : ℕ} (hj : j < N) :
    devQ Ψ (∑ j' ∈ Finset.range N, E j' * Ψ ^ j') j = E j := by
  classical
  rw [devQ_finsetSum hΨ, Finset.sum_congr rfl (fun j' _ => devQ_term hΨ (hE j') j' j),
    Finset.sum_ite_eq (Finset.range N) j E, if_pos (Finset.mem_range.mpr hj)]

end Chain

/-! ## The exactness theorem, part 2: `biRep`, the two-variable presentation of one polynomial

`biRep F A` is `A` read as a `Z`-polynomial over `O[x]`: its `Z^b`-coefficient is the `b`-th
`Φ′`-adic digit of `A`.  It is the honest-side twin of C.71's `biRead` (which reduces the digits
mod `Φ′`); the two are related by `map (AdjoinRoot.mk Φ′)`, which is exactly the relation the
exactness proof exploits.

Everything here is unconditional — no x-freeness, no locus. -/

section BiRep

variable {F : KeyFrame O π}

/-- the two-variable presentation of a single polynomial: its `Φ′`-digits against `Z`. -/
noncomputable def biRep (F : KeyFrame O π) (A : Polynomial O) : Polynomial (Polynomial O) :=
  ∑ b ∈ Finset.range (A.natDegree + 1), Polynomial.C (dev F.key A b) * Polynomial.X ^ b

/-- every coefficient of `biRep F A` is the corresponding `Φ′`-digit — including past
`A.natDegree`, where both sides vanish (C.127's `biRead_coeff` one reduction earlier). -/
theorem biRep_coeff (F : KeyFrame O π) (A : Polynomial O) (b : ℕ) :
    (biRep F A).coeff b = dev F.key A b := by
  classical
  rw [biRep, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (A.natDegree + 1)) b (fun b' => dev F.key A b')]
  by_cases hb : b ∈ Finset.range (A.natDegree + 1)
  · rw [if_pos hb]
  · rw [if_neg hb]
    rw [Finset.mem_range, not_lt] at hb
    refine (dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos A b ?_).symm
    calc A.natDegree < b := by omega
      _ = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * F.key.natDegree := Nat.mul_le_mul_left b F.natDegree_key_pos

/-- the presentation never grows the degree. -/
theorem biRep_natDegree_le (F : KeyFrame O π) (A : Polynomial O) :
    (biRep F A).natDegree ≤ A.natDegree := by
  rw [biRep]
  refine natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
  have hb' : b ≤ A.natDegree := by
    have := Finset.mem_range.mp hb; omega
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact hb'

/-- **the presentation presents**: evaluating at `Φ′` returns `A` (B.05's `sum_dev_eq`). -/
theorem biRep_eval (F : KeyFrame O π) (A : Polynomial O) :
    Polynomial.eval F.key (biRep F A) = A := by
  rw [biRep, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  refine sum_dev_eq F.hmonic F.natDegree_key_pos A ?_
  calc A.natDegree < A.natDegree + 1 := by omega
    _ = (A.natDegree + 1) * 1 := by ring
    _ ≤ (A.natDegree + 1) * F.key.natDegree :=
        Nat.mul_le_mul_left _ F.natDegree_key_pos

/-- **the presentation is IN-GRID**: every coefficient is a `Φ′`-digit, hence of degree `< D′`
(B.03's `degree_dev_lt`).  This is `EFF.GENTOW3.26`'s "`deg A_J ≤ D′−1 < D′`", verbatim. -/
theorem biRep_coeff_natDegree_le (F : KeyFrame O π) (A : Polynomial O) (i : ℕ) :
    ((biRep F A).coeff i).natDegree ≤ F.key.natDegree - 1 := by
  rw [biRep_coeff]
  have hlt : (dev F.key A i).degree < F.key.degree :=
    degree_dev_lt F.hmonic F.natDegree_key_pos A i
  by_cases h0 : dev F.key A i = 0
  · rw [h0, natDegree_zero]
    exact Nat.zero_le _
  · have h1 : (dev F.key A i).natDegree < F.key.natDegree := natDegree_lt_natDegree h0 hlt
    omega

/-- the `Z`-degree of the presentation is bounded by the `Φ′`-adic length: if `A` sits below
`Φ′^m` in degree then `biRep F A` sits below `Z^m`.  (Used at `m = e₂f₂`, where it says a
development coefficient of `Φ₂` presents as a `Z`-polynomial of degree `< deg_Z Φ₂`.) -/
theorem biRep_natDegree_lt (F : KeyFrame O π) (A : Polynomial O) {m : ℕ} (hm : 0 < m)
    (hA : A.natDegree < m * F.key.natDegree) : (biRep F A).natDegree < m := by
  have hle : (biRep F A).natDegree ≤ m - 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rw [biRep_coeff]
    refine dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos A N ?_
    calc A.natDegree < m * F.key.natDegree := hA
      _ ≤ N * F.key.natDegree := Nat.mul_le_mul_right _ (by omega)
  omega

end BiRep

/-! ## The exactness theorem, part 3: `keyY`, the composed key as a `Z`-polynomial

`keyY T` is C.43's display read in `O[x][Z]`: `Z^{e₂f₂}` minus the lift terms parked at
`Z^{e₂t}`.  Three of its four properties are UNCONDITIONAL — it evaluates to `Φ₂` at `Z = Φ′`
(`keyY_eval`), and it is monic of `Z`-degree `e₂f₂` (`keyY_monic`, `keyY_natDegree`).

**The fourth is where x-freeness enters, and it enters here and nowhere else**:
`keyY_coeff_natDegree_le` says every coefficient of `keyY T` is a CONSTANT (`X`-degree `0`).
That is exactly the hypothesis `EFF.GENTOW3.26` uses ("at an x-free genre every `K₂`-coefficient
is x-free"), and it is what keeps the products `biRep(C_{j'})·keyY^{j'}` in-grid.  At a
non-x-free datum this single lemma fails, and with it the whole argument — which is the honest
statement of why (iii) is an x-free phenomenon. -/

section KeyY

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-- C.43's composed key, read as a `Z`-polynomial over `O[x]`: `Z^{e₂f₂} − Σ_{t<f₂} L_t·Z^{e₂t}`
with `L_t` the `t`-th lift coefficient.  `eval Φ′` sends it to `Φ₂` (`keyY_eval`). -/
noncomputable def keyY (T : TowerDatum F H₀ hpin) : Polynomial (Polynomial O) :=
  Polynomial.X ^ (T.e₂ * T.f₂)
    - ∑ t ∈ Finset.range T.f₂,
        Polynomial.C (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t)))
          * Polynomial.X ^ (T.e₂ * t)

/-- **`keyY` presents the composed key**: `eval Φ′ (keyY T) = Φ₂`, C.43's body verbatim. -/
theorem keyY_eval (T : TowerDatum F H₀ hpin) :
    Polynomial.eval F.key (keyY T) = composedKey T := by
  rw [keyY, composedKey]
  simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]

/-- the lift tail sits strictly below `Z^{e₂f₂}`: every parked exponent is `e₂t < e₂f₂`. -/
private theorem keyY_tail_natDegree_le (T : TowerDatum F H₀ hpin) :
    (∑ t ∈ Finset.range T.f₂,
        Polynomial.C (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t)))
          * Polynomial.X ^ (T.e₂ * t)).natDegree ≤ T.e₂ * T.f₂ - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
  have ht' : t < T.f₂ := Finset.mem_range.mp ht
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  have hstep : T.e₂ * t + T.e₂ ≤ T.e₂ * T.f₂ := by
    calc T.e₂ * t + T.e₂ = T.e₂ * (t + 1) := by ring
      _ ≤ T.e₂ * T.f₂ := Nat.mul_le_mul_left _ (by omega)
  have he : 0 < T.e₂ := T.he₂
  omega

private theorem keyY_tail_degree_lt (T : TowerDatum F H₀ hpin) :
    (-(∑ t ∈ Finset.range T.f₂,
        Polynomial.C (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t)))
          * Polynomial.X ^ (T.e₂ * t))).degree
      < ((Polynomial.X : Polynomial (Polynomial O)) ^ (T.e₂ * T.f₂)).degree := by
  rw [degree_neg]
  refine degree_lt_degree ?_
  have hnd := keyY_tail_natDegree_le T
  have hm : 2 ≤ T.e₂ * T.f₂ := T.hcomp
  rw [natDegree_X_pow]
  omega

/-- `keyY T` is MONIC — unconditionally, x-free or not: the lift tail is parked strictly below
the leading `Z^{e₂f₂}`. -/
theorem keyY_monic (T : TowerDatum F H₀ hpin) : (keyY T).Monic := by
  rw [keyY, sub_eq_add_neg]
  exact (monic_X_pow _).add_of_left (keyY_tail_degree_lt T)

/-- `keyY T` has `Z`-degree exactly `e₂f₂` — unconditionally. -/
theorem keyY_natDegree (T : TowerDatum F H₀ hpin) : (keyY T).natDegree = T.e₂ * T.f₂ := by
  rw [keyY, sub_eq_add_neg]
  refine natDegree_eq_of_degree_eq_some ?_
  rw [degree_add_eq_left_of_degree_lt (keyY_tail_degree_lt T), degree_X_pow]

/-- **THE X-FREE INPUT, and the only one.**  At an x-free datum every coefficient of `keyY T` is a
CONSTANT: the leading one is `1`, and each lift coefficient has `X`-degree `0` — by
`isXFree_iff_forall`, at EVERY slot `t < f₂`, vanishing residual slots included (which is why the
guard-closure lemma was needed).

This is `EFF.GENTOW3.26`'s "at an x-free genre every `K₂`-coefficient is x-free".  It is the
single step of the exactness proof that fails at a non-x-free datum. -/
theorem keyY_coeff_natDegree_le (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (hx : IsXFree T) : ∀ i, ((keyY T).coeff i).natDegree ≤ 0 := by
  have hlift := (isXFree_iff_forall T hπ).mp hx
  have htail : ∀ k, ((∑ t ∈ Finset.range T.f₂,
        Polynomial.C (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t)))
          * Polynomial.X ^ (T.e₂ * t)).coeff k).natDegree ≤ 0 := by
    intro k
    rw [finsetSum_coeff]
    refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
    have ht' : t < T.f₂ := Finset.mem_range.mp ht
    exact le_trans (natDegree_coeff_C_mul_X_pow_le _ _ _) (le_of_eq (hlift t ht'))
  rw [keyY, sub_eq_add_neg]
  refine natDegree_coeff_add_le (fun k => natDegree_coeff_X_pow_le _ _) ?_
  intro k
  rw [coeff_neg, natDegree_neg]
  exact htail k

end KeyY

/-! ## The exactness theorem, part 4: reassembly inverts the presentation, and the assembly -/

section Exact

open IsLocalRing

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-- **`reass` inverts `biRep` after transport.**  C.71's reassembly recovers a polynomial from the
mod-`Φ′` classes of its own `Φ′`-digits, because those digits are already the canonical
degree-`< D′` representatives (`degree_dev_lt` + `modByMonic_eq_self_iff`).  This is the last step
of the shadow read, and the reason the shadow can return the honest answer at all. -/
theorem reass_map_biRep (F : KeyFrame O π) (A : Polynomial O) :
    reass F ((biRep F A).map (AdjoinRoot.mk F.key)) = A := by
  have hle : ((biRep F A).map (AdjoinRoot.mk F.key)).natDegree < A.natDegree + 1 := by
    have h1 : ((biRep F A).map (AdjoinRoot.mk F.key)).natDegree ≤ (biRep F A).natDegree :=
      natDegree_map_le
    have h2 := biRep_natDegree_le F A
    omega
  rw [reass_eq_sum_range F _ hle]
  have hterm : ∀ b ∈ Finset.range (A.natDegree + 1),
      (AdjoinRoot.modByMonicHom F.hmonic
          (((biRep F A).map (AdjoinRoot.mk F.key)).coeff b)) * F.key ^ b
        = dev F.key A b * F.key ^ b := by
    intro b _
    rw [coeff_map, biRep_coeff, AdjoinRoot.modByMonicHom_mk,
      (modByMonic_eq_self_iff F.hmonic).2 (degree_dev_lt F.hmonic F.natDegree_key_pos A b)]
  rw [Finset.sum_congr rfl hterm]
  refine sum_dev_eq F.hmonic F.natDegree_key_pos A ?_
  calc A.natDegree < A.natDegree + 1 := by omega
    _ = (A.natDegree + 1) * 1 := by ring
    _ ≤ (A.natDegree + 1) * F.key.natDegree :=
        Nat.mul_le_mul_left _ F.natDegree_key_pos

-- The A-C.1-signed binders `hh`, `[Finite (ResidueField O)]`, `μ₂` and `hf` are NOT consumed:
-- (iii) is a degree identity and the proof establishes it for EVERY `f : Polynomial O`, exactly
-- as `EFF.GENTOW3.26` presents it ("no x-overflow ever occurs, reduction mod Φ′ is the identity
-- on every coefficient").  They are kept because the signature is frozen (statement fence), and
-- the fact is recorded in the module docstring rather than papered over.  `hπ` IS consumed, via
-- `isXFree_iff_forall` (the zero-slot branch) and `composedKey_natDegree`.
set_option linter.unusedVariables false in
/-- **NODE C.73 — GENTOW-3(iii), X-FREE EXACTNESS.**  At an x-free datum the discrepancy between
C.71's two reads is ZERO at every coordinate: the stage-shadow read IS the composed (honest)
read, `shadowDev T f j = dev (composedKey T) f j`.

The proof is `EFF.GENTOW3.26`'s degree argument, formalized through the two-variable
presentation.  Write `Φ′ = F.key`, `D′ = deg Φ′`, `m = e₂f₂`, `Φ₂ = composedKey T`, and let
`C_{j'} = dev Φ₂ f j'` be the honest development coefficients.  Then

* `keyY T` presents `Φ₂` in `O[x][Z]`, monic of `Z`-degree `m`, with every coefficient a CONSTANT
  — this last is exactly x-freeness (`keyY_coeff_natDegree_le`), and the only place it is used;
* `Ap = Σ_{j' < N} biRep F C_{j'} · (keyY T)^{j'}` presents `f`, and is IN-GRID because the
  `keyY`-powers contribute `X`-degree `0`: no coefficient ever reaches `X`-degree `D′`, so "no
  x-overflow ever occurs";
* `Ap` is BY CONSTRUCTION the `keyY`-adic chain, so `devQ` reads `biRep F C_j` back out of it
  (`devQ_chain`) — and the identical computation runs after transport by `AdjoinRoot.mk Φ′`,
  since the division is in `Z` and the reduction mod `Φ′` cannot disturb it;
* `reass` inverts `biRep ∘ map` (`reass_map_biRep`), returning `C_j` on the nose.

At a non-x-free datum the second bullet fails — the products leave the grid — which is precisely
the content of C.72's floor and C.74's attainment, and precisely why (iii) is an x-free
statement. -/
theorem shadow_exact_of_xfree (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hx : IsXFree T)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (j : ℕ) :
    shadowDev T f j = dev (composedKey T) f j := by
  classical
  haveI : Nontrivial (AdjoinRoot F.key) := F.nontrivial_adjoinRoot
  have hDpos : 0 < F.key.natDegree := F.natDegree_key_pos
  have hmpos : 0 < T.e₂ * T.f₂ := by have := T.hcomp; omega
  -- the composed key: monic, of degree `m·D′`
  have hΦmonic : (composedKey T).Monic := composedKey_monic T
  have hΦdeg : (composedKey T).natDegree = (T.e₂ * T.f₂) * F.key.natDegree := by
    have hd : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
    have hl : (T.levelDatum hπ).ℓ = T.e₂ := rfl
    rw [composedKey_natDegree T hπ, LevelDatum.keyDeg₂, hd, hl, F.hdeg]
    ring
  have hΦpos : 0 < (composedKey T).natDegree := by
    rw [hΦdeg]; exact Nat.mul_pos hmpos hDpos
  -- how many chain coordinates the presentation needs
  obtain ⟨N, hjN, hfN⟩ : ∃ N, j < N ∧ f.natDegree < N * (composedKey T).natDegree := by
    refine ⟨max (f.natDegree + 1) (j + 1),
      lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _), ?_⟩
    have h1 : f.natDegree + 1 ≤ max (f.natDegree + 1) (j + 1) := le_max_left _ _
    have h2 : max (f.natDegree + 1) (j + 1) * 1
        ≤ max (f.natDegree + 1) (j + 1) * (composedKey T).natDegree :=
      Nat.mul_le_mul_left _ hΦpos
    omega
  -- the key's presentation
  have hKmonic : (keyY T).Monic := keyY_monic T
  have hKcoef : ∀ i, ((keyY T).coeff i).natDegree ≤ 0 := keyY_coeff_natDegree_le T hπ hx
  have hKgrid : ∀ i, ((keyY T).coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hKcoef hDpos
  have hKpow : ∀ (n i : ℕ), (((keyY T) ^ n).coeff i).natDegree ≤ 0 := by
    intro n i
    have h := natDegree_coeff_pow_le hKcoef n i
    simpa using h
  -- `f`'s presentation, as the `keyY`-adic chain of its honest development
  set Ap : Polynomial (Polynomial O) :=
    ∑ j' ∈ Finset.range N, biRep F (dev (composedKey T) f j') * (keyY T) ^ j' with hAp
  have hAcoef : ∀ i, (Ap.coeff i).natDegree ≤ F.key.natDegree - 1 := by
    intro i
    rw [hAp, finsetSum_coeff]
    refine natDegree_sum_le_of_forall_le _ _ fun j' _ => ?_
    have h := natDegree_coeff_mul_le
      (p := biRep F (dev (composedKey T) f j')) (q := (keyY T) ^ j')
      (d := F.key.natDegree - 1) (e := 0)
      (biRep_coeff_natDegree_le F (dev (composedKey T) f j')) (hKpow j') i
    simpa using h
  have hAgrid : ∀ i, (Ap.coeff i).degree < F.key.degree :=
    degree_coeff_lt_of_natDegree_le F hAcoef (by omega)
  have hAe : Polynomial.eval F.key Ap = f := by
    rw [hAp, eval_finsetSum]
    have hterm : ∀ j' ∈ Finset.range N,
        Polynomial.eval F.key (biRep F (dev (composedKey T) f j') * (keyY T) ^ j')
          = dev (composedKey T) f j' * (composedKey T) ^ j' := by
      intro j' _
      rw [eval_mul, eval_pow, biRep_eval, keyY_eval]
    rw [Finset.sum_congr rfl hterm]
    exact sum_dev_eq hΦmonic hΦpos f hfN
  -- the transported key, and the in-grid bound on the transported chain entries
  have hKbarmonic : ((keyY T).map (AdjoinRoot.mk F.key)).Monic := hKmonic.map _
  have hKbardeg : ((keyY T).map (AdjoinRoot.mk F.key)).natDegree = T.e₂ * T.f₂ := by
    rw [hKmonic.natDegree_map, keyY_natDegree T]
  have hEbar : ∀ j', ((biRep F (dev (composedKey T) f j')).map (AdjoinRoot.mk F.key)).degree
      < ((keyY T).map (AdjoinRoot.mk F.key)).degree := by
    intro j'
    rw [degree_eq_natDegree hKbarmonic.ne_zero, hKbardeg]
    refine (degree_lt_iff_coeff_zero _ _).2 ?_
    intro k hk
    rw [coeff_map, biRep_coeff]
    have hd1 : (dev (composedKey T) f j').natDegree < (T.e₂ * T.f₂) * F.key.natDegree := by
      by_cases h0 : dev (composedKey T) f j' = 0
      · rw [h0, natDegree_zero]
        exact Nat.mul_pos hmpos hDpos
      · have h2 := natDegree_lt_natDegree h0 (degree_dev_lt hΦmonic hΦpos f j')
        rw [hΦdeg] at h2
        exact h2
    have hz : dev F.key (dev (composedKey T) f j') k = 0 := by
      refine dev_eq_zero_of_lt F.hmonic hDpos _ k ?_
      calc (dev (composedKey T) f j').natDegree
            < (T.e₂ * T.f₂) * F.key.natDegree := hd1
        _ ≤ k * F.key.natDegree := Nat.mul_le_mul_right _ hk
    rw [hz, map_zero]
  -- the assembly
  rw [shadowDev_of_ingrid T hKgrid hAgrid (keyY_eval T) hAe j]
  have hmapA : Ap.map (AdjoinRoot.mk F.key)
      = ∑ j' ∈ Finset.range N,
          ((biRep F (dev (composedKey T) f j')).map (AdjoinRoot.mk F.key))
            * ((keyY T).map (AdjoinRoot.mk F.key)) ^ j' := by
    rw [hAp, Polynomial.map_sum]
    exact Finset.sum_congr rfl fun j' _ => by
      rw [Polynomial.map_mul, Polynomial.map_pow]
  rw [hmapA, devQ_chain hKbarmonic
    (fun j' => (biRep F (dev (composedKey T) f j')).map (AdjoinRoot.mk F.key)) hEbar hjN]
  exact reass_map_biRep F (dev (composedKey T) f j)

end Exact

end Uniformity.Density.Tower

/-! ## Unfolding checks

`example`s, not declarations: the local pins on the shape of the signed definition and on the two
places a transposition would otherwise pass silently — that `IsXFree` is read at the composed
key's OWN lift argument (`−ψ₂.coeff t · η^{W(t)}` at height `(f₂−t)u₂`, C.43's body), and that the
`f₁ = 1` companion's right-hand side is the slot index of that SAME height. -/

section UnfoldingChecks

open Uniformity.Density.Tower Uniformity.Density.Leaf Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the body, verbatim: `IsXFree` IS the guarded `X`-degree-zero condition on C.43's lift slots. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) :
    IsXFree T
      ↔ ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 →
          (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))).natDegree = 0 := Iff.rfl

/-- `keyY` is read against `Z^{e₂t}`, matching C.43's `Φ′^{e₂t}` — a transposed `e₂ ↔ f₂` or a
dropped `wrapExp` would break `keyY_eval`, which is `rfl`-grade after `simp only`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) :
    Polynomial.eval F.key (keyY T) = composedKey T := keyY_eval T

/-- at an x-free datum the discrepancy is zero at EVERY coordinate, `j ≥ μ₂` included: the
statement is a coordinatewise identity, not a band statement (contrast C.72). -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (hπ : Irreducible π) (hh : 1 ≤ F.h) [Finite (IsLocalRing.ResidueField O)] (hx : IsXFree T)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) :
    ∀ j, shadowDev T f j - dev (composedKey T) f j = 0 := fun j => by
  rw [shadow_exact_of_xfree T hπ hh hx hf j, sub_self]

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.IsXFree
#print axioms Uniformity.Density.Tower.isXFree_iff_forall
#print axioms Uniformity.Density.Tower.isXFree_iff_slot_of_f1
#print axioms Uniformity.Density.Tower.devQ_finsetSum
#print axioms Uniformity.Density.Tower.devQ_term
#print axioms Uniformity.Density.Tower.devQ_chain
#print axioms Uniformity.Density.Tower.biRep
#print axioms Uniformity.Density.Tower.biRep_coeff
#print axioms Uniformity.Density.Tower.biRep_natDegree_le
#print axioms Uniformity.Density.Tower.biRep_eval
#print axioms Uniformity.Density.Tower.biRep_coeff_natDegree_le
#print axioms Uniformity.Density.Tower.biRep_natDegree_lt
#print axioms Uniformity.Density.Tower.keyY
#print axioms Uniformity.Density.Tower.keyY_eval
#print axioms Uniformity.Density.Tower.keyY_monic
#print axioms Uniformity.Density.Tower.keyY_natDegree
#print axioms Uniformity.Density.Tower.keyY_coeff_natDegree_le
#print axioms Uniformity.Density.Tower.reass_map_biRep
#print axioms Uniformity.Density.Tower.shadow_exact_of_xfree

end AxCheck
