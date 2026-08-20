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

end Uniformity.Density.Tower
