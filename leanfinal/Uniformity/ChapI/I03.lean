/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity
import Uniformity.Density.QuadCert
import Uniformity.Density.Drainage
import Uniformity.ChapH.H93

/-!
# Uniformity.ChapI.I03 — `A1_n`, the exact-core-menu law — **CARRIER + VOIDED COPY + 4 GATES**

**Chapter I, NODE I.03** [def] [fresh], **RE-SIGNED AT AMENDMENT A-I.1 (2026-08-16)**
(`blueprint/CHAP-I_capstone_conditionality.md` §4 `### NODE I.03` — whose displayed SIGNATURE
block is ⛔ VOIDED — and the A-I.1 re-signed block immediately below it; SIGNED twin
`leanspec/Leanspec/ChapI.lean`, the `### NODE I.03` block, lines 447–490).  **ENV-I1**.
Statements transcribed BYTE-FROZEN from the leanspec; re-namespaced only (GC-6.2).

**AMENDMENTS SUPERSEDE FROZEN TEXT.**  The blueprint's own §4 signature for `MenuLawAt` is
struck; this file lands **A-I.1's re-signed form** (four conjuncts, `@id`-spelled membership),
and — separately — the pre-amendment form under the name `MenuLawAtVoided`, which the
blueprint's disposition table lists as its one *`def` NAMED-AND-VOIDED (refutation record,
cite-forbidden)* entry: *"I.03's pre-A-I.1 form, kept so its vacuity proof survives verbatim."*

## ⚠ DISPOSITION

* **Nothing is asserted about the capstone.**  Both declarations are `Prop` carriers; neither is
  proved at general `n`.  No axiom declared, no cite imported, no capstone statement asserted.
* **NOT owner-gated.**  I.03 is Display A's `(A1)` conjunct (ledger `HYP.26`) and resolves the
  `COND:A1_n` orphan (I.13); its terminal fate is a discharge node, not a cite.
* **`MenuLawAtVoided` IS CITE-FORBIDDEN.**  It exists to be refuted.  **No consumer, gate or
  census row may hypothesize it or discharge anything with it.**  Gate (3) below proves it is
  EQUAL to its bare menu clause, i.e. its `A1Family` existential carries nothing at all.

## MANDATORY BINDER-VACUITY AUDIT (A-C.8.4; verdict committed before any proving)

**Verdict on `MenuLawAt` (the live carrier): NON-VACUOUS, and SHARP AT A NAMED WITNESS — the
repair is CERTIFIED to the A-E.2 standard.  Verdict on `MenuLawAtVoided`: PROVABLY VACUOUS in
its shape clause, machine-refuted below, retained only as the refutation record.**

**(1) THE DEFECT THAT WAS FOUND (I-D9), and why it was a real one.**  The pre-A-I.1 shape clause
was one-directional — `∀ C ∈ F, C.σ ∈ S` only.  Under it `r = 0, F = []` satisfies the shape
requirement for EVERY menu `S`, so the entire `A1Family` existential is free and `MenuLawAt n`
collapses to its bare menu clause.  That collapse is **proved**, not alleged: gate (3) is an
`Iff` between `MenuLawAtVoided n` and the menu clause with no family in it.  This is the OM-4
FINDING-0 genre — a conjunct that looks like structure and asserts none — and it is **not** what
I.03's ⚠ SIGNATURE NOTE disclosed, which is why it counted as a defect rather than a disclosure.

**(2) THE RE-SIGN, and the certification that it is not cosmetic.**  A-I.1 adds the second
direction `∀ σ ∈ S, ∃ C ∈ F, C.σ = σ`, making the clause the two-directional ENUMERATION the
node's own STATEMENT always said (*"whose cells' σ-labels enumerate `S`"*).  Two machine legs,
in the A-E.2 shape (*the witness that killed the old form must FAIL against the new one*):
  * **gate (4): the killer witness dies.**  The empty family provably does NOT satisfy the
    re-signed enumeration clause at a nonempty (singleton) menu.  The vacuity genre is dead.
  * **gate (5): nothing was traded away.**  `MenuLawAt n → MenuLawAtVoided n`.  A-I.1
    STRENGTHENED I.03; it did not respell it.

**(3) NON-VACUITY IS MACHINE-WITNESSED at `n = 2`, at a REAL three-cell family** (gate (6)).
`MenuLawAt 2` is PROVED from landed `coveringMenu_two` (`Density/Drainage.lean:1087`) with the
family `[a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType]` and menu
`{splitType, inertType, ramType}`, degrees from landed `splitType_degree`/`inertType_degree`/
`ramType_degree` (`Density/QuadCert.lean:55–59`).  Under the re-signed clause the witness must
now EXHIBIT a cell for every menu member, which is exactly what the 0e gate's empty list could
not do.  So the carrier is inhabited at a real degree and is not provable in general.

**(4) ⚠ WHAT THE `n = 2` WITNESS DOES AND DOES NOT CERTIFY.**  The three cells carry the
σ-labels and nothing else: `r = 0`, so the locus, stride, exponent and visibility data are
vacuously trivial and `coeff = 1` is a placeholder.  **The label ENUMERATION is certified.  The
WEIGHT-correctness tie is NOT**, by anything in this file.

**(5) THE CARRIER'S ONE DELIBERATE UNDER-STATEMENT, disclosed (the ⚠ SIGNATURE NOTE, unchanged
by A-I.1).**  HYP.26's *"internal σ_F labels and exact weights"* has its exact-weights half
carried by the `A1Cell.coeff` field plus the count laws (C.114 / CHAP-H §7).  This carrier states
**menu + shape + labels only**; the weight-correctness tie stays OPEN-MATH (§3 rows
`HYP.23`/`HYP.32`/`HYP.35`) and is deliberately not smuggled in.

**(6) The five complete-DVR instance binders are inhabited** (`ℤ_[p]`, landed
`Density/LocalData.lean` §6), verbatim the bundle of landed `DrainageAt`; not the C.113 `hne`
shape.  No unpinned carrier field (C.111): every cell of `F` is tied to `S` in both directions by
the two shape conjuncts.  No self-loop or quantified history (C.94).  No guarded `≠ ⊤` (C.118).

## Definitional choices made here (flagged for human review)

1. **Namespace** `Uniformity.Density`, flat (GC-6.2).  `A1Cell`/`A1Family` are referenced at
   their landed path `Uniformity.Density.Induction.*` (`ChapH/H93.lean:36–70`), verified by `rg`.
2. **THE `@id` SPELLING IS SIGNED, NOT MINE, and it is load-bearing for elaboration** (defect
   I-D5).  `∀ C ∈ F` does not elaborate: `Induction.A1Family r` is a plain `def` for
   `List (A1Cell r)`, and instance search will not unfold a plain `def` to find `Membership`.
   The signed spelling is `∀ C ∈ @id (List (Induction.A1Cell r)) F`, which is **type-identical**.
   It reverts to the plain spelling if and only if H.93 later lands an `abbrev` or a `Membership`
   instance.  A human reviewing this should read it as `∀ C ∈ F` and nothing more.
3. **`a1LabelCell` is `private`**, so this file exports exactly the two signed public names.  Its
   ten field values are forced: at `r = 0` every `Fin 0`-indexed field is `Fin.elim0`, and
   `expConst`/`visConst`/`coeff` are the only free choices — set to `0`, `0`, `1`.  **These three
   are arbitrary** and carry no content; see audit item (4).
4. **Imports** are per-node minimal (`GenuineDensity` for `CoveringMenu`, `QuadCert` for the
   degree-2 types, `Drainage` for `coveringMenu_two`, `ChapH.H93` for the cells) rather than
   ENV-I1's nominal `import Uniformity`, which inherits leanspec defect **I-D1** (the `ChapD`
   roll-up plus the chapter-E deep-twist branch is a hard Lean error at HEAD).
5. **Gates are anonymous `example`s**, transcribed from the leanspec's executed §4 gate items
   (7)/(7a)/(7b) (lines 828–856) and the I.23 witness (lines 1229–1257).
-/

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- `A1_n` (Display A; ledger HYP.26; COND:A1_n's resolution — I.13): a q-independent
`(A1)`-admissible family list whose σ-labels ENUMERATE a covering menu at degree `n`. The shape
clause uses chapter H's landed `A1Family`/`A1Cell` (H.93, with W-12 r4's σ-label field).

⚠ SIGNATURE NOTE (blueprint's own, UNCHANGED by A-I.1): the exact-weights clause of HYP.26 is
carried by the `A1Cell.coeff` field plus the count laws (C.114/H §7) — this carrier states menu
+ shape + labels, and the WEIGHT-correctness tie stays OPEN-MATH (§3 rows HYP.23/32/35).
⚠ A-I.1 (I-D9): the second conjunct (`∀ σ ∈ S, ∃ C ∈ F, C.σ = σ`) is the half that was missing.
Without it `r = 0, F = []` satisfies the shape clause for EVERY `S` and the `A1Family`
existential is vacuous — proved in the gate below against `MenuLawAtVoided`, and the empty
family is proved NOT to satisfy the re-signed clause at a nonempty menu.
⚠ A-I.1 (I-D5): `∀ C ∈ F` is spelled `∀ C ∈ @id (List (Induction.A1Cell r)) F` because
`Induction.A1Family` is a plain `def` and instance search will not unfold it. Type-identical;
reverts to the plain spelling if H.93 lands an `abbrev` or a `Membership` instance. -/
def MenuLawAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧
    (∀ σ ∈ S, ∃ C ∈ @id (List (Induction.A1Cell r)) F, C.σ = σ) ∧
    (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S

/-- **NAMED-AND-VOIDED (A-I.1, defect I-D9): I.03's pre-amendment form**, kept so its machine
refutation survives verbatim (the `OM4Shadow.*` pattern). The shape clause here is the
one-directional one; the gate below proves this `Prop` is EQUAL to its bare menu clause, i.e.
the `A1Family` existential carries nothing. **No consumer, gate or census row may cite this
name**; it exists to be refuted. -/
def MenuLawAtVoided (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧ (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S

section GateThree

-- (3) **DEFECT I-D9, machine-PROVED, PRESERVED VERBATIM AGAINST THE VOIDED NAME.** The
-- pre-A-I.1 shape clause is one-directional, so `r = 0, F = []` satisfies it for every `S`, and
-- `MenuLawAtVoided` is EQUAL to its bare menu clause. This is the OM-4 FINDING-0 genre and is
-- NOT what I.03's ⚠ SIGNATURE NOTE disclosed.
example (n : ℕ) : MenuLawAtVoided n ↔
    ∃ S : Finset FactorizationType, (∀ σ ∈ S, σ.degree = n) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        CoveringMenu O n S := by
  constructor
  · rintro ⟨_, _, S, _, hdeg, hmenu⟩
    exact ⟨S, hdeg, hmenu⟩
  · rintro ⟨S, hdeg, hmenu⟩
    exact ⟨0, ([] : List (Induction.A1Cell 0)), S, by intro C hC; simp at hC, hdeg, hmenu⟩

-- (4) **A-I.1's CERTIFICATION of the I-D9 re-sign (the A-E.2 standard: the witness that killed
-- the old form must FAIL against the new one).** The empty family does not satisfy the
-- re-signed enumeration clause at any nonempty menu — so the vacuity witness genre is dead.
example (σ₀ : FactorizationType) :
    ¬ (∀ σ ∈ ({σ₀} : Finset FactorizationType),
        ∃ C ∈ @id (List (Induction.A1Cell 0)) ([] : Induction.A1Family 0), C.σ = σ) := by
  intro h
  obtain ⟨C, hC, _⟩ := h σ₀ (Finset.mem_singleton_self σ₀)
  simp at hC

-- (5) the re-signed carrier still IMPLIES the old one (nothing was traded away): A-I.1
-- STRENGTHENED I.03, it did not respell it.
example (n : ℕ) (h : MenuLawAt n) : MenuLawAtVoided n := by
  obtain ⟨r, F, S, hsub, _, hdeg, hmenu⟩ := h
  exact ⟨r, F, S, hsub, hdeg, hmenu⟩

-- (6) **NON-VACUITY of `A1` at `n = 2`, at a REAL three-cell family** — so the witness has to
-- EXHIBIT a family whose σ-labels run over the whole menu, which the 0e gate's empty-list
-- witness could not. ⚠ The three cells carry the σ-labels and nothing else (`r = 0`): the label
-- ENUMERATION is certified, the WEIGHT-correctness tie is not certified by anything here.
private def a1LabelCell (σ : FactorizationType) : Induction.A1Cell 0 where
  offset := fun i => i.elim0
  stride := fun i => i.elim0
  stride_pos := fun i => i.elim0
  expCoeff := fun i => i.elim0
  expCoeff_pos := fun i => i.elim0
  expConst := 0
  visCoeff := fun i => i.elim0
  visConst := 0
  coeff := 1
  σ := σ

example : MenuLawAt 2 := by
  refine ⟨0, [a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType],
    {splitType, inertType, ramType}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    · exact ⟨a1LabelCell splitType, by simp, rfl⟩
    · exact ⟨a1LabelCell inertType, by simp, rfl⟩
    · exact ⟨a1LabelCell ramType, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    exacts [splitType_degree, inertType_degree, ramType_degree]
  · intro O _ _ _ _ _
    exact coveringMenu_two

end GateThree

end Uniformity.Density

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.MenuLawAt
#print axioms Uniformity.Density.MenuLawAtVoided
