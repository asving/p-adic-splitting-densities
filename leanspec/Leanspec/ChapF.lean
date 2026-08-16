import Uniformity

/-!
# Chapter F — THE GRT WELD LAYER: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-F_weld_layer.md` (30 nodes F.01–F.30; the consumer-first weld
layer authored backwards from Display A's two surviving weld conjuncts), landed in the isolated
`leanspec` environment **before** the chapter-F fleet fires, in the blueprint's node order.

**STATE: OPEN (stage-0e gate executed 2026-08-16).** Chapter F has landed nothing in `leanfinal`
(`grep` for `Density.Weld` / `CarryCocycle` / `LedgerJunction` / `JD0Box2` over
`leanfinal/Uniformity/`: zero hits), so every theorem-shaped stub is in the UNLANDED state of
`Leanspec.lean`'s stub lifecycle — an `axiom` at the exact signed type. Nothing is retired; there
is no name collision with `Uniformity.*`.

**Wrapper choice, declared per GC-6.6:** wrapper `namespace LeanspecF` (the CHAP-B/E/H route),
which the blueprint's §0.2 and §12 instruct directly. Consequently the blueprint's
`namespace Uniformity.Density.Weld` headers in the SIGNATURE blocks are DROPPED here and every
declaration is flat inside `LeanspecF`; the landed-side namespace assignment (all F definitions →
`Uniformity.Density.Weld`; no F node is a theorem about a landed object, so nothing goes to
`Uniformity.Density`) is what the fleet must land.

**This file is never imported by `leanfinal` or `leancheck`.** It carries `axiom`s by design; it is
an interface contract, not mathematics. Nothing here is proved. `sorry` appears nowhere; the file
elaborates with `autoImplicit`/`relaxedAutoImplicit` **off**.

## The two Display-A supply nodes (the chapter's product — read this first)

`JD0Box2` (F.04) and `GenhnBox2` (F.11) are the two `Prop`-carriers chapter I consumes as Display-A
conjunct fields, so their types must elaborate EXACTLY as signed. **Both elaborate verbatim, with
no stub-side adjustment** — see the two nodes below and the report:

* `JD0Box2 : ∀ {Γ K} [AddCommGroup Γ] [Field K], ValueDictSite Γ K → Prop`, unfolding to
  `∃ u : Γ → Kˣ, site.slotAct = slotScale u ∧ site.ledgerAct = gaugeCobdry u` — byte-identical to
  the blueprint's §4 signature.
* `GenhnBox2 : ∀ {K} [Field K], CarrySite K → Prop`, unfolding to
  `3 ≤ s.μ → ∃ (h : NeZero s.E) (cc : CarryCocycle s.E K), ∀ a b, (cc.c a b : K) = s.carry a b` —
  byte-identical, and in particular the **non-instance-implicit `∃ (h : NeZero s.E)` binder DOES
  serve as the instance for `CarryCocycle s.E K`** (Lean 4.31 registers every local hypothesis of
  class type as a local instance). This was the single riskiest signature in the chapter and it
  needs no repair.

`W1Transport` (F.12), the named sub-residue, needs ONE stub-side repair — the bound variable is
spelled `λ` in the blueprint, which is the lambda keyword (defect **F-D2**); the TYPE is unchanged
by the rename.

## Census (mechanical, over this file)

| kind | count | note |
|---|---:|---|
| `structure` (real bodies) | **8** | `ValueDictSite`, `JD0SiteStrike`, `CarryCocycle`, `CarrySite`, `LedgerJunction`, `WeldMPkg`, `WeldSupply`, `WeldObligations` |
| `def` / `noncomputable def` (real bodies) | **16** | `gaugeCobdry`, `slotScale`, `slotScaleEquiv`, `resTwist`, `JD0Box2`, `TwistedAlgebra`, `single`, `GenhnBox2`, `W1Transport`, `SigmaLedgerLaw`, `xiChar`, `JAResLaw`, `JAGridLaw`, `XiWSatisfies`, `jbShear`, `JBVtxFace`, `gaugeBdry`, `DmultW` (18 counting the two below-the-line helpers `single` and the gate data) |
| `instance` (below-the-line helpers, F.08) | **5** | `Mul`, `AddCommGroup`, `Module K`, `One`, `Pow _ ℕ` on `TwistedAlgebra` |
| `axiom` stubs of theorem-shaped rows | **13** | F.02, F.03 (×3), F.06, F.09, F.10 (×2), F.13, F.15, F.16, F.18, F.23 (×2), F.25 — 15 axioms over 11 nodes |
| gate `example`s / `#eval`s, all executed | **§10** | F.29, F.30 — see the gate block |

Nodes with no Lean declaration of their own: none in §§4–9; F.29/F.30 are gate blocks whose
"signature" is the executed check list.

## Gate order (GC-6.6(c) / CHAP-H §15) as actually run

(a) the seven FRAGILE signatures of §12(a) first — F.08 (the `Type _` wrapper + the twisted
instances), F.10 (`Module.finrank` through the wrapper, the `single`/`•` spelling), F.28 (the
`Prop`-valued structure with three index-type parameters), F.26 (`DmultW`'s quantifier order),
F.29/F.30's concrete field instances, F.15 (the multiplied-form `δ_j`), F.03 (`resTwist`'s
`noncomputable` marker); (b) the `def` bodies, real; (c) **the §10 numeric gates EXECUTED at
`q = 2` AND `q = 3`**; (d) the `axiom` stubs.

## THE DEFECT LIST (stage-0e gate, 2026-08-16)

Recorded here and in the 0e report; **NOT repaired in the blueprint** (§12 rule / CHAP-H §15
rule 5: elaboration failures in a stub are blueprint defects, versioned by a dated append in the
blueprint, never patched in `leanspec`). Every stub-side adjustment made to get this file to
elaborate is listed; nothing was adjusted silently.

* **F-D1 — `Σmap` / `hΣ` / `hΣx` / `hΣρ` are NOT legal Lean identifiers (hard parse error).**
  F.14's `LedgerJunction` field is signed `Σmap`, used as `J.Σmap` in F.15/F.16/F.17; F.27's
  `WeldSupply` field is signed `hΣ`; and F.15 additionally signs two HYPOTHESIS binders `hΣx`,
  `hΣρ`. At the Lean 4.31 pin `Σ` (U+03A3) is explicitly EXCLUDED from `isLetterLike` (as is `Π`),
  because it is the Sigma-type token: `structure P (K) [Field K] where Σmap : K → K` fails with
  `unexpected token 'Σ'; expected command`, and `(hΣx : …)` with `unexpected token 'Σ'; expected
  ')'`. *Class: illegal identifier (same family as CHAP-E's E-D3 `hλ`).* **Stub-side repair:**
  `Σmap` → `sigmaMap`, `hΣ` → `hSigma`, `hΣx`/`hΣρ` → `hSigmax`/`hSigmarho`, consistently at F.14,
  F.15, F.16, F.17, F.27. Field/binder RENAME only — every type is unchanged (binder names are not
  part of a type; the `LedgerJunction`/`WeldSupply` FIELD names are, so those two are the ones the
  fleet must land as respelled). It CANNOT land the signed spelling.
* **F-D2 — F.12's `∀ λ, …` is a hard parse error.** `W1Transport`'s bound variable is spelled `λ`,
  the lambda keyword: `unexpected token 'λ'; expected '(', '[', '_', '{', '⦃' or identifier`. Note
  the blueprint's own F.26 avoids this (`∀ lam mu : Λ`), so the two nodes are internally
  inconsistent. *Class: illegal identifier.* **Stub-side repair:** `∀ l, Rharness l = …`. The TYPE
  is identical (bound-variable names are not part of it), so the Display-A sub-residue carrier is
  unaffected.
* **F-D3 — F.10's `^` has no signed instance: `One` and `Pow` on `TwistedAlgebra` are missing from
  F.08's helper list.** F.08 signs exactly four helpers (`Mul`, `single`, `AddCommGroup`,
  `Module K`); F.10's `pow_card_single` writes `(single 1 1 : TwistedAlgebra cc) ^ E`, which needs
  `Pow (TwistedAlgebra cc) ℕ`, i.e. (via `npowRec`) a `One`. *Class: missing declaration in a
  signed helper list.* **Stub-side repair, following F.09's own prose** ("`single 0 (cc.c 0 0)⁻¹`
  is a two-sided unit"): `One (TwistedAlgebra cc) := ⟨single 0 ((cc.c 0 0 : K))⁻¹⟩` and
  `Pow (TwistedAlgebra cc) ℕ := ⟨fun f n => npowRec n f⟩` — the same `npow` any later `Monoid`
  instance would carry, so F.10's statement is unchanged in content. The fleet must land these two
  instances (or a full `Monoid`/`Ring` instance, which is the natural target once F.09 is proved).
* **F-D4 — F.22's below-the-line helper is signed in prose only.** "`jbShear` injectivity (`e ≠ 0`)
  is a below-the-line helper lemma the gate uses" has no SIGNATURE block, so there is nothing to
  stub at an exact type; this file's F.30 gate uses pointwise image values instead (which is what
  the blueprint's own §10 leg 6 pins), and no `jbShear_injective` stub is signed. *Class: unsigned
  helper.* No stub-side repair; recorded so the fleet does not read the absence as an omission
  here.
* **F-D5 — three §10 legs are not `decide`-able as written; executed in equivalent decidable form
  (all expected VALUES reproduced).** (i) F.29 leg 3 / F.30's `Module.finrank` and `Nat.card` legs
  are noncomputable: `finrank` is executed as the `Fintype.card`/`Nat.card` pair through the
  carrier `ZMod E → K` (the def's own body), and `Nat.card` via `Nat.card_eq_fintype_card`.
  (ii) F.30 leg 1's `orderOf z = 4` is executed as the power certificate `z ^ 4 = 1 ∧ z ^ 2 ≠ 1`
  (order divides 4, is not 1 or 2 ⟹ order 4) — `orderOf` does not kernel-reduce. (iii) F.30 legs 3
  and 6 are set-level (`slotScale u '' S = S`, `jbShear e h '' V = V'`); executed pointwise on the
  named finite witnesses, which is the arithmetic content the blueprint pins. *Class: gate-form
  (not a statement defect).*
* **F-D6 — F.29/F.30's `AdjoinRoot` field constructions do not carry `decide`-able instances; the
  pre-authorised table fallback was used.** `F₄ := AdjoinRoot (X² + X + 1 : (ZMod 2)[X])` and
  `F₉ := AdjoinRoot (X² + 1 : (ZMod 3)[X])` have no `DecidableEq`/`Fintype` instances (AdjoinRoot
  is a quotient of a polynomial ring), so no `decide` gate can fire on them. Per §10's own
  pre-authorisation ("a private table-built field instance below the gate in the same file"), the
  gate uses table-built `F4 = ZMod 2 × ZMod 2` (`θ² = θ + 1`) and `F9 = ZMod 3 × ZMod 3`
  (`θ² = −1`), each with a `CommRing` proved by `decide` and a `Field` built on the explicit
  inverse `x⁻¹ = x ^ (q − 2)`. `native_decide` is NOT used anywhere in this file. *Class:
  gate-form; the fallback the blueprint itself authorised.*

## What is real and what is a stub

Per stage-0e rule 1: the definitional layer lands as REAL BODIES (8 `structure`s, the `def`s, and
F.08's below-the-line instances); theorem-shaped nodes land as `axiom` stubs at the exact signed
type. **No `sorry`.** The two GC-13 BLOCKED-UNTIL-RESOLUTION instance obligations (F.17's C-side
`SigmaLedgerLaw` discharge, F.24's M4 instance) are NOT stubbed as provable — only their carrier
declarations land, exactly as §12 instructs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LeanspecF

open Finset Polynomial

/-! ## §4 — THE `JD0-BOX-2` INTERFACE (F.01–F.06) -/

/-! ### NODE F.01 [def] — the unit-character gauge action (`EFF.JD0.05` lines 1–2).
Lands `Uniformity.Density.Weld.gaugeCobdry` and `.slotScale`. ENV-F1 + `[Field K]`. -/

/-- The coboundary transform of a `Kˣ`-valued 2-cochain by a 1-cochain `u`
(`EFF.JD0.05` line 1: `c ↦ c·∂u`). -/
def gaugeCobdry {Γ : Type*} [AddCommGroup Γ] {K : Type*} [Field K]
    (u : Γ → Kˣ) (c : Γ → Γ → Kˣ) : Γ → Γ → Kˣ :=
  fun γ γ' => c γ γ' * u γ * u γ' * (u (γ + γ'))⁻¹

/-- The slot-wise unit action (`EFF.JD0.05` line 2): coordinatewise unit scaling of a
slot family. -/
def slotScale {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) (v : Γ → K) : Γ → K :=
  fun γ => (u γ : K) * v γ

/-! ### NODE F.02 [lemma] — the slot action is a bijection; counts are blind to it.
The `def` half lands real (its two signed `simp [slotScale]` proof bodies elaborate as written);
the count identity is the `axiom` stub. -/

/-- Slot-wise unit scaling is an equivalence (`EFF.JD0.06` clause (i)'s mechanism shadow). -/
def slotScaleEquiv {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) :
    (Γ → K) ≃ (Γ → K) where
  toFun := slotScale u
  invFun := slotScale u⁻¹
  left_inv := by intro v; funext γ; simp [slotScale]
  right_inv := by intro v; funext γ; simp [slotScale]

axiom card_image_slotScale {Γ K : Type*} [Field K] (u : Γ → Kˣ) (S : Set (Γ → K)) :
    Nat.card ↥(slotScale u '' S) = Nat.card ↥S

/-! ### NODE F.03 [lemma] — the residual ξ-twist's CONCLUSIONS (WZ-BOX-7 compliant: degree,
monicity, root census; never a type-preservation claim). -/

/-- The monic-normalized residual twist by a unit `ξ` (`EFF.JD0.05` line 3). -/
noncomputable def resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) : K[X] :=
  C ((ξ : K) ^ R.natDegree)⁻¹ * R.comp (C (ξ : K) * X)

axiom natDegree_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) :
    (resTwist ξ R).natDegree = R.natDegree

axiom monic_resTwist {K : Type*} [Field K] (ξ : Kˣ) {R : K[X]} (hR : R.Monic) :
    (resTwist ξ R).Monic

axiom isRoot_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) (r : K) :
    (resTwist ξ R).IsRoot r ↔ R.IsRoot ((ξ : K) * r)

/-! ### NODE F.04 [interface-carrier] — `JD0-BOX-2`, the gauge-form perimeter (HYP.74, CARRY).
**Display-A supply node (1 of 2).** Elaborates verbatim. -/

/-- A weld VALUE-DICTIONARY site: an indexed action on slot families, with its residual and
ledger legs. Abstract — instances are the seven cone sites' in-note data. -/
structure ValueDictSite (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  slotAct : (Γ → K) → (Γ → K)
  ledgerAct : (Γ → Γ → Kˣ) → (Γ → Γ → Kˣ)

/-- `JD0-BOX-2` at ledger strength (HYP.74): the site's dictionary is realized by a
slot-wise unit character — a carry gauge in the `EFF.JD0.05` class. CARRIED, not proved;
chapter I's conjunct field. -/
def JD0Box2 {Γ K : Type*} [AddCommGroup Γ] [Field K] (site : ValueDictSite Γ K) : Prop :=
  ∃ u : Γ → Kˣ, site.slotAct = slotScale u ∧ site.ledgerAct = gaugeCobdry u

/-! ### NODE F.05 [def] — the per-site strike ledger (HYP.74's fold route as a datum). -/

/-- A per-site STRIKE (HYP.74's fold route): the site's gauge exhibited as an explicit
z-power unit character. One instance per audited cone site. -/
structure JD0SiteStrike (Γ K : Type*) [AddCommGroup Γ] [Field K] where
  site : ValueDictSite Γ K
  z : Kˣ
  a : Γ → ℤ
  strike : site.slotAct = slotScale (fun γ => z ^ a γ)

/-! ### NODE F.06 [lemma] — the `F₂` degeneracy disclosure, made structural (`JD0-BOX-5`). -/

axiom slotScale_eq_id_of_card_two {Γ K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) (u : Γ → Kˣ) : slotScale u = id

/-! ## §5 — THE `GENHN-BOX-2` / W-9 FACE (F.07–F.13) -/

/-! ### NODE F.07 [def] — the carry-cocycle datum (W-9 clauses (i)+(ii) as a structure).
Kind inversion disclosed in the blueprint: the corpus PROVES (i)/(ii); here they are FIELDS, so
the corpus conditionality is carried by instantiation. -/

/-- A carry cocycle over `ZMod E` (`EFF.GRTJC.89` clauses (i)/(ii)): the `Kˣ`-valued
2-cocycle with its `{0,1}`-valued integer shadow. -/
structure CarryCocycle (E : ℕ) [NeZero E] (K : Type*) [Field K] where
  c : ZMod E → ZMod E → Kˣ
  δ : ZMod E → ZMod E → ℕ
  cocycle : ∀ a b d, c a b * c (a + b) d = c b d * c a (b + d)
  δ_le_one : ∀ a b, δ a b ≤ 1
  δ_cocycle : ∀ a b d, δ a b + δ (a + b) d = δ b d + δ a (b + d)

/-! ### NODE F.08 [def] — the twisted group algebra `K^c[ℤ/E]` (W-9 clause (iii)'s object),
with the below-the-line helpers. `Type _` `def` (not `abbrev`) so the twisted `Mul` cannot leak
onto plain `ZMod E → K`. -/

/-- The twisted group algebra `K^c[ℤ/E]` of the abscissa-coset group over the carry cocycle
(`EFF.GRTJC.89` clause (iii)). Carrier: `ZMod E → K`; multiplication: `c`-twisted
convolution. -/
def TwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Type _ := ZMod E → K

/-- `(f ⋆ g) t = ∑ a, c a (t − a) · f a · g (t − a)`. -/
instance instMulTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Mul (TwistedAlgebra cc) :=
  ⟨fun f g t => ∑ a : ZMod E, (cc.c a (t - a) : K) * f a * g (t - a)⟩

/-- The `single` basis vectors of `TwistedAlgebra cc`. -/
def single {E : ℕ} [NeZero E] {K : Type*} [Field K] {cc : CarryCocycle E K}
    (a : ZMod E) (x : K) : TwistedAlgebra cc :=
  fun t => if t = a then x else 0

instance instAddCommGroupTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : AddCommGroup (TwistedAlgebra cc) := Pi.addCommGroup

instance instModuleTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Module K (TwistedAlgebra cc) := Pi.module _ _ _

/-- **Defect F-D3's stub-side repair**, following F.09's own prose (`single 0 (cc.c 0 0)⁻¹` is the
two-sided unit): the `One`/`Pow` pair F.10's `^` needs and F.08's helper list omits. -/
instance instOneTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : One (TwistedAlgebra cc) := ⟨single 0 ((cc.c 0 0 : K))⁻¹⟩

instance instPowTwistedAlgebra {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Pow (TwistedAlgebra cc) ℕ := ⟨fun f n => npowRec n f⟩

/-! ### NODE F.09 [theorem] — associativity IS the cocycle identity (abstract half). -/

axiom TwistedAlgebra.mul_assoc {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) (f g h : TwistedAlgebra cc) :
    f * g * h = f * (g * h)

/-! ### NODE F.10 [theorem] — dimension `E` and the power basis (clause (iii)'s count +
JC-F1's cyclic presentation). SPLIT-MANDATED to two files at landing (F.10a/F.10b). The
`single 0 1` normalization is a STATEMENT FENCE: the `•`-form is the contract. -/

axiom TwistedAlgebra.finrank_eq {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) : Module.finrank K (TwistedAlgebra cc) = E

axiom TwistedAlgebra.pow_card_single {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (cc : CarryCocycle E K) :
    (single 1 1 : TwistedAlgebra cc) ^ E
      = (∏ k ∈ Finset.Ico 1 E, (cc.c 1 (k : ZMod E) : K)) • single 0 1

/-! ### NODE F.11 [interface-carrier] — `GENHN-BOX-2` at ledger strength (HYP.148, CARRY;
live at `n ≥ 6`). **Display-A supply node (2 of 2).** Elaborates verbatim, including the
non-instance-implicit `∃ (h : NeZero s.E)` binder. Clause (iv) is structurally ABSENT. -/

/-- A composite-stage CARRY SITE at multiplicity `μ`: the stage's carry bookkeeping as an
abstract indexed family. Instances are chapter-H/C stage objects (GC-13). -/
structure CarrySite (K : Type*) [Field K] where
  E : ℕ
  hE : 1 ≤ E
  μ : ℕ
  carry : ZMod E → ZMod E → K   -- the stage's own carry table (site data)

/-- `GENHN-BOX-2` at ledger strength (HYP.148): at `μ ≥ 3` the site's carry bookkeeping is
realized by a carry cocycle's twisted algebra — W-9 clauses (i)–(iii), clause (iv) absent.
CARRIED, not proved; chapter I's `n ≥ 6`-indexed conjunct field. -/
def GenhnBox2 {K : Type*} [Field K] (s : CarrySite K) : Prop :=
  3 ≤ s.μ → ∃ (h : NeZero s.E) (cc : CarryCocycle s.E K),
    ∀ a b, (cc.c a b : K) = s.carry a b

/-! ### NODE F.12 [interface-carrier] — the `W-1` transport, `GENHN-BOX-2`'s sub-residue
(HYP.139, MATH-class: a PROOF obligation, not a citation one). Defect **F-D2**: the signed bound
variable `λ` is the lambda keyword; renamed `l` here, type unchanged. -/

/-- `W-1` (HYP.139) at ledger strength: the harness-to-FGMN transport dictionary exists at
the site's order — a line-wise unit system relating the two residual operators. MATH-class
obligation; chapter I's field, riding under `GenhnBox2`. -/
def W1Transport {K : Type*} [Field K] {ι : Type*}
    (Rharness RGMN : ι → K) : Prop :=
  ∃ c : ι → Kˣ, ∀ l, Rharness l = (c l : K) * RGMN l

/-! ### NODE F.13 [lemma] — the count form of the twisted layer (cardinality, not
type-preservation). Interface citations (annotations, not Lean deps): H.87 `carry_cancel` /
`carry_cancel_char_two`, H.61 `TriangularUnitPivot.card_fibre`. -/

axiom TwistedAlgebra.nat_card {E : ℕ} [NeZero E] {K : Type*} [Field K] [Finite K]
    (cc : CarryCocycle E K) :
    Nat.card (TwistedAlgebra cc) = Nat.card K ^ E

/-! ## §6 — THE Σ-LAW (SIGMALAW) (F.14–F.18); DECISION D-F3 in force: no F node declares a
`FactorizationType`-valued function — σ-valued outputs consume chapter E's `ladderSigma`
(unlanded at this gate: `leanfinal/Uniformity/ChapE/` is empty, so the GC-13 placeholder stands
and NO Lean reference to `ladderSigma` appears here — none is signed). -/

/-! ### NODE F.14 [def] — the abstract ledger junction (`(Σ-LEDGER)` as a structure).
Defect **F-D1**: the signed field name `Σmap` is not a legal identifier; `sigmaMap` here. -/

/-- An abstract ledger junction (`EFF.SIGMALAW.05`'s `(Σ-LEDGER)` as a structure):
prints = slot constant × Σ of reads. -/
structure LedgerJunction (K : Type*) [Field K] (ι α : Type*) where
  sigmaMap : K → K
  u : ι → Kˣ
  Prnt : ι → α → K
  read : ι → α → K
  hledger : ∀ j a, Prnt j a = (u j : K) * sigmaMap (read j a)

/-! ### NODE F.15 [lemma] — SL-C1's core: the slot constant cancels and `δ = ρ/Σ(ρ)`.
The multiplied-form normalization is deliberate (avoids `0/0` junk) — a statement fence. -/

axiom LedgerJunction.delta_eq {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) (j : ι) (C P : α) (ρ : Kˣ)
    (hx : J.read j C ≠ 0) (hP : J.read j P = (ρ : K) * J.read j C)
    (hmul : J.sigmaMap ((ρ : K) * J.read j C) = J.sigmaMap (ρ : K) * J.sigmaMap (J.read j C))
    (hSigmax : J.sigmaMap (J.read j C) ≠ 0) (hSigmarho : J.sigmaMap (ρ : K) ≠ 0) :
    (J.Prnt j C * ((ρ : K) * J.read j C)) / (J.Prnt j P * J.read j C)
      = (ρ : K) / J.sigmaMap (ρ : K)

/-! ### NODE F.16 [lemma] — SL-C2's core: strict ⟹ unit-trivial, on the WEAKER hypotheses
(injective + fixes 1; no automorphism property). The CONVERSE (the note's N-1) is stated
nowhere. -/

axiom unit_eq_one_of_sigma_eq_one {K : Type*} [Field K]
    {sigmaMap : K → K} (hinj : Function.Injective sigmaMap) (h1 : sigmaMap 1 = 1)
    (ρ : Kˣ) (hρ : sigmaMap (ρ : K) = 1) : (ρ : K) = 1

/-! ### NODE F.17 [interface-carrier] — THEOREM SL-1 at corpus scope (ACCEPTED 2/2 + CERTIFIED).
The carrier DECLARATION lands here; its C-side instance discharge is
**BLOCKED: GC-13 (`EFF.SIGMALAW.03 [supplied-by: chapter C]`)** and is NOT stubbed. -/

/-- SL-1's Σ-properties package: what the corollaries consume from the corpus theorem. -/
def SigmaLedgerLaw {K : Type*} [Field K] {ι α : Type*}
    (J : LedgerJunction K ι α) : Prop :=
  Function.Injective J.sigmaMap ∧ J.sigmaMap 1 = 1 ∧
    ∀ x y, J.sigmaMap (x * y) = J.sigmaMap x * J.sigmaMap y

/-! ### NODE F.18 [def+lemma] — the formula character and its `q = 2` degeneration
(`ξ₂ = θ₂⁻¹`). Statement fence carried from F.17: `Σ_m` is NEVER the bare interior twist. -/

/-- The §3.4 formula character `ξ = χ^γ · z^{−eA}` (`EFF.SIGMALAW.03`). -/
def xiChar {K : Type*} [Field K] (χ : Kˣ) (γ : ℤ) (z : Kˣ) (e A : ℤ) : Kˣ :=
  χ ^ γ * z ^ (-(e * A))

axiom xiChar_base {K : Type*} [Field K] (γ : ℤ) (z : Kˣ) (e A : ℤ) :
    xiChar 1 γ z e A = (z ^ (e * A))⁻¹

/-! ## §7 — THE REACHABLE GRT STRUCTURAL CLAUSES (F.19–F.26).
DECISIONS D-F1/D-F2 (the two MUTUAL-RECON SCC directions) are DAG rulings, not Lean
declarations — nothing to stub. -/

/-! ### NODE F.19 [interface-carrier] — THEOREM JA-RES at its recorded scope. GRTJA arc **1/2**
— the single priced input on J-D0's critical path (honesty F-7); carried, never upgraded.
JA-BOX-1's refuted slot-independent form is fenced structurally: the exponent is
`abscissa i * A`, never a constant. -/

/-- JA-RES at recorded scope (`EFF.GRTJA.08`): the per-slot pure-character law relating
print residual coefficients to harness packed digits. Carried at GRTJA arc 1/2. -/
def JAResLaw {K : Type*} [Field K] {ι : Type*}
    (printCoeff harnessDigit : ι → K) (z : Kˣ) (A : ℤ) (abscissa : ι → ℤ) : Prop :=
  ∀ i, printCoeff i = (z ^ (-(abscissa i * A)) : Kˣ) * harnessDigit i

/-! ### NODE F.20 [interface-carrier] — JA-GRID-CORR's UNCONDITIONAL half (terminal C2-4).
The print T-point clause (which needs `u(V) ≥ 0`, HYP.21, OUT of cone) is deliberately absent. -/

/-- JA-GRID-CORR's unconditional half (`EFF.GRTJA.07`, terminal C2-4): the integer-grid
digit/coordinate identity with its carry clause, as an abstract indexed law. -/
def JAGridLaw {ι : Type*} (digit : ι → ℤ) (coord : ι → ℤ) (carry : ι → ℤ) : Prop :=
  ∀ i, digit i = coord i + carry i

/-! ### NODE F.21 [interface-carrier] — the `(ξ, w)` covariance family at its ACCEPTED fenced
scope: SATISFACTION, never uniqueness (`EFF.GRTW2.21`'s support-stabilizer non-uniqueness). -/

/-- The (ξ,w) orbit-equation predicate (`EFF.GRTW2.19`): the displayed pair SATISFIES the
covariance equations — an existence/satisfaction form, never uniqueness. -/
def XiWSatisfies {K : Type*} [Field K] (ξ w : Kˣ) (R ψ : K[X]) : Prop :=
  R = (w : K) • ψ.comp (C (ξ : K) * X)

/-! ### NODE F.22 [interface-carrier] — the JB position faces at ACCEPTED 2/2 (J-D0's L4 leg).
JB-DEV(i) (the division-chain identity) enters as PROVENANCE on F.04/F.11, not as a predicate
here: chapter C owns "the classifier's division". Defect **F-D4**: the prose-only injectivity
helper is unsigned. -/

/-- The JB frame shear `Σ_q(i,u) = (i, e·u + h·i)` (`EFF.GRTJB.86/.101`). -/
def jbShear (e h : ℤ) : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, e * p.2 + h * p.1)

/-- JB-VTX's vertex transport, abstract: the shear maps the harness vertex set onto the
print vertex set (`EFF.GRTJB.102`). ACCEPTED 2/2; instances are site data. -/
def JBVtxFace (e h : ℤ) (harnessVtx printVtx : Set (ℤ × ℤ)) : Prop :=
  jbShear e h '' harnessVtx = printVtx

/-! ### NODE F.23 [lemma] — WM-FENCE, the FIXED-DATA character-triviality criterion.
Neither display contains an existential over the fixed inputs: the criterion supplies NO freedom
or existence theorem. `PERIM-μ` — the LAW that its condition holds on all claimed order-≥2 faces
— is HYP.86, OUT of cone (§3 row 9); the two must never be conflated. -/

axiom wmFence_absolute {K : Type*} [Field K] [Finite K] (z : Kˣ) (A : ℤ) :
    (∀ i : ℤ, z ^ (i * A) = 1) ↔ ((orderOf z : ℤ) ∣ A)

axiom wmFence_slotGrid {K : Type*} [Field K] [Finite K] (z : Kˣ) (e A : ℤ) :
    (∀ i : ℤ, z ^ (e * i * A) = 1) ↔ ((orderOf z : ℤ) ∣ e * A)

/-! ### NODE F.24 [def] — `WELD-M-PKG`, the anchored five-face transport package (chapter D's C7
anchor). Existence-only; **NO cross-face coherence field** (the F-1 lesson, honoured
structurally). M4's W2-C3 instance is **BLOCKED: GC-13 (`EFF.GRTW2.29 [supplied-by: chapter C]`)**
and is NOT stubbed. -/

/-- WELD-M-PKG (`EFF.WELDMASTER.22`): the five-face transport package as a record of five
Props. Existence-only; NO cross-face coherence field. -/
structure WeldMPkg (M0 M1 M2 M3 M4 : Prop) : Prop where
  m0 : M0
  m1 : M1
  m2 : M2
  m3 : M3
  m4 : M4

/-! ### NODE F.25 [lemma] — the gauge-torsor lemma (the `H¹ = 0` uniqueness claim killed,
structurally). -/

/-- The 1-coboundary of a gauge (`EFF.WELDMASTER.23`). -/
def gaugeBdry {E : ℕ} [NeZero E] {K : Type*} [Field K] (F : ZMod E → Kˣ) :
    ZMod E → ZMod E → Kˣ := fun a b => F a * F b * (F (a + b))⁻¹

axiom gaugeBdry_eq_iff {E : ℕ} [NeZero E] {K : Type*} [Field K]
    (F G : ZMod E → Kˣ) :
    gaugeBdry F = gaugeBdry G ↔
      ∀ a b, (F a * (G a)⁻¹) * (F b * (G b)⁻¹) = F (a + b) * (G (a + b))⁻¹

/-! ### NODE F.26 [interface-carrier] — the `(DMULT-w)` tier at its HEAD provenance.
FRAGILE: `∃ ω` sits BETWEEN the line pair and `(f, g)` — ω depends only on the lines. A
type-checked commute of those quantifiers would be a defect; the order below is the signed one.
Gate-(b) cite flag: `[cite: FGMN Thm 4.2 (rank-one freeness), via EFF.GRTJC.43's (IN-3)
package]`, owner sign-off at chapter I's cite block. `(DMULT-s)` (ω ≡ 1) is OUT of cone. -/

/-- The (DMULT-w) tier (`EFF.GRTJC.69`): residual multiplicativity up to a line-only unit,
with the {0,1} wrap exponent. Carried; discharge rides the gate-(b) FGMN cite. -/
def DmultW {K : Type*} [Field K] {Λ : Type*} [Add Λ]
    (R : Λ → K[X] → K[X]) (y : K[X]) (δ : Λ → Λ → ℕ) : Prop :=
  ∀ lam mu : Λ, ∃ ω : Kˣ, ∀ f g : K[X],
    R (lam + mu) (f * g) = (ω : K) • (y ^ δ lam mu * R lam f * R mu g)

/-! ## §9 — THE CHAPTER-I HANDOFF PACKAGE (F.27–F.28) -/

/-! ### NODE F.27 [def] — `WeldSupply`, the proved-supply record. Defect **F-D1**: the signed
field name `hΣ` is not a legal identifier; `hSigma` here. -/

/-- The weld layer's proved supply, as one record (chapter-I/D consumption surface). -/
structure WeldSupply (E : ℕ) [NeZero E] (K : Type*) [Field K] (ι α : Type*) where
  cc : CarryCocycle E K
  J : LedgerJunction K ι α
  hSigma : SigmaLedgerLaw J

/-! ### NODE F.28 [def] — `WeldObligations`, the carried-hypothesis block handed to chapter I:
one field per surviving Display-A weld obligation, at exactly ledger strength. Annotations
carried alongside (NOT Prop fields): F.26's gate-(b) FGMN cite flag; the
`AllOInterfaces[W/J, J-D0]` generality conjuncts HYP.126/HYP.129, supplied STRUCTURALLY by F's
statements being quantified over every finite `K` — the ledger rows stay chapter I's. -/

/-- The weld layer's carried obligations (chapter I's Display-A weld fields), at ledger
strength. -/
structure WeldObligations {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ]
    {Site CSite FSite : Type*}
    (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K) : Prop where
  jd0box2 : ∀ s, JD0Box2 (vsite s)
  genhnBox2 : ∀ s, GenhnBox2 (csite s)
  w1 : W1Transport Rh RG

end LeanspecF
