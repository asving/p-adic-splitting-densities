/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H104
import Uniformity.ChapH.H97r4

/-!
# Uniformity.ChapI.IFCG2 — `[A0G3 2026-08-28]` the uniform-`a0` campaign's node `A0G-PD`

**Uniform-`a0` campaign, NODE `A0G-PD`** (`docs/in-progress/A0_GENERAL_2026-08-28.md` §5, the
recursion architecture, and the §6 rows `A0G-PD0`/`A0G-PD1`): the **n-ary coprime residual
product and factorization-type convolution**, plus the **generic peel-decided injection** that
recovers the landed cubic `DBL` (linear × quadratic) peel use.

## The dedup finding — read this before the proofs

The blueprint's §6 row lists `typeOf_of_residual_coprime` (`Density/TypeOfAlgebra.lean:131`) and
`C133mh3.dvResPoly_mul_gen` (`ChapC/C133mh3.lean:1843`) as the landed inputs for `A0G-PD0`.
Both were read (per the unit's `(rg it)` instruction). **Neither is the right tool.**
`typeOf_of_residual_coprime` only handles an ALREADY-KNOWN exact factorization (no level-`N`
class, no "decided" quantifier); `dvResPoly_mul_gen` is Theorem M clause 3 of the *dv-graded
MacLane tower engine* (`KeyFrame`, `dvResPoly`, `dvSideMin` — the machinery `A0G-HE`/`A0G-NP`/
`A0G-GC` need downstream), not the `Coeff`/`DecidedAt` combinatorics this row is actually
convolving.

**What IS the right tool, and was already landed by an EARLIER phase of this same blueprint**
(`blueprint/CHAP-H_general_induction.md` §17.1, chapter H's `N-1` "level-0 class transport",
unit T-1/OM-2, 2026-08-16 — the *same* `leanfinal/` target, the *same* `Uniformity.Density`
`Coeff`/`proj`/`DecidedAt`/`typeOf` objects `DecidedSliceAt` is built from):

* `Uniformity.Density.Induction.decidedAt_mulClass` (H.103, `ChapH/H103.lean:97`) is **already**
  the fully degree-generic two-block decided/type injection: for ANY coprime monic residue
  factors `g₁, g₂` of degrees `n₁, n₂`, `DecidedAt σ₁ c₁` and `DecidedAt σ₂ c₂` at a shared
  stratum give `DecidedAt ⟨σ₁.data + σ₂.data⟩ (mulClass c₁ c₂)` at degree `n₁ + n₂` — no `Fin 3`,
  no fixed degree anywhere in the statement.
* `Uniformity.Density.Induction.mulClass_mem_levelZeroStratum` (H.102) is its stratum-closure
  half, and `mem_levelZeroStratum_iff` (H.100) turns one exhibited lift into full stratum
  membership at `1 ≤ N` — exactly the bookkeeping an n-ary fold needs at every step.

Per the standing dedup discipline (the `[A0G2]` note on `IFCG1`: "check H123a's bank before
re-deriving anything"), **this file does NOT re-derive the binary decided/type injection.** It:

1. bridges H.103's abstract `levelZeroStratum`/`mulClass` presentation to the concrete
   "a root with unit derivative peels off a linear factor" presentation `H97r4` uses (§1–§2:
   `A0G-PD0`'s actual new content is this bridge, stated at ARBITRARY degree, not just cubic);
2. proves the **recovery corollary** the GATE demands: H.97r4's cubic-specific
   `decidedAt_of_peel_decided` is a byte-identical-statement consequence of the generic bridge
   at `n = 2` (§3);
3. builds the genuinely new **n-ary fold** over a list of pairwise-coprime blocks (§4–§5,
   `A0G-PD1`), and proves it is **order-independent**: the resulting degree and the resulting
   factorization-type convolution do not depend on which order the blocks are combined in (§6).

## GATE

* §3's `decidedAt_of_peel_decided_recovered` has the EXACT statement of
  `Uniformity.Density.decidedAt_of_peel_decided` (`H97r4.lean:107`), reproved through the
  generic two-block injection — the "recovers the landed cubic `DBL` use" clause.
  Degrees add exactly: the generic theorem's conclusion lives at `Fin (1 + n)`, which is `Fin 3`
  on the nose at `n = 2` — no cast, no `Fin`-reindexing lemma needed anywhere in the recovery.
* §6's `degSum_perm`/`typeSum_perm` show the n-ary fold's degree and type are `List.Perm`-
  invariant — the "order-independent" clause of the `A0G-PD1` row; `gProd_perm` extends this to
  the residue-product the stratum membership is stated against, so every ingredient of
  `decidedAt_combinedClass` (hypothesis, degree, type, and stratum witness) is order-independent.

## Downstream consumption (§5 of the blueprint's recursion architecture)

`PDBlock` is the unit this file exports for the critical-path chain `PD ───→ FP → CL → AS → DS
→ ALL` (the blueprint's §6 diagram): a `ClusterLaw`/`decidedDensity` recurrence assembles its
level-`N` genre laws by convolving exactly this kind of coprime residual block list, and needs
three things from `A0G-PD` that this file supplies unconditionally at every degree: (i) that the
fold's DEGREE only depends on the multiset of block sizes (`degSum_perm`), so a genre's weight
computation may reassociate freely; (ii) that the fold's TYPE is the honest multiset convolution
`typeSum` — not merely "some type", so `A0G-AS`'s later value-law bookkeeping can read off
`(ℕ × ℕ)` pairs directly; (iii) that decidedness at level `N` transports along the fold with NO
loss (`decidedAt_combinedClass`), so the `A0G-CH` child-decrease step may recurse on strictly
smaller residual clusters without re-deriving Hensel's completeness argument at every level.
`A0G-HE`/`A0G-NP` will supply the ACTUAL `PDBlock`s (their `g`, `c`, `strat`, `dec` fields) from
the dv-graded engine's certified pure blocks; nothing in this file constructs one from scratch
beyond §2's linear-peel leaf.

## Status

Sorry-free. AxCheck footer expects Lean core (`propext`, `Classical.choice`, `Quot.sound`) only:
no new axiom, and the C.33 dissection cite is NOT inherited (this file never touches
`C33Cite`/`fgmn_dvDissection_factor_eq` or anything downstream of them).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.IFCG2

open IsLocalRing Polynomial Uniformity.Density.Induction

/-! ## §1 (`A0G-PD0`, part a) — the coprimality bridge

The concrete "unit-derivative root" presentation of a peel (`H97r4`'s hypothesis) and the
abstract "coprime residue factors" presentation `decidedAt_mulClass` needs are the same fact
read two ways. This section is the bridge, at an ARBITRARY field/degree — nothing here is
`Fin 3`-specific. -/

section Bridge

/-- **A linear factor is coprime to any polynomial it doesn't vanish at.** The field-theoretic
half of the bridge: `X - C c` is irreducible of degree `1`, so `EuclideanDomain.dvd_or_coprime`
gives divisibility or coprimality, and divisibility would force `g.eval c = 0` via
`dvd_iff_isRoot`. -/
theorem isCoprime_X_sub_C_of_eval_ne_zero {K : Type*} [Field K] {c : K} {g : Polynomial K}
    (hg : g.eval c ≠ 0) : IsCoprime (X - C c) g := by
  have hirr : Irreducible (X - C c) := irreducible_of_degree_eq_one (degree_X_sub_C c)
  rcases EuclideanDomain.dvd_or_coprime (X - C c) g hirr with hdvd | hcop
  · exact absurd (Polynomial.dvd_iff_isRoot.1 hdvd) hg
  · exact hcop

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Peeling a linear factor off, at ARBITRARY degree, by existence.** If `a : Fin (1+n) → O`
has a root `r`, the quotient `monicPoly a /ₘ (X - C r)` is monic of degree `n` (division by a
monic linear polynomial with vanishing remainder, since `r` is a root) — so `exists_monicPoly_eq`
reads it as a coefficient vector `b`. Generalizes `H97r1.cubic_peel`'s CLOSED FORM (`peel`) to an
EXISTENCE statement at every degree; the closed form is recovered at `n = 2` in §3 via
`cubic_peel` itself, not by unfolding this proof. -/
theorem exists_peel_of_root {n : ℕ} (a : Fin (1 + n) → O) (r : O)
    (hr : (monicPoly a).eval r = 0) :
    ∃ b : Fin n → O, monicPoly a = (X - C r) * monicPoly b := by
  set q := monicPoly a /ₘ (X - C r) with hq
  have hdeg1 : (monicPoly a).natDegree = 1 + n := monicPoly_natDegree a
  have hqdeg : q.natDegree = n := by
    rw [hq, natDegree_divByMonic _ (monic_X_sub_C r), hdeg1, natDegree_X_sub_C]
    omega
  have hdegle : (X - C r).degree ≤ (monicPoly a).degree := by
    rw [degree_X_sub_C, monicPoly_degree a]
    exact_mod_cast Nat.le_add_right 1 n
  have hqmonic : q.Monic := by
    show q.leadingCoeff = 1
    rw [hq, leadingCoeff_divByMonic_of_monic (monic_X_sub_C r) hdegle]
    exact monicPoly_monic a
  have hmod : monicPoly a %ₘ (X - C r) = 0 := by
    rw [modByMonic_X_sub_C_eq_C_eval, hr, map_zero]
  have heq : (X - C r) * q = monicPoly a := by
    have hkey := X_sub_C_mul_divByMonic_eq_sub_modByMonic (monicPoly a) r
    rw [hmod, sub_zero] at hkey
    rwa [hq]
  obtain ⟨b, hb⟩ := exists_monicPoly_eq hqmonic hqdeg
  exact ⟨b, by rw [← heq, hb]⟩

/-- **The derivative at the root is the cofactor's value there.** The product rule for
`monicPoly a = (X - C r) * monicPoly b`: `(X - C r)' = 1` kills the first term's `(X - C r)`
factor at `x = r`, leaving exactly `(monicPoly b).eval r`. This is the degree-generic form of
`H97r1.cubic_deriv_eval`'s role inside `cubic_structure`/`decidedAt_of_peel_decided`. -/
theorem eval_derivative_eq_eval_peel {n : ℕ} {a : Fin (1 + n) → O} {r : O} {b : Fin n → O}
    (hb : monicPoly a = (X - C r) * monicPoly b) :
    (monicPoly a).derivative.eval r = (monicPoly b).eval r := by
  rw [hb, derivative_mul, derivative_X_sub_C]
  simp

end Bridge

/-! ## §2 (`A0G-PD0`, part b) — the generic peel-decided injection

The main new theorem: peeling ANY unit-derivative root off a degree-`(1+n)` class, with the
cofactor's class decided at level `N`, decides the whole class — at every `n`, not just `n = 2`.
The proof does no Hensel work of its own: it packages §1's bridge and hands the actual work to
the landed `decidedAt_mulClass` (H.103). -/

section PeelDecided

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **`A0G-PD0` — the generic two-block peel-decided injection.** If `a` has a root `r` with a
unit derivative and the cofactor `b`'s level-`N` class is decided at `σ'`, then `a`'s own
level-`N` class is decided, at the type `(1,1) ::ₘ σ'.data` — the linear leaf prepended to the
cofactor's type. No degree bound: `n` is arbitrary. -/
theorem decidedAt_of_linearPeel_decided {n N : ℕ} (hN : 1 ≤ N) {a : Fin (1 + n) → O} {r : O}
    (hr : (monicPoly a).eval r = 0) (hu : IsUnit ((monicPoly a).derivative.eval r))
    {b : Fin n → O} (hb : monicPoly a = (X - C r) * monicPoly b) {σ' : FactorizationType}
    (hdec : DecidedAt O n σ' N (proj O n N b)) :
    DecidedAt O (1 + n) ⟨(1, 1) ::ₘ σ'.data⟩ N (proj O (1 + n) N a) := by
  classical
  -- the two residue factors: the linear leaf `X - C rbar` and the cofactor's reduction
  set rbar : ResidueField O := residue O r with hrbar
  set g₂ : Polynomial (ResidueField O) := (monicPoly b).map (residue O) with hg₂
  have hg₁monic : (X - C rbar).Monic := monic_X_sub_C rbar
  have hg₁deg : (X - C rbar).natDegree = 1 := natDegree_X_sub_C rbar
  have hg₂monic : g₂.Monic := (monicPoly_monic b).map _
  have hg₂deg : g₂.natDegree = n := by rw [hg₂, (monicPoly_monic b).natDegree_map]; exact monicPoly_natDegree b
  -- coprimality: the cofactor's eval at `r` is the unit derivative (§1's bridge)
  have hbeval : IsUnit ((monicPoly b).eval r) := eval_derivative_eq_eval_peel hb ▸ hu
  have hg₂eval : g₂.eval rbar ≠ 0 := by
    rw [hg₂, hrbar, Polynomial.eval_map_apply]
    intro h0
    exact (IsLocalRing.notMem_maximalIdeal.2 hbeval) ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hcop : IsCoprime (X - C rbar) g₂ := isCoprime_X_sub_C_of_eval_ne_zero hg₂eval
  -- the linear leaf's level-`N` class: `a₁ 0 := -r`
  set a₁ : Fin 1 → O := fun _ => -r with ha₁
  have hg₁eq : monicPoly a₁ = X - C r := by
    ext i
    rcases lt_trichotomy i 1 with hi | hi | hi
    · interval_cases i
      · rw [monicPoly_coeff_lt a₁ (by omega : (0:ℕ) < 1)]
        simp [ha₁]
    · subst hi
      simp [monicPoly, ha₁]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_sub_C]; omega)]
  have hc₁strat : proj O 1 N a₁ ∈ levelZeroStratum O 1 N (X - C rbar) :=
    (mem_levelZeroStratum_iff hN _ _).2 ⟨a₁, rfl, by rw [hg₁eq, Polynomial.map_sub, map_X, map_C]⟩
  have hc₂strat : proj O n N b ∈ levelZeroStratum O n N g₂ :=
    (mem_levelZeroStratum_iff hN _ _).2 ⟨b, rfl, rfl⟩
  have hσ₁ : DecidedAt O 1 ⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ N (proj O 1 N a₁) := by
    intro a' _
    exact typeOf_of_natDegree_one (monicPoly_monic a') (monicPoly_natDegree a')
  have hmain := decidedAt_mulClass hN hg₁monic hg₂monic hg₁deg hg₂deg hcop hc₁strat hc₂strat
    hσ₁ hdec
  -- `mulClass (proj a₁) (proj b) = proj a`, and the type matches `(1,1) ::ₘ σ'.data`
  have hprodeq : monicPoly a₁ * monicPoly b = monicPoly a := by rw [hg₁eq, ← hb]
  have hfe : (fun i : Fin (1 + n) => (monicPoly a).coeff (i : ℕ)) = a :=
    funext fun i => monicPoly_coeff_lt a i.isLt
  have hclass : mulClass (proj O 1 N a₁) (proj O n N b) = proj O (1 + n) N a := by
    rw [← mulClass_proj a₁ b, hprodeq, hfe]
  have htype : (⟨({(1, 1)} : Multiset (ℕ × ℕ))⟩ : FactorizationType).data + σ'.data
      = (1, 1) ::ₘ σ'.data := by
    simp
  rw [hclass, htype] at hmain
  exact hmain

end PeelDecided

/-! ## §3 — the recovery corollary (THE GATE)

`H.97r4`'s cubic-specific `decidedAt_of_peel_decided` has an IDENTICAL statement to a `n = 2`
instance of §2's generic theorem, fed through `H97r1`'s explicit closed-form `peel`/`cubic_peel`
instead of §1's existence lemma. `1 + 2` reduces to `3` on the nose, so no `Fin`-cast or
reindexing appears anywhere below — this is the "degrees add exactly" half of the gate. -/

section Recovery

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **THE RECOVERY LEMMA (GATE).** Byte-identical statement to
`Uniformity.Density.decidedAt_of_peel_decided` (`H97r4.lean:107`), reproved through the generic
two-block injection `decidedAt_of_linearPeel_decided` at `n = 2`, with `H97r1.cubic_peel`
supplying the peel equation `monicPoly a = (X - C r) * monicPoly (peel a r)`. The hypothesis
`hπ : Irreducible π` is carried (unused) only to match the recovered statement's binder list
byte-for-byte; `decidedAt_mulClass`'s Hensel route needs no distinguished uniformizer. -/
theorem decidedAt_of_peel_decided_recovered {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {N : ℕ}
    (hN : 1 ≤ N) {r : O} (hr : (monicPoly a).eval r = 0)
    (hu : IsUnit ((monicPoly a).derivative.eval r)) {σ' : FactorizationType}
    (hdec : DecidedAt O 2 σ' N (proj O 2 N (peel a r))) :
    DecidedAt O 3 ⟨(1, 1) ::ₘ σ'.data⟩ N (proj O 3 N a) :=
  decidedAt_of_linearPeel_decided (n := 2) hN hr hu (cubic_peel a r hr) hdec

/-- The recovery is not vacuous: the two theorems' conclusion TYPES coincide on the nose,
`Fin (1 + 2) = Fin 3`, so this typechecks with no `cast`, `HEq`, or degree-transport lemma. -/
example : (1 + 2 : ℕ) = 3 := rfl

end Recovery

/-! ## §4 (`A0G-PD1`, part a) — the n-ary block system

A list of pairwise-coprime blocks: each block bundles a monic residue polynomial of a known
degree together with a level-`N` class known to lie in its stratum and to be decided at a known
type. The fold (`combinedClass`) and its accompanying degree/type sums are defined by PLAIN
structural recursion on the list — not via `List.sum`/`List.prod` — so that the dependent return
type `Coeff O (degSum L) N` unifies with the recursive step BY CONSTRUCTION, with no cast. -/

section Blocks

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ)

/-- **A coprime residual block at level `N`.** -/
structure PDBlock where
  n : ℕ
  g : Polynomial (ResidueField O)
  gMonic : g.Monic
  gDeg : g.natDegree = n
  c : Coeff O n N
  σ : FactorizationType
  strat : c ∈ levelZeroStratum O n N g
  dec : DecidedAt O n σ N c

variable {O N}

/-- The total degree of a block list, by plain recursion. -/
def degSum : List (PDBlock O N) → ℕ
  | [] => 0
  | b :: L => b.n + degSum L

/-- The convolved factorization type of a block list, by plain recursion. -/
def typeSum : List (PDBlock O N) → FactorizationType
  | [] => ⟨0⟩
  | b :: L => ⟨b.σ.data + (typeSum L).data⟩

/-- The product of the blocks' residue polynomials, by plain recursion. -/
def gProd : List (PDBlock O N) → Polynomial (ResidueField O)
  | [] => 1
  | b :: L => b.g * gProd L

/-- **The n-ary class fold.** `mulClass`-fold of the blocks' classes, in list order. Its type
`Coeff O (degSum L) N` matches the recursive step definitionally: `degSum (b :: L) = b.n +
degSum L` by `degSum`'s own equation, and `mulClass : Coeff O n₁ N → Coeff O n₂ N → Coeff O
(n₁ + n₂) N`. -/
def combinedClass : (L : List (PDBlock O N)) → Coeff O (degSum L) N
  | [] => fun i => i.elim0
  | b :: L => mulClass b.c (combinedClass L)

/-! ### Equation lemmas

`degSum`, `typeSum`, `gProd`, `combinedClass` are all defined by direct pattern-matching
recursion, so their defining equations are `rfl`; they are still recorded as named `@[simp]`
lemmas (rather than left as bare unfoldings) because every downstream `A0G-CL`/`A0G-AS` consumer
should `rw`/`simp` through this public API instead of reaching for the private recursive
definitions. -/

@[simp] theorem degSum_nil : degSum ([] : List (PDBlock O N)) = 0 := rfl

@[simp] theorem degSum_cons (b : PDBlock O N) (L : List (PDBlock O N)) :
    degSum (b :: L) = b.n + degSum L := rfl

@[simp] theorem typeSum_nil : typeSum ([] : List (PDBlock O N)) = ⟨0⟩ := rfl

@[simp] theorem typeSum_cons (b : PDBlock O N) (L : List (PDBlock O N)) :
    typeSum (b :: L) = ⟨b.σ.data + (typeSum L).data⟩ := rfl

@[simp] theorem gProd_nil : gProd ([] : List (PDBlock O N)) = 1 := rfl

@[simp] theorem gProd_cons (b : PDBlock O N) (L : List (PDBlock O N)) :
    gProd (b :: L) = b.g * gProd L := rfl

theorem combinedClass_nil : combinedClass ([] : List (PDBlock O N)) = fun i => i.elim0 := rfl

theorem combinedClass_cons (b : PDBlock O N) (L : List (PDBlock O N)) :
    combinedClass (b :: L) = mulClass b.c (combinedClass L) := rfl

/-- `gProd` is monic — a product of monics. -/
theorem gProd_monic : ∀ L : List (PDBlock O N), (gProd L).Monic
  | [] => monic_one
  | b :: L => (b.gMonic).mul (gProd_monic L)

/-- `gProd`'s degree is `degSum` — the sum of monic degrees is the degree of the product. -/
theorem gProd_natDegree : ∀ L : List (PDBlock O N), (gProd L).natDegree = degSum L
  | [] => natDegree_one
  | b :: L => by
      rw [gProd, degSum, (b.gMonic).natDegree_mul (gProd_monic L), gProd_natDegree L, b.gDeg]

/-- A residue polynomial coprime to every block in a list is coprime to their product. -/
theorem isCoprime_gProd_of_forall {g : Polynomial (ResidueField O)} :
    ∀ (L : List (PDBlock O N)), (∀ b ∈ L, IsCoprime g b.g) → IsCoprime g (gProd L)
  | [], _ => isCoprime_one_right
  | b :: L, h => by
      rw [gProd]
      exact (h b (List.mem_cons_self)).mul_right
        (isCoprime_gProd_of_forall L (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- **Convenience: the pairwise-coprimality hypothesis for a 2-element list unfolds to a single
`IsCoprime`.** Spares every 2-block consumer (e.g. `A0G-CH`'s child-decrease step, or the
recovery-style sanity check of a length-2 fold against `decidedAt_mulClass` directly) the
`List.pairwise_cons`/`List.pairwise_singleton` bookkeeping `combinedClass_mem_and_decided`'s
proof performs internally at every step. -/
theorem pairwise_coprime_pair {b b' : PDBlock O N} (h : IsCoprime b.g b'.g) :
    [b, b'].Pairwise (fun x y => IsCoprime x.g y.g) := by
  simp [List.pairwise_cons, h]

/-- The empty list's combined class is the (unique) degree-`0` class, and it lies in the
degree-`0` stratum of `1`: every `a : Fin 0 → O` has `monicPoly a = 1`. -/
theorem combinedClass_nil_strat (hN : 1 ≤ N) :
    (combinedClass ([] : List (PDBlock O N))) ∈ levelZeroStratum O 0 N (1 : Polynomial (ResidueField O)) := by
  refine (mem_levelZeroStratum_iff hN _ _).2 ⟨fun i => i.elim0, funext fun i => i.elim0, ?_⟩
  have : monicPoly (fun i : Fin 0 => (i.elim0 : O)) = (1 : Polynomial O) := by simp [monicPoly]
  rw [this, Polynomial.map_one]

/-- The empty list's combined class is decided, at the empty type `⟨0⟩`: `1`'s type is `⟨0⟩`. -/
theorem combinedClass_nil_decided :
    DecidedAt O 0 (⟨0⟩ : FactorizationType) N (combinedClass ([] : List (PDBlock O N))) := by
  intro a _
  have ha1 : monicPoly a = (1 : Polynomial O) := by simp [monicPoly]
  have hF : IsMonicFactorization (1 : Polynomial O) (0 : Multiset (Polynomial O)) :=
    ⟨by simp, by simp⟩
  rw [ha1]
  apply FactorizationType.ext
  rw [typeOf_data, monicFactors_eq hF]
  simp

/-- **The empty block list is a two-sided unit for `mulClass`.** Folding in the trivial
degree-`0` class changes nothing (up to the defeq `n + 0 = n`, needed by NO cast: `Nat.add`
recurses on its right argument, so `n + 0` reduces to `n` on the nose). This is the gluing fact
an assembler over `A0G-CL`-style cluster laws needs when padding a shorter block list to a
common length, or when peeling the LAST block off a fold instead of the first. -/
theorem mulClass_unit_right {n : ℕ} (c : Coeff O n N) :
    mulClass c (combinedClass ([] : List (PDBlock O N))) = c := by
  funext i
  rw [mulClass_apply]
  show (monicPoly c * monicPoly (combinedClass ([] : List (PDBlock O N)))).coeff (i : ℕ) = c i
  have h1 : monicPoly (combinedClass ([] : List (PDBlock O N))) = (1 : Polynomial (Res O N)) := by
    simp [monicPoly, combinedClass_nil]
  rw [h1, mul_one, coeff_monicPoly_class]

end Blocks

/-! ## §5 (`A0G-PD1`, part b) — the n-ary induction: `A0G-PD0` propagated along the list -/

section Fold

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] {N : ℕ}

/-- **`A0G-PD1`, the main induction.** For a pairwise-coprime block list, the combined class both
lies in the combined stratum AND is decided at the convolved type — proved together because
`decidedAt_mulClass` needs the tail's stratum membership as a hypothesis, not merely its
decidedness. -/
theorem combinedClass_mem_and_decided (hN : 1 ≤ N) :
    ∀ L : List (PDBlock O N), L.Pairwise (fun b b' => IsCoprime b.g b'.g) →
      combinedClass L ∈ levelZeroStratum O (degSum L) N (gProd L) ∧
      DecidedAt O (degSum L) (typeSum L) N (combinedClass L)
  | [], _ => ⟨combinedClass_nil_strat hN, combinedClass_nil_decided⟩
  | b :: L, hpw => by
      obtain ⟨hstratL, hdecL⟩ := combinedClass_mem_and_decided hN L hpw.of_cons
      have hcopbL : IsCoprime b.g (gProd L) :=
        isCoprime_gProd_of_forall L (fun x hx => List.rel_of_pairwise_cons hpw hx)
      refine ⟨mulClass_mem_levelZeroStratum hN b.strat hstratL, ?_⟩
      exact decidedAt_mulClass hN b.gMonic (gProd_monic L) b.gDeg (gProd_natDegree L) hcopbL
        b.strat hstratL b.dec hdecL

/-- **`A0G-PD1`, the exported statement.** The n-ary coprime residual product decides its
combined class at the multiset-convolved type, at every list length. -/
theorem decidedAt_combinedClass (hN : 1 ≤ N) (L : List (PDBlock O N))
    (hpw : L.Pairwise (fun b b' => IsCoprime b.g b'.g)) :
    DecidedAt O (degSum L) (typeSum L) N (combinedClass L) :=
  (combinedClass_mem_and_decided hN L hpw).2

/-- **The `k = 1` sanity instance.** A single block trivially satisfies pairwise coprimality
(`List.pairwise_singleton`), so the fold is well-founded at the smallest nontrivial length: the
n-ary theorem specializes to exactly the block's own `DecidedAt` fact (`degSum [b] = b.n`,
`typeSum [b] = b.σ` up to the empty-tail `Multiset.add_zero`). -/
theorem decidedAt_combinedClass_singleton (hN : 1 ≤ N) (b : PDBlock O N) :
    DecidedAt O (degSum [b]) (typeSum [b]) N (combinedClass [b]) :=
  decidedAt_combinedClass hN [b] (List.pairwise_singleton _ _)

end Fold

/-! ## §6 — order-independence

The `A0G-PD1` row's gate: reassociating/reordering the blocks changes neither the resulting
degree nor the resulting type. Both `degSum` and `typeSum` are shown equal to a `List.map`-then-
`List.sum`/`Multiset.sum` reading (a separate PROPOSITIONAL equation, not needed for
`combinedClass`'s definitional typing above), and `List.Perm.sum_eq` transports along any
permutation. The pairwise-coprimality HYPOTHESIS transports too, by the symmetric-relation
`Pairwise` transport `List.Perm.pairwise_iff` (`IsCoprime.symm`). -/

section OrderIndependence

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}

private theorem degSum_eq_sum (L : List (PDBlock O N)) :
    degSum L = (L.map PDBlock.n).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [degSum, ih]

private theorem typeSum_eq_sum (L : List (PDBlock O N)) :
    (typeSum L).data = (L.map (fun b => b.σ.data)).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [typeSum, ih]

/-- **Order-independence of the resulting degree.** -/
theorem degSum_perm {L L' : List (PDBlock O N)} (h : L.Perm L') : degSum L = degSum L' := by
  rw [degSum_eq_sum, degSum_eq_sum]
  exact (h.map PDBlock.n).sum_eq

/-- **Order-independence of the resulting factorization type.** -/
theorem typeSum_perm {L L' : List (PDBlock O N)} (h : L.Perm L') : typeSum L = typeSum L' := by
  apply FactorizationType.ext
  rw [typeSum_eq_sum, typeSum_eq_sum]
  exact (h.map (fun b => b.σ.data)).sum_eq

private theorem gProd_eq_prod (L : List (PDBlock O N)) : gProd L = (L.map PDBlock.g).prod := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [gProd, ih]

/-- **Order-independence of the underlying residue-polynomial product too.** Not needed for the
degree/type gate above, but completes the picture: the THIRD ingredient a reordered fold could
in principle depend on — which residue polynomial the stratum membership `combinedClass L ∈
levelZeroStratum O (degSum L) N (gProd L)` is stated against — is equally order-independent,
since `Polynomial (ResidueField O)` multiplication is commutative. -/
theorem gProd_perm {L L' : List (PDBlock O N)} (h : L.Perm L') : gProd L = gProd L' := by
  rw [gProd_eq_prod, gProd_eq_prod]
  exact (h.map PDBlock.g).prod_eq

/-- **Order-independence of the pairwise-coprimality hypothesis' underlying data.** Together
with `pairwiseCoprime_perm` below, this closes the loop: every ingredient that feeds
`decidedAt_combinedClass` — the hypothesis, the degree, the type, and the residue-product the
stratum is read against — transports along any reordering of the block list. -/
example {L L' : List (PDBlock O N)} (h : L.Perm L') :
    degSum L = degSum L' ∧ typeSum L = typeSum L' ∧ gProd L = gProd L' :=
  ⟨degSum_perm h, typeSum_perm h, gProd_perm h⟩

/-- **Order-independence of the pairwise-coprimality hypothesis itself.** `IsCoprime` is
symmetric, so `Pairwise` for it transports both ways along a permutation. -/
theorem pairwiseCoprime_perm {L L' : List (PDBlock O N)} (h : L.Perm L')
    (hpw : L.Pairwise (fun b b' => IsCoprime b.g b'.g)) :
    L'.Pairwise (fun b b' => IsCoprime b.g b'.g) :=
  (List.Perm.pairwise_iff (fun {x y} hxy => hxy.symm) h).mp hpw

end OrderIndependence

end Uniformity.Density.IFCG2

/-! ## AxCheck footer — expect Lean core (`propext`, `Classical.choice`, `Quot.sound`) only -/

section AxCheck

#print axioms Uniformity.Density.IFCG2.isCoprime_X_sub_C_of_eval_ne_zero
#print axioms Uniformity.Density.IFCG2.exists_peel_of_root
#print axioms Uniformity.Density.IFCG2.eval_derivative_eq_eval_peel
#print axioms Uniformity.Density.IFCG2.decidedAt_of_linearPeel_decided
#print axioms Uniformity.Density.IFCG2.decidedAt_of_peel_decided_recovered
#print axioms Uniformity.Density.IFCG2.degSum
#print axioms Uniformity.Density.IFCG2.typeSum
#print axioms Uniformity.Density.IFCG2.gProd
#print axioms Uniformity.Density.IFCG2.combinedClass
#print axioms Uniformity.Density.IFCG2.degSum_nil
#print axioms Uniformity.Density.IFCG2.degSum_cons
#print axioms Uniformity.Density.IFCG2.typeSum_nil
#print axioms Uniformity.Density.IFCG2.typeSum_cons
#print axioms Uniformity.Density.IFCG2.gProd_nil
#print axioms Uniformity.Density.IFCG2.gProd_cons
#print axioms Uniformity.Density.IFCG2.combinedClass_nil
#print axioms Uniformity.Density.IFCG2.combinedClass_cons
#print axioms Uniformity.Density.IFCG2.gProd_monic
#print axioms Uniformity.Density.IFCG2.gProd_natDegree
#print axioms Uniformity.Density.IFCG2.isCoprime_gProd_of_forall
#print axioms Uniformity.Density.IFCG2.pairwise_coprime_pair
#print axioms Uniformity.Density.IFCG2.combinedClass_nil_strat
#print axioms Uniformity.Density.IFCG2.combinedClass_nil_decided
#print axioms Uniformity.Density.IFCG2.mulClass_unit_right
#print axioms Uniformity.Density.IFCG2.combinedClass_mem_and_decided
#print axioms Uniformity.Density.IFCG2.decidedAt_combinedClass
#print axioms Uniformity.Density.IFCG2.decidedAt_combinedClass_singleton
#print axioms Uniformity.Density.IFCG2.degSum_perm
#print axioms Uniformity.Density.IFCG2.typeSum_perm
#print axioms Uniformity.Density.IFCG2.gProd_perm
#print axioms Uniformity.Density.IFCG2.pairwiseCoprime_perm

end AxCheck
