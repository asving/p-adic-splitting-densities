/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C13
import Uniformity.ChapC.C14
import Uniformity.ChapC.C46

/-!
# Uniformity.ChapC.C47 — HETOW-2 at the (LIFT)-form: `composedKey T` as a test key

**Chapter C, NODE C.47** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §6, the composed
key and the tower bridges; signed A-C.1, repaired upstream at A-C.5 item 2, landed as FU-3 of the
A-C.5 item-2 follow-up chain). **ENV-C3.**

## ✔ LANDED WHOLE (2026-08-16) — `composedKey_isTestKey` at its byte-unchanged signature

`composedKey_isTestKey` is the A-C.1 signature, byte-unchanged through A-C.5 and through both
repairs, with **no added hypothesis**: the composed key `Φ₂` of C.43 IS a test key for the level
datum `T.levelDatum hπ` in C.13's sense, given only `hπ : Irreducible π`, `hh : 1 ≤ F.h` and
`[Finite (ResidueField O)]`. Sorry-free, Lean core only.

Getting here took two defect/repair rounds, both recorded below because both are load-bearing for
anyone re-reading §6.

## Defect 1 (A-C.5): the read mismatch — REPAIRED UPSTREAM

The first defect — the read mismatch between C.13 clause 5's untwisted `slotRes` and C.43's ϖ-read
composed key — was machine-refuted (`C47_REFUTATION.lean.txt`), adjudicated by A-C.5 against
`EFF.HE6.14`, and repaired at C.13 (FU-1) and C.14 (FU-2). That repair discharges the residue half
exactly as A-C.5 predicted: `composedKey_slot_residue_clause` below IS landed C.46, with no
hypothesis added.

## Defect 2 (found HERE at FU-3, commit `da950c29`): the zero-slot branch — REPAIRED AT C.14a

A **second, independent defect survived the A-C.5 repair, and this file isolated it.** C.13's
conjunct 5 has two branches, and the A-C.5 accounting (blueprint: *"what remains is the four shape
clauses"*; the refutation record: *"the other four conjuncts and the height half of clause 5 are
NOT in question"*) counted only one of them. The **zero-slot branch**

```
L.r.coeff t = 0  →  dev Φ′ Φ₂ (e₂t) = 0
```

was not provable at these binders. It was machine-reduced here to a single equation about C.14a's
residue section:

```
dev Φ′ (composedKey T) (e₂t) = 0   ↔   resLift (0 : ResidueField O) = 0
```

(`composedKey_zero_slot_iff`, via `stageLiftO_zero_iff`; both retained below, now as the *proof
route* rather than as a gap record). Pre-repair, `resLift` was the bare
`(IsLocalRing.residue_surjective x).choose` — a `Classical.choose` section whose ONLY pinned
property was `resLift_spec : residue O (resLift x) = x`. At `x = 0` that says exactly
`resLift 0 ∈ maximalIdeal O`, which in a DVR is a nonzero ideal. So the equation was **independent**
of everything the corpus carried: not false, not provable. (`Classical.choose` is opaque; its value
is a function of the *proposition* alone, and `∃ a, residue O a = 0` does not name a witness.)

**The cure, applied 2026-08-16 at C.14a (option 1 of the four recorded below, the RECOMMENDED
one).** `resLift` is now guarded: `if x = 0 then 0 else (residue_surjective x).choose`. Its new
companion lemma `resLift_zero : resLift 0 = 0` is `if_pos rfl`; `resLift_spec`'s STATEMENT is
byte-unchanged (its proof gained a `by_cases`); all five other consumers (C.14, C.24, C.46, C.56a,
C.84) rebuilt unchanged, since each reads `resLift` only through `resLift_spec` or writes it into
a def body. `composedKey_isTestKey` below is then
`composedKey_isTestKey_of_resLift_zero T hπ hh resLift_zero`.

### Why defect 2 was there, and why it was real (retained verbatim from the BLOCKED record)

* **C.43's `composedKey` has no zero guard.** Its display sums `L_{(f₂−t)u₂}(c_t·η^{W(t)})` over
  ALL `t < f₂`. `EFF.HE6.14`'s DEFINITION HE6-1, which C.13 transcribes, is explicit that
  `B_t := 0` when `c_t = 0` — the guard lives in the source and was dropped in the §6 display,
  which silently assumes `L_M(0) = 0`. That is true of "the" lift and was false of the corpus's
  junk-defaulting `resLift`-section implementation of it. The C.14a repair makes the
  implementation satisfy `L_M(0) = 0` (`stageLiftO_zero_iff` + `resLift_zero`), so the §6 display
  may keep its unguarded form.
* **Both neighbours DO guard.** C.14's own `exists_testKey` returns the literal `0` in its
  `L.r.coeff t = 0` branch (`hlift`'s first `by_cases`), and C.24 writes
  `if c t = 0 then 0 else resLift (c t)` in the body of its lift. C.43 was the outlier; the cure
  hoists their shared convention into `resLift` itself.
* **The vanishing case is legal** — so the branch is reachable, and the repair is not vacuous
  bookkeeping. `TowerDatum` constrains only `ψ₂.coeff 0` (`hψ0`); middle coefficients are free.
  `T² + 1` over `F₃` — the very residual the C.47 refutation record certifies irreducible on its
  mandatory `(e₁,f₁,h) = (2,2,3)` gate frame — is monic irreducible of degree `2` with nonzero
  constant term and `coeff 1 = 0`. Taken as `ψ₂` with `e₂ = 1, f₂ = 2` and any `u₂ > D′h` coprime
  to `1`, it is a legal `TowerDatum` at which the zero-slot branch fires. The coefficient shape is
  machine-checked in the `LegalityCheck` section below.
* **`towerLabel` transports the vanishing exactly.** `r̃_t = η^{−Qf₂}·ψ₂_t·η^{Qt}` and `η ≠ 0`, so
  `r̃_t = 0 ↔ ψ₂_t = 0`; the branch cannot be dodged by reading the label instead of `ψ₂`
  (`towerLabel_coeff_eq_zero_iff`).

## What is landed here

The signed node, plus the seven clauses it is assembled from — all sorry-free and Lean-core, at
the signed binders:

1. `composedKey_monic` — clause 1.
2. `composedKey_natDegree` — clause 2, `natDegree = keyDeg₂ = D′e₂f₂`.
3. `composedKey_top_digit` — clause 3, the leading `Φ′`-digit is `1`.
4. `composedKey_offLattice_digit` — clause 4, the digits off the `e₂`-lattice vanish.
5. `composedKey_slot_height` — clause 5's height half (H.55(i) at the frame, re-derived: C.14's
   exact-height calculus is `private`).
6. `composedKey_slot_residue_clause` — clause 5's ϖ-read residue half, which IS landed C.46. This
   is the A-C.5 repair paying out.
7. `composedKey_zero_slot` — clause 5's zero-slot branch, UNCONDITIONAL since the C.14a repair.
   This is the defect-2 cure paying out.

and

8. `composedKey_isTestKey_of_resLift_zero` — the signed statement with
   `resLift (0 : ResidueField O) = 0` as an explicit hypothesis. Retained: it was the BLOCKED
   record of the exact gap, and it is now the honest audit trail showing that C.14a's guard is the
   *only* thing the node needs beyond the six A-C.5 clauses. Nothing depends on it but item 9.
9. `composedKey_isTestKey` — **THE NODE**, the A-C.1 signature verbatim, item 8 fed `resLift_zero`.

## The four repair options that were on the table (adjudication record, 2026-08-15)

1. **Guard `resLift` (RECOMMENDED) — ✔ THIS IS THE ONE TAKEN, 2026-08-16.** Re-sign C.14a's
   `resLift` as `if x = 0 then 0 else (residue_surjective x).choose` — precisely C.24's own
   convention. Then `resLift 0 = 0` by `if_pos`, `stageLiftO M 0 = 0` follows from
   `stageLiftO_zero_iff`, and C.47 lands whole with its signature byte-unchanged. `resLift_spec`'s
   STATEMENT is byte-unchanged (its proof gains a `by_cases`), and every consumer (C.14, C.24,
   C.46, C.56a, C.84) reads `resLift` only through `resLift_spec` — C.14a's own docstring says so
   ("the choice itself is junk"). Blast radius: one definition, one proof. *(Executed exactly as
   written; the predicted blast radius held — all five consumers rebuilt with no edit.)*
2. **Guard `composedKey`.** Re-sign C.43 to sum `if T.ψ₂.coeff t = 0 then 0 else stageLiftO …`.
   Closest to `EFF.HE6.14`'s literal `B_t := 0`, but it changes a §6 signature and forces a case
   split inside landed C.46. NOT TAKEN.
3. **Constrain `TowerDatum` (dishonest).** Adding `∀ t < f₂, ψ₂.coeff t ≠ 0` excludes legal inner
   residuals (`T²+1` over `F₃`); recorded only to be rejected. NOT TAKEN.
4. **Hypothesize the equation.** Item 8 above, made permanent. Rejected as a signature: it would
   propagate a `Classical.choose` artefact into every §6 consumer. NOT TAKEN.

## Status

Sorry-free, Lean-core axioms only. The signed `composedKey_isTestKey` is **LANDED** at its
byte-unchanged A-C.1 signature, with no added hypothesis and no statement weakened anywhere: the
one thing that changed is the BODY of C.14a's `resLift` (a stub-side helper, not a blueprint node),
whose two exported facts are `resLift_spec` (statement byte-unchanged) and the new `resLift_zero`.

**DEPENDS.** C.13 (`IsTestKey`) · C.14 (packaging; `resLift_spec`) · C.14a (`stageLiftIA`,
`stageLiftO`, `stageCoord`, `sum_stageCoord`, `resLift`, and — since the 2026-08-16 zero-guard
repair — `resLift_zero`) · C.42 (`TowerDatum`) · C.43
(`composedKey`, `wrapExp`) · C.44 (`towerLabel`, `levelDatum`) · C.46
(`composedKey_slot_residue`) · B.04/B.06/B.32a/B.35a/B.39b (the `dev` calculus) — by committed
node ID (GC-13(b)).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **D9 (cured).** The order-0 key `X` is an order-1 key; the private-copy pattern
(C.04/C.12/C.14/C.19/C.21/C.22/C.44/C.46 each carry one), because `private` does not export. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-! ### The `Φ′`-development of a power, and of a reduced polynomial times a power

Both are `dev`-calculus bookkeeping over B.04/B.35a; neither is in the blueprint, and both stay
`private`. Together they give the composed key's ENTIRE development in one formula, which is what
turns C.13's four shape clauses into `if`-arithmetic. -/

private theorem dev_key_pow (F : KeyFrame O π) (n b : ℕ) :
    dev F.key (F.key ^ n) b = if b = n then 1 else 0 := by
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hkeypos : 0 < F.key.natDegree := by rw [F.hdeg]; exact hD
  have hone : F.key ^ n = (1 : Polynomial O) * F.key ^ n := (one_mul _).symm
  have hdeg1 : (1 : Polynomial O).degree < F.key.degree :=
    Polynomial.degree_lt_degree (by simpa using hkeypos)
  rcases lt_trichotomy b n with hb | rfl | hb
  · rw [hone, dev_mul_pow_of_lt F.hmonic _ _ _ hb, if_neg (Nat.ne_of_lt hb)]
  · have hshift := dev_mul_pow F.hmonic b (1 : Polynomial O) 0
    rw [Nat.add_zero] at hshift
    rw [hone, hshift, if_pos rfl]
    change (1 : Polynomial O) %ₘ F.key = 1
    exact (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr hdeg1
  · obtain ⟨m, hm⟩ : ∃ m, b = n + m := ⟨b - n, by omega⟩
    subst hm
    rw [hone, dev_mul_pow F.hmonic, if_neg (by omega)]
    refine dev_eq_zero_of_lt F.hmonic hkeypos _ _ ?_
    have hm1 : 1 ≤ m := by omega
    have hmul : 1 * F.key.natDegree ≤ m * F.key.natDegree := Nat.mul_le_mul_right _ hm1
    simpa using by omega

private theorem dev_reduced_mul_pow (F : KeyFrame O π) {A : Polynomial O}
    (hA : A.natDegree < F.e₁ * F.f₁) (n b : ℕ) :
    dev F.key (A * F.key ^ n) b = if b = n then A else 0 := by
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hkeypos : 0 < F.key.natDegree := by rw [F.hdeg]; exact hD
  have hAlt : A.natDegree < F.key.natDegree := by rw [F.hdeg]; exact hA
  rcases lt_trichotomy b n with hb | rfl | hb
  · rw [dev_mul_pow_of_lt F.hmonic _ _ _ hb, if_neg (Nat.ne_of_lt hb)]
  · have hshift := dev_mul_pow F.hmonic b A 0
    rw [Nat.add_zero] at hshift
    rw [hshift, if_pos rfl]
    change A %ₘ F.key = A
    exact (Polynomial.modByMonic_eq_self_iff F.hmonic).mpr (Polynomial.degree_lt_degree hAlt)
  · obtain ⟨m, hm⟩ : ∃ m, b = n + m := ⟨b - n, by omega⟩
    subst hm
    rw [dev_mul_pow F.hmonic, if_neg (by omega)]
    refine dev_eq_zero_of_lt F.hmonic hkeypos _ _ ?_
    have hm1 : 1 ≤ m := by omega
    have hmul : 1 * F.key.natDegree ≤ m * F.key.natDegree := Nat.mul_le_mul_right _ hm1
    omega

/-! ### C.43's lift terms -/

/-- The `t`-th lift term of C.43's TERMINAL display, named so that the development formula below
can be stated. Private: C.47 signs one declaration and the blueprint gives this object no node. -/
private noncomputable def cLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : ℕ) : Polynomial O :=
  F.stageLiftO H₀ hpin ((T.f₂ - s) * T.u₂)
    (- T.ψ₂.coeff s * F.stageLetter H₀ hpin ^ (wrapExp T s))

private theorem composedKey_eq {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) :
    composedKey T
      = F.key ^ (T.e₂ * T.f₂)
        - (Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s) := rfl

/-- **H.55(ii) at the frame.** Every lift term is already reduced: `deg < D′`. -/
private theorem natDegree_cLift_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : ℕ) : (cLift T s).natDegree < F.e₁ * F.f₁ := by
  classical
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hbound : (cLift T s).natDegree ≤ F.e₁ * F.f₁ - 1 := by
    rw [cLift, KeyFrame.stageLiftO, KeyFrame.stageLiftIA]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    have hj' : j < F.f₁ := Finset.mem_range.mp hj
    have hmul : F.e₁ * (j + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hj'
    have hexp : F.e₁ * (j + 1) = F.e₁ * j + F.e₁ := by ring
    have hi : F.slotIdx ((T.f₂ - s) * T.u₂) < F.e₁ := (F.slotIdx_spec _).1
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  omega

/-- **The composed key's whole `Φ′`-development, in one formula.** Since every lift term is
reduced (`natDegree_cLift_lt`), C.43's display IS the `Φ′`-adic development: digit `1` at
`e₂f₂`, digit `−(cLift T t)` at each `e₂t` with `t < f₂`, and `0` everywhere else. -/
private theorem dev_composedKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (b : ℕ) :
    dev F.key (composedKey T) b
      = (if b = T.e₂ * T.f₂ then 1 else 0)
        - ∑ s ∈ Finset.range T.f₂, (if b = T.e₂ * s then cLift T s else 0) := by
  classical
  have hterm : ∀ s ∈ Finset.range T.f₂,
      dev F.key (cLift T s * F.key ^ (T.e₂ * s)) b
        = if b = T.e₂ * s then cLift T s else 0 := fun s _ =>
    dev_reduced_mul_pow F (natDegree_cLift_lt T s) _ _
  rw [composedKey_eq, sub_eq_add_neg, dev_add_of_monic F.hmonic, dev_neg F.hmonic,
    dev_finsetSum F.hmonic, Finset.sum_congr rfl hterm, dev_key_pow, ← sub_eq_add_neg]

/-- The development at a lattice slot, unwound: `−(cLift T t)`. -/
private theorem dev_composedKey_slot {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {t : ℕ} (ht : t < T.f₂) :
    dev F.key (composedKey T) (T.e₂ * t) = - cLift T t := by
  classical
  rw [dev_composedKey, if_neg (by
    intro he
    have := Nat.eq_of_mul_eq_mul_left T.he₂ he
    omega)]
  have hcong : ∀ s ∈ Finset.range T.f₂,
      (if T.e₂ * t = T.e₂ * s then cLift T s else 0) = if s = t then cLift T s else 0 := by
    intro s _
    by_cases hst : s = t
    · rw [if_pos (by rw [hst]), if_pos hst]
    · rw [if_neg (by
        intro he
        exact hst (Nat.eq_of_mul_eq_mul_left T.he₂ he).symm), if_neg hst]
  rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq' (Finset.range T.f₂) t,
    if_pos (Finset.mem_range.mpr ht), zero_sub]

/-! ### Degree bookkeeping: the tail is dominated -/

private theorem tail_natDegree_lt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) :
    ((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s)).natDegree
      < (T.e₂ * T.f₂) * (F.e₁ * F.f₁) := by
  classical
  set D := F.e₁ * F.f₁ with hDdef
  have hD : 0 < D := Nat.mul_pos F.he₁ F.hf₁
  have hpos : 0 < (T.e₂ * T.f₂) * D := Nat.mul_pos (Nat.mul_pos T.he₂ T.hf₂) hD
  have hbound : ((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s)).natDegree
      ≤ (T.e₂ * T.f₂) * D - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    have hs' : s < T.f₂ := Finset.mem_range.mp hs
    have h1 : (cLift T s * F.key ^ (T.e₂ * s)).natDegree
        ≤ (cLift T s).natDegree + T.e₂ * s * D := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, F.hdeg]
    have h2 : (cLift T s).natDegree < D := natDegree_cLift_lt T s
    have h3 : T.e₂ * (s + 1) ≤ T.e₂ * T.f₂ := Nat.mul_le_mul_left _ hs'
    have h4 : T.e₂ * (s + 1) = T.e₂ * s + T.e₂ := by ring
    have h5 : (T.e₂ * s + T.e₂) * D ≤ (T.e₂ * T.f₂) * D := Nat.mul_le_mul_right D (by omega)
    have h6 : (T.e₂ * s + T.e₂) * D = T.e₂ * s * D + T.e₂ * D := by ring
    have h7 : D ≤ T.e₂ * D := Nat.le_mul_of_pos_left _ T.he₂
    omega
  omega

/-! ### C.14's exact-height calculus, re-derived (it is `private` there) -/

private theorem isUnit_of_residue_ne_zero {x : O} (hx : residue O x ≠ 0) : IsUnit x := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff] at hx
  exact IsLocalRing.notMem_maximalIdeal.mp hx

private theorem addVal_mul_pow (hπ : Irreducible π) (x : O) (n : ℕ) :
    addVal O (x * π ^ n) = addVal O x + (n : ℕ∞) := by
  rw [AddValuation.map_mul, hπ.addVal_pow]

private theorem slot_eq (F : KeyFrame O π) {M : ℕ} (hM : F.slotIdx M * F.h ≤ M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M := by
  have hdvd : F.e₁ ∣ M - F.slotIdx M * F.h :=
    (Nat.modEq_iff_dvd' hM).mp (F.slotIdx_spec M).2
  rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hM]

private theorem coeff_stageLiftIA_mem (F : KeyFrame O π) {i a s : ℕ} (hs : s < F.f₁)
    (lift : ℕ → O) :
    (F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s) = lift s * π ^ (a - s * F.h) := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff, Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbs
    have hne : i + F.e₁ * s ≠ i + F.e₁ * b := by
      intro he
      exact hbs (Nat.eq_of_mul_eq_mul_left F.he₁ (by omega)).symm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  · intro hns
    exact absurd (Finset.mem_range.mpr hs) hns

private theorem coeff_stageLiftIA_not_mem (F : KeyFrame O π) {i a n : ℕ} (lift : ℕ → O)
    (hn : ∀ s < F.f₁, n ≠ i + F.e₁ * s) :
    (F.stageLiftIA (π := π) i a lift).coeff n = 0 := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hne := hn s (Finset.mem_range.mp hs)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]

/-- **H.55(iii) at the frame.** -/
private theorem cost_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) {i a M s : ℕ}
    (hs : s < F.f₁) (hsa : s * F.h ≤ a) (hM : i * F.h + F.e₁ * a = M) (lift : ℕ → O) :
    F.e₁ • addVal O ((F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s))
        + ((F.h * (i + F.e₁ * s) : ℕ) : ℕ∞)
      = F.e₁ • addVal O (lift s) + (M : ℕ∞) := by
  rw [coeff_stageLiftIA_mem F hs lift, addVal_mul_pow hπ, smul_add]
  have hnat : F.e₁ * (a - s * F.h) + F.h * (i + F.e₁ * s) = M := by
    have hsub : F.e₁ * (a - s * F.h) = F.e₁ * a - F.e₁ * (s * F.h) := by rw [Nat.mul_sub]
    have hle : F.e₁ * (s * F.h) ≤ F.e₁ * a := Nat.mul_le_mul_left _ hsa
    have hexp : F.h * (i + F.e₁ * s) = i * F.h + F.e₁ * (s * F.h) := by ring
    omega
  rw [add_assoc]
  congr 1
  rw [show F.e₁ • ((a - s * F.h : ℕ) : ℕ∞) = ((F.e₁ * (a - s * F.h) : ℕ) : ℕ∞) by
    push_cast [nsmul_eq_mul]; ring]
  rw [← Nat.cast_add, hnat]

/-- **The exact-height clause.** -/
private theorem stageHeight_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) {i a M s₀ : ℕ}
    (hM : i * F.h + F.e₁ * a = M) (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a)
    (lift : ℕ → O) (hs₀ : s₀ < F.f₁) (hu : IsUnit (lift s₀)) :
    F.stageHeight (F.stageLiftIA (π := π) i a lift) = (M : ℕ∞) := by
  classical
  set A := F.stageLiftIA (π := π) i a lift with hA
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  have hcoeff₀ : A.coeff (i + F.e₁ * s₀) = lift s₀ * π ^ (a - s₀ * F.h) :=
    coeff_stageLiftIA_mem F hs₀ lift
  have hne₀ : A.coeff (i + F.e₁ * s₀) ≠ 0 := by
    rw [hcoeff₀]
    exact mul_ne_zero hu.ne_zero (pow_ne_zero _ hπ.ne_zero)
  rw [hinf]
  refine le_antisymm ?_ ?_
  · have hmem : i + F.e₁ * s₀ ∈ Finset.range (A.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hne₀))
    refine le_trans (Finset.inf_le hmem) ?_
    rw [cost_stageLiftIA F hπ hs₀ (hsa s₀ hs₀) hM lift,
      addVal_eq_zero_iff.mpr hu, smul_zero, zero_add]
  · refine Finset.le_inf fun j _ => ?_
    by_cases hex : ∃ s, s < F.f₁ ∧ j = i + F.e₁ * s
    · obtain ⟨s, hs, rfl⟩ := hex
      rw [cost_stageLiftIA F hπ hs (hsa s hs) hM lift]
      exact le_add_self
    · have hz : A.coeff j = 0 :=
        coeff_stageLiftIA_not_mem F lift (fun s hs he => hex ⟨s, hs, he⟩)
      rw [hz, addVal_zero, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add]
      exact le_top

/-- **H.55(i) for the element-at-height lift.** Above the fullness threshold `D′h < M`, a NONZERO
stage-field element lifts to exact height `M`. -/
private theorem stageHeight_stageLiftO (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) {c : F.stageField H₀ hpin}
    (hc : c ≠ 0) : F.stageHeight (F.stageLiftO H₀ hpin M c) = (M : ℕ∞) := by
  classical
  have hbelow : ∀ s, s < F.f₁ → (F.slotIdx M + F.e₁ * s) * F.h < M := by
    intro s hs
    have hi : F.slotIdx M < F.e₁ := (F.slotIdx_spec M).1
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    have hle : F.slotIdx M + F.e₁ * s ≤ F.e₁ * F.f₁ := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hM
  have hile : F.slotIdx M * F.h ≤ M := by
    have h0 := hbelow 0 F.hf₁
    rw [Nat.mul_zero, Nat.add_zero] at h0
    omega
  set a := (M - F.slotIdx M * F.h) / F.e₁ with hadef
  have hMa : F.slotIdx M * F.h + F.e₁ * a = M := slot_eq F hile
  have hsa : ∀ s, s < F.f₁ → s * F.h ≤ a := by
    intro s hs
    have h1 := hbelow s hs
    have hexp : (F.slotIdx M + F.e₁ * s) * F.h = F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
    have h2 : F.e₁ * (s * F.h) < F.e₁ * a := by omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left h2)
  have hex : ∃ s, s < F.f₁ ∧ F.stageCoord H₀ hpin c s ≠ 0 := by
    by_contra hall
    refine hc (Eq.trans (F.sum_stageCoord H₀ hpin c).symm ?_)
    refine Finset.sum_eq_zero fun s hs => ?_
    have hzero : F.stageCoord H₀ hpin c s = 0 := by
      by_contra hd
      exact hall ⟨s, Finset.mem_range.mp hs, hd⟩
    rw [hzero, map_zero, map_zero, zero_mul]
  obtain ⟨s₀, hs₀, hd₀⟩ := hex
  rw [KeyFrame.stageLiftO]
  refine stageHeight_stageLiftIA F hπ hMa hsa _ hs₀ ?_
  exact isUnit_of_residue_ne_zero (by rw [resLift_spec]; exact hd₀)

/-! ### The label's coefficients, and the fullness threshold at a slot -/

private theorem coeff_comp_C_mul_X {K : Type*} [CommRing K] (p : Polynomial K) (a : K) (t : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff t = p.coeff t * a ^ t := by
  classical
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  have hsummand : ∀ e ∈ p.support,
      (Polynomial.C (p.coeff e) * (Polynomial.C a * Polynomial.X) ^ e).coeff t
        = if e = t then p.coeff e * a ^ e else 0 := by
    intro e _
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    by_cases he : e = t
    · simp [he]
    · simp [he, Ne.symm he]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_ite_eq' p.support t]
  by_cases ht : t ∈ p.support
  · rw [if_pos ht]
  · rw [if_neg ht, Polynomial.notMem_support_iff.mp ht, zero_mul]

/-- **The vanishing transports.** `r̃_t = η^{−Qf₂}·ψ₂_t·η^{Qt}` with `η ≠ 0`, so the translated
label's `t`-th coefficient vanishes exactly when `ψ₂`'s does. This is why C.13 conjunct 5's
zero-slot branch cannot be dodged by reading the label instead of the inner residual. -/
theorem towerLabel_coeff_eq_zero_iff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (t : ℕ) :
    (towerLabel T).coeff t = 0 ↔ T.ψ₂.coeff t = 0 := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  have hη : F.stageLetter H₀ hpin ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  have hlabel : (towerLabel T).coeff t
      = (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂)
        * (T.ψ₂.coeff t * ((F.stageLetter H₀ hpin) ^ F.twistExp T.u₂) ^ t) := by
    have hEq : towerLabel T
        = Polynomial.C ((F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂))
            * T.ψ₂.comp (Polynomial.C ((F.stageLetter H₀ hpin) ^ F.twistExp T.u₂)
              * Polynomial.X) := rfl
    rw [hEq, Polynomial.coeff_C_mul, coeff_comp_C_mul_X]
  rw [hlabel]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (pow_ne_zero _ (inv_ne_zero hη))
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero _ (pow_ne_zero _ hη))
  · intro hz
    rw [hz, zero_mul, mul_zero]

/-- The fullness threshold `D′h < (f₂−t)u₂` at every slot `t < f₂`, from C.42's node floor
`hfloor` (`EFF.HETOW.18`'s chain). -/
private theorem slot_fullness {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {t : ℕ} (ht : t < T.f₂) :
    F.e₁ * F.f₁ * F.h < (T.f₂ - t) * T.u₂ := by
  have hsub : 1 ≤ T.f₂ - t := by omega
  have hfloor : T.e₂ * (F.e₁ * F.f₁) * F.h < T.u₂ := T.hfloor
  have hle : F.e₁ * F.f₁ * F.h ≤ T.e₂ * (F.e₁ * F.f₁) * F.h :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ T.he₂)
  have hgrow : T.u₂ ≤ (T.f₂ - t) * T.u₂ := Nat.le_mul_of_pos_left _ hsub
  omega

/-! ### THE SIX UNCONDITIONAL CLAUSES -/

/-- **C.13 conjunct 1 at the composed key.** -/
theorem composedKey_monic {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : (composedKey T).Monic := by
  have htail : (-((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s))).degree
      < (F.key ^ (T.e₂ * T.f₂)).degree := by
    rw [Polynomial.degree_neg]
    refine Polynomial.degree_lt_degree ?_
    rw [Polynomial.natDegree_pow, F.hdeg]
    exact tail_natDegree_lt T
  have hsplit : composedKey T
      = -((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s))
        + F.key ^ (T.e₂ * T.f₂) := by
    rw [composedKey_eq, sub_eq_neg_add]
  rw [hsplit]
  exact (F.hmonic.pow (T.e₂ * T.f₂)).add_of_right htail

/-- **C.13 conjunct 2 at the composed key:** `deg Φ₂ = D″ = D′e₂f₂`. -/
theorem composedKey_natDegree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (composedKey T).natDegree = (T.levelDatum hπ).keyDeg₂ := by
  have htail : (-((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s))).degree
      < (F.key ^ (T.e₂ * T.f₂)).degree := by
    rw [Polynomial.degree_neg]
    refine Polynomial.degree_lt_degree ?_
    rw [Polynomial.natDegree_pow, F.hdeg]
    exact tail_natDegree_lt T
  have hsplit : composedKey T
      = -((Finset.range T.f₂).sum fun s => cLift T s * F.key ^ (T.e₂ * s))
        + F.key ^ (T.e₂ * T.f₂) := by
    rw [composedKey_eq, sub_eq_neg_add]
  have hdegeq : (composedKey T).degree = (F.key ^ (T.e₂ * T.f₂)).degree := by
    rw [hsplit]
    exact Polynomial.degree_add_eq_right_of_degree_lt htail
  have hd : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  have hℓ : (T.levelDatum hπ).ℓ = T.e₂ := rfl
  rw [Polynomial.natDegree_eq_of_degree_eq hdegeq, Polynomial.natDegree_pow, F.hdeg,
    LevelDatum.keyDeg₂, hℓ, hd]
  ring

/-- **C.13 conjunct 3 at the composed key:** the leading `Φ′`-digit is `1`. -/
theorem composedKey_top_digit {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : dev F.key (composedKey T) (T.e₂ * T.f₂) = 1 := by
  classical
  rw [dev_composedKey, if_pos rfl]
  have hzero : ∀ s ∈ Finset.range T.f₂,
      (if T.e₂ * T.f₂ = T.e₂ * s then cLift T s else 0) = 0 := by
    intro s hs
    refine if_neg fun he => ?_
    exact absurd (Nat.eq_of_mul_eq_mul_left T.he₂ he) (by
      have := Finset.mem_range.mp hs; omega)
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

/-- **C.13 conjunct 4 at the composed key:** the digits off the `e₂`-lattice vanish. -/
theorem composedKey_offLattice_digit {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {b : ℕ} (hb : b < T.e₂ * T.f₂) (hnd : ¬ T.e₂ ∣ b) :
    dev F.key (composedKey T) b = 0 := by
  classical
  rw [dev_composedKey, if_neg (by omega)]
  have hzero : ∀ s ∈ Finset.range T.f₂, (if b = T.e₂ * s then cLift T s else 0) = 0 := by
    intro s _
    exact if_neg fun he => hnd ⟨s, he⟩
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

/-- **C.13 conjunct 5, the height half, at the composed key** (H.55(i) at the frame): at a slot
whose label coefficient is NONZERO the digit sits at exact stage height `(f₂−t)u₂`. -/
theorem composedKey_slot_height {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {t : ℕ} (ht : t < T.f₂)
    (hne : (towerLabel T).coeff t ≠ 0) :
    F.stageHeight (dev F.key (composedKey T) (T.e₂ * t)) = (((T.f₂ - t) * T.u₂ : ℕ) : ℕ∞) := by
  classical
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  have hη : F.stageLetter H₀ hpin ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  have hψ : T.ψ₂.coeff t ≠ 0 := fun hz =>
    hne ((towerLabel_coeff_eq_zero_iff T hπ t).mpr hz)
  have hc : (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hψ) (pow_ne_zero _ hη)
  rw [dev_composedKey_slot T ht, KeyFrame.stageHeight, suppVal_neg Polynomial.monic_X,
    ← KeyFrame.stageHeight, cLift]
  exact stageHeight_stageLiftO F hπ H₀ hpin (slot_fullness T ht) hc

/-- **C.13 conjunct 5, the ϖ-read residue half, at the composed key — this IS landed C.46.**
Under the A-C.5 re-sign of C.13 clause 5 the residue obligation is discharged, not relocated:
the statement below is `composedKey_slot_residue` verbatim. -/
theorem composedKey_slot_residue_clause {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h) {t : ℕ} (ht : t < T.f₂) :
    F.twistRead H₀ hpin ((T.f₂ - t) * T.u₂) (dev F.key (composedKey T) (T.e₂ * t))
      = (towerLabel T).coeff t :=
  composedKey_slot_residue T hπ hh ht

/-! ### C.13 conjunct 5's zero-slot branch — WAS the gap, cured at C.14a on 2026-08-16

The two `iff`s below are the machine-reduction that isolated defect 2. They are kept verbatim
(statements byte-unchanged from the BLOCKED record, commit `da950c29`): with C.14a's `resLift`
now guarded, their right-hand side `resLift (0 : ResidueField O) = 0` is the landed
`resLift_zero`, so the same two lemmas that *diagnosed* the defect now *discharge* the branch. -/

private theorem stageCoord_zero (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (s : ℕ) :
    F.stageCoord H₀ hpin 0 s = 0 := by
  simp [KeyFrame.stageCoord]

/-- **The reduction, in one equation about C.14a's residue section.** The zero lift is zero
exactly when `resLift 0` is. Pre-repair this was the gap: `resLift` was `(residue_surjective
x).choose`, whose only pinned property (`resLift_spec`) said at `x = 0` merely that
`resLift 0 ∈ maximalIdeal O`, a NONZERO ideal in a DVR, so nothing in the corpus decided the
equation either way. Since the 2026-08-16 C.14a zero guard the right-hand side is `resLift_zero`,
and this `iff` is the proof route rather than the obstruction. -/
theorem stageLiftO_zero_iff (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) (M : ℕ) :
    F.stageLiftO H₀ hpin M 0 = 0 ↔ resLift (0 : ResidueField O) = 0 := by
  constructor
  · intro h
    rw [KeyFrame.stageLiftO] at h
    have hc := coeff_stageLiftIA_mem F (i := F.slotIdx M)
      (a := (M - F.slotIdx M * F.h) / F.e₁) (s := 0) F.hf₁
      (fun s => resLift (F.stageCoord H₀ hpin (0 : F.stageField H₀ hpin) s))
    rw [h] at hc
    simp only [Polynomial.coeff_zero, Nat.zero_mul, Nat.sub_zero, stageCoord_zero] at hc
    rcases mul_eq_zero.mp hc.symm with h1 | h2
    · exact h1
    · exact absurd h2 (pow_ne_zero _ hπ.ne_zero)
  · intro h
    rw [KeyFrame.stageLiftO, KeyFrame.stageLiftIA]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [stageCoord_zero, h, zero_mul, Polynomial.C_0, zero_mul]

/-- **C.13 conjunct 5's zero-slot branch at the composed key, reduced.** At a slot whose label
coefficient vanishes, the required digit identity `dev Φ′ Φ₂ (e₂t) = 0` is EQUIVALENT to
`resLift 0 = 0`. C.43's display carries no zero guard, while `EFF.HE6.14`'s DEFINITION HE6-1 (the
source C.13 transcribes) says `B_t := 0` when `c_t = 0`, and both neighbouring nodes DO guard
(C.14's `exists_testKey`, C.24's `if c t = 0 then 0 else resLift (c t)`). THE CURE puts the guard
in `resLift` itself, which is what `composedKey_zero_slot` below reads off this `iff`. -/
theorem composedKey_zero_slot_iff {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {t : ℕ} (ht : t < T.f₂)
    (hz : (towerLabel T).coeff t = 0) :
    dev F.key (composedKey T) (T.e₂ * t) = 0 ↔ resLift (0 : ResidueField O) = 0 := by
  have hψ : T.ψ₂.coeff t = 0 := (towerLabel_coeff_eq_zero_iff T hπ t).mp hz
  have hcz : cLift T t = F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂) 0 := by
    rw [cLift, hψ, neg_zero, zero_mul]
  rw [dev_composedKey_slot T ht, neg_eq_zero, hcz]
  exact stageLiftO_zero_iff F hπ H₀ hpin _

/-- **C.13 conjunct 5, the zero-slot branch, at the composed key — UNCONDITIONAL.** The seventh
clause, and the payout of the 2026-08-16 C.14a zero guard: at a slot whose label coefficient
vanishes, the `Φ′`-digit vanishes. -/
theorem composedKey_zero_slot {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {t : ℕ} (ht : t < T.f₂)
    (hz : (towerLabel T).coeff t = 0) :
    dev F.key (composedKey T) (T.e₂ * t) = 0 :=
  (composedKey_zero_slot_iff T hπ ht hz).mpr resLift_zero

/-- **The signed statement, with the former gap as an explicit hypothesis.** Retained as the audit
trail of what defect 2 cost: everything except this one equation was already landed at FU-3
(commit `da950c29`). Since the 2026-08-16 C.14a zero guard the hypothesis is discharged by
`resLift_zero`, which is exactly what `composedKey_isTestKey` below does. -/
theorem composedKey_isTestKey_of_resLift_zero {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] (hzero : resLift (0 : ResidueField O) = 0) :
    IsTestKey (T.levelDatum hπ) (composedKey T) := by
  classical
  have hℓ : (T.levelDatum hπ).ℓ = T.e₂ := rfl
  have hu : (T.levelDatum hπ).u = T.u₂ := rfl
  have hr : (T.levelDatum hπ).r = towerLabel T := rfl
  have hd : (T.levelDatum hπ).r.natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1
  refine ⟨composedKey_monic T, composedKey_natDegree T hπ, ?_, ?_, ?_⟩
  · rw [hℓ, hd]; exact composedKey_top_digit T
  · intro b hb hnd
    rw [hℓ, hd] at hb
    rw [hℓ] at hnd
    exact composedKey_offLattice_digit T hb hnd
  · intro t ht
    rw [hd] at ht
    refine ⟨fun hz => ?_, fun hne => ⟨?_, ?_⟩⟩
    · rw [hr] at hz
      rw [hℓ]
      exact (composedKey_zero_slot_iff T hπ ht hz).mpr hzero
    · rw [hr] at hne
      rw [hℓ, hd, hu]
      exact composedKey_slot_height T hπ ht hne
    · rw [hℓ, hd, hu, hr]
      exact composedKey_slot_residue_clause T hπ hh ht

/-! ### THE NODE -/

/-- **NODE C.47 — HETOW-2 at the (LIFT)-form.** C.43's composed key `Φ₂` is a test key for the
level datum `T.levelDatum hπ` in C.13's sense. The A-C.1 signature, byte-unchanged through the
A-C.5 re-sign and through both repairs, with NO added hypothesis.

Six of the seven clauses were landed at FU-3 (commit `da950c29`); the seventh, C.13 conjunct 5's
zero-slot branch, was BLOCKED there on the `Classical.choose` artefact `resLift 0 = 0` and is
discharged by the 2026-08-16 C.14a zero guard (`resLift_zero`). See the module docstring for the
full two-defect record. -/
theorem composedKey_isTestKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] :
    IsTestKey (T.levelDatum hπ) (composedKey T) :=
  composedKey_isTestKey_of_resLift_zero T hπ hh resLift_zero

end Uniformity.Density.Tower

/-! ## The legality of the vanishing case

`TowerDatum` pins only `ψ₂.coeff 0` (`hψ0`); every middle coefficient is free. `X² + 1` over `F₃`
— the residual the C.47 refutation record certifies irreducible on its mandatory
`(e₁,f₁,h) = (2,2,3)` gate frame, since `−1` is a non-square mod `3` — has the shape a legal `ψ₂`
with `e₂ = 1, f₂ = 2` needs, and `coeff 1 = 0`. So the zero-slot branch is reachable, not vacuous.
Only the coefficient shape is machine-checked here; the irreducibility is the refutation record's. -/

section LegalityCheck

/-- Monic of degree `2`, nonzero constant term, and a VANISHING middle coefficient. -/
example : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 3)).Monic
    ∧ (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 3)).natDegree = 2
    ∧ (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 3)).coeff 0 ≠ 0
    ∧ (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 3)).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · monicity!
  · compute_degree!
  · simp
  · simp [Polynomial.coeff_one]

end LegalityCheck

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.towerLabel_coeff_eq_zero_iff
#print axioms Uniformity.Density.Tower.composedKey_monic
#print axioms Uniformity.Density.Tower.composedKey_natDegree
#print axioms Uniformity.Density.Tower.composedKey_top_digit
#print axioms Uniformity.Density.Tower.composedKey_offLattice_digit
#print axioms Uniformity.Density.Tower.composedKey_slot_height
#print axioms Uniformity.Density.Tower.composedKey_slot_residue_clause
#print axioms Uniformity.Density.Tower.stageLiftO_zero_iff
#print axioms Uniformity.Density.Tower.composedKey_zero_slot_iff
#print axioms Uniformity.Density.Tower.composedKey_zero_slot
#print axioms Uniformity.Density.Tower.composedKey_isTestKey_of_resLift_zero
#print axioms Uniformity.Density.Tower.composedKey_isTestKey

end AxCheck
