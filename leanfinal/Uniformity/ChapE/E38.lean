/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E10
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Uniformity.ChapE.E38 — slot domination, the fold (LEMMA HE7-12 clause (d))

**Chapter E, NODE E.38** [theorem], **first of the SPLIT-MANDATED pair**
(`blueprint/CHAP-E_sigma_ladder.md` §5: *"`slot_fold` and `offdisk_positivity` as two files
(`E38`, `E38a`) — independent consumers (E.42 needs the fold; E.23's HE7-12(a) row needs the
arithmetic)"*). This file lands `slot_fold`; the arithmetic clause is
`leanfinal/Uniformity/ChapE/E38a.lean`. ENV-E2.

## What the node says

`EFF.HE7.44`'s clause (d): a family of increments `w₁, …, w_j`, each of degree `< D″` and each of
slot value strictly above the threshold `T₂`, folds to `W = Σ wᵢ` whose slot value is the MINIMUM
of the summands' — *"the slot-min is ultrametric slotwise"* — and, under the `[r3]` rider, the
fold is EXACT and `W ≠ 0`:

> *"the values `dv₂(wᵢ)` are pairwise DISTINCT (they are the strictly increasing slopes … of
> LEMMA HE7-13 …), so the slot-min is attained by the least-slope increment ALONE and
> `dv₂(W) = minᵢ dv₂(wᵢ) < ∞ EXACTLY`."*

The signed conclusion is the three-conjunct form: `ws.sum ≠ 0`, the value is finite and still
`> T`, and it equals the fold `(ws.map C.hgt).foldr min ⊤`. Everything runs on E.10's carrier
laws — `hgt_add_eq` for the exact ultrametric step, `hgt_zero` for the `[r3]` nonvanishing rider.
No polygon, no root, no ξ.

## The mechanism, in one line

`W ≠ 0` is not an extra hypothesis and not an appeal to the polynomials: the carrier says
`hgt 0 = ⊤`, and the fold's value is a *coercion of an integer*, hence `≠ ⊤`. Finiteness of the
height IS the nonvanishing. That is why the `[r3]` rider costs nothing once distinctness is in
hand.

## ⚠ WHAT IS AND IS NOT SIGNED HERE (three honest disclosures)

1. **`hdeg` is threaded, not consumed at a leaf.** The signed conclusion says nothing about
   `deg W`, so the degree hypothesis is passed down the induction and never used. It is not
   decoration: blueprint clause (i) also asserts `deg W < D″`, and gate (a) below PROVES that
   half from `hdeg` alone (`natDegree_list_sum_lt`). The two halves are independent — the degree
   bound needs no ultrametric law and the fold needs no degree bound — which is exactly why the
   SIGNATURE carries only the fold. Nothing is lost: a consumer wanting the degree half applies
   `natDegree_list_sum_lt`, landed here.
2. **Clause (iii) of the blueprint STATEMENT — the package transport `TransportsTo` — is NOT in
   this file.** It is an obligation DEF whose eleven-item discharge audit (`EFF.HE7.44`(c) items
   (1)–(11), as COMPLETED by ANNEX R R4) is the INSTANCES' (E.23 rows), never E's.
3. **The `[r3]` vacuity disclosure travels with the TEETH, not with the statement.** `he7r2_supp.py`
   B2's `δ = ∞` half is vacuous on 41 of 42 members (recorded in the blueprint §13 honesty
   census); this file's B1 leg (slot geometry, 42/42) is the one it upgrades to a Lean theorem.

## ⚠ THE HE7-12 / HE7-13 CIRCULARITY, AND WHY THIS FILE IS NOT PART OF IT

The corpus flags OPEN-CALL 3: clause (d)'s `W ≠ 0` cites HE7-13's strictly increasing slopes,
while HE7-13's proof cites HE7-12(c)(d) — *"broken by simultaneous induction along the chain"*.
The Lean resolution is structural and is visible in the SIGNATURE: `slot_fold` takes pairwise
distinctness as an explicit HYPOTHESIS (`hdist`) and proves nothing about slopes. E.56 quantifies
the chain and establishes both invariants in ONE strong induction, discharging `hdist` at each
step. So no axiom-level circularity can survive elaboration, and this file cannot participate in
one: it is a statement about an arbitrary list of polynomials with pairwise-distinct heights.

DEPENDS: **E.10** (`leanfinal/Uniformity/ChapE/E10.lean` — `SlotCarrier`, and specifically
`hgt_add_eq`, `hgt_zero`; `hgt_add_ge` is NOT needed, the exact law does all the work) ·
**E.28** conceptually (the distinct-height uniqueness pattern; nothing is imported from it — E.28
lives on `RungDatum`, a different layer) · mathlib `List.Pairwise`, `List.sum`, `WithTop.coe_min`,
`Polynomial.natDegree_add_le`.

SOURCE: `EFF.HE7.44` (LEMMA HE7-12 clause (d) verbatim, including the `[r3]` `W ≠ 0` rider quoted
above); `EFF.HE7.43` (the slot-domination mechanism: key slots AT `T₂`, increment slots strictly
above); ANNEX R R4 (`EFF.HE7.44` CONDITIONALITY (a): the completed inventory, *"citation-
completeness on one sentence, no transfer breaks"*).

TEETH: `he7r2_supp.py` B1 (slot geometry, 42/42) → **Lean theorem**, landed here. B2 (the off-disk
inequality, 210/210) is E.38a's. Clause (c) is an obligation def and belongs to the instances.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free, axiom-free: every declaration reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. `slot_fold` is transcribed byte-for-byte against the
signed SIGNATURE (`leanspec/Leanspec/ChapE.lean` §5): binder list, implicit/explicit status,
hypothesis names, and the three-conjunct conclusion unchanged. The two other named declarations
are file-local helpers, not blueprint nodes.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **Helper (not a blueprint node).** The `foldr min ⊤` of a nonempty list of `WithTop ℤ` is one
of its entries. This is what turns the fold value back into *the height of an actual summand*, so
that `hdist` can be applied to it — the "attained by the least-slope increment ALONE" half of
`EFF.HE7.44`'s `[r3]` rider. -/
theorem foldr_min_mem_of_ne_nil : ∀ (l : List (WithTop ℤ)), l ≠ [] → l.foldr min ⊤ ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    rcases eq_or_ne t [] with rfl | ht
    · simp
    · have hmem := ih ht
      rw [List.foldr_cons]
      rcases min_cases a (t.foldr min ⊤) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; simp
      · rw [h]; exact List.mem_cons_of_mem _ hmem

/-- **Helper (not a blueprint node): the degree half of blueprint clause (i).** A list of
polynomials each of degree `< D` (with `D > 0`) sums to something of degree `< D`. Independent of
every slot law — which is why the signed `slot_fold` carries `hdeg` but does not conclude this,
and why it can be supplied separately to any consumer that needs `deg W < D″`. -/
theorem natDegree_list_sum_lt {O : Type*} [CommRing O] {D : ℕ} (hD : 0 < D) :
    ∀ (ws : List (Polynomial O)), (∀ w ∈ ws, w.natDegree < D) → ws.sum.natDegree < D := by
  intro ws
  induction ws with
  | nil => intro _; simpa using hD
  | cons w rest ih =>
    intro hdeg
    rw [List.sum_cons]
    have h1 : w.natDegree < D := hdeg w (by simp)
    have h2 : rest.sum.natDegree < D := ih fun x hx => hdeg x (List.mem_cons_of_mem _ hx)
    have := Polynomial.natDegree_add_le w rest.sum
    omega

/-- **E.38 — slot domination, the fold** (LEMMA HE7-12 clause (d), `EFF.HE7.44`). Increments of
pairwise-distinct slot heights, all strictly above the threshold `T`, fold to a sum that is
NONZERO, still strictly above `T`, and whose height is EXACTLY the min of the summands'
heights. -/
theorem slot_fold {O : Type*} [CommRing O] {K : Type*} [Field K]
    (C : SlotCarrier O K) {T : ℤ} (ws : List (Polynomial O)) (hne : ws ≠ [])
    (hdeg : ∀ w ∈ ws, w.natDegree < C.D)
    (hval : ∀ w ∈ ws, ∃ v : ℤ, C.hgt w = (v : WithTop ℤ) ∧ T < v)
    (hdist : ws.Pairwise fun w w' => C.hgt w ≠ C.hgt w') :
    ws.sum ≠ 0 ∧ (∃ v : ℤ, C.hgt ws.sum = (v : WithTop ℤ) ∧ T < v) ∧
      C.hgt ws.sum = (ws.map C.hgt).foldr min ⊤ := by
  -- the `[r3]` rider's whole mechanism: a finite height forces nonvanishing (`hgt 0 = ⊤`)
  have hnz : ∀ (A : Polynomial O) (v : ℤ), C.hgt A = (v : WithTop ℤ) → A ≠ 0 := by
    intro A v hA h0
    rw [h0, C.hgt_zero] at hA
    exact absurd hA (by simp)
  revert hne hdeg hval hdist
  induction ws with
  | nil => intro h; exact absurd rfl h
  | cons w rest ih =>
    intro _ hdeg hval hdist
    obtain ⟨vw, hvw, hTvw⟩ := hval w (by simp)
    rcases eq_or_ne rest [] with rfl | hrest
    · -- base: a single increment; the fold is `min (hgt w) ⊤ = hgt w`
      refine ⟨?_, ?_, ?_⟩
      · simpa using hnz w vw hvw
      · exact ⟨vw, by simpa using hvw, hTvw⟩
      · simp
    · have hdegr : ∀ x ∈ rest, x.natDegree < C.D := fun x hx => hdeg x (List.mem_cons_of_mem _ hx)
      have hvalr : ∀ x ∈ rest, ∃ v : ℤ, C.hgt x = (v : WithTop ℤ) ∧ T < v :=
        fun x hx => hval x (List.mem_cons_of_mem _ hx)
      have hdistr := (List.pairwise_cons.mp hdist).2
      obtain ⟨hrne, ⟨vr, hvr, hTvr⟩, hfold⟩ := ih hrest hdegr hvalr hdistr
      -- the tail's height IS the height of one of its members, so `hdist` applies to it
      have hmem : (rest.map C.hgt).foldr min ⊤ ∈ rest.map C.hgt :=
        foldr_min_mem_of_ne_nil _ (by simpa using hrest)
      have hdiff : C.hgt w ≠ C.hgt rest.sum := by
        rw [hfold]
        obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hmem
        rw [← hxeq]
        exact (List.pairwise_cons.mp hdist).1 x hx
      -- distinct heights ⟹ the ultrametric step is an EQUALITY
      have hadd : C.hgt (w + rest.sum) = min (C.hgt w) (C.hgt rest.sum) := C.hgt_add_eq _ _ hdiff
      have hval2 : C.hgt ((w :: rest).sum) = ((min vw vr : ℤ) : WithTop ℤ) := by
        rw [List.sum_cons, hadd, hvw, hvr]
        exact (WithTop.coe_min vw vr).symm
      refine ⟨hnz _ _ hval2, ⟨min vw vr, hval2, lt_min hTvw hTvr⟩, ?_⟩
      rw [hval2, List.map_cons, List.foldr_cons, ← hfold, hvw, hvr]
      exact (WithTop.coe_min vw vr).symm

/-! ## Gates (executed `example`s, not blueprint declarations)

**(a) Blueprint clause (i)'s degree half, under `slot_fold`'s own hypotheses.** The signed
conclusion omits `deg W < D″`; the gate supplies it from `hdeg` and `C.hD`, so the omission is a
factorization of the clause and not a silent loss. Read together with disclosure 1 above.

**(b) `hdist` IS LOAD-BEARING — abstractly, at every carrier.** Not an appeal to intuition: for
ANY slot carrier and ANY `w` of finite height, `hgt (−w) = hgt w` is FORCED by the carrier laws
(if the two heights differed, `hgt_add_eq` would make `hgt 0 = ⊤` the min of two heights, pushing
both to `⊤`). So `[w, −w]` satisfies `hne`, `hdeg` and `hval` while failing `hdist` — and its sum
is `0`, refuting the `W ≠ 0` conjunct. Every carrier therefore carries a counterexample to the
`hdist`-free statement; there is no arena in which the hypothesis could be dropped.

**(c) `hne` is load-bearing, for the same conjunct.** The empty list sums to `0`.

Gates (b) and (c) together pin the `[r3]` rider exactly: `W ≠ 0` fails without EITHER hypothesis,
so the signed statement is minimal in both. -/

section Gate

-- (a) clause (i)'s degree half, from `slot_fold`'s hypothesis set.
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K)
    (ws : List (Polynomial O)) (hdeg : ∀ w ∈ ws, w.natDegree < C.D) :
    ws.sum.natDegree < C.D :=
  natDegree_list_sum_lt C.hD ws hdeg

-- (b) `hdist` is load-bearing: at every carrier, `[w, −w]` breaks exactly it, and sums to `0`.
example {O : Type*} [CommRing O] {K : Type*} [Field K] (C : SlotCarrier O K)
    {v : ℤ} (w : Polynomial O) (hw : C.hgt w = (v : WithTop ℤ)) :
    C.hgt (-w) = (v : WithTop ℤ) ∧ [w, -w].sum = 0 ∧
      ¬ [w, -w].Pairwise fun a b => C.hgt a ≠ C.hgt b := by
  have hsame : C.hgt w = C.hgt (-w) := by
    by_contra hne
    have h := C.hgt_add_eq w (-w) hne
    rw [add_neg_cancel, C.hgt_zero] at h
    have hwtop : C.hgt w = ⊤ := (min_eq_top.mp h.symm).1
    rw [hw] at hwtop
    exact absurd hwtop (by simp)
  refine ⟨hsame ▸ hw, by simp, ?_⟩
  intro hp
  exact ((List.pairwise_cons.mp hp).1 (-w) (by simp)) hsame

-- (c) `hne` is load-bearing: the empty fold is `0`.
example {O : Type*} [CommRing O] : ([] : List (Polynomial O)).sum = 0 := List.sum_nil

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.foldr_min_mem_of_ne_nil
#print axioms Uniformity.Density.Ladder.natDegree_list_sum_lt
#print axioms Uniformity.Density.Ladder.slot_fold

end AxCheck
