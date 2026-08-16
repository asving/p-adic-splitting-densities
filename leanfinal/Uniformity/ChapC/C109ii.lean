/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C109a
import Uniformity.ChapB.B08
import Uniformity.ChapB.B11
import Uniformity.ChapB.B25
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapC.C109ii — NODE C.109-ii, the block slot count

**Chapter C, NODE C.109-ii** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md`, the A-C.5
amendment, ITEM 1 — the C.109 SPLIT), **ENV-C1 + `[Finite (ResidueField O)]`**.
`[signed: A-C.5, 2026-08-16 — layer 2 of five under C.109's byte-unchanged assembly]`.

Prescribing only the polygon FLOORS leaves `Σ_{j<m}(N − P j)` digit slots: the box of level-`N`
classes whose block heights clear `P` has cardinality `Q ^ (Σ_{j<m}(N − P j))`, where
`Q = Nat.card (resField Φ)`.  This is `EFF.W12.24`'s *"slot `j` contributes `N − ⌈P(j)⌉` free
digits"*, and it is the `B_v(N)` of C.109's assembly BEFORE the `L` priced digits are removed
by C.109-iii.

## The three moves

1. **The box splits componentwise** (C.109a, `dev_box_bridge`).  The bridge `E` is pinned at an
   arbitrary integral lift, so the floor condition — an `∃`-over-lifts in the signed statement —
   reads off the CLASS: through `E`, `c` clears `P` iff every block class `E c j` has all `d`
   of its slots divisible by `π ^ (P j)`.  `hP` is what makes that a class condition: a class
   that is `π ^ h`-divisible mod `𝔪 ^ N` has `π ^ h`-divisible lifts as soon as `h ≤ N`
   (`divRes_mk_iff`), and the coefficients of a development block above `Φ.natDegree` vanish
   outright, so B.08's `le_gaussVal_iff` sees exactly the `d` in-block slots.
2. **One slot's fibre** (`card_divRes`).  The classes mod `𝔪 ^ N` divisible by `π ^ h` are the
   KERNEL of the truncation `Res O N → Res O h`; that truncation is a surjective additive map,
   so `q ^ N = #ker · q ^ h` (`card_preimage_of_surjective` + `card_res`) and `#ker = q ^ (N−h)`.
3. **Assemble.**  `Equiv.subtypePiEquivPi` twice (blocks, then slots inside a block) and
   `Nat.card_pi`: `∏_{j<m} (q^{N−P j})^d = ∏_{j<m} Q^{N−P j} = Q^{Σ_j (N − P j)}`, using
   `Q = q ^ d` (`card_resField'`).

## Why `card_resField` is re-proved here (the C.04 precedent, not a new fact)

B.26(c)'s `card_resField` sits in that module's `ENVC` section and its ELABORATED signature
carries `[IsAdicComplete (maximalIdeal O) O]`, which this node's signed signature does not bind
(ENV-C1 + residue finiteness, no completeness).  The signature is signed and frozen, so the
completeness-free re-derivation `card_resField'` is the only route onto the signed type.  This
is exactly the environment mismatch NODE C.04 documented and cured the same way (its private
`card_resField_X`); the proof here is B.26(c)'s proof at a general key, minus the section
hypothesis it never used.  `private`, so it cannot collide with B.26's public row.

**DEPENDS.** C.109a (`dev_box_bridge` — the development bridge) · B.08 (`le_gaussVal_iff`) ·
B.11 (`npHgt`) · B.04 (`degree_dev_lt`) · B.25 (`resField`) · B.26 (`card_resField` — used as a
PATTERN, see the environment note) · landed `Coeff`/`proj`/`proj_surjective`/`monicPoly`/
`Res`/`resFactor`/`card_res`/`card_preimage_of_surjective`/`residueCard`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.24` (*"slot `j` contributes `N − ⌈P(j)⌉` free digits"*, verbatim);
`EFF.W12.23` (the free-module digit-slot display).

**TEETH.** the A-C.2 battery's `B` column at all 13 instances
(`verification/c109_ac2_cell_check.py`, re-run green 2026-08-16); the exponent is exactly this
layer's output, minus the `L` priced digits.  `verification/c109_ac5_sweep_check.py`'s XCELL
rows (`cell = Q^B × sweep`) are the same identity read against the full cell count (124/0).

**NOTE on the unused binders.** `[Finite (resField Φ)]` is carried by the signed signature and
is not needed by the proof (the count goes through `Q = q ^ d` and `Finite (Res O N)`, which
`[Finite (ResidueField O)]` already supplies).  The binder is kept because the signature is
signed; `linter.unusedVariables` is silenced at the theorem only.

## Status

Sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's signed surface
is exactly `ht_box_slot_card`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. `|resField Φ| = q ^ d` at ENV-C1 -/

private theorem card_resField' [Finite (ResidueField O)] {Φ : Polynomial O} (hΦ : IsKey Φ) :
    Nat.card (resField Φ) = residueCard O ^ Φ.natDegree := by
  have hne : (Φ.map (IsLocalRing.residue O)) ≠ 0 := hΦ.irred.ne_zero
  haveI : Module.Finite (ResidueField O) (resField Φ) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  have hfr : Module.finrank (ResidueField O) (resField Φ) = Φ.natDegree := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne,
      hΦ.monic.natDegree_map (IsLocalRing.residue O)]
  rw [Module.natCard_eq_pow_finrank (K := ResidueField O), hfr]
  rfl

/-! ### 2. The floored residue predicate and its fibre count -/

/-- `divRes π h x` — the level-`N` class `x` is divisible by `π ^ h`. -/
private def divRes [Finite (ResidueField O)] (π : O) (h : ℕ) {N : ℕ} (x : Res O N) : Prop :=
  ∃ y : O, x = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (π ^ h * y)

private theorem divRes_mk_iff [Finite (ResidueField O)] (hπ : Irreducible π) {h N : ℕ}
    (hle : h ≤ N) (x : O) :
    divRes π h (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) x) ↔ π ^ h ∣ x := by
  constructor
  · rintro ⟨y, hy⟩
    have hmem : x - π ^ h * y ∈ (IsLocalRing.maximalIdeal O) ^ N := Ideal.Quotient.eq.1 hy
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hdvd : π ^ h ∣ x - π ^ h * y := (pow_dvd_pow π hle).trans hmem
    have : x = (x - π ^ h * y) + π ^ h * y := by ring
    rw [this]
    exact dvd_add hdvd ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

private theorem divRes_iff_resFactor [Finite (ResidueField O)] (hπ : Irreducible π) {h N : ℕ}
    (hle : h ≤ N) (x : Res O N) :
    divRes π h x ↔ resFactor (O := O) hle x = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) x
  rw [divRes_mk_iff hπ hle, resFactor_mk, Ideal.Quotient.eq_zero_iff_mem,
    hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- **the fibre count of one floored digit slot**: the classes mod `𝔪 ^ N` divisible by
`π ^ h` are the kernel of the truncation `Res O N → Res O h`, hence `q ^ (N − h)` of them. -/
private theorem card_divRes [Finite (ResidueField O)] (hπ : Irreducible π) {h N : ℕ}
    (hle : h ≤ N) :
    Nat.card {x : Res O N // divRes π h x} = residueCard O ^ (N - h) := by
  classical
  set f : Res O N →+ Res O h := (resFactor (O := O) hle).toAddMonoidHom with hf
  have hsurj : Function.Surjective f := resFactor_surjective hle
  have hcong : Nat.card {x : Res O N // divRes π h x} = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [divRes_iff_resFactor hπ hle]; exact Iff.rfl)
  have htot' : Nat.card (Res O N) = Nat.card f.ker * Nat.card (Res O h) := by
    have h1 : Nat.card ((Set.univ : Set (Res O N))) = Nat.card (Res O N) :=
      Nat.card_congr (Equiv.Set.univ _)
    have h2 : Nat.card ((Set.univ : Set (Res O h))) = Nat.card (Res O h) :=
      Nat.card_congr (Equiv.Set.univ _)
    have := card_preimage_of_surjective (A := Res O N) (B := Res O h) f hsurj Set.univ
    rw [Set.preimage_univ, h1, h2] at this
    exact this
  rw [card_res, card_res] at htot'
  have hsplit : residueCard O ^ N = residueCard O ^ (N - h) * residueCard O ^ h := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hsplit] at htot'
  rw [hcong]
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) h) htot'.symm)

/-! ### 3. NODE C.109-ii -/

set_option linter.unusedVariables false in
theorem ht_box_slot_card (hπ : Irreducible π) [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) [Finite (resField Φ)]
    (m N : ℕ) (P : ℕ → ℕ) (hP : ∀ j, j < m → P j < N) :
    Nat.card {c : Coeff O (m * Φ.natDegree) N //
        ∃ a : Fin (m * Φ.natDegree) → O, proj O (m * Φ.natDegree) N a = c ∧
          ∀ j, j < m → ((P j : ℕ) : ℕ∞) ≤ npHgt Φ (monicPoly a) j}
      = Nat.card (resField Φ) ^ (∑ j ∈ Finset.range m, (N - P j)) := by
  classical
  obtain ⟨E, hE⟩ := dev_box_bridge (O := O) hΦ.monic hΦ.pos m N
  -- the coefficients above `Φ.natDegree` of a development block vanish
  have hcoeff_high : ∀ (a : Fin (m * Φ.natDegree) → O) (j i : ℕ), Φ.natDegree ≤ i →
      (dev Φ (monicPoly a) j).coeff i = 0 := by
    intro a j i hi
    refine Polynomial.coeff_eq_zero_of_degree_lt ?_
    refine lt_of_lt_of_le (degree_dev_lt hΦ.monic hΦ.pos (monicPoly a) j) ?_
    rw [degree_eq_natDegree hΦ.monic.ne_zero]
    exact_mod_cast hi
  -- the predicate is the componentwise floor through the bridge
  have hiff : ∀ c : Coeff O (m * Φ.natDegree) N,
      (∃ a : Fin (m * Φ.natDegree) → O, proj O (m * Φ.natDegree) N a = c ∧
          ∀ j, j < m → ((P j : ℕ) : ℕ∞) ≤ npHgt Φ (monicPoly a) j)
        ↔ (∀ j : Fin m, ∀ i : Fin Φ.natDegree, divRes π (P (j : ℕ)) (E c j i)) := by
    intro c
    constructor
    · rintro ⟨a, rfl, hh⟩ j i
      rw [hE a j i]
      have := (le_gaussVal_iff hπ).1 (hh (j : ℕ) j.isLt) (i : ℕ)
      obtain ⟨y, hy⟩ := this
      exact ⟨y, by rw [hy]⟩
    · intro hcl
      obtain ⟨a, rfl⟩ := proj_surjective O (m * Φ.natDegree) N c
      refine ⟨a, rfl, ?_⟩
      intro j hj
      refine (le_gaussVal_iff hπ).2 fun i => ?_
      by_cases hi : i < Φ.natDegree
      · have hd := hcl ⟨j, hj⟩ ⟨i, hi⟩
        rw [hE a ⟨j, hj⟩ ⟨i, hi⟩] at hd
        exact (divRes_mk_iff hπ (hP j hj).le _).1 hd
      · rw [hcoeff_high a j i (Nat.not_lt.1 hi)]
        exact dvd_zero _
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  -- transport along the bridge, then split into blocks and slots
  rw [Nat.card_congr (E.subtypeEquiv
    (p := fun c => ∀ (j : Fin m) (i : Fin Φ.natDegree), divRes π (P (j : ℕ)) (E c j i))
    (q := fun g => ∀ (j : Fin m) (i : Fin Φ.natDegree), divRes π (P (j : ℕ)) (g j i))
    fun _ => Iff.rfl)]
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (j : Fin m) (b : Coeff O Φ.natDegree N) => ∀ i, divRes π (P (j : ℕ)) (b i)))]
  rw [Nat.card_pi]
  have hblock : ∀ j : Fin m,
      Nat.card {b : Coeff O Φ.natDegree N // ∀ i, divRes π (P (j : ℕ)) (b i)}
        = Nat.card (resField Φ) ^ (N - P (j : ℕ)) := by
    intro j
    rw [Nat.card_congr (Equiv.subtypePiEquivPi
      (p := fun (_ : Fin Φ.natDegree) (x : Res O N) => divRes π (P (j : ℕ)) x)), Nat.card_pi]
    rw [Finset.prod_congr rfl fun i _ => card_divRes hπ (hP (j : ℕ) j.isLt).le]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm,
      pow_mul, ← card_resField' hΦ]
  rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => N - P j) m]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_box_slot_card

end AxCheck
