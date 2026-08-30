/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG46

/-!
# Uniformity.ChapI.IFCG49 — [DTD 2026-08-30] the deep tail drained by KÖNIG + KRASNER:
`DeepTailDrainAt n` (every `n`) from ONE pointwise decision Prop and ONE null-count Prop

**Unit DTD.**  UDR's IFCG46 reduced the capstone's `a2` field to `DeepTailDrainAt n`
(`n ≥ 4`): the proportion of level-`N` classes that are undecided AND admit no shallow
split tends to `0`, over every complete DVR with finite residue field.  THIS file
discharges that reduction down to two DECOUPLED classical facts, by the compactness
skeleton of the classical proof:

* `undecidedSet` is **truncation-closed**: a decided truncation decides the class
  (`DecidedAt` is a ∀-lifts predicate), so undecided classes truncate to undecided
  classes (§2).
* **THE KÖNIG ENGINE** (§3): any truncation-closed family of nonempty class sets admits
  a single integral point lying in the family at EVERY level — finite levels, the
  infinite pigeonhole (`Finite.exists_infinite_fiber`) for extendable elements, and
  `IsPrecomplete` (adic completeness) for the limit.
* **THE ENVELOPE** (§4): run the engine on `{undecided} ∩ {discriminant ≢ 0 mod π^D}`.
  A surviving point would be undecided at every level yet have NONZERO discriminant
  resultant `Res(f, f')` — contradicting the pointwise Krasner Prop.  So beyond some
  level `N₀(D)` EVERY undecided class lies in the level-`D` discriminant-null cylinder,
  whose proportion at every level `N ≥ D` equals its level-`D` proportion
  (IFCG46 §0's exact fiber count).
* Hence `undecidedSeq O n N → 0` per `O` — and `deepTailSet ⊆ undecidedSet` (§5), so

      ★★★ `deepTailDrainAt_of_krasner_discNull :
             KrasnerAt n → DiscNullAt n → DeepTailDrainAt n`      -- EVERY n
      ★★★ `drainageAt_all_of_krasner_discNull :
             (∀ m ≥ 4, KrasnerAt m) → (∀ m ≥ 4, DiscNullAt m) → ∀ n, DrainageAt n`

The two named residual Props are the two PURE PHASES of the drain:

* `KrasnerAt n` — **field theory, no counting**: every `a : Fin n → O` with
  `Res(monicPoly a, (monicPoly a)') ≠ 0` is eventually decided (∃-form, per-point;
  quantitative Krasner / Okutsu–Montes completeness — textbook content).
* `DiscNullAt n` — **counting, no field theory**: the proportion of level-`D` classes
  whose discriminant resultant vanishes mod `π^D` tends to `0` (Serre's zero-measure
  lemma for the one explicit hypersurface `Res(f, f') = 0`; nonzero as a function on
  every DVR — any product of distinct monic linear factors witnesses it).

**Route decision** (recorded in `runs/wave-c/verdict_DTD.md`): the charge's deep-box
arm was refuted before designing — CN4's deep box has CONSTANT proportion
`q^(−m(m+1)/2)` in the level, so the recentring cascade would have to recurse through
the open `CellTypeScalingAt`, the open CN5 unramified bridge, and B.42.  The König
skeleton lands the whole reduction unconditionally, cite-free, with residuals strictly
simpler in species than the tail itself.

## Honesty

`DeepTailDrainAt`, `DrainageAt`, `DecidedAt`, `UndecidedAt`, `undecidedSeq` are consumed
byte-unchanged; nothing is weakened.  The residual Props quantify over EVERY complete
DVR with finite residue field (`O : Type`, the corpus's ZcURLim universe convention) —
uniform in `q` and per-`n`.  The drain itself is a per-`O` Tendsto, exactly as the
capstone consumes it.  Axioms: Lean core only.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.IFCG49

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction

/-! ## §1 The class discriminant

The discriminant resultant `Res(f, f')` of a monic class, read intrinsically at each
finite level: `classPoly c` is the monic polynomial over `O ⧸ 𝔪^N` with coefficient
vector `c`, and `classDisc c` its resultant against its derivative.  Because the
resultant is a polynomial (Sylvester determinant) in the coefficients, it commutes with
the level projection (`classDisc_proj`) — so the vanishing condition is a level-`D`
cylinder condition on integral points. -/

section Disc

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The monic level-`N` polynomial of a class (the class-level `monicPoly`). -/
noncomputable def classPoly {n N : ℕ} (c : Coeff O n N) : Polynomial (Res O N) :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

theorem classPoly_proj {n N : ℕ} (a : Fin n → O) :
    classPoly (proj O n N a) = (monicPoly a).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  simp only [classPoly, monicPoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- The level-`N` **discriminant resultant** `Res(f, f')` of a class. -/
noncomputable def classDisc {n N : ℕ} (c : Coeff O n N) : Res O N :=
  Polynomial.resultant (classPoly c) (derivative (classPoly c)) n (n - 1)

/-- The class discriminant is the projected integral discriminant: vanishing mod `π^N`
is a cylinder condition. -/
theorem classDisc_proj {n N : ℕ} (a : Fin n → O) :
    classDisc (proj O n N a)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
          (Polynomial.resultant (monicPoly a) (derivative (monicPoly a)) n (n - 1)) := by
  unfold classDisc
  rw [classPoly_proj, Polynomial.derivative_map, Polynomial.resultant_map_map]

end Disc

section DiscSet

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The discriminant-null classes at level `D`. -/
def discNullSet (n D : ℕ) : Set (Coeff O n D) := {c | classDisc c = 0}

/-- The discriminant-null proportion at level `D`. -/
noncomputable def discNullSeq (n D : ℕ) : ℝ :=
  (Nat.card (discNullSet O n D) : ℝ) / (residueCard O : ℝ) ^ (n * D)

theorem discNullSeq_nonneg (n D : ℕ) : 0 ≤ discNullSeq O n D :=
  div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le

end DiscSet

/-! ## §2 Truncation monotonicity

`DecidedAt` is a ∀-lifts predicate, and every lift of a class lifts its truncation
(`coeffFactor_proj` is `rfl`) — so decidedness propagates UP levels from a truncation,
and undecidedness propagates DOWN onto truncations.  Together with the (lift-mediated)
truncation composition, these are the whole order theory the König engine needs. -/

section Mono

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Truncations compose (mediated by a lift; `coeffFactor_proj` is `rfl`). -/
theorem coeffFactor_coeffFactor {n K N M : ℕ} (h₁ : K ≤ N) (h₂ : N ≤ M) (c : Coeff O n M) :
    coeffFactor (O := O) n h₁ (coeffFactor (O := O) n h₂ c)
      = coeffFactor (O := O) n (h₁.trans h₂) c := by
  obtain ⟨a, rfl⟩ := proj_surjective O n M c
  rfl

/-- A decided truncation decides the class. -/
theorem decidedAt_of_coeffFactor {n N M : ℕ} (h : N ≤ M) {σ : FactorizationType}
    {c : Coeff O n M} (hd : DecidedAt O n σ N (coeffFactor (O := O) n h c)) :
    DecidedAt O n σ M c := by
  intro a ha
  exact hd a (by rw [← ha]; rfl)

/-- Undecided classes truncate to undecided classes. -/
theorem undecidedAt_coeffFactor {n N M : ℕ} (h : N ≤ M) {c : Coeff O n M}
    (hc : UndecidedAt O n M c) : UndecidedAt O n N (coeffFactor (O := O) n h c) :=
  fun σ hσ => hc σ (decidedAt_of_coeffFactor h hσ)

end Mono

/-! ## §3 THE KÖNIG ENGINE

Finite levels + nested truncations ⟹ a single integral point.  `extSet S N` collects
the level-`N` members with family witnesses above them at EVERY level; the infinite
pigeonhole (`Finite.exists_infinite_fiber` over the levels) shows extendable members
exist and extend one step at a time, a `Nat.rec` chain threads them compatibly, and
adic completeness (`IsPrecomplete.prec`) resolves the compatible chain into a point of
`O^n` lying in the family at every level. -/

section Konig

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

variable {n : ℕ}

/-- A level-indexed family of class sets is **truncation-closed** when every member
truncates to a member at every lower level. -/
def TruncClosed (S : ∀ N, Set (Coeff O n N)) : Prop :=
  ∀ {N M : ℕ} (h : N ≤ M), ∀ c ∈ S M, coeffFactor (O := O) n h c ∈ S N

/-- The **extendable** members at level `N`: members with family witnesses truncating
onto them from every higher level. -/
def extSet (S : ∀ N, Set (Coeff O n N)) (N : ℕ) : Set (Coeff O n N) :=
  {c | c ∈ S N ∧ ∀ M (h : N ≤ M), ∃ c' ∈ S M, coeffFactor (O := O) n h c' = c}

/-- Extendable members exist at every level (infinite pigeonhole over the levels). -/
theorem extSet_nonempty {S : ∀ N, Set (Coeff O n N)} (hcl : TruncClosed S)
    (hne : ∀ N, (S N).Nonempty) (N : ℕ) : (extSet S N).Nonempty := by
  classical
  choose w hw using hne
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => coeffFactor (O := O) n (Nat.le_add_right N k) (w (N + k)))
  have hfib := Set.infinite_coe_iff.mp hc
  obtain ⟨k₀, hk₀, -⟩ := hfib.exists_gt 0
  have hk₀' : coeffFactor (O := O) n (Nat.le_add_right N k₀) (w (N + k₀)) = c := hk₀
  refine ⟨c, ?_, ?_⟩
  · rw [← hk₀']
    exact hcl _ _ (hw _)
  · intro M hM
    obtain ⟨k, hk, hkM⟩ := hfib.exists_gt M
    have hk' : coeffFactor (O := O) n (Nat.le_add_right N k) (w (N + k)) = c := hk
    have hMk : M ≤ N + k := by omega
    exact ⟨coeffFactor (O := O) n hMk (w (N + k)), hcl hMk _ (hw _),
      by rw [coeffFactor_coeffFactor]; exact hk'⟩

/-- Every extendable member has an extendable child one level up. -/
theorem extSet_step {S : ∀ N, Set (Coeff O n N)} (hcl : TruncClosed S) {N : ℕ}
    {c : Coeff O n N} (hc : c ∈ extSet S N) :
    ∃ d ∈ extSet S (N + 1), coeffFactor (O := O) n (Nat.le_succ N) d = c := by
  classical
  obtain ⟨hcS, hext⟩ := hc
  choose w hwS hwc using fun k : ℕ => hext (N + 1 + k) (by omega)
  obtain ⟨d, hd⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => coeffFactor (O := O) n (Nat.le_add_right (N + 1) k) (w k))
  have hfib := Set.infinite_coe_iff.mp hd
  obtain ⟨k₀, hk₀, -⟩ := hfib.exists_gt 0
  have hk₀' : coeffFactor (O := O) n (Nat.le_add_right (N + 1) k₀) (w k₀) = d := hk₀
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · rw [← hk₀']
    exact hcl _ _ (hwS k₀)
  · intro M hM
    obtain ⟨k, hk, hkM⟩ := hfib.exists_gt M
    have hk' : coeffFactor (O := O) n (Nat.le_add_right (N + 1) k) (w k) = d := hk
    have hMk : M ≤ N + 1 + k := by omega
    exact ⟨coeffFactor (O := O) n hMk (w k), hcl hMk _ (hwS k),
      by rw [coeffFactor_coeffFactor]; exact hk'⟩
  · rw [← hk₀', coeffFactor_coeffFactor]
    exact hwc k₀

/-- ★★ **THE KÖNIG POINT** — a truncation-closed family of nonempty class sets contains
the projections of a single integral point at every level. -/
theorem exists_point_of_truncClosed {S : ∀ N, Set (Coeff O n N)} (hcl : TruncClosed S)
    (hne : ∀ N, (S N).Nonempty) : ∃ a : Fin n → O, ∀ N, proj O n N a ∈ S N := by
  classical
  -- the extendable chain
  have hstep : ∀ N (c : {c : Coeff O n N // c ∈ extSet S N}),
      ∃ d : {d : Coeff O n (N + 1) // d ∈ extSet S (N + 1)},
        coeffFactor (O := O) n (Nat.le_succ N) d.1 = c.1 := by
    intro N c
    obtain ⟨d, hd, hdc⟩ := extSet_step hcl c.2
    exact ⟨⟨d, hd⟩, hdc⟩
  choose step hstepc using hstep
  obtain ⟨c₀, hc₀⟩ := extSet_nonempty hcl hne 0
  let ch : (N : ℕ) → {c : Coeff O n N // c ∈ extSet S N} :=
    fun N => Nat.rec ⟨c₀, hc₀⟩ (fun M ih => step M ih) N
  have hch_succ : ∀ N, coeffFactor (O := O) n (Nat.le_succ N) (ch (N + 1)).1 = (ch N).1 :=
    fun N => hstepc N (ch N)
  have hch : ∀ {K M : ℕ} (h : K ≤ M), coeffFactor (O := O) n h (ch M).1 = (ch K).1 := by
    intro K M h
    induction M, h using Nat.le_induction with
    | base =>
        obtain ⟨a, ha⟩ := proj_surjective O n K (ch K).1
        rw [← ha]; rfl
    | succ M hKM ih =>
        have h2 : coeffFactor (O := O) n (hKM.trans (Nat.le_succ M)) (ch (M + 1)).1
            = (ch K).1 := by
          rw [← coeffFactor_coeffFactor hKM (Nat.le_succ M), hch_succ M, ih]
        exact h2
  -- lifts of the chain, coordinatewise Cauchy, the adic limit
  choose b hb using fun N => proj_surjective O n N (ch N).1
  have hcau : ∀ i : Fin n, ∀ {m M : ℕ}, m ≤ M →
      b m i ≡ b M i [SMOD ((maximalIdeal O) ^ m • ⊤ : Ideal O)] := by
    intro i m M h
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    have hpp : proj O n m (b m) = proj O n m (b M) := by
      have h1 : coeffFactor (O := O) n h (proj O n M (b M)) = proj O n m (b M) := rfl
      rw [hb m, ← h1, hb M, hch h]
    have hi : Ideal.Quotient.mk ((maximalIdeal O) ^ m) (b m i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ m) (b M i) := congrFun hpp i
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hi
  choose L hL using fun i : Fin n =>
    IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal O) O)
      (f := fun N => b N i) (fun {m M} h => hcau i h)
  refine ⟨L, fun N => ?_⟩
  have hproj : proj O n N L = (ch N).1 := by
    funext i
    have h1 := hL i N
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at h1
    have h3 : L i - b N i ∈ (maximalIdeal O) ^ N := by
      have h4 := neg_mem h1
      rwa [neg_sub] at h4
    have h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (L i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (b N i) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr h3
    show Ideal.Quotient.mk ((maximalIdeal O) ^ N) (L i) = (ch N).1 i
    rw [h2]
    exact congrFun (hb N) i
  rw [hproj]
  exact (ch N).2.1

end Konig

/-! ## §4 The envelope: König + pointwise Krasner ⟹ the eventual discriminant cylinder

Run the engine on the SURVIVOR family — undecided classes whose level-`D` discriminant
is nonzero.  A König point of the family would be undecided at every level yet
separable, contradicting the pointwise Krasner hypothesis; so the family dies at some
level `N₀(D)`, and beyond it every undecided class lies inside the level-`D`
discriminant-null cylinder, whose proportion never exceeds `discNullSeq O n D`
(the exact fiber law, IFCG46 §0). -/

section Envelope

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

variable (O) in
/-- The König survivor family at discriminant level `D`: undecided classes whose
level-`D` discriminant is nonzero (the `D ≤ N` guard binds a proof, so the family is
defined at every level). -/
def survivorSet (n D N : ℕ) : Set (Coeff O n N) :=
  {c | UndecidedAt O n N c ∧ ∀ h : D ≤ N, classDisc (coeffFactor (O := O) n h c) ≠ 0}

theorem truncClosed_survivorSet (n D : ℕ) : TruncClosed (survivorSet O n D) := by
  intro N M h c hc
  refine ⟨undecidedAt_coeffFactor h hc.1, fun hD => ?_⟩
  rw [coeffFactor_coeffFactor]
  exact hc.2 (hD.trans h)

/-- ★ **The König–Krasner contradiction**: no survivor family is everywhere nonempty. -/
theorem not_forall_survivor_nonempty {n : ℕ}
    (hK : ∀ a : Fin n → O,
      Polynomial.resultant (monicPoly a) (derivative (monicPoly a)) n (n - 1) ≠ 0 →
      ∃ (N : ℕ) (σ : FactorizationType), DecidedAt O n σ N (proj O n N a))
    (D : ℕ) : ¬ ∀ N, (survivorSet O n D N).Nonempty := by
  intro hne
  obtain ⟨a, ha⟩ := exists_point_of_truncClosed (truncClosed_survivorSet n D) hne
  have hd : classDisc (proj O n D a) ≠ 0 := (ha D).2 le_rfl
  have hres : Polynomial.resultant (monicPoly a) (derivative (monicPoly a)) n (n - 1) ≠ 0 := by
    intro h0
    apply hd
    rw [classDisc_proj, h0, map_zero]
  obtain ⟨N, σ, hdec⟩ := hK a hres
  exact (ha N).1 σ hdec

/-- The eventual envelope: beyond the survivor-death level, every undecided class lies
in the level-`D` discriminant-null cylinder. -/
theorem undecidedSet_subset_discNull {n D N₀ : ℕ}
    (hemp : survivorSet O n D N₀ = ∅) {N : ℕ} (hN : N₀ ≤ N) (hDN : D ≤ N) :
    undecidedSet O n N ⊆ (coeffFactor (O := O) n hDN) ⁻¹' (discNullSet O n D) := by
  intro c hc
  by_contra hnull
  have hcs : c ∈ survivorSet O n D N := ⟨hc, fun _ h0 => hnull h0⟩
  have h2 := truncClosed_survivorSet n D hN _ hcs
  rw [hemp] at h2
  exact h2

/-- ★ The envelope's proportion bound: beyond the survivor-death level, the undecided
proportion is at most the level-`D` discriminant-null proportion. -/
theorem undecidedSeq_le_discNullSeq {n D N₀ : ℕ}
    (hemp : survivorSet O n D N₀ = ∅) {N : ℕ} (hN : N₀ ≤ N) (hDN : D ≤ N) :
    undecidedSeq O n N ≤ discNullSeq O n D := by
  have hsub := undecidedSet_subset_discNull hemp hN hDN
  have hcard : undecidedCount O n N
      ≤ Nat.card (discNullSet O n D) * residueCard O ^ (n * (N - D)) := by
    calc undecidedCount O n N
        ≤ Nat.card ((coeffFactor (O := O) n hDN) ⁻¹' (discNullSet O n D)) :=
          Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective _)
      _ = Nat.card (discNullSet O n D) * residueCard O ^ (n * (N - D)) :=
          IFCG46.card_preimage_coeffFactor_eq n hDN (discNullSet O n D)
  have hexp : n * (N - D) + n * D = n * N := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hDN]
  have hℕ : undecidedCount O n N * residueCard O ^ (n * D)
      ≤ Nat.card (discNullSet O n D) * residueCard O ^ (n * N) := by
    calc undecidedCount O n N * residueCard O ^ (n * D)
        ≤ (Nat.card (discNullSet O n D) * residueCard O ^ (n * (N - D)))
            * residueCard O ^ (n * D) := Nat.mul_le_mul_right _ hcard
      _ = Nat.card (discNullSet O n D) * residueCard O ^ (n * N) := by
          rw [mul_assoc, ← pow_add, hexp]
  rw [undecidedSeq, discNullSeq, div_le_div_iff₀ (qpow_pos _) (qpow_pos _)]
  exact_mod_cast hℕ

/-- ★★ **THE PER-`O` DRAIN** — pointwise Krasner decision + the discriminant null-count
⟹ the σ-free undecided proportion drains, over this `O`. -/
theorem tendsto_undecidedSeq_zero_of_krasner_discNull {n : ℕ}
    (hK : ∀ a : Fin n → O,
      Polynomial.resultant (monicPoly a) (derivative (monicPoly a)) n (n - 1) ≠ 0 →
      ∃ (N : ℕ) (σ : FactorizationType), DecidedAt O n σ N (proj O n N a))
    (hZ : Tendsto (discNullSeq O n) atTop (𝓝 0)) :
    Tendsto (undecidedSeq O n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨D₀, hD₀⟩ := (Metric.tendsto_atTop.mp hZ) ε hε
  have hDε : discNullSeq O n D₀ < ε := by
    have h1 := hD₀ D₀ le_rfl
    rwa [Real.dist_0_eq_abs, abs_of_nonneg (discNullSeq_nonneg O n D₀)] at h1
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, survivorSet O n D₀ N₀ = ∅ := by
    by_contra hall
    exact not_forall_survivor_nonempty hK D₀
      (fun N => Set.nonempty_iff_ne_empty.mpr (fun h => hall ⟨N, h⟩))
  refine ⟨max N₀ D₀, fun N hN => ?_⟩
  rw [Real.dist_0_eq_abs, abs_of_nonneg (IFCG46.undecidedSeq_nonneg n N)]
  exact lt_of_le_of_lt
    (undecidedSeq_le_discNullSeq hN₀ (le_trans (le_max_left _ _) hN)
      (le_trans (le_max_right _ _) hN)) hDε

end Envelope

/-! ## §5 The named residual Props and the capstone feed -/

/-- ★ **THE FIELD-THEORY RESIDUAL** `KrasnerAt n` — pointwise, per-`O`: every integral
coefficient vector whose monic polynomial has nonzero discriminant resultant
`Res(f, f')` is DECIDED at some finite level.  Quantitative Krasner / Okutsu–Montes
completeness in its weakest form (∃-level, single point, no rate, no uniformity in
`a`).  No counting occurs.  Textbook content — citable under owner gate (b) if the
in-corpus proof stalls. -/
def KrasnerAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ a : Fin n → O,
      Polynomial.resultant (monicPoly a) (Polynomial.derivative (monicPoly a)) n (n - 1) ≠ 0 →
      ∃ (N : ℕ) (σ : FactorizationType), DecidedAt O n σ N (proj O n N a)

/-- ★ **THE COUNTING RESIDUAL** `DiscNullAt n` — per-`O`: the proportion of level-`D`
classes whose discriminant resultant vanishes mod `π^D` tends to `0` as `D → ∞`.
Serre's zero-measure lemma for the ONE explicit hypersurface `Res(f, f') = 0` (nonzero
as a polynomial function on every DVR: products of distinct monic linear factors
witness nonvanishing — every DVR is infinite).  No decidedness, no factorization types
occur. -/
def DiscNullAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    Tendsto (discNullSeq O n) atTop (𝓝 0)

section Tail

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The deep collision tail sits inside the undecided set — proportionwise. -/
theorem deepTailSeq_le_undecidedSeq (π : O) (n N : ℕ) :
    IFCG46.deepTailSeq π n N ≤ undecidedSeq O n N := by
  have hsub : IFCG46.deepTailSet π n N ⊆ undecidedSet O n N := fun c hc => hc.1
  have hcard : Nat.card (IFCG46.deepTailSet π n N) ≤ undecidedCount O n N :=
    Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective _)
  rw [IFCG46.deepTailSeq, undecidedSeq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (qpow_pos _).le

end Tail

/-- ★★ The σ-free drain Prop itself (IFCG45's carrier), from the two residuals. -/
theorem undecidedDrainAt_of_krasner_discNull {n : ℕ} (hK : KrasnerAt n) (hZ : DiscNullAt n) :
    IFCG45.UndecidedDrainAt n := by
  intro O _ _ _ _ _
  exact tendsto_undecidedSeq_zero_of_krasner_discNull (hK O) (hZ O)

/-- ★★★ **THE TAIL DRAINS** — `KrasnerAt n` + `DiscNullAt n` discharge UDR's named
remainder `DeepTailDrainAt n`, at EVERY degree `n` (not only the consumed `n ≥ 4`). -/
theorem deepTailDrainAt_of_krasner_discNull {n : ℕ} (hK : KrasnerAt n) (hZ : DiscNullAt n) :
    IFCG46.DeepTailDrainAt n := by
  intro O _ _ _ _ _ π _
  exact squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le)
    (fun N => deepTailSeq_le_undecidedSeq π n N)
    (tendsto_undecidedSeq_zero_of_krasner_discNull (hK O) (hZ O))

/-- ★★★ **THE CAPSTONE FEED** — the ENTIRE `a2` field (`∀ n, DrainageAt n`) from the two
named residuals at degrees ≥ 4 alone, through UDR's reduction (IFCG46) and DRN's
dissection (IFCG45). -/
theorem drainageAt_all_of_krasner_discNull
    (hK : ∀ m, 4 ≤ m → KrasnerAt m) (hZ : ∀ m, 4 ≤ m → DiscNullAt m) :
    ∀ n, DrainageAt n :=
  IFCG46.drainageAt_all_of_deepTailDrain
    (fun m hm => deepTailDrainAt_of_krasner_discNull (hK m hm) (hZ m hm))

/-! ## §6 Nonvacuity witnesses at degree 1

Both residual Props hold at `n = 1` — machine-checking the definitions' conventions
(the resultant's formal degrees, the decision target, the level normalization): linear
classes are decided inert-⟨{(1,1)}⟩ at level 1 (CN-21 through IFCG46's packaging), and
the linear discriminant resultant is the UNIT `1`, so the null set is empty at every
level ≥ 1. -/

theorem krasnerAt_one : KrasnerAt 1 := by
  intro O _ _ _ _ _ a _
  refine ⟨1, ⟨{(1, 1)}⟩, IFCG46.decidedAt_of_irreducible_residue one_ne_zero one_ne_zero ?_⟩
  have hmm : ((monicPoly a).map (residue O)).Monic := (monicPoly_monic a).map _
  refine hmm.irreducible_of_degree_eq_one ?_
  rw [Polynomial.degree_eq_natDegree hmm.ne_zero, (monicPoly_monic a).natDegree_map,
    monicPoly_natDegree, Nat.cast_one]

theorem discNullAt_one : DiscNullAt 1 := by
  intro O _ _ _ _ _
  have hempty : ∀ D, 1 ≤ D → discNullSet O 1 D = ∅ := by
    intro D hD
    rw [Set.eq_empty_iff_forall_notMem]
    intro c hc
    have hder : derivative (classPoly c) = 1 := by
      simp [classPoly]
    have hdisc : classDisc c = 1 := by
      unfold classDisc
      rw [hder]
      simp
    have hc0 : (1 : Res O D) = 0 := by
      rw [← hdisc]
      exact hc
    have hmem : (1 : O) ∈ (maximalIdeal O) ^ D := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
      exact hc0
    have htop : ((maximalIdeal O) ^ D : Ideal O) = ⊤ := (Ideal.eq_top_iff_one _).mpr hmem
    have hle : ((maximalIdeal O) ^ D : Ideal O) ≤ maximalIdeal O :=
      Ideal.pow_le_self (by omega)
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.mp hle)
  have hzero : ∀ D, 1 ≤ D → discNullSeq O 1 D = 0 := by
    intro D hD
    rw [discNullSeq, hempty D hD]
    simp
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with D hD
  exact (hzero D hD).symm

end Uniformity.Density.IFCG49

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG49.classDisc_proj
#print axioms Uniformity.Density.IFCG49.coeffFactor_coeffFactor
#print axioms Uniformity.Density.IFCG49.undecidedAt_coeffFactor
#print axioms Uniformity.Density.IFCG49.exists_point_of_truncClosed
#print axioms Uniformity.Density.IFCG49.not_forall_survivor_nonempty
#print axioms Uniformity.Density.IFCG49.undecidedSeq_le_discNullSeq
#print axioms Uniformity.Density.IFCG49.tendsto_undecidedSeq_zero_of_krasner_discNull
#print axioms Uniformity.Density.IFCG49.deepTailSeq_le_undecidedSeq
#print axioms Uniformity.Density.IFCG49.undecidedDrainAt_of_krasner_discNull
#print axioms Uniformity.Density.IFCG49.deepTailDrainAt_of_krasner_discNull
#print axioms Uniformity.Density.IFCG49.drainageAt_all_of_krasner_discNull
#print axioms Uniformity.Density.IFCG49.krasnerAt_one
#print axioms Uniformity.Density.IFCG49.discNullAt_one
