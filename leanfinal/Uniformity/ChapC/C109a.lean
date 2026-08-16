/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData
import Uniformity.ChapB.B03
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapB.B10

/-!
# Uniformity.ChapC.C109a — the level-`N` development ↔ coefficient-box bridge

**Chapter C, NODE C.109a** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §11, the HT
count layer), **ENV-C1** (pure algebra: no completeness, no finiteness).
`[signed: A-C.2, 2026-08-16 — NEW node, DECISION D-C.2-BRIDGE]`.

For monic `Φ` of positive degree, the level-`N` coefficient box of monic degree-`m·d`
polynomials (`d = Φ.natDegree`) is in bijection with `m`-tuples of level-`N` degree-`< d`
blocks, THROUGH the `Φ`-adic development:

`Coeff O (m * d) N ≃ (Fin m → Coeff O d N)`,

the forward map reading, **at any lift**, the level-`N` classes of the coefficient vectors of
`dev Φ (monicPoly a) j`.  Level-`N` well-definedness of `dev` (monic division preserves
coefficientwise congruence mod `𝔪 ^ N` — B.10's content one level up) is PART of the claim:
the componentwise spec at an arbitrary lift is contradictory without it.

This is the node the C.109 refutation record named as C.109's real cost (`C109_REFUTATION.
lean.txt`, "A second, deeper failure": *"formalizing it needs the level-`N` development ↔
coefficient-box bridge … which does not exist in `leanfinal` yet"*), and it is where
`EFF.W12.23`'s *"Monic division gives the UNIQUE `Φ`-adic development … `f ↦ (a_j)_{j<m}` is a
bijection"* lands as a reusable carrier.

## Why the statement is an `∃`, and what pins the equivalence

The signed form is `∃ E : Coeff O (m*d) N ≃ (Fin m → Coeff O d N), <componentwise spec>` — a
single `Prop`, no data axiom.  The spec

`E (proj O (m*d) N a) j i = Ideal.Quotient.mk (𝔪 ^ N) ((dev Φ (monicPoly a) j).coeff i)`

quantifies over **every** integral lift `a`, so it simultaneously (i) pins `E` uniquely (`proj`
is surjective) and (ii) asserts that the right-hand side depends on `a` only through
`proj O (m*d) N a`, which is exactly level-`N` well-definedness of the development.

## Proof route (the three moves, no finiteness anywhere)

The equivalence is built with an explicit two-sided inverse — the counting shortcut
("injective + equal cardinality") is unavailable here on purpose: ENV-C1 has no
`Finite (ResidueField O)`, and `Coeff O n N` is genuinely infinite over a DVR with infinite
residue field.

1. **Forward, well defined.**  `G a j i = [ (dev Φ (monicPoly a) j).coeff i ]`.  If
   `proj a = proj a'` then `monicPoly a` and `monicPoly a'` have the same image in
   `(O ⧸ 𝔪 ^ N)[X]`, and B.10 (`dev_congr`, at the uniformizer supplied by the DVR) transports
   that to every development coefficient.  `F` is `G` composed with a chosen lift; the spec
   `F (proj a) = G a` is precisely well-definedness.
2. **Backward, by assembly.**  Lift each block to `β j : Fin d → O` and form
   `asmPoly Φ m β = ∑_{j ≤ m} devFam m β j * Φ ^ j` with `devFam m β j = blockPoly (β j)` for
   `j < m` and `= 1` at `j = m`.  It is monic of degree `m·d` (the tail has degree `< m·d`), so
   it is `monicPoly` of its own coefficient vector, and B.06 (`dev_unique`) reads its
   development back off the assembly: `dev Φ (asmPoly Φ m β) j = blockPoly (β j)` for `j < m`.
3. **The two round trips.**  `F ∘ H = id` is move 2 plus `blockPoly_coeff`.  `H ∘ F = id` uses
   B.05 (`sum_dev_eq`, at `k = m + 1`) to write `monicPoly a` as its own assembly, plus
   `dev_top` — for `f` monic of degree `k·d` the top development coefficient `dev Φ f k` is
   `1` — so that the two assemblies agree term by term mod `𝔪 ^ N`.

**DEPENDS.** B.02–B.06 (`dev`, the development calculus: `degree_dev_lt`, `sum_dev_eq`,
`dev_unique`) · B.10 (`dev_congr` — the congruence leg) · landed `Coeff`/`proj`/`monicPoly`
(`Uniformity/Density/LocalData.lean`).

**SOURCE.** `EFF.W12.23` (the development display + the bijection sentence, verbatim); the
C.109 refutation record (`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`).

**TEETH.** `verification/c109_ac2_cell_check.py` computes every LHS through exactly this bridge
(dev-blocks over `ℤ/p^N`) — 13 instances green.

## Status

Sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's signed surface
is exactly `dev_box_bridge`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf IsLocalRing
  IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ### 1. Block polynomials: the degree-`< d` window read off a coefficient vector -/

/-- the degree-`< d` polynomial with coefficient vector `c` — the tail of `monicPoly`. -/
private noncomputable def blockPoly {d : ℕ} (c : Fin d → O) : Polynomial O :=
  ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem monicPoly_eq_add {n : ℕ} (a : Fin n → O) :
    monicPoly a = X ^ n + blockPoly a := rfl

private theorem degree_blockPoly_lt {d : ℕ} (c : Fin d → O) :
    (blockPoly c).degree < (d : WithBot ℕ) := by
  have h := degree_tail_lt c
  rwa [degree_X_pow] at h

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem blockPoly_coeff {d : ℕ} (c : Fin d → O) (k : ℕ) :
    (blockPoly c).coeff k = if h : k < d then c ⟨k, h⟩ else 0 := by
  classical
  simp only [blockPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases h : k < d
  · rw [dif_pos h, Finset.sum_eq_single (⟨k, h⟩ : Fin d)]
    · simp
    · intro b _ hb
      exact if_neg fun hk => hb (Fin.ext hk.symm)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => if_neg fun hk => ?_
    exact h (hk ▸ i.isLt)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem monicPoly_coeff_of_lt {n : ℕ} (a : Fin n → O) {k : ℕ} (hk : k < n) :
    (monicPoly a).coeff k = a ⟨k, hk⟩ := by
  rw [monicPoly_eq_add, coeff_add, coeff_X_pow, blockPoly_coeff, dif_pos hk,
    if_neg (Nat.ne_of_lt hk), zero_add]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- a monic polynomial of degree `n` is `monicPoly` of its own coefficient vector. -/
private theorem monicPoly_coeffFun {n : ℕ} {g : Polynomial O} (hg : g.Monic)
    (hn : g.natDegree = n) :
    monicPoly (fun i : Fin n => g.coeff (i : ℕ)) = g := by
  refine Polynomial.ext fun k => ?_
  rw [monicPoly_eq_add, coeff_add, coeff_X_pow, blockPoly_coeff]
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [dif_pos hk, if_neg (Nat.ne_of_lt hk), zero_add]
  · subst hk
    rw [dif_neg (lt_irrefl k), if_pos rfl, add_zero]
    exact (hn ▸ hg.coeff_natDegree).symm
  · rw [dif_neg (Nat.not_lt.2 hk.le), if_neg (Nat.ne_of_gt hk), add_zero]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ### 2. Degree bookkeeping for `∑_{j < m} A j · Φ ^ j` -/

private theorem degree_sum_mul_pow_lt {Φ : Polynomial O} (hΦm : Φ.Monic)
    (A : ℕ → Polynomial O) (hA : ∀ j, (A j).degree < Φ.degree) (m : ℕ) :
    (∑ j ∈ Finset.range m, A j * Φ ^ j).degree < (Φ ^ m).degree := by
  have hΦ0 : Φ ≠ 0 := hΦm.ne_zero
  have hdegΦ : Φ.degree = (Φ.natDegree : WithBot ℕ) := degree_eq_natDegree hΦ0
  have hdegpow : ∀ k : ℕ, (Φ ^ k : Polynomial O).degree = ((k * Φ.natDegree : ℕ) : WithBot ℕ) := by
    intro k
    rw [degree_eq_natDegree (hΦm.pow k).ne_zero, hΦm.natDegree_pow]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [hdegpow m, Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (m * Φ.natDegree))]
  intro j hj
  have hjm : j < m := Finset.mem_range.1 hj
  rcases eq_or_ne (A j) 0 with h0 | h0
  · rw [h0, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hAj : (A j).natDegree < Φ.natDegree := by
      have := hA j
      rw [degree_eq_natDegree h0, hdegΦ] at this
      exact_mod_cast this
    rw [degree_mul, degree_eq_natDegree h0, hdegpow j, ← Nat.cast_add]
    refine Nat.cast_lt.2 ?_
    calc (A j).natDegree + j * Φ.natDegree
        < Φ.natDegree + j * Φ.natDegree := by omega
      _ = (j + 1) * Φ.natDegree := by ring
      _ ≤ m * Φ.natDegree := Nat.mul_le_mul_right _ hjm

/-! ### 3. The top development coefficient of a monic polynomial of degree `k · d` -/

private theorem dev_top {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree) :
    ∀ (k : ℕ) (f : Polynomial O), f.Monic → f.natDegree = k * Φ.natDegree → dev Φ f k = 1 := by
  have hΦ0 : Φ ≠ 0 := hΦm.ne_zero
  have hdegΦ : Φ.degree = (Φ.natDegree : WithBot ℕ) := degree_eq_natDegree hΦ0
  intro k
  induction k with
  | zero =>
    intro f hf hdeg
    have hf1 : f = 1 := hf.natDegree_eq_zero.1 (by simpa using hdeg)
    subst hf1
    change (1 : Polynomial O) %ₘ Φ = 1
    refine (modByMonic_eq_self_iff hΦm).2 ?_
    rw [degree_one, hdegΦ]
    exact_mod_cast hΦd
  | succ k ih =>
    intro f hf hdeg
    have hf0 : f ≠ 0 := hf.ne_zero
    have hle : Φ.degree ≤ f.degree := by
      rw [hdegΦ, degree_eq_natDegree hf0, hdeg]
      exact_mod_cast Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    have hmono : (f /ₘ Φ).Monic := by
      unfold Polynomial.Monic
      rw [leadingCoeff_divByMonic_of_monic hΦm hle]
      exact hf
    have hdeg' : (f /ₘ Φ).natDegree = k * Φ.natDegree := by
      rw [natDegree_divByMonic f hΦm, hdeg, Nat.succ_mul, Nat.add_sub_cancel]
    change dev Φ (f /ₘ Φ) k = 1
    exact ih _ hmono hdeg'

/-! ### 4. The assembly of a block family into a monic polynomial -/

/-- the development family of a block family: `blockPoly (β j)` below the top, `1` at the top,
`0` above (the shape `dev_unique` consumes). -/
private noncomputable def devFam {d : ℕ} (m : ℕ) (β : Fin m → Fin d → O) : ℕ → Polynomial O :=
  fun j => if h : j < m then blockPoly (β ⟨j, h⟩) else if j = m then 1 else 0

/-- the assembly `Φ ^ m + ∑_{j < m} blockPoly (β j) · Φ ^ j`, written as one range sum. -/
private noncomputable def asmPoly (Φ : Polynomial O) {d : ℕ} (m : ℕ) (β : Fin m → Fin d → O) :
    Polynomial O :=
  ∑ j ∈ Finset.range (m + 1), devFam m β j * Φ ^ j

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem devFam_of_lt {d m : ℕ} (β : Fin m → Fin d → O) {j : ℕ} (hj : j < m) :
    devFam m β j = blockPoly (β ⟨j, hj⟩) := dif_pos hj

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem devFam_top {d m : ℕ} (β : Fin m → Fin d → O) : devFam m β m = 1 := by
  rw [devFam, dif_neg (lt_irrefl m), if_pos rfl]

private theorem degree_devFam_lt {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (β : Fin m → Fin Φ.natDegree → O) (j : ℕ) : (devFam m β j).degree < Φ.degree := by
  have hdegΦ : Φ.degree = (Φ.natDegree : WithBot ℕ) := degree_eq_natDegree hΦm.ne_zero
  rw [devFam]
  split
  · rw [hdegΦ]; exact degree_blockPoly_lt _
  · split
    · rw [degree_one, hdegΦ]; exact_mod_cast hΦd
    · rw [degree_zero, hdegΦ]; exact WithBot.bot_lt_coe _

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem asmPoly_eq {Φ : Polynomial O} {m d : ℕ} (β : Fin m → Fin d → O) :
    asmPoly Φ m β = (∑ j ∈ Finset.range m, devFam m β j * Φ ^ j) + Φ ^ m := by
  rw [asmPoly, Finset.sum_range_succ, devFam_top, one_mul]

private theorem asmPoly_monic {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (β : Fin m → Fin Φ.natDegree → O) : (asmPoly Φ m β).Monic := by
  rw [asmPoly_eq]
  exact (hΦm.pow m).add_of_right
    (degree_sum_mul_pow_lt hΦm _ (degree_devFam_lt hΦm hΦd β) m)

private theorem asmPoly_natDegree {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (β : Fin m → Fin Φ.natDegree → O) :
    (asmPoly Φ m β).natDegree = m * Φ.natDegree := by
  have hdeg : (asmPoly Φ m β).degree = ((m * Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [asmPoly_eq, degree_add_eq_right_of_degree_lt
      (degree_sum_mul_pow_lt hΦm _ (degree_devFam_lt hΦm hΦd β) m),
      degree_eq_natDegree (hΦm.pow m).ne_zero, hΦm.natDegree_pow]
  rw [natDegree, hdeg]
  rfl

/-- **the assembly's development is the block family** (B.06's uniqueness). -/
private theorem dev_asmPoly {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    {m : ℕ} (β : Fin m → Fin Φ.natDegree → O) {j : ℕ} (hj : j < m + 1) :
    dev Φ (asmPoly Φ m β) j = devFam m β j :=
  (dev_unique hΦm hΦd (degree_devFam_lt hΦm hΦd β) rfl j hj).symm

/-! ### 5. Level-`N` congruence at the ideal `𝔪 ^ N` (B.10's congruence leg)

B.10 is stated at a uniformizer (`π ^ N ∣ ·` coefficientwise); the bridge is stated at the
ideal `𝔪 ^ N`, which carries no `π`.  The DVR supplies one (`exists_irreducible`) and
`Irreducible.maximalIdeal_eq` identifies the two readings; `map_mk_eq_iff` is that dictionary
and `map_mk_dev` is B.10's `dev_congr` read through it. -/

private theorem map_mk_eq_iff {π : O} (hπ : Irreducible π) (N : ℕ) (f f' : Polynomial O) :
    f.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
        = f'.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
      ↔ ∀ k, π ^ N ∣ (f - f').coeff k := by
  have hspan : (IsLocalRing.maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · intro h k
    have hk := congrArg (fun p => Polynomial.coeff p k) h
    simp only [coeff_map] at hk
    rw [coeff_sub, ← Ideal.mem_span_singleton, ← hspan, ← Ideal.Quotient.eq]
    exact hk
  · intro h
    refine Polynomial.ext fun k => ?_
    simp only [coeff_map]
    rw [Ideal.Quotient.eq, hspan, Ideal.mem_span_singleton, ← coeff_sub]
    exact h k

private theorem map_mk_dev {π : O} (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic)
    {N : ℕ} {f f' : Polynomial O}
    (h : f.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
      = f'.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))) (j : ℕ) :
    (dev Φ f j).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
      = (dev Φ f' j).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)) :=
  (map_mk_eq_iff hπ N _ _).2 (dev_congr hπ hΦm ((map_mk_eq_iff hπ N f f').1 h) j)

/-! ### 6. The two maps of the bridge

The landed `proj_surjective` (`Uniformity/Density/LocalData.lean`) auto-includes
`[Finite (ResidueField O)]` from its section although the three-line proof never uses it;
C.109a is ENV-C1 (no finiteness anywhere), so the same proof is repeated here at ENV-C1
strength.  Nothing else in this file needs a lift lemma. -/

private theorem proj_surjective' (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (n N : ℕ) : Function.Surjective (proj O n N) := by
  intro c
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := (IsLocalRing.maximalIdeal O) ^ N) (c i)
  exact ⟨a, funext ha⟩

/-- a chosen integral lift of a level-`N` coefficient class. -/
private noncomputable def boxLift (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (n N : ℕ) (c : Coeff O n N) : Fin n → O :=
  (proj_surjective' O n N c).choose

private theorem boxLift_spec (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n N : ℕ) (c : Coeff O n N) : proj O n N (boxLift O n N c) = c :=
  (proj_surjective' O n N c).choose_spec

/-- the raw forward map on an integral lift: the level-`N` classes of the coefficient vectors of
the `Φ`-adic development of `monicPoly a`. -/
private noncomputable def devBlocks (Φ : Polynomial O) (m N : ℕ)
    (a : Fin (m * Φ.natDegree) → O) : Fin m → Coeff O Φ.natDegree N :=
  fun j i =>
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ))

/-- **well-definedness** — `devBlocks` factors through `proj` (B.10's content at level `N`). -/
private theorem devBlocks_congr {π : O} (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic)
    (m N : ℕ) {a a' : Fin (m * Φ.natDegree) → O}
    (h : proj O (m * Φ.natDegree) N a = proj O (m * Φ.natDegree) N a') :
    devBlocks Φ m N a = devBlocks Φ m N a' := by
  have hmap : (monicPoly a).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
      = (monicPoly a').map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)) := by
    refine Polynomial.ext fun k => ?_
    simp only [coeff_map]
    by_cases hk : k < m * Φ.natDegree
    · rw [monicPoly_coeff_of_lt a hk, monicPoly_coeff_of_lt a' hk]
      exact congrFun h ⟨k, hk⟩
    · rw [monicPoly_eq_add, monicPoly_eq_add, coeff_add, coeff_add, blockPoly_coeff,
        blockPoly_coeff, dif_neg hk, dif_neg hk]
  refine funext fun j => funext fun i => ?_
  have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) (map_mk_dev hπ hΦm hmap (j : ℕ))
  simpa [devBlocks] using this

/-- the forward map of the bridge, on level-`N` classes. -/
private noncomputable def devBox (Φ : Polynomial O) (m N : ℕ)
    (c : Coeff O (m * Φ.natDegree) N) : Fin m → Coeff O Φ.natDegree N :=
  devBlocks Φ m N (boxLift O (m * Φ.natDegree) N c)

/-- the backward map of the bridge: lift each block, assemble, read the coefficient vector. -/
private noncomputable def boxAsm (Φ : Polynomial O) (m N : ℕ)
    (b : Fin m → Coeff O Φ.natDegree N) : Coeff O (m * Φ.natDegree) N :=
  proj O (m * Φ.natDegree) N
    (fun i : Fin (m * Φ.natDegree) =>
      (asmPoly Φ m (fun j => boxLift O Φ.natDegree N (b j))).coeff (i : ℕ))

private theorem devBox_proj {π : O} (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic)
    (m N : ℕ) (a : Fin (m * Φ.natDegree) → O) :
    devBox Φ m N (proj O (m * Φ.natDegree) N a) = devBlocks Φ m N a :=
  devBlocks_congr hπ hΦm m N (boxLift_spec O (m * Φ.natDegree) N _)

/-! ### 7. The two round trips -/

private theorem devBox_boxAsm {π : O} (hπ : Irreducible π) {Φ : Polynomial O} (hΦm : Φ.Monic)
    (hΦd : 0 < Φ.natDegree) (m N : ℕ) (b : Fin m → Coeff O Φ.natDegree N) :
    devBox Φ m N (boxAsm Φ m N b) = b := by
  set β : Fin m → Fin Φ.natDegree → O := fun j => boxLift O Φ.natDegree N (b j) with hβ
  have hmp : monicPoly (fun i : Fin (m * Φ.natDegree) => (asmPoly Φ m β).coeff (i : ℕ))
      = asmPoly Φ m β :=
    monicPoly_coeffFun (asmPoly_monic hΦm hΦd β) (asmPoly_natDegree hΦm hΦd β)
  rw [boxAsm, ← hβ, devBox_proj hπ hΦm]
  refine funext fun j => funext fun i => ?_
  rw [devBlocks, hmp, dev_asmPoly hΦm hΦd β (Nat.lt_succ_of_lt j.isLt),
    devFam_of_lt β j.isLt, Fin.eta, blockPoly_coeff, dif_pos i.isLt, Fin.eta]
  exact congrFun (boxLift_spec O Φ.natDegree N (b j)) i

private theorem boxAsm_devBox {Φ : Polynomial O} (hΦm : Φ.Monic)
    (hΦd : 0 < Φ.natDegree) (m N : ℕ) (c : Coeff O (m * Φ.natDegree) N) :
    boxAsm Φ m N (devBox Φ m N c) = c := by
  set a : Fin (m * Φ.natDegree) → O := boxLift O (m * Φ.natDegree) N c with ha
  have hac : proj O (m * Φ.natDegree) N a = c := boxLift_spec O (m * Φ.natDegree) N c
  set β : Fin m → Fin Φ.natDegree → O :=
    fun j => boxLift O Φ.natDegree N (devBox Φ m N c j) with hβ
  -- the block lifts agree with the development coefficients mod `𝔪 ^ N`
  have hblocks : ∀ (j : Fin m) (i : Fin Φ.natDegree),
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N) (β j i)
        = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
            ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ)) := by
    intro j i
    have h1 := congrFun (boxLift_spec O Φ.natDegree N (devBox Φ m N c j)) i
    rw [hβ]
    refine h1.trans ?_
    rw [devBox, ← ha]
    rfl
  -- the two assemblies agree termwise mod `𝔪 ^ N`
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (devFam m β j).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
        = (dev Φ (monicPoly a) j).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)) := by
    intro j hj
    have hjm : j < m + 1 := Finset.mem_range.1 hj
    rcases Nat.lt_or_ge j m with hlt | hge
    · rw [devFam_of_lt β hlt]
      refine Polynomial.ext fun k => ?_
      simp only [coeff_map]
      by_cases hk : k < Φ.natDegree
      · rw [blockPoly_coeff, dif_pos hk]
        exact hblocks ⟨j, hlt⟩ ⟨k, hk⟩
      · rw [blockPoly_coeff, dif_neg hk, map_zero]
        have hdlt : (dev Φ (monicPoly a) j).degree < (k : WithBot ℕ) :=
          lt_of_lt_of_le (degree_dev_lt hΦm hΦd (monicPoly a) j)
            (by rw [degree_eq_natDegree hΦm.ne_zero]; exact_mod_cast Nat.not_lt.1 hk)
        rw [coeff_eq_zero_of_degree_lt hdlt, map_zero]
    · have hjeq : j = m := by omega
      rw [hjeq, devFam_top,
        dev_top hΦm hΦd m (monicPoly a) (monicPoly_monic a) (monicPoly_natDegree a)]
  have hsum : ∑ j ∈ Finset.range (m + 1), dev Φ (monicPoly a) j * Φ ^ j = monicPoly a :=
    sum_dev_eq hΦm hΦd _
      (by rw [monicPoly_natDegree, Nat.succ_mul]; exact Nat.lt_add_of_pos_right hΦd)
  have hmap : (asmPoly Φ m β).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N))
      = (monicPoly a).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)) := by
    rw [asmPoly, ← hsum, Polynomial.map_sum, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Polynomial.map_mul, Polynomial.map_mul, hterm j hj]
  rw [boxAsm, ← hβ, ← hac]
  refine funext fun i => ?_
  have hco := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hmap
  simp only [coeff_map] at hco
  rw [monicPoly_coeff_of_lt a i.isLt, Fin.eta] at hco
  exact hco

/-! ### 8. NODE C.109a — the bridge -/

/-- **NODE C.109a — the level-`N` development ↔ coefficient-box bridge.**  For monic `Φ` of
positive degree, `Coeff O (m * Φ.natDegree) N ≃ (Fin m → Coeff O Φ.natDegree N)`, the
equivalence pinned componentwise through `dev` at an ARBITRARY integral lift — so level-`N`
well-definedness of the development (B.10's content) is part of the claim, not an assumption.

`EFF.W12.23`: *"Monic division gives the UNIQUE `Φ`-adic development `f = Φ^m + ∑_{j<m} a_j Φ^j`,
`a_j ∈ (O/π^N)[x]_{<d}` … `f ↦ (a_j)_{j<m}` is a bijection."* -/
theorem dev_box_bridge {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    (m N : ℕ) :
    ∃ E : Coeff O (m * Φ.natDegree) N ≃ (Fin m → Coeff O Φ.natDegree N),
      ∀ (a : Fin (m * Φ.natDegree) → O) (j : Fin m) (i : Fin Φ.natDegree),
        E (proj O (m * Φ.natDegree) N a) j i
          = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
              ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨⟨devBox Φ m N, boxAsm Φ m N, boxAsm_devBox hΦm hΦd m N,
    devBox_boxAsm hπ hΦm hΦd m N⟩, ?_⟩
  intro a j i
  change devBox Φ m N (proj O (m * Φ.natDegree) N a) j i = _
  rw [devBox_proj hπ hΦm]
  rfl

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.dev_box_bridge

end AxCheck
