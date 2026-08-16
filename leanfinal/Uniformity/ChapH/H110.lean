/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H108
import Uniformity.Density.Transport
import Uniformity.ChapB.B15
import Uniformity.ChapB.B29

/-!
# Uniformity.ChapH.H110 — the composite-stage (CS) bucket

**Chapter H, NODE H.110** [def+lemma] (`blueprint/CHAP-H_general_induction.md` §17.2 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §3.2 N-2a's CS case, source
`EFF.GENIND.08`).  Fifth node of **N-2**, the cluster event grammar over `O`.

`IsCSState π c` says: the state is non-drain, and every monic lift's visible polygon carries, on
some side `(u, ℓ)`, a REPEATED irreducible residual factor `ψ` with block size
`ℓ * ψ.natDegree ≥ 2` — the composite-stage opening.  By **DECISION D-H17.1** the conservative
reader exits UNDECIDED here: stage laws are `StageInterface` FIELDS, ledger-gated, and are never
read by the reader; the stage improvement of the CS mass is a future gated consumer, not part of
this definition.

Per **DECISION D-H17.3** this is the ONE discriminator of §17 that consults a residual
polynomial, and it does so through chapter B's LANDED order-1 polygon API at the key `φ = X`,
with `H₀` pinned at `sideMin` (GC-1).  No new polygon type is declared (GC-2).

* `IsCSState` (def half) — the ∀-lift form, over chapter B's `sideSet` (B.16), `npHgt` (B.11),
  `sideMin` (B.20), `resPoly` (B.29), `resField` (B.25), all by landed name at `φ = X`;
* `suppVal_lt_window`, `not_mem_sideSet_of_window_le` (lemma half) — the **visible-polygon
  principle**, in the two forms §17 consumes.

## The visible-polygon principle, and exactly how far it is proved here

On a NON-drain state the constant coefficient is visible: `resOrd (c 0) ≤ N − 1`, so every lift's
`a 0` has `addVal O (a 0) = v` for a natural `v < N` (`exists_addVal_coeff_zero_lt`).  At `φ = X`
the polygon heights ARE the coefficient valuations (`B15.npHgt_X`), so the abscissa `0` puts the
cleared support value at `≤ ℓ * v`, whence

* `suppVal_lt_window` : `suppVal X (monicPoly a) u ℓ < ℓ * N` for every `0 < ℓ`;
* `not_mem_sideSet_of_window_le` : an abscissa `j` whose height reaches the window
  (`N ≤ npHgt X (monicPoly a) j`) — i.e. an INVISIBLE coefficient, exactly where two lifts of the
  same class are free to disagree — lies in NO `sideSet`.

**What is NOT proved here.**  The full lift-independence of `IsCSState` (that `sideSet`,
`sideMin` and `resPoly` agree across lifts, so that the ∀-lift and ∃-lift readings coincide) is
NOT established.  The two lemmas above are its geometric half (invisible coefficients are off
every side); the blueprint's remaining steps — that such coefficients therefore contribute
junk-`0` to every `resPoly` and create no vertex, plus the digit-level agreement of the
`resCoeff`s below the window (B.77's `resPoly_congr`) — are NOT proved here.  The
definition is therefore used as it is stated: **∀-lift**, which is the conservative (pessimistic)
reading and the one D-H17.1 wants.  Consumers that need the ∃-lift form must discharge the
remaining half; the blueprint books it in the PROOF fields of H.110/H.112.

DEPENDS: H.106 (`ClusterState`), H.107 (`resOrd`, `resOrd_ge_iff`), H.108 (`IsDrainState`,
`resOrd_zero_le_of_not_isDrainState`) · landed CHAP-B `npHgt` (B.11), `suppVal` (B.14),
`npHgt_X` (B.15), `OnSide`/`sideSet` (B.16), `sideMin`/`onSide_of_mem_sideSet` (B.20),
`resField` (B.25), `resPoly` (B.29) — all by landed name, at `φ = X` · landed
`Uniformity.Hensel.pow_dvd_iff_le_addVal`, `monicPoly_coeff_lt`
(`Uniformity/Density/Transport.lean`).

## TEETH (GC-8)

Battery `P1(g) zero CS below m=4` and `P1(g) CS criterion (eμγ=4 ⟹ two solutions)` of
`verification/openmath/OM2_genindb_battery.py` (RESULTS 2026-08-16, 612/612).  Both are pure
block arithmetic and are reproduced verbatim below as `#guard`s over `csSolutions`, the
enumeration of admissible CS blocks `(e, γ, μ)` — `1 ≤ e`, `1 ≤ γ`, repeated factor `2 ≤ μ`,
block size `2 ≤ e * γ`, and `e * μ * γ ≤ m`.  At `m ≤ 3` the enumeration is EMPTY (the battery's
`buckets['CS'] == 0`); at `m = 4` it is exactly `[(1, 2, 2), (2, 1, 2)]`, the battery's two
solutions, all with `e * μ * γ = 4`.

This is the DETECTION side, which is what the battery certifies; the Lean `IsCSState` is the
reader-side predicate, and no claim is made here that the two are welded (that weld is H.117's,
and it is the node that needs `2 ≤ m ≤ 3 ⟹ CS empty`).

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

/-! ## 1. Non-drain makes the constant coefficient visible -/

section Visible

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The constant coefficient of a non-drain lift has a NATURAL valuation `< N`.**  Its
`resOrd` is `≤ N − 1` (H.108), and `π ^ N ∣ a 0` would push the `resOrd` back up to `N`
(H.107 clause (i)); so `addVal O (a 0)` is finite and below the window. -/
theorem exists_addVal_coeff_zero_lt {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 0 < m)
    (hN : 1 ≤ N) {c : ClusterState O m N} (h0 : ¬ IsDrainState c)
    {a : Fin m → O} (ha : proj O m N a = c.1) :
    ∃ v : ℕ, v < N ∧
      IsDiscreteValuationRing.addVal O ((monicPoly a).coeff 0) = (v : ℕ∞) := by
  have hc0 : (monicPoly a).coeff 0 = a ⟨0, hm⟩ := monicPoly_coeff_lt a hm
  have hres : resOrd (c.1 ⟨0, hm⟩) ≤ N - 1 := resOrd_zero_le_of_not_isDrainState hm c h0
  have hmk : c.1 ⟨0, hm⟩ = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a ⟨0, hm⟩) :=
    (congrFun ha ⟨0, hm⟩).symm
  have hnd : ¬ π ^ N ∣ a ⟨0, hm⟩ := by
    intro hdvd
    have hge := (resOrd_ge_iff hπ (le_refl N) (a ⟨0, hm⟩)).2 hdvd
    rw [← hmk] at hge
    omega
  have hlt : IsDiscreteValuationRing.addVal O (a ⟨0, hm⟩) < (N : ℕ∞) := by
    by_contra hcon
    exact hnd ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 (not_lt.1 hcon))
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  refine ⟨v, ?_, ?_⟩
  · rw [← hv] at hlt
    exact_mod_cast hlt
  · rw [hc0, ← hv]

/-! ## 2. The visible-polygon principle -/

/-- **The visible-polygon principle (the inequality).**  On a non-drain state the cleared support
value of every lift, at every `(u, ℓ)` with `0 < ℓ`, is STRICTLY below `ℓ * N`: the abscissa `0`
already caps it at `ℓ * v` with `v < N`.  Equivalently: every side line of the visible polygon
lies strictly below the window at every abscissa. -/
theorem suppVal_lt_window {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 0 < m) (hN : 1 ≤ N)
    {c : ClusterState O m N} (h0 : ¬ IsDrainState c) {a : Fin m → O} (ha : proj O m N a = c.1)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    suppVal X (monicPoly a) u ℓ < ((ℓ * N : ℕ) : ℕ∞) := by
  obtain ⟨v, hvN, hv⟩ := exists_addVal_coeff_zero_lt hπ hm hN h0 ha
  have hmem : 0 ∈ Finset.range ((monicPoly a).natDegree + 1) := Finset.mem_range.2 (by omega)
  have hle : suppVal X (monicPoly a) u ℓ
      ≤ ℓ • npHgt X (monicPoly a) 0 + ((u * 0 : ℕ) : ℕ∞) := Finset.inf_le hmem
  have hh0 : npHgt X (monicPoly a) 0 = (v : ℕ∞) := by rw [npHgt_X]; exact hv
  have hval : ℓ • ((v : ℕ) : ℕ∞) + ((u * 0 : ℕ) : ℕ∞) = ((ℓ * v : ℕ) : ℕ∞) := by
    simp [nsmul_eq_mul]
  rw [hh0, hval] at hle
  refine lt_of_le_of_lt hle ?_
  have hlt : ℓ * v < ℓ * N := by
    calc ℓ * v < ℓ * v + ℓ := by omega
      _ = ℓ * (v + 1) := by ring
      _ ≤ ℓ * N := Nat.mul_le_mul (le_refl ℓ) hvN
  exact_mod_cast hlt

/-- **The visible-polygon principle (the form §17 consumes).**  An abscissa whose development
height reaches the window is on NO side: `N ≤ npHgt X (monicPoly a) j` puts the point strictly
above every side line, so `j ∉ sideSet X (monicPoly a) u ℓ`.

These are exactly the coefficients two lifts of the same class may disagree on; the principle is
why the polygon of a non-drain state never sees the disagreement. -/
theorem not_mem_sideSet_of_window_le {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 0 < m)
    (hN : 1 ≤ N) {c : ClusterState O m N} (h0 : ¬ IsDrainState c) {a : Fin m → O}
    (ha : proj O m N a = c.1) {u ℓ : ℕ} (hℓ : 0 < ℓ) {j : ℕ}
    (hj : ((N : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) j) :
    j ∉ sideSet X (monicPoly a) u ℓ := by
  intro hmem
  have hon : OnSide X (monicPoly a) u ℓ j := onSide_of_mem_sideSet hmem
  have hlt := suppVal_lt_window hπ hm hN h0 ha (u := u) hℓ
  rw [← hon] at hlt
  have hge : ((ℓ * N : ℕ) : ℕ∞) ≤ ℓ • npHgt X (monicPoly a) j := by
    have hc : ((ℓ * N : ℕ) : ℕ∞) = ℓ • ((N : ℕ) : ℕ∞) := by simp [nsmul_eq_mul]
    rw [hc]
    simp only [nsmul_eq_mul]
    gcongr
  exact absurd (lt_of_le_of_lt (le_trans hge le_self_add) hlt) (lt_irrefl _)

end Visible

/-! ## 3. The CS bucket -/

/-- **H.110 (def half).** CS: some side of the visible polygon carries a repeated irreducible
residual factor `ψ` with block size `ℓ * deg ψ ≥ 2` — the conservative reader exits UNDECIDED
at depth 0 (the pessimistic reading; DECISION D-H17.1: stage data is HYP-gated, never read
here).  ∀-lift form; `H₀` pinned at `sideMin` per GC-1. -/
def IsCSState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧
    ∀ (a : Fin m → O), proj O m N a = c.1 →
      ∃ (u ℓ : ℕ) (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) (H₀ : ℕ),
        0 < ℓ ∧ Nat.Coprime u ℓ ∧
        npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞) ∧
        ∃ ψ : Polynomial (resField (X : Polynomial O)),
          Irreducible ψ ∧ 2 ≤ ℓ * ψ.natDegree ∧
          ψ ^ 2 ∣ resPoly π X (monicPoly a) u ℓ hne H₀

/-- A CS state is not a drain state — the first conjunct, exported so consumers need not
destructure. -/
theorem not_isDrainState_of_isCSState {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {m N : ℕ} {c : ClusterState O m N}
    (h : IsCSState π c) : ¬ IsDrainState c := h.1

/-- The side witnessed by a CS state has `0 < ℓ`, so the visible-polygon principle of §2 applies
to it: the repeated residual factor is read off a side line strictly below the window. -/
theorem isCSState_side_pos {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} (h : IsCSState π c) {a : Fin m → O}
    (ha : proj O m N a = c.1) :
    ∃ (u ℓ : ℕ), 0 < ℓ ∧ (sideSet X (monicPoly a) u ℓ).Nonempty := by
  obtain ⟨u, ℓ, hne, _, hℓ, _⟩ := h.2 a ha
  exact ⟨u, ℓ, hℓ, hne⟩

end Uniformity.Density.Induction

/-! ## 4. TEETH — the CS block arithmetic, reproduced

`csSolutions m` enumerates the admissible CS blocks `(e, γ, μ)` at cluster size `m`: `1 ≤ e`,
`1 ≤ γ`, a repeated factor `2 ≤ μ`, block size `2 ≤ e * γ` (the definition's
`2 ≤ ℓ * ψ.natDegree`), and `e * μ * γ ≤ m` (the block fits in the cluster).  The battery's two
`P1(g)` checks are exactly the two `#guard`s below. -/

section NumericGate

/-- Admissible CS blocks `(e, γ, μ)` at cluster size `m`. -/
def csSolutions (m : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((List.range (m + 1)).flatMap fun e =>
    (List.range (m + 1)).flatMap fun g =>
      (List.range (m + 1)).map fun mu => (e, g, mu)).filter
    fun t => decide (1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 2 ≤ t.2.2 ∧ 2 ≤ t.1 * t.2.1 ∧ t.1 * t.2.2 * t.2.1 ≤ m)

#eval csSolutions 4  -- expect [(1, 2, 2), (2, 1, 2)]

-- battery `P1(g) zero CS below m=4`: no admissible block at `m ≤ 3` (so `buckets['CS'] == 0`,
-- which is what puts H.121/H.122 at `2 ≤ m ≤ 3` per DECISION D-H17.1)
#guard csSolutions 0 == [] && csSolutions 1 == [] && csSolutions 2 == [] && csSolutions 3 == []

-- battery `P1(g) CS criterion (eμγ=4 ⟹ two solutions)`: at `m = 4` exactly two blocks
#guard csSolutions 4 == [(1, 2, 2), (2, 1, 2)]

-- and both saturate the cluster, `e * μ * γ = 4` — the battery's `4 <= e*mu*gam <= m`
#guard (csSolutions 4).all fun t => t.1 * t.2.2 * t.2.1 == 4

end NumericGate

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.exists_addVal_coeff_zero_lt
#print axioms Uniformity.Density.Induction.suppVal_lt_window
#print axioms Uniformity.Density.Induction.not_mem_sideSet_of_window_le
#print axioms Uniformity.Density.Induction.IsCSState
#print axioms Uniformity.Density.Induction.not_isDrainState_of_isCSState
#print axioms Uniformity.Density.Induction.isCSState_side_pos

end AxCheck
