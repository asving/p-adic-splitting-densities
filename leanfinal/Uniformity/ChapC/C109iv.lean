/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C108
import Uniformity.ChapB.B04
import Uniformity.ChapB.B12
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B20

/-!
# Uniformity.ChapC.C109iv — NODE C.109-iv, the node/polygon side dictionary under `WF`

**Chapter C, NODE C.109-iv** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md`, the A-C.5
amendment, ITEM 1 — the C.109 SPLIT), **ENV-C1**.
`[signed: A-C.5, 2026-08-16 — layer 4 of five under C.109's byte-unchanged assembly]`.

For a member `f` of the node cell `htCell π Φ v`, the node's purely combinatorial side data —
A-C.2's ℚ-free chord-test encodings `HTNode.nodeSideSet` / `HTNode.nodeSideDeg` — CONTROLS the
member's own polygon reads (B.16/B.20's `sideSet` / `sideMin` / `sideDeg`):

* `sideSet Φ f u ℓ ⊆ v.nodeSideSet u ℓ` (containment),
* the two ENDPOINTS agree (`Finset.min` and `Finset.max` of the two sets are equal),
* the residual degrees agree (`sideDeg Φ f u ℓ = v.nodeSideDeg u ℓ`),
* the left endpoint's height is the node's floor there
  (`npHgt Φ f (sideMin …) = Pceil (sideMin …)`).

Those four clauses are exactly what the residual read `resPoly … (sideMin …) H₀` consumes.

## ⚠ CONTAINMENT, NOT EQUALITY — and this is certified, not assumed

The natural dictionary `sideSet Φ f u ℓ = v.nodeSideSet u ℓ` is **FALSE** on the re-signed cell.
A priced digit at a NON-VERTEX on-side lattice point may VANISH — the cell only demands
`≥ Pceil` there — and then that abscissa does not attain the support minimum, so it drops out of
the polynomial's own side.  Machine-found witness (A-C.5's `[DICT]` leg,
`verification/c109_ac5_sweep_check.py`): `Φ = X`, `f = X² + 4` over `ℤ/2⁵`, `Pceil = (2,1,0)`,
side `(1,1)`, residual `(Y+1)²` of type `(1²)`; there `sideSet = {0,2}` while
`nodeSideSet = {0,1,2}`.  This is the same char-2 mechanism as A-C.2's defect D3, now biting a
different statement.  **Any agent who "strengthens" this clause to an equality has
re-introduced a refuted statement.**

## The proof in one paragraph

Write `nodeVal j = ℓ·Pceil j + u·j` for the node's cleared support function on `j ≤ m`.  By
definition `v.nodeSideSet u ℓ` is its argmin set, so with `j₀ = min`, `j₁ = max` of that set and
`Mn = nodeVal j₀` we have `nodeVal j ≥ Mn` for all `j ≤ m`, with equality exactly on
`nodeSideSet`.  **`j₀` and `j₁` are hull VERTICES** (`isVertex_min` / `isVertex_max` below): an
abscissa strictly to the left of `j₀` cannot be in the argmin set, so it beats the chord test
strictly — this is `chord_strict`, a three-line ℕ-computation in which the `u`-terms cancel
identically.  The cell pins `npHgt Φ f = Pceil` at vertices and only bounds `npHgt Φ f ≥ Pceil`
elsewhere; past `m` the development vanishes, so `npHgt = ⊤`.  Hence `suppVal Φ f u ℓ = Mn`
(attained at `j₀`), every `f`-on-side abscissa has `nodeVal = Mn` and so lies in `nodeSideSet`
(containment), and `j₀`, `j₁` themselves are `f`-on-side (endpoint equality).  The degree clause
is then formal, and the height clause is the vertex clause at `j₀`.

## Honest scope notes

* `hπ`, `hvis` and `hwf`'s clauses (i)–(iii), (v) are **not consumed**: only the sides law
  (clause (iv), which turns `(u, ℓ) ∈ v.sides` into `0 < ℓ` and `2 ≤ (nodeSideSet).card`) is
  used.  The binders are kept because the signature is signed and C.109's assembly passes them
  through; `linter.unusedVariables` is silenced at the theorem only.
* `hne` is likewise not logically needed for nonemptiness (`j₀` is always `f`-on-side) but is
  the `Finset.min'` argument of `sideMin`/`sideDeg` in the statement.

**DEPENDS.** C.108 (the A-C.2 `WF` apparatus + `htCell`) · B.14/B.16 (`suppVal`, `OnSide`,
`sideSet`) · B.20 (`sideMin`/`sideMax`/`sideDeg`) · B.11/B.12 (`npHgt`, `npHgt_eq_top_iff`) ·
B.04 (`dev_eq_zero_of_lt`).

**SOURCE.** `EFF.W12.83` (the `L_v` display: sides are the sides OF THE POLYGON) ·
`EFF.W12.23` (the three-way membership law).

**TEETH.** `verification/c109_ac5_sweep_check.py` `[DICT]` (the witness above, plus the four
surviving clauses verified at it).

## Status

Sorry-free, axiom-free (Lean core only).  Every helper is `private`: the node's signed surface
is exactly `ht_side_dictionary`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Polynomial Uniformity Uniformity.Density Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### 1. The chord test, from a strict beat on one side -/

/-- The ℕ-computation behind "an argmin endpoint is a hull vertex".  If `j` weakly beats both
`i < j` and `k > j` in the cleared support order and STRICTLY beats one of them, then `(j, P j)`
lies strictly below the chord from `(i, P i)` to `(k, P k)`.  The `u`-terms cancel identically
because `(k − j)·i + (j − i)·k = (k − i)·j`. -/
private theorem chord_strict {ℓ u : ℕ} (P : ℕ → ℕ) {i j k : ℕ}
    (hij : i < j) (hjk : j < k)
    (h1 : ℓ * P j + u * j ≤ ℓ * P i + u * i)
    (h2 : ℓ * P j + u * j ≤ ℓ * P k + u * k)
    (hstrict : ℓ * P j + u * j < ℓ * P i + u * i ∨ ℓ * P j + u * j < ℓ * P k + u * k) :
    (k - i) * P j < (k - j) * P i + (j - i) * P k := by
  obtain ⟨a, rfl⟩ : ∃ a, j = i + (a + 1) := ⟨j - i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = i + (a + 1) + (b + 1) := ⟨k - i - a - 2, by omega⟩
  have s1 : i + (a + 1) + (b + 1) - i = (a + 1) + (b + 1) := by omega
  have s2 : i + (a + 1) + (b + 1) - (i + (a + 1)) = b + 1 := by omega
  have s3 : i + (a + 1) - i = a + 1 := by omega
  rw [s1, s2, s3]
  -- abbreviate the three heights so that `nlinarith` sees only the linear combination
  set Pi := P i with hPi
  set Pj := P (i + (a + 1)) with hPj
  set Pk := P (i + (a + 1) + (b + 1)) with hPk
  have key : ℓ * (((a + 1) + (b + 1)) * Pj) < ℓ * ((b + 1) * Pi + (a + 1) * Pk) := by
    rcases hstrict with hstr | hstr
    · have e1 : (b + 1) * (ℓ * Pj + u * (i + (a + 1)) + 1) ≤ (b + 1) * (ℓ * Pi + u * i) :=
        Nat.mul_le_mul (le_refl _) hstr
      have e2 : (a + 1) * (ℓ * Pj + u * (i + (a + 1)))
          ≤ (a + 1) * (ℓ * Pk + u * (i + (a + 1) + (b + 1))) :=
        Nat.mul_le_mul (le_refl _) h2
      nlinarith [e1, e2]
    · have e1 : (b + 1) * (ℓ * Pj + u * (i + (a + 1))) ≤ (b + 1) * (ℓ * Pi + u * i) :=
        Nat.mul_le_mul (le_refl _) h1
      have e2 : (a + 1) * (ℓ * Pj + u * (i + (a + 1)) + 1)
          ≤ (a + 1) * (ℓ * Pk + u * (i + (a + 1) + (b + 1))) :=
        Nat.mul_le_mul (le_refl _) hstr
      nlinarith [e1, e2]
  exact Nat.lt_of_mul_lt_mul_left key

/-! ### 2. The node's argmin set, and its endpoints as hull vertices -/

private theorem mem_nodeSideSet {v : HTNode} {u ℓ j : ℕ} :
    j ∈ v.nodeSideSet u ℓ ↔ j ≤ v.m ∧ v.NodeOnSide u ℓ j := by
  classical
  have : j ∈ Finset.filter (v.NodeOnSide u ℓ) (Finset.range (v.m + 1))
      ↔ j ∈ v.nodeSideSet u ℓ := Iff.rfl
  rw [← this, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- the left endpoint of the node's `(u, ℓ)`-argmin set is a hull VERTEX. -/
private theorem isVertex_min (v : HTNode) {u ℓ : ℕ}
    (hnode : (v.nodeSideSet u ℓ).Nonempty) :
    v.IsVertex ((v.nodeSideSet u ℓ).min' hnode) := by
  classical
  set j₀ := (v.nodeSideSet u ℓ).min' hnode with hj₀
  have hmem : j₀ ∈ v.nodeSideSet u ℓ := Finset.min'_mem _ _
  obtain ⟨hj₀le, hj₀on⟩ := mem_nodeSideSet.1 hmem
  intro i k hi hk hkm
  have him : i ≤ v.m := le_trans hi.le hj₀le
  -- `i` is strictly to the left of the argmin, hence not in it, hence strictly beaten
  have hinot : i ∉ v.nodeSideSet u ℓ := fun hc => absurd (Finset.min'_le _ _ hc) (not_le.2 hi)
  have hstr : ℓ * v.Pceil j₀ + u * j₀ < ℓ * v.Pceil i + u * i := by
    rcases lt_or_ge (ℓ * v.Pceil j₀ + u * j₀) (ℓ * v.Pceil i + u * i) with h | h
    · exact h
    · exact absurd (mem_nodeSideSet.2 ⟨him, fun i' hi' => le_trans h (hj₀on i' hi')⟩) hinot
  exact chord_strict v.Pceil hi hk (le_of_lt hstr) (hj₀on k hkm) (Or.inl hstr)

/-- the right endpoint of the node's `(u, ℓ)`-argmin set is a hull VERTEX. -/
private theorem isVertex_max (v : HTNode) {u ℓ : ℕ}
    (hnode : (v.nodeSideSet u ℓ).Nonempty) :
    v.IsVertex ((v.nodeSideSet u ℓ).max' hnode) := by
  classical
  set j₁ := (v.nodeSideSet u ℓ).max' hnode with hj₁
  have hmem : j₁ ∈ v.nodeSideSet u ℓ := Finset.max'_mem _ _
  obtain ⟨hj₁le, hj₁on⟩ := mem_nodeSideSet.1 hmem
  intro i k hi hk hkm
  have hknot : k ∉ v.nodeSideSet u ℓ := fun hc => absurd (Finset.le_max' _ _ hc) (not_le.2 hk)
  have hstr : ℓ * v.Pceil j₁ + u * j₁ < ℓ * v.Pceil k + u * k := by
    rcases lt_or_ge (ℓ * v.Pceil j₁ + u * j₁) (ℓ * v.Pceil k + u * k) with h | h
    · exact h
    · exact absurd (mem_nodeSideSet.2 ⟨hkm, fun i' hi' => le_trans h (hj₁on i' hi')⟩) hknot
  exact chord_strict v.Pceil hi hk (hj₁on i (le_trans hi.le hj₁le)) (le_of_lt hstr)
    (Or.inr hstr)

/-! ### 3. `ℕ∞` bookkeeping -/

private theorem smul_cast_add (ℓ c u j : ℕ) :
    ℓ • ((c : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * c + u * j : ℕ) : ℕ∞) := by
  push_cast [nsmul_eq_mul]
  ring

private theorem mem_sideSet_of {Φ f : Polynomial O} {u ℓ j : ℕ} (hj : j ≤ f.natDegree)
    (hon : OnSide Φ f u ℓ j) : j ∈ sideSet Φ f u ℓ := by
  classical
  have : j ∈ Finset.filter (OnSide Φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hj), hon⟩
  exact this

/-! ### 4. NODE C.109-iv -/

set_option linter.unusedVariables false in
/-- **NODE C.109-iv — the node/polygon side dictionary under `WF`.**  Containment plus
endpoint equality, residual degree and the left-endpoint height.  **Not** set equality: see the
`[DICT]` witness in the module docstring. -/
theorem ht_side_dictionary (hπ : Irreducible π)
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    (v : HTNode) (hwf : v.WF) {N : ℕ} (hvis : ∀ j, j ≤ v.m → v.Pceil j < N)
    {f : Polynomial O} (hf : f ∈ htCell π Φ v) {u ℓ : ℕ} (hs : (u, ℓ) ∈ v.sides)
    (hne : (sideSet Φ f u ℓ).Nonempty) :
    sideSet Φ f u ℓ ⊆ v.nodeSideSet u ℓ ∧
      (sideSet Φ f u ℓ).min = (v.nodeSideSet u ℓ).min ∧
      (sideSet Φ f u ℓ).max = (v.nodeSideSet u ℓ).max ∧
      sideDeg Φ f u ℓ hne = v.nodeSideDeg u ℓ ∧
      npHgt Φ f (sideMin Φ f u ℓ hne)
        = ((v.Pceil (sideMin Φ f u ℓ hne) : ℕ) : ℕ∞) := by
  classical
  obtain ⟨hmonic, hdeg, hge, hvert, -⟩ := hf
  obtain ⟨hℓ, hcop, hcard⟩ := (hwf.2.2.2.1 u ℓ).1 hs
  have hnode : (v.nodeSideSet u ℓ).Nonempty := Finset.card_pos.1 (by omega)
  set j₀ := (v.nodeSideSet u ℓ).min' hnode with hj₀def
  set j₁ := (v.nodeSideSet u ℓ).max' hnode with hj₁def
  obtain ⟨hj₀le, hj₀on⟩ := mem_nodeSideSet.1 (Finset.min'_mem (v.nodeSideSet u ℓ) hnode)
  obtain ⟨hj₁le, hj₁on⟩ := mem_nodeSideSet.1 (Finset.max'_mem (v.nodeSideSet u ℓ) hnode)
  set Mn : ℕ := ℓ * v.Pceil j₀ + u * j₀ with hMndef
  -- the node's cleared support minimum, and its argmin characterisation
  have hMin : ∀ i, i ≤ v.m → Mn ≤ ℓ * v.Pceil i + u * i := hj₀on
  have hMemIff : ∀ i, i ≤ v.m → (i ∈ v.nodeSideSet u ℓ ↔ ℓ * v.Pceil i + u * i = Mn) := by
    intro i hi
    rw [mem_nodeSideSet]
    constructor
    · rintro ⟨-, hon⟩
      exact le_antisymm (hon j₀ hj₀le) (hMin i hi)
    · intro he
      exact ⟨hi, fun i' hi' => by rw [he]; exact hMin i' hi'⟩
  -- the two endpoints are hull vertices, so the cell PINS the height there
  have hnp₀ : npHgt Φ f j₀ = ((v.Pceil j₀ : ℕ) : ℕ∞) :=
    hvert j₀ hj₀le (isVertex_min v hnode)
  have hnp₁ : npHgt Φ f j₁ = ((v.Pceil j₁ : ℕ) : ℕ∞) :=
    hvert j₁ hj₁le (isVertex_max v hnode)
  have hj₁val : ℓ * v.Pceil j₁ + u * j₁ = Mn :=
    (hMemIff j₁ hj₁le).1 (Finset.max'_mem (v.nodeSideSet u ℓ) hnode)
  -- past `m` the development vanishes
  have hmle : v.m ≤ f.natDegree := by
    rw [hdeg]; exact Nat.le_mul_of_pos_right _ hΦ.pos
  have htop : ∀ j, v.m < j → npHgt Φ f j = ⊤ := by
    intro j hj
    refine npHgt_eq_top_iff.2 (dev_eq_zero_of_lt hΦ.monic hΦ.pos f j ?_)
    rw [hdeg]
    exact mul_lt_mul_of_pos_right hj hΦ.pos
  -- the polynomial's cleared support value IS the node's
  have hsupp : suppVal Φ f u ℓ = ((Mn : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (Finset.inf_le (f := fun j => ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞))
        (Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hj₀le hmle)))) ?_
      rw [hnp₀, smul_cast_add]
    · refine Finset.le_inf ?_
      intro j hj
      by_cases hjm : j ≤ v.m
      · calc ((Mn : ℕ) : ℕ∞) ≤ ((ℓ * v.Pceil j + u * j : ℕ) : ℕ∞) := by
              exact_mod_cast hMin j hjm
          _ = ℓ • ((v.Pceil j : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := (smul_cast_add _ _ _ _).symm
          _ ≤ ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞) := by gcongr; exact hge j hjm
      · rw [htop j (Nat.lt_of_not_le hjm)]
        simp [nsmul_eq_mul, hℓ.ne']
  -- CLAUSE 1: containment
  have hsubset : sideSet Φ f u ℓ ⊆ v.nodeSideSet u ℓ := by
    intro j hj
    have hon : OnSide Φ f u ℓ j := onSide_of_mem_sideSet hj
    have hval : ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞) = ((Mn : ℕ) : ℕ∞) := by
      rw [show ℓ • npHgt Φ f j + ((u * j : ℕ) : ℕ∞) = suppVal Φ f u ℓ from hon, hsupp]
    have hjm : j ≤ v.m := by
      by_contra hcon
      rw [htop j (Nat.lt_of_not_le hcon)] at hval
      simp [nsmul_eq_mul, hℓ.ne'] at hval
    have hle : ((ℓ * v.Pceil j + u * j : ℕ) : ℕ∞) ≤ ((Mn : ℕ) : ℕ∞) := by
      rw [← hval, ← smul_cast_add]
      gcongr
      exact hge j hjm
    exact (hMemIff j hjm).2 (le_antisymm (by exact_mod_cast hle) (hMin j hjm))
  -- the two node endpoints are themselves `f`-on-side
  have hj₀side : j₀ ∈ sideSet Φ f u ℓ := by
    refine mem_sideSet_of (le_trans hj₀le hmle) ?_
    change ℓ • npHgt Φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) = suppVal Φ f u ℓ
    rw [hnp₀, smul_cast_add, hsupp]
  have hj₁side : j₁ ∈ sideSet Φ f u ℓ := by
    refine mem_sideSet_of (le_trans hj₁le hmle) ?_
    change ℓ • npHgt Φ f j₁ + ((u * j₁ : ℕ) : ℕ∞) = suppVal Φ f u ℓ
    rw [hnp₁, smul_cast_add, hsupp, hj₁val]
  -- CLAUSES 2, 3: the endpoints agree
  have hminEq : (sideSet Φ f u ℓ).min' hne = j₀ :=
    le_antisymm (Finset.min'_le _ _ hj₀side)
      (Finset.min'_le _ _ (hsubset (Finset.min'_mem _ hne)))
  have hmaxEq : (sideSet Φ f u ℓ).max' hne = j₁ :=
    le_antisymm (Finset.le_max' _ _ (hsubset (Finset.max'_mem _ hne)))
      (Finset.le_max' _ _ hj₁side)
  refine ⟨hsubset, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.coe_min' hne, ← Finset.coe_min' hnode, hminEq]
  · rw [← Finset.coe_max' hne, ← Finset.coe_max' hnode, hmaxEq]
  · -- CLAUSE 4: the residual degrees agree
    have hmg : (v.nodeSideSet u ℓ).min.getD 0 = j₀ := by
      rw [← Finset.coe_min' hnode]; rfl
    have hMg : (v.nodeSideSet u ℓ).max.getD 0 = j₁ := by
      rw [← Finset.coe_max' hnode]; rfl
    rw [sideDeg, HTNode.nodeSideDeg, hmg, hMg,
      show sideMax Φ f u ℓ hne = j₁ from hmaxEq, show sideMin Φ f u ℓ hne = j₀ from hminEq]
  · -- CLAUSE 5: the left endpoint's height is the node's floor
    rw [show sideMin Φ f u ℓ hne = j₀ from hminEq, hnp₀]

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.ht_side_dictionary

end AxCheck
