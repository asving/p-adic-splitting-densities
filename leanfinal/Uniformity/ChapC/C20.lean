/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C02
import Uniformity.ChapC.C16
import Uniformity.ChapC.C17

/-!
# Uniformity.ChapC.C20 — `stageHeight_class`, `stageHeight_unattained`: class separation of slots

**Chapter C, NODE C.20** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1**. Two signed declarations.

The `dv`-height of `A ∈ O[X]` at a frame is `dv(A) = min_i (e₁·v(a_i) + i·h)` (C.02, realised as
B.14's `suppVal` at the order-0 key `X`). The slot value at index `i` is the `i`-th term of that
minimum. Both clauses below say the same thing from two sides: **a slot value knows its index's
residue class mod `e₁`**, because `e₁·v(a_i)` is invisible mod `e₁`.

* `KeyFrame.stageHeight_class F hi hval` — clause (i). If the slot value at `i` equals `k`, then
  `i·h ≡ k (mod e₁)`. Consequence (via C.16's `slotIdx_unique`, at the consumer): the only slots
  that can realise height `k` are those with `i ≡ slotIdx F k (mod e₁)`.
* `KeyFrame.stageHeight_unattained F hA hwin` — clause (iii), **the emptiness clause**
  (`EFF.HE6.13`'s twist-free "if `T(k) = ∅` the height `k` is not attained at all"). If the slot
  window `T(k)` (C.17) is empty then no `A` of degree `< D′ = e₁f₁` has `dv(A) = k`.

## How (iii) is proved

`dv(A)` is an `inf` over the nonempty `Finset.range (A.natDegree + 1)` in `ℕ∞`, hence **attained**
(`Finset.exists_mem_eq_inf`). Say it is attained at `j`, with value `k`. Then the slot value at
`j` is finite, so `v(a_j)` is a natural number `v` and `e₁·v + j·h = k` **in ℕ** — which is where
both halves come from at once: reducing mod `e₁` gives clause (i), and `j·h ≤ k` gives the window
membership. Writing `j = (j % e₁) + e₁·(j / e₁)`, C.16's `slotIdx_unique` identifies `j % e₁` with
`slotIdx F k`, and `hA : A.natDegree < e₁·f₁` forces `t := j / e₁ < f₁`. So
`t ∈ T(k) = slotWindow F k`, contradicting `hwin`. This is the blueprint's PROOF step 3 verbatim,
and `hA` is exactly its *"(`t < f₁` from `i < D′`)"* parenthesis.

**Observation, recorded not acted on.** `hA` is avoidable. Since `slotWindow` filters an
increasing cost `(slotIdx F k + e₁t)·h` over `range f₁`, and `F.hf₁ : 0 < F.f₁`, an empty window
is *equivalent* to the `t = 0` row failing, i.e. to `slotIdx F k · h > k`; and any attaining index
`j` is `≡ slotIdx F k (mod e₁)`, hence `j ≥ slotIdx F k`, hence `j·h > k` — contradicting
`j·h ≤ k` with no degree bound at all. Dropping the hypothesis would be a statement change, which
is out of scope here (signatures are frozen), so the landed proof takes the blueprint's route and
consumes `hA`. Flagged for the orchestrator: the signed clause is *weaker* than what the argument
supports.

## Divergence from the blueprint STATEMENT (twin authoritative), and what is NOT signed

The blueprint's STATEMENT lists three clauses; the SIGNATURE block signs two. Clause (ii) — *the
minimum is attained, and attained ONLY in the class `slotIdx F k`* — carries **no signature** and
therefore does not land: signatures are frozen and a node may not grow one (the disposition C.16
already recorded for its unsigned clauses (iv)/(v)). This is also why **H.52 is not imported**.
The blueprint's DEPENDS names `H.52` (`slot_height_injective`, the arithmetic no-tie engine) and
H.52 is exactly what clause (ii)'s *uniqueness* half needs — cross-class ties. Neither signed
clause needs it: (i) is one congruence, and (iii) needs only *some* attaining slot, not a unique
one. A consumer wanting (ii) should take `slot_height_injective F.hcop` at `Uniformity.ChapH.H52`
together with clause (i) here.

Also, the signed hypothesis `hi : i ≤ A.natDegree` of clause (i) is **not consumed**: the
congruence follows from `hval` alone (a slot value above `natDegree` has `a_i = 0`, hence
`addVal = ⊤`, hence value `⊤ ≠ k`, so `hval` already implies `hi` at any frame with `0 < e₁`).
It is kept, unweakened, because the signature is frozen — B.18's precedent for signed-but-unused
side conditions.

**DEPENDS.** C.02 (`stageHeight`) · C.15 (`slotIdx`) · C.16 (`slotIdx_unique`) · C.17
(`slotWindow`) · B.15 (`npHgt_X`, through C.02's import) · C.01 (`KeyFrame.he₁`) — by committed
node ID (GC-13(b)). Imports: `Uniformity.ChapC.C02`, `Uniformity.ChapC.C16` (which pulls C.15 and
H.51), `Uniformity.ChapC.C17`.

**PROOF.** The blueprint's three-step PROOF field, with step 2's attainment supplied by
`Finset.exists_mem_eq_inf` (`ℕ∞` is a `LinearOrder` with `OrderTop`, and the range is nonempty)
and step 3's `t < f₁` by `Nat.div_lt_iff_lt_mul` at `hA`.

SOURCE: `EFF.HE6.15` (the (T1) role, verbatim mechanism); `EFF.HE6.13` (the `T(k) = ∅` clause).

**TEETH.** `HE6R1`'s P3 NOT-onto rows (`k < λ` fails — `EFF.HE6R1.27`) → **executable regression**
retained at §13; not dischargeable at this node's binders (an abstract `KeyFrame O π` offers no
numeral, the D7 consequence recorded at C.15). For the record, C.17's `(e₁, f₁, h) = (3, 1, 2)`
audit row is the emptiness clause's own witness: `slotIdx 1 = 2`, the only candidate `t = 0` costs
`(2 + 0)·2 = 4 > 1`, so `T(1) = ∅` and clause (iii) says no `A` of degree `< 3` reaches `dv = 1`.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The shared private step: a finite slot value is an exact ℕ-equation -/

/-- **The arithmetic core of both clauses.** A slot value that equals the *natural number* `k`
forces the coefficient valuation to be finite, and then `e₁·v(a_i) + i·h = k` holds in `ℕ`, not
just in `ℕ∞`. Clause (i) reads this mod `e₁`; clause (iii) reads off `i·h ≤ k`.
`private`: a file-local helper, not a blueprint node. -/
private theorem slot_value_nat (F : KeyFrame O π) {A : Polynomial O} {i k : ℕ}
    (hval : F.e₁ • addVal O (A.coeff i) + ((i * F.h : ℕ) : ℕ∞) = (k : ℕ∞)) :
    ∃ v : ℕ, F.e₁ * v + i * F.h = k := by
  -- The valuation cannot be `⊤`: `e₁ > 0` would make the whole slot value `⊤ ≠ k`.
  obtain ⟨v, hv⟩ : ∃ v : ℕ, addVal O (A.coeff i) = (v : ℕ∞) := by
    rcases eq_or_ne (addVal O (A.coeff i)) ⊤ with h | h
    · exfalso
      rw [h, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add] at hval
      exact (ENat.coe_ne_top k) hval.symm
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
      exact ⟨m, hm.symm⟩
  refine ⟨v, ?_⟩
  rw [hv] at hval
  have hcast : ((F.e₁ * v + i * F.h : ℕ) : ℕ∞)
      = F.e₁ • ((v : ℕ) : ℕ∞) + ((i * F.h : ℕ) : ℕ∞) := by
    push_cast [nsmul_eq_mul]
    ring
  exact_mod_cast hcast.trans hval

/-! ### The signed declarations -/

-- `hi` is a signed hypothesis of the frozen statement; the congruence follows from `hval` alone
-- (see the header). It is kept, unweakened.
set_option linter.unusedVariables false in
/-- **C.20 (i) — class separation of slot values.** `e₁·v(a_i) + i·h ≡ i·h (mod e₁)`, so a slot
value equal to `k` pins the index's class: `i·h ≡ k (mod e₁)`. With C.16's `slotIdx_unique` this
says the only slots that can realise height `k` are the ones in the class `slotIdx F k`. -/
theorem KeyFrame.stageHeight_class (F : KeyFrame O π) {A : Polynomial O} {i k : ℕ}
    (hi : i ≤ A.natDegree) (hval : F.e₁ • addVal O (A.coeff i) + (i * F.h : ℕ∞) = (k : ℕ∞)) :
    i * F.h ≡ k [MOD F.e₁] := by
  obtain ⟨v, hv⟩ := slot_value_nat F (A := A) (i := i) (k := k) (by push_cast; exact hval)
  show i * F.h % F.e₁ = k % F.e₁
  rw [← hv, Nat.mul_add_mod]

/-- **C.20 (iii) — the emptiness clause** (`EFF.HE6.13`, twist-free): if the slot window `T(k)` is
empty then the height `k` is not attained at all, on any `A` of degree `< D′ = e₁f₁`. -/
theorem KeyFrame.stageHeight_unattained (F : KeyFrame O π) {A : Polynomial O} {k : ℕ}
    (hA : A.natDegree < F.e₁ * F.f₁) (hwin : F.slotWindow k = ∅) :
    F.stageHeight A ≠ (k : ℕ∞) := by
  intro hk
  -- `dv(A)` is an `inf` of slot values over a nonempty finite range, hence attained.
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  obtain ⟨j, hjmem, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (A.natDegree + 1)) Finset.nonempty_range_add_one
      (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞))
  rw [hinf, hjeq] at hk
  -- the attaining slot's exact ℕ-equation
  obtain ⟨v, hv⟩ := slot_value_nat F (A := A) (i := j) (k := k) (by rw [Nat.mul_comm]; exact hk)
  -- its class index is `slotIdx F k` (C.16(ii)) and its band index is `t = j / e₁ < f₁`
  have hjlt : j < F.e₁ * F.f₁ :=
    lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)) hA
  have hcls : j % F.e₁ = F.slotIdx k := by
    refine F.slotIdx_unique (Nat.mod_lt _ F.he₁) ?_
    calc (j % F.e₁) * F.h ≡ j * F.h [MOD F.e₁] := (Nat.mod_modEq j F.e₁).mul_right F.h
      _ ≡ k [MOD F.e₁] := by show j * F.h % F.e₁ = k % F.e₁; rw [← hv, Nat.mul_add_mod]
  have hsplit : F.slotIdx k + F.e₁ * (j / F.e₁) = j := by
    rw [← hcls]; exact Nat.mod_add_div j F.e₁
  have htf : j / F.e₁ < F.f₁ :=
    (Nat.div_lt_iff_lt_mul F.he₁).mpr (by rw [Nat.mul_comm]; exact hjlt)
  -- so the band index sits in the window, which is empty
  have hmem : j / F.e₁ ∈ F.slotWindow k := by
    rw [KeyFrame.slotWindow, Finset.mem_filter, Finset.mem_range]
    exact ⟨htf, by rw [hsplit]; omega⟩
  rw [hwin] at hmem
  simp at hmem

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_class
#print axioms Uniformity.Density.Tower.KeyFrame.stageHeight_unattained

end AxCheck
