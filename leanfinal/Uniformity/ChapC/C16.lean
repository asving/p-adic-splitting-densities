/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C15
import Uniformity.ChapH.H51

/-!
# Uniformity.ChapC.C16 — `slotIdx_spec`, `slotIdx_unique`, `twistExp_spec`: the slot-index laws

**Chapter C, NODE C.16** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1** *[A-C.1 re-tag per defect **D7**: ENV-C5 → ENV-C1,
stated over `KeyFrame`, which binds the DVR telescope; see C.15's rider]*. Three signed
declarations. This is **the SPEC node for C.15** — C.15's bodies (a `List.find?` search and a
truncated-subtraction/division) promise nothing on their own, and every consumer of `slotIdx`
or `twistExp` must cite the three theorems below, never the bodies.

* `KeyFrame.slotIdx_spec F k` — clause (i): `slotIdx F k < F.e₁` **and**
  `slotIdx F k * F.h ≡ k [MOD F.e₁]`. This is where the search is proved to succeed: the
  existence half is `F.hcop : Nat.Coprime F.h F.e₁` (C.01) run through H.51's mod-`e₁`
  bijection, so the `getD 0` fallback of C.15's body is never reached at a `KeyFrame`.
* `KeyFrame.slotIdx_unique F hi hcong` — clause (ii): any `i < F.e₁` with
  `i * F.h ≡ k [MOD F.e₁]` **is** `slotIdx F k`. This is the usable form: it lets a consumer
  who has produced its own slot by any route identify it with `slotIdx` without touching the
  `List.find?`.
* `KeyFrame.twistExp_spec F k` — clause (iii), the `EFF.HE6.13` RIDER identity
  `i₀·k = i(k) + e₁·q(k)` with `i₀ = slotIdx F 1`. Exactness of the ℕ-division in C.15's body
  is the content: `slotIdx F k` is proved to be `(i₀·k) % e₁`, so `i₀·k − slotIdx F k` is the
  exact multiple `e₁·((i₀·k)/e₁)` and the truncated subtraction never truncates.

## What is signed here, and what is not

The blueprint STATEMENT lists five clauses; the SIGNATURE block signs three. Clauses (iv)
(`e₁`-periodicity in `k`, and `slotIdx F k = k % e₁` at `h ≡ 1`) and (v) (the degenerate
`F.e₁ = 1` frame, where `slotIdx = 0` and `twistExp = 0`) carry **no signature** and therefore
do not land as declarations — signatures are frozen and a node may not grow one. Neither is
lost: (v) is an immediate corollary of clause (i) alone (`slotIdx F k < 1` forces `0`, and then
`twistExp F k = (0 − 0)/1 = 0`), and (iv) likewise follows from (ii) by exhibiting the candidate
slot. A consumer that needs either should derive it at its own node from `slotIdx_unique`.

## Divergence from the blueprint SIGNATURE (twin authoritative)

The blueprint writes the third statement's right-hand side as
`F.slotIdx k + F.e₁ * F.twistExp F k`. That text does not elaborate: `F.twistExp F k` is
`KeyFrame.twistExp F F k`, and `twistExp`'s second explicit argument is a `ℕ`, not a frame. The
gate-verified twin `leanspec/Leanspec/ChapC.lean` writes `F.slotIdx k + F.e₁ * F.twistExp k`,
which is both the unique elaborable reading and the one the twin signs; the twin is
authoritative on divergence, so it is what lands. This is a transcription typo in the
blueprint, not a statement change: the mathematical content (`i₀k = i(k) + e₁q(k)`) is
identical, and it is C.15's own docstring display.

## The proof, and where the coprimality enters

Existence — *the* content of clause (i) — is H.51(b) `class_sep_bij`: for `Nat.Coprime h e` the
map `i ↦ i·h % e` is a `Set.BijOn` of `↑(Finset.range e)` onto itself, so its `SurjOn` half hits
`k % e₁` (which lies in `range e₁` because `F.he₁ : 0 < F.e₁`). That produces an `i < F.e₁` with
`i * F.h % F.e₁ = k % F.e₁`, which is *definitionally* `Nat.ModEq`, so C.15's `List.find?`
cannot return `none`; `List.mem_of_find?_eq_some` then returns the range bound and
`List.find?_some` the congruence. Uniqueness (ii) is H.51(a) `class_sep` verbatim, applied to
`i` and `slotIdx F k` against the common residue `k % F.e₁`.

Clause (iii) is (ii) applied once more: `(i₀k % e₁) * h ≡ i₀k · h = k · (i₀ h) ≡ k · 1`, so
`i₀k % e₁ = slotIdx F k` by uniqueness, and the rest is `Nat.div_add_mod` /
`Nat.mul_div_cancel_left` at `F.he₁`. **This is why the ℕ-truncation flagged at C.15 is safe**:
the subtraction `i₀k − slotIdx F k` is subtracting a remainder from its own dividend.

Note that H.51 needs `Nat.Coprime F.h F.e₁` in exactly the orientation `F.hcop` supplies it
(`Nat.Coprime h e₁`), so no `.symm` gymnastics are needed at the call sites; `class_sep`'s own
body does the `gcd`-flip internally.

**DEPENDS.** C.15 (`slotIdx`, `twistExp`) · C.01 (`KeyFrame.hcop`, `KeyFrame.he₁`) · H.51
(`class_sep`, `class_sep_bij`) — all by committed node ID (GC-13(b)). The imports are
`Uniformity.ChapC.C15` (which pulls C.01 and the whole B chain) and `Uniformity.ChapH.H51`
(the H §8 slice only, never the ChapH roll-up — §0.2's rule against re-creating the backward
arc H-14 removed).

**PROOF.** As above; the blueprint's three-step PROOF field is followed exactly, with H.51
supplying step 1's bijection and step 2's division argument executed through
`Nat.div_add_mod`. Step 3 (the `e₁ = 1` degenerate) is clause (v), unsigned — see above.

SOURCE: `EFF.HE6.13` (the RIDER `i₀k = i + qe₁`, `a₀k − a = −qh`); `EFF.HE6.15` (the (T1) role:
*"`i ↦ ih mod e₁` is a bijection of `ℤ/e₁` because `gcd(h,e₁) = 1`"* — verbatim the proof
mechanism used here, and the reason H.51 is the cited dependency rather than a fresh argument);
`EFF.HE6.58` (`i(k)` as re-displayed).

**TEETH.** The `.13` audit's `q(3) = 1` at `(e₁, f₁, h) = (2, 2, 3)` → **executable regression at
§13** (gate value; C.123/C.124's numeric mirrors). It is not dischargeable at this node's
binders: over an abstract `KeyFrame O π` there is no numeral to `#guard`, which is exactly the
D7 re-tag's consequence recorded at C.15. For the record, the audit value is reproduced by the
bodies that land here: at `e₁ = 2, h = 3` the search gives `i₀ = slotIdx 1 = 1` and
`slotIdx 3 = 1`, hence `twistExp 3 = (1·3 − 1)/2 = 1`.

ENVIRONMENT: ENV-C1 (post-D7).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Induction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.16 (i) — the slot-index spec.** `i(k) = slotIdx F k` lands in `[0, e₁)` and solves
`i·h ≡ k (mod e₁)`.  The existence half (which is what makes C.15's `getD 0` fallback
unreachable at a frame) is `F.hcop` through H.51's mod-`e₁` bijection. -/
theorem KeyFrame.slotIdx_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx k < F.e₁ ∧ F.slotIdx k * F.h ≡ k [MOD F.e₁] := by
  -- H.51(b): `i ↦ i·h % e₁` is onto `range e₁`, so the class of `k` is hit.
  have hex : ∃ i ∈ (↑(Finset.range F.e₁) : Set ℕ), i * F.h % F.e₁ = k % F.e₁ :=
    (class_sep_bij F.hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt k F.he₁)
  -- hence C.15's search cannot fail
  have hnone : (List.range F.e₁).find? (fun i => (i * F.h) % F.e₁ == k % F.e₁) ≠ none := by
    intro hn
    obtain ⟨i, hi, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    exact (List.find?_eq_none.mp hn i (List.mem_range.mpr hi)) (by simpa using hcong)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : F.slotIdx k = a := by rw [KeyFrame.slotIdx, ha]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some ha), ?_⟩
  have hp := List.find?_some ha
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

/-- **C.16 (ii) — uniqueness.** Any `i < e₁` with `i·h ≡ k (mod e₁)` IS `slotIdx F k`
(H.51(a) `class_sep`).  This is the form consumers should cite: it identifies a slot produced
by any other route with C.15's search value. -/
theorem KeyFrame.slotIdx_unique (F : KeyFrame O π) {k i : ℕ} (hi : i < F.e₁)
    (hcong : i * F.h ≡ k [MOD F.e₁]) : i = F.slotIdx k := by
  obtain ⟨hlt, hsp⟩ := F.slotIdx_spec k
  exact class_sep F.hcop hi hlt (hcong.trans hsp.symm)

/-- **C.16 (iii) — the twist identity** (`EFF.HE6.13` RIDER): `i₀·k = i(k) + e₁·q(k)` for
`i₀ = slotIdx F 1`.  Equivalently: `slotIdx F k` is the remainder of `i₀·k` mod `e₁`, so
C.15's ℕ-truncated subtraction and ℕ-division are both exact. -/
theorem KeyFrame.twistExp_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx 1 * k = F.slotIdx k + F.e₁ * F.twistExp k := by
  have h1 := (F.slotIdx_spec 1).2
  set m := F.slotIdx 1 * k with hm
  have hmod : m % F.e₁ = F.slotIdx k := by
    refine F.slotIdx_unique (Nat.mod_lt _ F.he₁) ?_
    calc (m % F.e₁) * F.h ≡ m * F.h [MOD F.e₁] := (Nat.mod_modEq m F.e₁).mul_right F.h
      _ = k * (F.slotIdx 1 * F.h) := by rw [hm]; ring
      _ ≡ k * 1 [MOD F.e₁] := h1.mul_left k
      _ = k := by ring
  have hsub : m - F.slotIdx k = F.e₁ * (m / F.e₁) := by
    have := Nat.div_add_mod m F.e₁
    omega
  have htw : F.twistExp k = m / F.e₁ := by
    rw [KeyFrame.twistExp, ← hm, hsub, Nat.mul_div_cancel_left _ F.he₁]
  rw [htw, ← hmod]
  exact (Nat.mod_add_div m F.e₁).symm

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_spec
#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_unique
#print axioms Uniformity.Density.Tower.KeyFrame.twistExp_spec

end AxCheck
