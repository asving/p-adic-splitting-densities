/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09
import Uniformity.ChapH.H51

/-!
# Uniformity.ChapC.C28 — `shift`, `cocycle`: the level-2 normalizer cocycle

**Chapter C, NODE C.28** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge
layer; the A-C.1 amendment set governs). **ENV-C5** in content — pure `ℕ` arithmetic on a level
datum's numerals `(u, ℓ)` — stated over `LevelDatum` (C.09), so the DVR telescope is bound; this
is the same D7 over-binding C.15/C.16/C.17 carry, and it is why the executable rows at the bottom
go through numeral mirrors rather than the declarations themselves. Four signed declarations.

Over a level datum `L` with side `(u, ℓ)` (`L.hℓ : 0 < ℓ`, `L.hcop : Nat.Coprime u ℓ`):

* `LevelDatum.shift L m` — the **shift** `s(m)`: the unique `0 ≤ β < ℓ` with `β·u ≡ m (mod ℓ)`.
  It is the `Φ′`-exponent of the canonical height-`m` level-2 monomial `ϖ^{(m−βu)/ℓ}Φ′^{β}`.
* `LevelDatum.cocycle L a b` — the **cocycle** `c₁(a,b) = (s(a) + s(b) − s(a+b))/ℓ`, the
  `EFF.HE6R1.35` (PE2 F-2) display verbatim.
* `LevelDatum.cocycle_mem L a b` — clause (i): `ℓ·c₁(a,b) = s(a) + s(b) − s(a+b)` **exactly** (so
  the ℕ-truncated subtraction and the ℕ-division in the body are both exact) and
  `c₁(a,b) ≤ 1`, i.e. `c₁` is `{0,1}`-valued.
* `LevelDatum.cocycle_eq_zero_of_ell_one L hℓ a b` — clause (ii), **twist-triviality at `ℓ = 1`**:
  `s ≡ 0` and `c₁ ≡ 0`. This is `EFF.HE6R1.06`'s *"`s(·) ≡ 0` at `ℓ = 1`"* and the mechanism of
  tooth `HE6R1-T-TWIST0` (*"the level-2 normalizer cocycle degenerates at `ℓ = 1`, `n₂(k) = ϖ^k`"*)
  as a theorem, not as a battery observation.

## The bodies are C.15's pattern at `(u, ℓ)`, and they promise nothing on their own

Defect **D2**: the blueprint writes `LevelDatum.shift … : ℕ := …` with the body only in a trailing
comment (*"the unique `β < ℓ` with `β·u ≡ m (mod ℓ)`; C.15's pattern at `(u, ℓ)`"*). The
gate-verified twin `leanspec/Leanspec/ChapC.lean` lands C.15's own total, computable,
junk-`0`-defaulting `List.find?` body at the pair `(u, ℓ)`, and the twin is authoritative on
divergence. That body is landed here **byte-identical**.

As at C.15/C.16, the body is not the content: `List.find?` can return `none`, and `getD 0` then
hands back junk. The private `shift_spec`/`shift_unique` below are this node's C.16 — they prove
the search succeeds, and **every consumer of `shift` must cite them, never the body**. The
coprimality doing the work is the structure field `L.hcop`, run through H.51's mod-`ℓ` bijection
exactly as C.16 does at `(h, e₁)`. Without it the search genuinely fails: at `(u, ℓ) = (2, 4)`
there is no `β` with `2β ≡ 1 (mod 4)`, and `shift 1` silently returns `0` — the negative control
`#guard`ed at the bottom.

## Where clause (i) comes from

`s(a)·u + s(b)·u ≡ a + b (mod ℓ)`, so `(s(a) + s(b)) % ℓ` solves `(a+b)`'s congruence and is
`< ℓ`; `shift_unique` identifies it with `s(a+b)`. Hence
`ℓ·((s(a)+s(b))/ℓ) + s(a+b) = s(a)+s(b)` (`Nat.div_add_mod`), which is the exactness half; and
`s(a), s(b) < ℓ` gives `s(a)+s(b) < 2ℓ`, so the quotient is `< 2`. Both halves are the blueprint's
*"subtracting the reduced representative leaves a multiple of `ℓ` in `{0, ℓ}` since both
`s`-values are `< ℓ` — `omega` after C.16's spec"*.

## ⚠ FAITHFULNESS + PLACEHOLDER (transcribed from the node, unchanged)

The corpus's `s(·)`/`c₁` live in HE7's level-2 frame (`ANNEX-LEMMA R1-a`(iii)/(iv) — chapter E's).
**This node defines the arithmetic normal form and proves its arithmetic only.** The
RESIDUE-transport law (the cocycle unit's residue is `β^{c₁}`, R1-a(iii)) is §5's scalar node
C.39, which carries the placeholder `EFF.HE7.<nn> — ANNEX-LEMMA R1-a(iii)/(iv)
[supplied-by: chapter E]` (GC-13). **The orchestrator reconciles E's transcription with this
arithmetic normal form at freeze; a mismatch is a stop-the-line finding, not a silent
adjustment.** Nothing here may be read as asserting the transport law.

**DEPENDS.** C.09 (`LevelDatum`, and its fields `u`, `ℓ`, `hℓ`, `hcop`) · C.15/C.16 (the pattern
being instantiated — cited by node ID, not imported: nothing here consumes a `slotIdx`
declaration) · H.51 (`class_sep`, `class_sep_bij` — the mod-`ℓ` bijection) — by committed node ID
(GC-13(b)). Imports: `Uniformity.ChapC.C09` (which pulls C.03/C.01 and the B chain),
`Uniformity.ChapH.H51` (the H §8 slice only, never the ChapH roll-up).

**PROOF.** The blueprint's two-step PROOF field: (i) as displayed above; (ii) everything is mod 1
(`shift m < L.ℓ = 1` forces `0`, and then `c₁ = (0+0−0)/1 = 0`).

SOURCE: `EFF.HE6R1.35` (PE2 F-2: the cocycle display, verbatim); `EFF.HE6R1.39` (PE3 F-1: the
pin-height argument — consumed at C.39, recorded here so the TERMINAL form is not lost);
`EFF.HE6R1.06` (`s(·) ≡ 0` at `ℓ = 1`); `EFF.HE6R1.29` (T-TWIST0, the 1,276-exponent tooth).

**TEETH.** `HE6R1-T-TWIST0` (1,276 level-2 twist exponents all zero at `ℓ = 1`) →
**Lean theorem** (clause (ii), `cocycle_eq_zero_of_ell_one`) **+ executable regression retained**
(the `#guard` block below, including the non-coprime negative control). The contrastive half
(HE7-T-BADTWIST: dropping the twist at `ℓ ≥ 2` mispredicts σ on 21 reads) stays with chapter E's
battery inheritance (GC-8) and is NOT claimed here.

ENVIRONMENT: ENV-C5 in content, ENV-C1 in binding (the D7 shape).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Uniformity.Density.Induction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed definitions (C.15's pattern at the pair `(u, ℓ)`) -/

/-- **C.28 (a) — the shift `s(m)`.** The unique `β < ℓ` with `β·u ≡ m (mod ℓ)`: the `Φ′`-exponent
of the canonical height-`m` level-2 monomial `ϖ^{(m−βu)/ℓ}Φ′^{β}`.
[A-C.1/D2: the blueprint gives the body only in a trailing comment; this is the gate-verified
twin's text, C.15's own total junk-`0`-defaulting search at `(u, ℓ)`.]
**The body promises nothing** — cite `shift_spec`/`shift_unique`'s consumers, i.e. `cocycle_mem`
and `cocycle_eq_zero_of_ell_one`, never this. -/
def LevelDatum.shift {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (m : ℕ) : ℕ :=
  ((List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ)).getD 0

/-- **C.28 (b) — the level-2 normalizer cocycle** `c₁(a,b) = (s(a) + s(b) − s(a+b))/ℓ`
(`EFF.HE6R1.35`, PE2 F-2, verbatim). Exactness of the ℕ-subtraction and the ℕ-division is
`cocycle_mem`. -/
def LevelDatum.cocycle {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : ℕ := (L.shift a + L.shift b - L.shift (a + b)) / L.ℓ

/-! ### Private helpers — this node's C.16 (the search is proved to succeed) -/

/-- **The `shift` spec.** `s(m) < ℓ` and `s(m)·u ≡ m (mod ℓ)`. The existence half — which is what
makes the `getD 0` fallback of the body unreachable at a `LevelDatum` — is `L.hcop` through H.51's
mod-`ℓ` bijection. `private`: a file-local helper, not a blueprint node (C.16's clause (i) at
`(u, ℓ)`; the node signs no spec of its own). -/
private theorem shift_spec {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) (m : ℕ) :
    L.shift m < L.ℓ ∧ L.shift m * L.u ≡ m [MOD L.ℓ] := by
  have hex : ∃ b ∈ (↑(Finset.range L.ℓ) : Set ℕ), b * L.u % L.ℓ = m % L.ℓ :=
    (class_sep_bij L.hcop).surjOn (by
      simpa only [Finset.coe_range, Set.mem_Iio] using Nat.mod_lt m L.hℓ)
  have hnone : (List.range L.ℓ).find? (fun b => (b * L.u) % L.ℓ == m % L.ℓ) ≠ none := by
    intro hn
    obtain ⟨b, hb, hcong⟩ := hex
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    exact (List.find?_eq_none.mp hn b (List.mem_range.mpr hb)) (by simpa using hcong)
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hnone
  have hval : L.shift m = c := by rw [LevelDatum.shift, hc]; rfl
  refine ⟨hval ▸ List.mem_range.mp (List.mem_of_find?_eq_some hc), ?_⟩
  have hp := List.find?_some hc
  simp only [beq_iff_eq] at hp
  rw [hval]
  exact hp

/-- **`shift` uniqueness** (H.51(a) `class_sep` at `(u, ℓ)`): any `β < ℓ` with `β·u ≡ m (mod ℓ)`
IS `s(m)`. `private`: a file-local helper, not a blueprint node. -/
private theorem shift_unique {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) {m b : ℕ}
    (hb : b < L.ℓ) (hcong : b * L.u ≡ m [MOD L.ℓ]) : b = L.shift m := by
  obtain ⟨hlt, hsp⟩ := shift_spec L m
  exact class_sep L.hcop hb hlt (hcong.trans hsp.symm)

/-! ### The signed lemmas -/

/-- **C.28 (i).** `ℓ·c₁(a,b) = s(a) + s(b) − s(a+b)` exactly — so both the ℕ-truncated subtraction
and the ℕ-division in `cocycle`'s body are exact — and `c₁(a,b) ≤ 1`, i.e. the cocycle is
`{0,1}`-valued. -/
theorem LevelDatum.cocycle_mem {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : L.ℓ * L.cocycle a b = L.shift a + L.shift b - L.shift (a + b)
      ∧ L.cocycle a b ≤ 1 := by
  obtain ⟨hal, hac⟩ := shift_spec L a
  obtain ⟨hbl, hbc⟩ := shift_spec L b
  -- the two shifts' sum is a representative of `(a+b)`'s class
  have hsum : (L.shift a + L.shift b) % L.ℓ = L.shift (a + b) := by
    refine shift_unique L (Nat.mod_lt _ L.hℓ) ?_
    calc ((L.shift a + L.shift b) % L.ℓ) * L.u
        ≡ (L.shift a + L.shift b) * L.u [MOD L.ℓ] := (Nat.mod_modEq _ L.ℓ).mul_right L.u
      _ = L.shift a * L.u + L.shift b * L.u := by ring
      _ ≡ a + b [MOD L.ℓ] := hac.add hbc
  have hkey : L.ℓ * ((L.shift a + L.shift b) / L.ℓ) + L.shift (a + b)
      = L.shift a + L.shift b := by
    rw [← hsum]; exact Nat.div_add_mod _ _
  -- both `s`-values are `< ℓ`, so the quotient is `0` or `1`
  have hq2 : (L.shift a + L.shift b) / L.ℓ < 2 :=
    (Nat.div_lt_iff_lt_mul L.hℓ).mpr (by omega)
  have hsub : L.shift a + L.shift b - L.shift (a + b)
      = L.ℓ * ((L.shift a + L.shift b) / L.ℓ) := by omega
  have hcoc : L.cocycle a b = (L.shift a + L.shift b) / L.ℓ := by
    rw [LevelDatum.cocycle, hsub, Nat.mul_div_cancel_left _ L.hℓ]
  exact ⟨by rw [hcoc, ← hsub], by rw [hcoc]; omega⟩

/-- **C.28 (ii) — twist-triviality at `ℓ = 1`** (`EFF.HE6R1.06`; the tooth `HE6R1-T-TWIST0` as a
theorem). At `ℓ = 1` the shift and the cocycle both vanish identically: the level-2 normalizer
degenerates to `n₂(k) = ϖ^k` and there is no twist to carry. -/
theorem LevelDatum.cocycle_eq_zero_of_ell_one {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hℓ : L.ℓ = 1) (a b : ℕ) :
    L.shift a = 0 ∧ L.cocycle a b = 0 := by
  have h0 : ∀ m, L.shift m = 0 := by
    intro m
    have := (shift_spec L m).1
    omega
  refine ⟨h0 a, ?_⟩
  rw [LevelDatum.cocycle, h0 a, h0 b, h0 (a + b), hℓ]

end Uniformity.Density.Tower

/-! ## Numeric regression (TEETH `HE6R1-T-TWIST0` + the non-coprime negative control)

The signed declarations are bound over `LevelDatum F H₀ hpin`, hence over the whole DVR telescope,
so they offer no numeral to `#guard` — the D7 consequence C.15/C.16/C.17 already record. The rows
below therefore run against **numeral mirrors** `shiftN`/`cocycleN`, which are the bodies of
`LevelDatum.shift`/`LevelDatum.cocycle` with the `LevelDatum` wrapper stripped (legitimate exactly
because those bodies read nothing of the datum but `u` and `ℓ`). They are `private`, and they are
**not blueprint declarations**; they carry no mathematical authority, only the regression. A
`#guard` fails elaboration when the proposition evaluates to `false`, so the block is a build-time
test. Rows transcribed from the gate-verified twin's numeric section.
-/

section NumericRegression

/-- Numeral mirror of `LevelDatum.shift` (body verbatim, wrapper stripped). Not a node. -/
private def shiftN (u l m : ℕ) : ℕ :=
  ((List.range l).find? (fun b => (b * u) % l == m % l)).getD 0

/-- Numeral mirror of `LevelDatum.cocycle` (body verbatim, wrapper stripped). Not a node. -/
private def cocycleN (u l a b : ℕ) : ℕ :=
  (shiftN u l a + shiftN u l b - shiftN u l (a + b)) / l

/-- `cocycle_mem` over every coprime `(u, ℓ)` with `ℓ ≤ 9`, `u ≤ 20`, `a, b ≤ 12`. -/
private def cocycleGrid : Bool := Id.run do
  let mut ok := true
  for l in [1:10] do
    for u in [0:21] do
      if Nat.gcd u l == 1 then
        for a in [0:13] do
          for b in [0:13] do
            let c := cocycleN u l a b
            if !(l * c == shiftN u l a + shiftN u l b - shiftN u l (a + b)) then ok := false
            if !(c ≤ 1) then ok := false
  return ok

#guard cocycleGrid

/-! GC-11's two-prime clause at the level this node reaches: the cocycle has no `q`, so the
witness pair is the two smallest denominators, `ℓ = 2` and `ℓ = 3`, each exhibited with a
**nonzero** `c₁` (a `c₁ ≡ 0` row would not distinguish the twist from its absence).
`(u, ℓ) = (1, 2)`: `s(1) = 1`, `s(2) = 0`, so `c₁(1,1) = (1+1−0)/2 = 1`.
`(u, ℓ) = (2, 3)`: `s(1) = 2` (`2·2 = 4 ≡ 1`), `s(2) = 1`, so `c₁(1,1) = (2+2−1)/3 = 1`. -/

#guard shiftN 1 2 1 == 1 && shiftN 1 2 2 == 0 && cocycleN 1 2 1 1 == 1
#guard shiftN 2 3 1 == 2 && shiftN 2 3 2 == 1 && cocycleN 2 3 1 1 == 1

/-! `HE6R1-T-TWIST0`, the executable half of clause (ii): at `ℓ = 1` every shift and every twist
exponent is `0`, for every `u` and every pair. -/

private def twist0Grid : Bool := Id.run do
  let mut ok := true
  for u in [0:21] do
    for a in [0:41] do
      if !(shiftN u 1 a == 0) then ok := false
      for b in [0:41] do
        if !(cocycleN u 1 a b == 0) then ok := false
  return ok

#guard twist0Grid

/-! **Negative control — `hcop` is load-bearing** (the corpus's `HE6-T-BADKEY` tooth, C.09's
FAITHFULNESS note). Drop coprimality and the search has nothing to find, so the body's `getD 0`
fallback fires and `s` is junk. At `(u, ℓ) = (2, 4)` there is no `β` with `2β ≡ 1 (mod 4)`, yet
`shiftN 2 4 1 = 0`; the honest witness is that the returned value fails the defining congruence
(`(2·0) % 4 = 0 ≠ 1 = 1 % 4`), i.e. `shift_spec` is FALSE without `L.hcop`. Note the cocycle
identity itself survives here by ℕ-truncation (`s(1)+s(1)−s(2) = 0+0−1 = 0 = 4·0`), which is
exactly why the control is stated on the congruence and not on the identity. -/

#guard shiftN 2 4 1 == 0 && shiftN 2 4 2 == 1 && (2 * 1) % 4 != 1 % 4
#guard (shiftN 2 4 1 * 2) % 4 != 1 % 4

end NumericRegression

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.LevelDatum.shift
#print axioms Uniformity.Density.Tower.LevelDatum.cocycle
#print axioms Uniformity.Density.Tower.LevelDatum.cocycle_mem
#print axioms Uniformity.Density.Tower.LevelDatum.cocycle_eq_zero_of_ell_one

end AxCheck
