/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C16
import Uniformity.ChapC.C17

/-!
# Uniformity.ChapC.C18 — `slotWindow_full_iff`, `slotWindow_full_of_le`: the window thresholds

**Chapter C, NODE C.18** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §4, the gauge layer;
the A-C.1 amendment set governs). **ENV-C1** *[A-C.1 re-tag per defect **D7**: the blueprint tags
this node ENV-C5, the arithmetic arena "no `O`, no polynomials", but the signed signature binds
`F : KeyFrame O π` and therefore the whole DVR telescope; this is the same tag/binder mismatch
D7 recorded at C.15–C.17, resolved the same way and for the same reason. The tag is
documentation, not a statement change: the two signatures below are transcribed byte-for-byte]*.
Two signed declarations — this is **the threshold layer C.17 deliberately withheld**.

* `KeyFrame.slotWindow_full_iff F hf k` — **(i) fullness.** `slotWindow F k = range F.f₁` iff
  the *top* slot is affordable: `(slotIdx F k + F.e₁·(F.f₁ − 1))·F.h ≤ k`. One inequality decides
  the whole window.
* `KeyFrame.slotWindow_full_of_le F k hk` — **(ii) uniform sufficiency.** The `k`-free,
  `slotIdx`-free bound `(F.e₁·F.f₁ − 1)·F.h ≤ k` already forces fullness. This is the form
  consumers want, because it mentions no `slotIdx` and so needs nothing about `k`'s residue class:
  once the budget passes `(D′ − 1)h`, every window is full, forever.

## Why (ii) is the useful one, and what it costs

(i) is an equivalence but its right-hand side still reads `slotIdx F k`, i.e. still depends on
`k mod e₁` through C.15's search. (ii) trades the equivalence for uniformity: it replaces
`slotIdx F k` by its worst case `e₁ − 1` (C.16(i)'s bound), which turns the threshold into the
`k`-independent numeral `(e₁f₁ − 1)h = (D′ − 1)h`. That is the arithmetic in `EFF.HE6.13`'s audit
clause (i), re-derived here rather than cited:

```
i₀ + e₁(f₁ − 1)  ≤  (e₁ − 1) + (e₁f₁ − e₁)  =  e₁f₁ − 1.
```

**C.16 is where the `≤ e₁ − 1` comes from, and it is the only place it can come from.** C.15's
`slotIdx` body is a total `List.find?` search with a junk-`0` default; nothing about its *value*
is available from the body. `slotIdx_spec`'s first clause `slotIdx F k < F.e₁` is the entire
content of the step, and it is a theorem about a frame (it consumes `F.hcop`), not an arithmetic
triviality. This is why C.18 imports C.16 and C.17 imports neither.

## The asymmetric `hf`, and why it is redundant *here* but not in general

Clause (i) carries `hf : 0 < F.f₁` and clause (ii) does not. At the binders that actually landed
this asymmetry costs nothing in either direction, because **`0 < F.f₁` is a structure field of
`KeyFrame`** (C.01's `hf₁`, alongside `he₁ : 0 < F.e₁`): (i)'s `hf` is derivable from `F.hf₁` and
is therefore a *redundant* hypothesis, kept because the signature is frozen, and (ii) needs no
`f₁` hypothesis because it can help itself to `F.hf₁` — which is exactly what the landed proof
does (`rw [F.slotWindow_full_iff F.hf₁ k]`, no case split, no dead branch).

The redundancy is an artefact of the D7 tag mismatch and is worth recording rather than deleting,
because in the ENV-C5 reading the blueprint intended — the same two statements over bare naturals
`(i₀, e₁, f₁, h, k)`, no frame — `hf` **is** load-bearing and (i) is false without it. At
`(i₀, e₁, f₁, h) = (2, 3, 0, 2)` and `k = 1`: the window is a filter of `Finset.range 0`, hence
`∅ = Finset.range 0`, i.e. vacuously full, so the left-hand side is TRUE; the right-hand side
degenerates to `(2 + 3·(0 − 1))·2 = (2 + 0)·2 = 4 ≤ 1` (ℕ-truncation makes `0 − 1 = 0`), which is
FALSE. So the hypothesis is not decoration in the arithmetic arena; it is the frame that makes it
free. A consumer that ever restates these thresholds over raw naturals must carry it.

## Clauses (iii) and (iv) carry no signature and therefore do not land

The blueprint STATEMENT lists four clauses; the SIGNATURE block signs two. Signatures are frozen
and a node may not grow one (the same ruling C.16 applied to its own clauses (iv)/(v)), so
downward closure and the `h = 0` degeneracy do **not** land as declarations here. Neither is lost,
and both are one line at a consumer's own node:

* **(iii) downward closure.** `t ∈ slotWindow F k` and `t' ≤ t` imply `t' ∈ slotWindow F k`.
  Proof: `Finset.mem_filter` both ways; `t' < f₁` from `t' ≤ t < f₁`, and
  `(i(k) + e₁t')h ≤ (i(k) + e₁t)h ≤ k` by `Nat.mul_le_mul_left` then `Nat.add_le_add_left` then
  `Nat.mul_le_mul_right`. It is not a separate declaration below because the proof of (i)'s
  backward direction *is* that monotonicity, applied at `t' ≤ f₁ − 1`, so landing (iii) would
  duplicate the only two lines it consists of (and GC-6.5's helper rule bites).
* **(iv) `F.h = 0` ⇒ every window is full.** Immediate from (i) through `F.hf₁`, since the
  threshold's left-hand side is `(…) * 0 = 0 ≤ k`; equally immediate from (ii), whose hypothesis
  reads `(…) * 0 = 0 ≤ k` and so holds outright. Worth naming because it is the *tame* frame: with
  no `h` to pay, the full power basis is available at every height, which is what makes the wild
  case the only interesting one.

## Teeth check, recorded rather than executed (the D7 consequence)

`EFF.HE6.13`'s audit (i) is discharged **as a Lean theorem** by clause (ii) — that is the teeth
row for this node, and it is closed here, not deferred. The numeric rows of the `.12`/`.13`
audits cannot be `#guard`ed at these binders (an abstract `KeyFrame O π` offers no numeral: the
D7 consequence C.15/C.16/C.17 each recorded), so they re-fire as executable regressions at
blueprint §13. For the record, C.17's two audit rows are reproduced *and* discriminated by the
thresholds that land here:

* `(e₁, f₁, h) = (3, 1, 2)`, `k = 1` (C.17's empty-window row): `slotIdx 1 = 2` (as `2·2 % 3 = 1`),
  so (i)'s threshold reads `(2 + 3·0)·2 = 4 ≤ 1` — false, and indeed `T(1) = ∅ ≠ range 1`. (ii)'s
  bound reads `(3·1 − 1)·2 = 4 ≤ 1` — also false, so (ii) is silent here, as it must be. **The
  same frame at `k = 0` separates the two clauses**, which is the check worth having: `slotIdx 0 = 0`,
  so (i) reads `0 ≤ 0` — true, and `T(0) = {0} = range 1` is full; (ii)'s uniform bound still reads
  `4 ≤ 0` — false. So (ii) is *strictly* sufficient-only, exactly as its statement claims, and (i)
  is not a repackaging of it.
* `(e₁, f₁, h) = (1, 2, 1)`, `k = 0` (C.17's proper-window row): `slotIdx k = 0` for every `k`
  (`e₁ = 1`), so (i)'s threshold reads `(0 + 1·1)·1 = 1 ≤ 0` — false, matching
  `T(0) = {0} ⊊ range 2`. At `k = 1` it reads `1 ≤ 1` — true, and `T(1) = {0, 1} = range 2`;
  (ii)'s bound `(1·2 − 1)·1 = 1 ≤ 1` fires at the same `k`. Here the two thresholds coincide
  identically, because `e₁ = 1` forces `slotIdx k = 0 = e₁ − 1`; this row therefore exercises the
  degenerate-`e₁` agreement case and *not* the separation the previous row exhibits.

**GC-11's numerics rider.** Both statements are arithmetic rows over the frame numerals
`(e₁, f₁, h)` and are **prime-free**: no `q`, no `residueCard`, no residue field appears in either
signature, so a single theorem discharges the row at `q = 2` and at `q = 3` simultaneously and no
per-prime case exists to split. The rider is served at §13, where C.123's `q = 3` frame and
C.124's `q = 2` analogue instantiate the same two theorems at their own `(e₁, f₁, h)`; the
genuinely wild `e₁ ≥ 2` shape GC-11 also demands is exercised by the first row above
(`e₁ = 3`, `h = 2`), which is the case where `slotIdx` is not identically `0` and the window is
therefore not full for free.

**DEPENDS.** C.15 (`slotIdx`) · C.16 (`slotIdx_spec`, clause (i)'s range bound — the only
dependency that is not definitional) · C.17 (`slotWindow`) · C.01 (`KeyFrame.e₁`, `f₁`, `h`) — all
by committed node ID (GC-13(b)). The imports are `Uniformity.ChapC.C16` and
`Uniformity.ChapC.C17`, which between them pull C.15, C.01, H.51 and the B chain.

**PROOF.** The blueprint's two steps, in its order:
1. Monotonicity of the filter's bound in `t` gives (iii), and (i) follows: fullness iff the top
   slot `t = f₁ − 1` is in. Forward is `Finset.mem_filter` at `f₁ − 1` (which is in `range f₁`
   because `hf`); backward is `Finset.filter_true_of_mem` with the monotonicity applied at
   `t ≤ f₁ − 1`.
2. (ii): rewrite by (i) at `F.hf₁`, then `i₀ + e₁(f₁ − 1) ≤ e₁f₁ − 1` from C.16(i)'s
   `slotIdx F k < F.e₁`, with `e₁(f₁ − 1) + e₁ = e₁f₁` supplied to `omega` as a `have` (the
   products are nonlinear, so `omega` cannot see the relation unaided); then `Nat.mul_le_mul_right`
   and transitivity through `hk`.

SOURCE: `EFF.HE6.13` (the fullness clause `k ≥ (i₀(k) + e₁(f₁−1))h`, the uniform `k ≥ (D′−1)h`,
both audited there).

**TEETH.** `EFF.HE6.13`'s audit (i) → **Lean theorem**, discharged at clause (ii) below; the
numeric rows → executable regression at §13 (see the teeth-check section above).

ENVIRONMENT: ENV-C1 (post-D7).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **C.18 (i) — fullness.** The window `T(k)` is all of `range f₁` exactly when its *top* slot
`t = f₁ − 1` is affordable.  `EFF.HE6.13`'s fullness clause.  The signed hypothesis `0 < F.f₁`
duplicates C.01's structure field `F.hf₁` and is redundant at these binders (kept: the signature
is frozen); it is genuinely load-bearing in the ENV-C5 reading over bare naturals, where at
`f₁ = 0` the window is vacuously full while the right-hand side degenerates to
`slotIdx F k · F.h ≤ k`, which can fail. -/
theorem KeyFrame.slotWindow_full_iff (F : KeyFrame O π) (hf : 0 < F.f₁) (k : ℕ) :
    F.slotWindow k = Finset.range F.f₁
      ↔ (F.slotIdx k + F.e₁ * (F.f₁ - 1)) * F.h ≤ k := by
  constructor
  · intro h
    have hmem : F.f₁ - 1 ∈ F.slotWindow k := by
      rw [h]; exact Finset.mem_range.mpr (Nat.sub_lt hf one_pos)
    rw [KeyFrame.slotWindow, Finset.mem_filter] at hmem
    exact hmem.2
  · intro h
    refine Finset.filter_true_of_mem ?_
    intro t ht
    -- clause (iii), inlined: the filter's bound is monotone in `t`
    have htle : t ≤ F.f₁ - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp ht)
    refine le_trans ?_ h
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ htle) _)

/-- **C.18 (ii) — uniform sufficiency.** Past the `k`-independent budget `(D′ − 1)h = (e₁f₁ − 1)h`
every window is full, whatever the residue class of `k`.  The step is `EFF.HE6.13`'s audit clause
`i₀ + e₁(f₁ − 1) ≤ e₁f₁ − 1`, which is C.16(i)'s `slotIdx F k < F.e₁` and nothing else.  No
`0 < F.f₁` binder is needed because the frame already carries it (`F.hf₁`). -/
theorem KeyFrame.slotWindow_full_of_le (F : KeyFrame O π) (k : ℕ)
    (hk : (F.e₁ * F.f₁ - 1) * F.h ≤ k) : F.slotWindow k = Finset.range F.f₁ := by
  rw [F.slotWindow_full_iff F.hf₁ k]
  have hi : F.slotIdx k < F.e₁ := (F.slotIdx_spec k).1
  have hsplit : F.e₁ * (F.f₁ - 1) + F.e₁ = F.e₁ * F.f₁ := by
    calc F.e₁ * (F.f₁ - 1) + F.e₁ = F.e₁ * (F.f₁ - 1 + 1) := by ring
      _ = F.e₁ * F.f₁ := by rw [Nat.sub_add_cancel F.hf₁]
  have hle : F.slotIdx k + F.e₁ * (F.f₁ - 1) ≤ F.e₁ * F.f₁ - 1 := by omega
  exact le_trans (Nat.mul_le_mul_right _ hle) hk

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.slotWindow_full_iff
#print axioms Uniformity.Density.Tower.KeyFrame.slotWindow_full_of_le

end AxCheck
