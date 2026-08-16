/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B06
import Uniformity.ChapC.C13
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C18

/-!
# Uniformity.ChapC.C14 — `exists_testKey`: the enlarged test family is nonempty

**Chapter C, NODE C.14** [lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level
frame; the A-C.1 amendment set governs, and this node's **D20 RE-SIGN** of 2026-08-16 is in
force). **ENV-C1′ + `[Finite (ResidueField O)]`**. One signed declaration.

C.13 turned `EFF.HE6.14`'s DEFINITION HE6-1 into the predicate `IsTestKey L Ψ` and asserted
nothing (the construction is non-canonical — the lifts `B_t` are choices). This node discharges
the existence obligation: for every level datum `L` over a frame `F` there **is** a `Ψ` of that
shape. The witness is the corpus's own display

`Ψ := Φ′^{ℓd} + Σ_{t < d} B_t · Φ′^{ℓt}`,   `d := deg r`, `c_t := r.coeff t`,

with `B_t` an exact-height lift of `c_t` at height `(d−t)u` when `c_t ≠ 0` and `B_t := 0`
otherwise.

## The proof, in the blueprint's four steps

**Step 1 — fullness.** For `t < d` the target height is `(d−t)u ≥ u > ℓ·D′·h ≥ D′·h`, using
`L.hκ` (`ℓ·D′·h < u`, the cleared `κ > D′h`) and `ℓ ≥ 1`. So every height a lift is asked for
sits strictly above `D′h` — `EFF.HE6.13`'s NON-PROPAGATION route (1), which is what makes the
slot window FULL at that height and hence the residue read surjective.

**Steps 2–3 — the lift, in ONE branch.** The blueprint splits here: `2 ≤ D′` fires H §8 through
C.14a's adapter, `D′ = 1` takes an "elementary lift" `π^{(d−t)u}·c̃_t`. Landed as a single
construction — see the divergence note below — in `KeyFrame.exists_slotRes_preimage`:

> above the fullness threshold `D′h < M`, every NONZERO `c ∈ K = F.stageField H₀ hpin` is
> `F.slotRes H₀ hpin M B` for some `B` with `deg B < D′` and `F.stageHeight B = M` exactly.

`B` is C.14a's landed `KeyFrame.stageLiftIA` (H.54's `stageLift'` body over the frame's numerals)
at `i := F.slotIdx M`, `a := (M − i·h)/e₁`, with digits the letter-basis coordinates of `c` lifted
by C.14a's `resLift`. Three clauses discharge it: the exponents `i + e₁s` (`s < f₁`) are distinct
and all `< D′`; each occupied slot's stage cost is `e₁·v(digit lift) + M`, so the `Finset.inf` is
`M` exactly, attained at any slot whose digit is a unit; and at a full window the slot residue
reads the digits back through B.22's `digAt_eq`, reassembling `c` by the power basis. At
`D′ = 1` (`e₁ = f₁ = 1`) the same term IS `π^M·c̃` — the blueprint's step-3 lift, not a second
construction.

**Step 4 — reading `IsTestKey` off the sum.** The displayed `Ψ` is `∑_{j ≤ ℓd} a_j Φ′^j` with
`a_{ℓd} = 1`, `a_{ℓt} = B_t`, and `a_j = 0` off the `ℓ`-lattice. Every `a_j` has degree `< D′`,
so B.06's `dev_unique` says this **is** the `Φ′`-development: `dev F.key Ψ j = a_j` for
`j ≤ ℓd`, which is clauses (iii)–(v) of `IsTestKey` verbatim. Monicity and
`natDegree Ψ = D″ = D′ℓd = L.keyDeg₂` come from the top term dominating the tail
(`natDegree (a_j Φ′^j) ≤ (D′−1) + D′j ≤ D′ℓd − 1` for `j < ℓd`) — `EFF.HE6.14`'s own audit
`deg(B_tΦ′^{ℓt}) < D″`, machine-checked.

## Divergences from the blueprint's PROOF field, recorded

**(a) No `D′` case split, and H.55/H.56 are NOT transported.** The blueprint routes step 2
through H.55 (degree, integrality, exact height) and H.56 (the quotient identity) at
`F.genreDatum`, and step 3 through a separate elementary lift. H.55's three landed theorems are
*pure `ℕ` arithmetic in `(e₁, f₁, h, keyDeg)`* — they never mention `stageLift'` — and H.01's
`GenreDatum` cannot be built at the frame's `D′ = 1` corner (`hkey : 2 ≤ e₁f₁`). Re-deriving the
same three numeral facts over the frame's own numerals (`natDegree_stageLiftIA_lt`,
`cost_stageLiftIA` and the `hsa` bound inside `exists_slotRes_preimage`) therefore *removes* the
case split instead of duplicating it, and the object being lifted is still C.14a's
`stageLiftIA`, i.e. H.54's body — the GC-5/H-14 door (`stageLiftIA_eq_stageLift'`) is not
bypassed, only unused. **H's landed side is untouched.**

**(b) `hh : 1 ≤ F.h` and `[Finite (ResidueField O)]` are NOT consumed.** Both are in the signed
signature and both stay (the signature is frozen; `set_option linter.unusedVariables false`
covers the linter). `hh` was added by the D20 RE-SIGN because the blueprint's step-2 branch needs
it (C.14a's `genreDatum` demands `1 ≤ h`); the single-branch route above is valid at `h = 0` too
— there `F.hcop` forces `e₁ = 1`, `slotIdx M = 0`, `a = M`, and the lift is `π^M·Σ_s c̃_s x^s`,
whose height and residue clauses go through unchanged. Finiteness entered only through
`genreDatum`'s `Q`. So the landed theorem is honestly *weaker in hypotheses used* than signed;
nothing about the statement changed.

**(c) `KeyFrame.exists_slotRes_preimage` is PUBLIC and is not a blueprint node.** It is the
step-2/3 kernel, and it is verbatim **PROOF step 2 of NODE C.24** (`slotRes_image`, unlanded):
"given `(c_t)`, the lift at height `k` produces `A` with the pinned height and residue; at
`D′ = 1` the elementary lift (C.14 step 3's mechanism)". Exporting it means C.24 consumes the
construction rather than replaying it. Its statement mentions only landed objects
(`stageHeight`, `slotRes`, `Pin`), so nothing junk-valued crosses the file boundary. RE-PLAN
item: C.24 should cite it.

## ⚠ DEFECT FOUND IN C.14a's `stageCoord` (flagged, not fixed here)

C.14a's `KeyFrame.stageCoord` reads the digits of `c` off `(AdjoinRoot.mk_surjective c).choose`,
an ARBITRARY representative, and its own docstring concedes the `choose` "is not guaranteed to
have degree `< f₁`" while promising that consumers pin it "through a residue equation asserted of
the resulting lift". **That promise cannot be kept.** The residue clause
`slotRes M (stageLiftO M c) = c` — the only thing that could pin `stageLiftO` — reduces to the
reconstruction identity `Σ_{s < f₁} stageCoord(c,s)·η^s = c`, and that identity holds only when
the representative has degree `< f₁`. `Classical.choice` supplies an OPAQUE witness: there is no
lemma bounding its degree, so the identity is **not provable** (nor refutable — the witness is
opaque, which is exactly the problem), and any consumer needing it is stuck. Note this is not
repairable downstream: it is a defect of the definition, whose fix is to read the digits off the
letter basis instead. This node therefore does **not** use `stageLiftO`; it
uses the private `stageDigit` below, the letter-basis coordinate through
`AdjoinRoot.powerBasis`, which is an honest invariant of `c` (`sum_stageDigit` is the
reconstruction identity that `stageCoord` lacks). Downstream consumers of `stageLiftO` (C.43's
`composedKey`, C.56a's `k2DigitLift`) inherit the defect and should be re-pointed at a
power-basis digit read; recorded here for the fleet, out of this node's scope.

### ✔ REPAIRED 2026-08-16 (the finding above is kept verbatim; this is its disposition)

C.14a's `KeyFrame.stageCoord` was **redefined** on `AdjoinRoot.powerBasis`, exactly as the finding
prescribes: the private `stagePB` / `stageDigit` / `sum_stageDigit` that this file carried are now
public C.14a declarations — `KeyFrame.stagePB` (+ `stagePB_dim`, `stagePB_gen`),
`KeyFrame.stageCoord` (signature byte-unchanged, body rebuilt) and `KeyFrame.sum_stageCoord` (the
reconstruction identity). This node's construction is unchanged in substance; it now *cites* the
hoisted machinery instead of privately duplicating it, so `exists_slotRes_preimage` reads
`F.stageCoord H₀ hpin c s` and closes on `F.sum_stageCoord H₀ hpin c`. With the power-basis read
gone from this file, so are its `isKey_X` and the `Field (resField X)` local instance: nothing
left here needs one. `stageLiftO` (hence C.43's `composedKey` and C.56a's `k2DigitLift`) is
pinnable at last, by the residue clause the finding names. ~~**Still open, and NOT touched by this
repair:** C.56a's `k2Coord` has the same defect one level up — it reads
`((AdjoinRoot.mk_surjective s).choose).coeff t` for the `K₂`-over-`K` digits — and wants the same
cure at `towerLabel T`'s power basis.~~ **CLOSED the same day**: C.56a's `k2Coord` was repaired on
2026-08-16 by exactly that cure — the tower power basis `k2PB` (`AdjoinRoot.powerBasis'` at the
monic `towerLabel T`, `k2PB_dim = f₂`, `k2PB_gen = β`), signature byte-unchanged, with the pin
`sum_k2Coord : Σ_{t < f₂} algebraMap(k2Coord T s t)·β^t = s`. Both digit reads of C.56a's
`k2DigitLift` are therefore power-basis coordinates now; nothing in this file consumes either, and
this paragraph is the cross-reference only.

## Private helpers (none is a blueprint node; GC-6.5)

* ~~**`isKey_X`**~~ and ~~**`stagePB` / `stageDigit` / `sum_stageDigit`**~~ — the letter power
  basis, its coordinate read in `ResidueField O` (through B.59a's `resFieldXEquiv`), the
  reconstruction `c = Σ_{s < f₁} digit_s·η^s`, and the `Field (resField X)` instance
  `AdjoinRoot.powerBasis` needs. **HOISTED to C.14a by the 2026-08-16 repair** and deleted here;
  this file now consumes `F.stageCoord` / `F.sum_stageCoord` and needs no `Field` instance.
* **`slot_eq`, `coeff_stageLiftIA_mem`, `coeff_stageLiftIA_not_mem`, `natDegree_stageLiftIA_lt`,
  `cost_stageLiftIA`, `stageHeight_stageLiftIA`, `slotRes_stageLiftIA`** — the frame readings of
  H.55(i)–(iii)/H.56 described in divergence (a).
* **`isUnit_of_residue_ne_zero`, `addVal_mul_pow`** — bureaucracy (`frameRes_ne_zero` went to
  C.14a with the power-basis cluster).

**DEPENDS.** C.01 (`KeyFrame`) · C.02 (`stageHeight`) · C.03 (`frameRes`, `stageField`) ·
C.09 (`LevelDatum`, `keyDeg₂`) · C.13 (`IsTestKey`) · C.14a (`Pin`, `stageLiftIA`, `resLift`,
`resLift_spec`, and — since the 2026-08-16 repair — `stageCoord`, `sum_stageCoord`) ·
C.15/C.16 (`slotIdx`, `slotIdx_spec`) · C.17 (`slotWindow`) ·
C.18 (`slotWindow_full_of_le`) · C.19 (`stageLetter`) · C.21 (`slotRes`) ·
B.02 (`dev`) · B.06 (`dev_unique`) · B.22 (`digAt_eq`) — all by committed node ID (GC-13(b)).
H.54 enters as the *shape* of C.14a's `stageLiftIA`; H.55/H.56 are not cited, per divergence (a).
The `AdjoinRoot.powerBasis` / `PowerBasis.coe_basis` / `Basis.sum_repr` mathlib cluster, and
B.59a's `resFieldXEquiv`/`resFieldXEquiv_coe`, are now reached through C.14a rather than used
directly here.

SOURCE: `EFF.HE6.14` (DEFINITION HE6-1's construction and its audit, verbatim); `EFF.HE6.13`
(LEMMA HE6-1L's fullness clause, which licenses step 1); `EFF.HE6.08` (the `1 ≤ h` frame, whence
the D20 re-sign's hypothesis).

**TEETH.** `EFF.HE6.14`'s audit → **Lean theorem** here: step 1's fullness inequality is `hbig`,
and step 4's `deg(B_tΦ′^{ℓt}) < D″` is `htailnat`. `HE6-T-BADKEY` (`gcd(u,ℓ) = 1` load-bearing)
is carried at C.09's structure field, not re-audited here.

ENVIRONMENT: ENV-C1′ + `[Finite (ResidueField O)]`, both as signed (see divergence (b) for what
is actually consumed).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Private helpers -/

private theorem isUnit_of_residue_ne_zero {x : O} (hx : residue O x ≠ 0) : IsUnit x := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff] at hx
  exact IsLocalRing.notMem_maximalIdeal.mp hx

private theorem addVal_mul_pow (hπ : Irreducible π) (x : O) (n : ℕ) :
    addVal O (x * π ^ n) = addVal O x + (n : ℕ∞) := by
  rw [AddValuation.map_mul, hπ.addVal_pow]

/-! ### The frame lift, and its three clauses

`KeyFrame.stageLiftIA` is C.14a's landed object — H.54's `stageLift'` body over the frame's
numerals, pinned to it by C.14a's `rfl` reconciliation. The three clauses below are the frame
readings of H.55(i)–(iii) and H.56; see the module docstring for why they are re-derived here
rather than transported. -/

/-- The normalizer equation `i·h + e₁·a = M` at C.15's junk-free solve. -/
private theorem slot_eq (F : KeyFrame O π) {M : ℕ} (hM : F.slotIdx M * F.h ≤ M) :
    F.slotIdx M * F.h + F.e₁ * ((M - F.slotIdx M * F.h) / F.e₁) = M := by
  have hdvd : F.e₁ ∣ M - F.slotIdx M * F.h :=
    (Nat.modEq_iff_dvd' hM).mp (F.slotIdx_spec M).2
  rw [Nat.mul_div_cancel' hdvd, Nat.add_sub_cancel' hM]

/-- The lift's coefficient at an occupied slot. -/
private theorem coeff_stageLiftIA_mem (F : KeyFrame O π) {i a s : ℕ} (hs : s < F.f₁)
    (lift : ℕ → O) :
    (F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s) = lift s * π ^ (a - s * F.h) := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b hb hbs
    have hne : i + F.e₁ * s ≠ i + F.e₁ * b := by
      intro he
      exact hbs (Nat.eq_of_mul_eq_mul_left F.he₁ (by omega)).symm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  · intro hns
    exact absurd (Finset.mem_range.mpr hs) hns

/-- The lift's coefficient off the occupied slots. -/
private theorem coeff_stageLiftIA_not_mem (F : KeyFrame O π) {i a n : ℕ} (lift : ℕ → O)
    (hn : ∀ s < F.f₁, n ≠ i + F.e₁ * s) :
    (F.stageLiftIA (π := π) i a lift).coeff n = 0 := by
  classical
  rw [KeyFrame.stageLiftIA, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hne := hn s (Finset.mem_range.mp hs)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]

/-- **H.55(ii) at the frame.** Every `X`-exponent of the lift is `< D′ = e₁f₁`. -/
private theorem natDegree_stageLiftIA_lt (F : KeyFrame O π) {i a : ℕ} (hi : i < F.e₁)
    (lift : ℕ → O) : (F.stageLiftIA (π := π) i a lift).natDegree < F.e₁ * F.f₁ := by
  classical
  have hpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hbound : (F.stageLiftIA (π := π) i a lift).natDegree ≤ F.e₁ * F.f₁ - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    have hs' : s < F.f₁ := Finset.mem_range.mp hs
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs'
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    omega
  omega

/-- **H.55(iii) at the frame.** The `s`-th slot's stage cost is `M` plus the digit's own
valuation — so the lift's height is `M` exactly when some digit is a unit. -/
private theorem cost_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) {i a M s : ℕ}
    (hs : s < F.f₁) (hsa : s * F.h ≤ a) (hM : i * F.h + F.e₁ * a = M)
    (lift : ℕ → O) :
    F.e₁ • addVal O ((F.stageLiftIA (π := π) i a lift).coeff (i + F.e₁ * s))
        + ((F.h * (i + F.e₁ * s) : ℕ) : ℕ∞)
      = F.e₁ • addVal O (lift s) + (M : ℕ∞) := by
  rw [coeff_stageLiftIA_mem F hs lift, addVal_mul_pow hπ, smul_add]
  have hnat : F.e₁ * (a - s * F.h) + F.h * (i + F.e₁ * s) = M := by
    have hsub : F.e₁ * (a - s * F.h) = F.e₁ * a - F.e₁ * (s * F.h) := by rw [Nat.mul_sub]
    have hle : F.e₁ * (s * F.h) ≤ F.e₁ * a := Nat.mul_le_mul_left _ hsa
    have hexp : F.h * (i + F.e₁ * s) = i * F.h + F.e₁ * (s * F.h) := by ring
    omega
  rw [add_assoc]
  congr 1
  rw [show F.e₁ • ((a - s * F.h : ℕ) : ℕ∞) = ((F.e₁ * (a - s * F.h) : ℕ) : ℕ∞) by
    push_cast [nsmul_eq_mul]; ring]
  rw [← Nat.cast_add, hnat]

/-- **The exact-height clause.** -/
private theorem stageHeight_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) {i a M s₀ : ℕ}
    (hM : i * F.h + F.e₁ * a = M) (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a)
    (lift : ℕ → O) (hs₀ : s₀ < F.f₁) (hu : IsUnit (lift s₀)) :
    F.stageHeight (F.stageLiftIA (π := π) i a lift) = (M : ℕ∞) := by
  classical
  set A := F.stageLiftIA (π := π) i a lift with hA
  have hinf : F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun j => F.e₁ • addVal O (A.coeff j) + ((F.h * j : ℕ) : ℕ∞)) := by
    simp only [KeyFrame.stageHeight, suppVal, npHgt_X]
  have hcoeff₀ : A.coeff (i + F.e₁ * s₀) = lift s₀ * π ^ (a - s₀ * F.h) :=
    coeff_stageLiftIA_mem F hs₀ lift
  have hne₀ : A.coeff (i + F.e₁ * s₀) ≠ 0 := by
    rw [hcoeff₀]
    exact mul_ne_zero hu.ne_zero (pow_ne_zero _ hπ.ne_zero)
  rw [hinf]
  refine le_antisymm ?_ ?_
  · have hmem : i + F.e₁ * s₀ ∈ Finset.range (A.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hne₀))
    refine le_trans (Finset.inf_le hmem) ?_
    rw [cost_stageLiftIA F hπ hs₀ (hsa s₀ hs₀) hM lift,
      addVal_eq_zero_iff.mpr hu, smul_zero, zero_add]
  · refine Finset.le_inf fun j _ => ?_
    by_cases hex : ∃ s, s < F.f₁ ∧ j = i + F.e₁ * s
    · obtain ⟨s, hs, rfl⟩ := hex
      rw [cost_stageLiftIA F hπ hs (hsa s hs) hM lift]
      exact le_add_self
    · have hz : A.coeff j = 0 :=
        coeff_stageLiftIA_not_mem F lift (fun s hs he => hex ⟨s, hs, he⟩)
      rw [hz, addVal_zero, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast F.he₁.ne'), top_add]
      exact le_top

/-- **H.56 at the frame — the residue clause.** At a full window the slot residue of the lift
reads its digits back. -/
private theorem slotRes_stageLiftIA (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {a M : ℕ} (hM : F.slotIdx M * F.h + F.e₁ * a = M)
    (hfull : F.slotWindow M = Finset.range F.f₁) (hsa : ∀ s, s < F.f₁ → s * F.h ≤ a)
    (lift : ℕ → O) :
    F.slotRes H₀ hpin M (F.stageLiftIA (π := π) (F.slotIdx M) a lift)
      = ∑ s ∈ Finset.range F.f₁,
          algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
            (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
              (residue O (lift s))) * F.stageLetter H₀ hpin ^ s := by
  classical
  rw [KeyFrame.slotRes, hfull]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < F.f₁ := Finset.mem_range.mp hs
  have hsa' : s * F.h ≤ a := hsa s hs'
  have hidx : (M - (F.slotIdx M + F.e₁ * s) * F.h) / F.e₁ = a - s * F.h := by
    have hexp : (F.slotIdx M + F.e₁ * s) * F.h = F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
    have hle : F.e₁ * (s * F.h) ≤ F.e₁ * a := Nat.mul_le_mul_left _ hsa'
    have heq : M - (F.slotIdx M + F.e₁ * s) * F.h = F.e₁ * (a - s * F.h) := by
      rw [Nat.mul_sub]
      omega
    rw [heq, Nat.mul_div_cancel_left _ F.he₁]
  rw [hidx, coeff_stageLiftIA_mem F hs' lift,
    digAt_eq hπ (mul_comm (lift s) (π ^ (a - s * F.h)))]

/-! ### The lift law -/

/-- **The lift law (`LEMMA GENHN-LIFT` at the frame; C.24's constructive direction).** Above the
fullness threshold `D′h < M`, every NONZERO stage-field value is the normalized slot residue,
at height exactly `M`, of a polynomial of degree `< D′`.

This is C.14's steps 2–3 in one statement, with no case split on `D′`: `EFF.HE6.14`'s
`GENHN-LIFT` branch and its degenerate `D′ = 1` "elementary lift" branch are the same
construction read at `f₁ = 1`/`e₁ = 1`. It is also exactly PROOF step 2 of NODE C.24
(`slotRes_image`, unlanded at the time of writing), and is public so that C.24 can consume it
instead of replaying the construction. -/
theorem KeyFrame.exists_slotRes_preimage (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M) {c : F.stageField H₀ hpin}
    (hc : c ≠ 0) :
    ∃ B : Polynomial O, B.natDegree < F.e₁ * F.f₁ ∧ F.stageHeight B = (M : ℕ∞) ∧
      F.slotRes H₀ hpin M B = c := by
  classical
  have hi : F.slotIdx M < F.e₁ := (F.slotIdx_spec M).1
  have hbelow : ∀ s, s < F.f₁ → (F.slotIdx M + F.e₁ * s) * F.h < M := by
    intro s hs
    have hmul : F.e₁ * (s + 1) ≤ F.e₁ * F.f₁ := Nat.mul_le_mul_left F.e₁ hs
    have hexp : F.e₁ * (s + 1) = F.e₁ * s + F.e₁ := by ring
    have hle : F.slotIdx M + F.e₁ * s ≤ F.e₁ * F.f₁ := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) hM
  have hile : F.slotIdx M * F.h ≤ M := by
    have h0 := hbelow 0 F.hf₁
    rw [Nat.mul_zero, Nat.add_zero] at h0
    omega
  set a := (M - F.slotIdx M * F.h) / F.e₁ with hadef
  have hMa : F.slotIdx M * F.h + F.e₁ * a = M := slot_eq F hile
  have hsa : ∀ s, s < F.f₁ → s * F.h ≤ a := by
    intro s hs
    have h1 := hbelow s hs
    have hexp : (F.slotIdx M + F.e₁ * s) * F.h = F.slotIdx M * F.h + F.e₁ * (s * F.h) := by ring
    have h2 : F.e₁ * (s * F.h) < F.e₁ * a := by omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left h2)
  have hfull : F.slotWindow M = Finset.range F.f₁ := by
    refine F.slotWindow_full_of_le M ?_
    have hsub : (F.e₁ * F.f₁ - 1) * F.h ≤ (F.e₁ * F.f₁) * F.h :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  have hex : ∃ s, s < F.f₁ ∧ F.stageCoord H₀ hpin c s ≠ 0 := by
    by_contra hall
    refine hc (Eq.trans (F.sum_stageCoord H₀ hpin c).symm ?_)
    refine Finset.sum_eq_zero fun s hs => ?_
    have hzero : F.stageCoord H₀ hpin c s = 0 := by
      by_contra hd
      exact hall ⟨s, Finset.mem_range.mp hs, hd⟩
    rw [hzero, map_zero, map_zero, zero_mul]
  obtain ⟨s₀, hs₀, hd₀⟩ := hex
  refine ⟨F.stageLiftIA (π := π) (F.slotIdx M) a
    (fun s => resLift (F.stageCoord H₀ hpin c s)), natDegree_stageLiftIA_lt F hi _, ?_, ?_⟩
  · refine stageHeight_stageLiftIA F hπ hMa hsa _ hs₀ ?_
    exact isUnit_of_residue_ne_zero (by rw [resLift_spec]; exact hd₀)
  · rw [slotRes_stageLiftIA F hπ H₀ hpin hMa hfull hsa]
    refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_) (F.sum_stageCoord H₀ hpin c)
    rw [resLift_spec]

/-! ### The signed declaration -/

set_option linter.unusedVariables false in
/-- **C.14 — test keys exist.** `EFF.HE6.14`'s enlarged family `Ψ_{κ,r}` is nonempty at every
level datum. -/
theorem exists_testKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) (hh : 1 ≤ F.h) :
    ∃ Ψ : Polynomial O, IsTestKey L Ψ := by
  classical
  set d := L.r.natDegree with hddef
  set D := F.e₁ * F.f₁ with hDdef
  have hD : 0 < D := Nat.mul_pos F.he₁ F.hf₁
  have hd : 0 < d := L.hrdeg
  have hℓ : 0 < L.ℓ := L.hℓ
  have hkeydeg : F.key.natDegree = D := F.hdeg
  have hkeypos : 0 < F.key.natDegree := by rw [hkeydeg]; exact hD
  -- Step 1: fullness. `(d − t)u ≥ u > ℓ·D′·h ≥ D′·h` for every `t < d` (`L.hκ`).
  have hbig : ∀ t, t < d → D * F.h < (d - t) * L.u := by
    intro t ht
    have h1 : L.ℓ * D * F.h < L.u := L.hκ
    have hassoc : L.ℓ * D * F.h = L.ℓ * (D * F.h) := by ring
    have h2 : D * F.h ≤ L.ℓ * (D * F.h) := Nat.le_mul_of_pos_left _ hℓ
    have h4 : L.u ≤ (d - t) * L.u := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- Steps 2–3: the lift family, uniformly (no `D′` case split; see the module docstring).
  have hlift : ∀ t : ℕ, ∃ Bt : Polynomial O,
      Bt.natDegree < D ∧ (L.r.coeff t = 0 → Bt = 0) ∧
      (t < d → L.r.coeff t ≠ 0 →
        F.stageHeight Bt = (((d - t) * L.u : ℕ) : ℕ∞) ∧
        F.slotRes H₀ hpin ((d - t) * L.u) Bt = L.r.coeff t) := by
    intro t
    by_cases hc : L.r.coeff t = 0
    · exact ⟨0, by simpa using hD, fun _ => rfl, fun _ hne => absurd hc hne⟩
    · by_cases ht : t < d
      · obtain ⟨Bt, hB1, hB2, hB3⟩ :=
          F.exists_slotRes_preimage hπ H₀ hpin (M := (d - t) * L.u) (hbig t ht) hc
        exact ⟨Bt, hB1, fun h => absurd h hc, fun _ _ => ⟨hB2, hB3⟩⟩
      · exact ⟨0, by simpa using hD, fun _ => rfl, fun h => absurd h ht⟩
  choose B hBdeg hBzero hBspec using hlift
  -- Step 4: the displayed sum, read as a `Φ′`-development (B.06).
  set a : ℕ → Polynomial O := fun j =>
    if j = L.ℓ * d then 1 else if L.ℓ ∣ j then B (j / L.ℓ) else 0 with hadef
  set Ψ : Polynomial O := ∑ j ∈ Finset.range (L.ℓ * d + 1), a j * F.key ^ j with hΨdef
  have hatop : a (L.ℓ * d) = 1 := by simp only [hadef, if_pos rfl]
  have hanat : ∀ j, (a j).natDegree < D := by
    intro j
    simp only [hadef]
    by_cases h1 : j = L.ℓ * d
    · simp only [if_pos h1, Polynomial.natDegree_one]; exact hD
    · rw [if_neg h1]
      by_cases h2 : L.ℓ ∣ j
      · simpa only [if_pos h2] using hBdeg (j / L.ℓ)
      · simp only [if_neg h2, Polynomial.natDegree_zero]; exact hD
  have hadeg : ∀ j, (a j).degree < F.key.degree := fun j =>
    Polynomial.degree_lt_degree (by rw [hkeydeg]; exact hanat j)
  have hdev : ∀ j < L.ℓ * d + 1, a j = dev F.key Ψ j :=
    dev_unique F.hmonic hkeypos hadeg rfl
  -- the top term dominates the tail, whence monicity and the degree
  have hsplit : Ψ = (∑ j ∈ Finset.range (L.ℓ * d), a j * F.key ^ j) + F.key ^ (L.ℓ * d) := by
    rw [hΨdef, Finset.sum_range_succ, hatop, one_mul]
  have hpownat : (F.key ^ (L.ℓ * d)).natDegree = L.ℓ * d * D := by
    rw [Polynomial.natDegree_pow, hkeydeg]
  have htailnat : (∑ j ∈ Finset.range (L.ℓ * d), a j * F.key ^ j).natDegree
      ≤ L.ℓ * d * D - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    have hj' : j < L.ℓ * d := Finset.mem_range.mp hj
    have h1 : (a j * F.key ^ j).natDegree ≤ (a j).natDegree + j * D := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, hkeydeg]
    have h2 := hanat j
    have h3 : (j + 1) * D ≤ L.ℓ * d * D := Nat.mul_le_mul_right D hj'
    have h4 : (j + 1) * D = j * D + D := by ring
    omega
  have htaildeg : (∑ j ∈ Finset.range (L.ℓ * d), a j * F.key ^ j).degree
      < (F.key ^ (L.ℓ * d)).degree := by
    refine Polynomial.degree_lt_degree ?_
    rw [hpownat]
    have hpos : 0 < L.ℓ * d * D := Nat.mul_pos (Nat.mul_pos hℓ hd) hD
    omega
  have hmonic : Ψ.Monic := by
    rw [hsplit]
    exact (F.hmonic.pow (L.ℓ * d)).add_of_right htaildeg
  have hnatΨ : Ψ.natDegree = L.keyDeg₂ := by
    have hdegeq : Ψ.degree = (F.key ^ (L.ℓ * d)).degree := by
      rw [hsplit]
      exact Polynomial.degree_add_eq_right_of_degree_lt htaildeg
    rw [Polynomial.natDegree_eq_of_degree_eq hdegeq, hpownat, LevelDatum.keyDeg₂, ← hDdef,
      ← hddef]
    ring
  refine ⟨Ψ, hmonic, hnatΨ, ?_, ?_, ?_⟩
  · rw [← hdev _ (Nat.lt_succ_self _), hatop]
  · intro b hb hnd
    rw [← hddef] at hb
    rw [← hdev b (by omega)]
    simp only [hadef, if_neg (Nat.ne_of_lt hb), if_neg hnd]
  · intro t ht
    rw [← hddef] at ht
    have hlt : L.ℓ * t < L.ℓ * d := (Nat.mul_lt_mul_left hℓ).mpr ht
    have hjt : a (L.ℓ * t) = B t := by
      simp only [hadef, if_neg (Nat.ne_of_lt hlt), if_pos (Dvd.intro t rfl),
        Nat.mul_div_cancel_left t hℓ]
    have hdt : dev F.key Ψ (L.ℓ * t) = B t := by rw [← hdev _ (by omega), hjt]
    exact ⟨fun hc => by rw [hdt, hBzero t hc], fun hc => by rw [hdt]; exact hBspec t ht hc⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame.exists_slotRes_preimage
#print axioms Uniformity.Density.Tower.exists_testKey

end AxCheck
