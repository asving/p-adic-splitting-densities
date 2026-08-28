/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C133mh3
import Uniformity.ChapC.C05
import Uniformity.ChapC.C84d
import Uniformity.ChapB.B39a
import Uniformity.ChapB.B43
import Uniformity.ChapB.B59a

/-!
# Uniformity.ChapC.C133h0leg — [H0LEG 2026-08-28] the degenerate `h = 0` leg and the FULL
retirement theorem for the declared cite `fgmn_dv_exact_mul`

**UNIT H0LEG (2026-08-28).**  C133mh3 landed `fgmn_dv_exact_mul_thm`: the declared cite's
statement (C66b.lean:90) as a Lean-core theorem, byte-identical except ONE inserted
hypothesis `hh : 0 < F.h` (the MH3 verdict's statement-level finding 1: `KeyFrame` admits
the DEGENERATE `h = 0` frame, which the axiom's quantifier includes but Theorem M does
not).  This file closes that gap and assembles the axiom's statement IN FULL:

* **the degenerate leg** — `fgmn_dv_exact_mul_h0`: the cite's statement at `F.h = 0`.
  Mechanism (the MH3 verdict's recommendation, executed): at `h = 0` coprimality forces
  `e₁ = 1`, the twist dies (`slotIdx ≡ 0`, `twistExp ≡ 0`), the pin collapses (`H₀ = 0`),
  and C.05's degenerate dictionary (`dvHgt = npHgt F.key`, `dvSupp = suppVal F.key`,
  extended here to `dvSideSet = sideSet F.key` under the C.05-DELTA finiteness guard)
  identifies the whole dv-calculus with chapter B's ORDER-1 polygon calculus at the key
  `F.key` — which IS an order-1 key at the degenerate frame (`isKey_key` below; C.01's
  header: `IsKey` fails at `h ≥ 1` and holds exactly at this seam).  The residual read
  transports along the ring hom `h0Hom : resField F.key →+* F.stageField H₀ hpin`
  (`AdjoinRoot.lift` over the identification `frameRes = (F.key.map residue).map ι`,
  `ι = resFieldXEquiv`), under which `dvResPoly = map h0Hom (resPoly)`; the landed
  order-1 exact chain (B39a's `resPoly_mul_gen` + side laws, B43's finiteness lemmas)
  then supplies both conjuncts.  The floor `hfloor` degenerates to exactly B39a's
  `0 < u`.

* **the FULL theorem** — `fgmn_dv_exact_mul_full`: statement BYTE-IDENTICAL to the
  axiom `fgmn_dv_exact_mul` (C66b.lean:90 — same binders, same order, no `h` hypothesis),
  by cases on `F.h = 0` (this file's leg) vs `0 < F.h` (C133mh3's landed
  `fgmn_dv_exact_mul_thm`).  Its `#print axioms` in the AxCheck footer printing exactly
  `[propext, Classical.choice, Quot.sound]` is the retirement's machine certificate:
  the declared cite's content is a theorem of Lean core.

**Retirement note.**  The axiom text in C66b is NOT physically removable by this unit:
the only proof consumer (`C131ac.lean:120`, the pow induction) sits INSIDE this theorem's
own import foundation (`C133mh3 → C133mh1 → C130nv3 → C130nv2 → C130nv → C131ae →
C131ac`), so re-routing it here would be an import cycle.  The physical removal (snip
`C130nv → C131ae` or re-prove the C131a* chain against this theorem) is flagged to the
orchestrator; the faithfulness record is `docs/AXIOM_FAITHFULNESS.md` (RETIRED-AS-THEOREM
entry, 2026-08-28).

## Status

Sorry-free; the AxCheck footer prints every public declaration, the star being
`fgmn_dv_exact_mul_full` at exactly Lean core.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133h0leg

open Uniformity.Density.Leaf IsLocalRing IsDiscreteValuationRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## Part 1 — frame arithmetic at the degenerate frame -/

/-- Coprimality forces `e₁ = 1` at `h = 0` (C.05's observation, local copy). -/
theorem e1_eq_one (F : KeyFrame O π) (hh0 : F.h = 0) : F.e₁ = 1 := by
  have hcop := F.hcop
  rw [hh0] at hcop
  exact (Nat.coprime_zero_left _).mp hcop

/-- The slot index is identically `0` at the degenerate frame. -/
theorem slotIdx_eq_zero (F : KeyFrame O π) (hh0 : F.h = 0) (k : ℕ) : F.slotIdx k = 0 := by
  have hpred : (fun i => (i * 0) % 1 == k % 1) = fun _ => true := by
    funext i
    simp [Nat.mod_one]
  rw [KeyFrame.slotIdx, e1_eq_one F hh0, hh0, hpred]
  rfl

/-- The twist exponent is identically `0` at the degenerate frame: the twist is trivial. -/
theorem twistExp_eq_zero (F : KeyFrame O π) (hh0 : F.h = 0) (k : ℕ) : F.twistExp k = 0 := by
  rw [KeyFrame.twistExp, slotIdx_eq_zero F hh0, slotIdx_eq_zero F hh0]
  simp

/-- The slot window is the full range `range f₁` at the degenerate frame. -/
theorem slotWindow_eq_range (F : KeyFrame O π) (hh0 : F.h = 0) (k : ℕ) :
    F.slotWindow k = Finset.range F.f₁ := by
  rw [KeyFrame.slotWindow, hh0]
  simp

/-! ## Part 2 — the key's own side at the degenerate frame -/

/-- The key's cleared support is finite (any frame; B.43 off the key's monicity). -/
theorem suppVal_key_ne_top' (F : KeyFrame O π) :
    suppVal Polynomial.X F.key F.h F.e₁ ≠ ⊤ :=
  suppVal_ne_top_of_ne_zero Polynomial.monic_X (by simp) F.hmonic.ne_zero

/-- The key's side has left endpoint `0` (any frame: `hpure.1` puts `0` on the side). -/
theorem sideMin_key_eq_zero (F : KeyFrame O π) :
    sideMin Polynomial.X F.key F.h F.e₁ F.hne = 0 := by
  have h0 : 0 ∈ sideSet Polynomial.X F.key F.h F.e₁ :=
    mem_sideSet_of_onSide Polynomial.monic_X (by simp) F.he₁ (suppVal_key_ne_top' F)
      F.hpure.1
  exact Nat.le_zero.mp (Finset.min'_le _ 0 h0)

/-- At `h = 0` the key's whole `X`-polygon sits at height `0`, so `npHgt` at `0` is `0`. -/
theorem npHgt_key_zero (F : KeyFrame O π) (hh0 : F.h = 0) :
    npHgt Polynomial.X F.key 0 = (0 : ℕ∞) := by
  have he := e1_eq_one F hh0
  have htop : npHgt Polynomial.X F.key F.key.natDegree = 0 :=
    npHgt_top Polynomial.monic_X (by simp) F.hmonic
      (by rw [Polynomial.natDegree_X, mul_one])
  have hle : suppVal Polynomial.X F.key F.h F.e₁ ≤ 0 := by
    have hmem : F.key.natDegree ∈ Finset.range (F.key.natDegree + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_self _)
    refine le_trans (Finset.inf_le hmem) (le_of_eq ?_)
    rw [htop, hh0]
    simp
  have hsupp : suppVal Polynomial.X F.key F.h F.e₁ = 0 := le_antisymm hle zero_le
  have h0 : F.e₁ • npHgt Polynomial.X F.key 0 + ((F.h * 0 : ℕ) : ℕ∞)
      = suppVal Polynomial.X F.key F.h F.e₁ := F.hpure.1
  rw [hsupp, he, one_smul, mul_zero, Nat.cast_zero, add_zero] at h0
  exact h0

/-- The pin collapses: `H₀ = 0` at the degenerate frame. -/
theorem pin_eq_zero (F : KeyFrame O π) (hh0 : F.h = 0) {H₀ : ℕ} (hpin : F.Pin H₀) :
    H₀ = 0 := by
  have h : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne)
      = (H₀ : ℕ∞) := hpin
  rw [sideMin_key_eq_zero F, npHgt_key_zero F hh0] at h
  exact_mod_cast h.symm

/-- The key's side spans its whole degree at the degenerate frame. -/
theorem sideDeg_key_eq (F : KeyFrame O π) (hh0 : F.h = 0) :
    sideDeg Polynomial.X F.key F.h F.e₁ F.hne = F.key.natDegree := by
  have he := e1_eq_one F hh0
  have htopmem : F.key.natDegree ∈ sideSet Polynomial.X F.key F.h F.e₁ := by
    have h2 := F.hpure.2
    rw [Polynomial.natDegree_X, Nat.div_one] at h2
    exact mem_sideSet_of_onSide Polynomial.monic_X (by simp) F.he₁
      (suppVal_key_ne_top' F) h2
  have hmax_le : sideMax Polynomial.X F.key F.h F.e₁ F.hne ≤ F.key.natDegree := by
    have := mul_sideMax_le_natDegree Polynomial.monic_X (by simp) F.he₁
      (suppVal_key_ne_top' F) F.hne
    rwa [Polynomial.natDegree_X, mul_one] at this
  have hmax : sideMax Polynomial.X F.key F.h F.e₁ F.hne = F.key.natDegree :=
    le_antisymm hmax_le (Finset.le_max' _ _ htopmem)
  show (sideMax Polynomial.X F.key F.h F.e₁ F.hne
      - sideMin Polynomial.X F.key F.h F.e₁ F.hne) / F.e₁ = F.key.natDegree
  rw [hmax, sideMin_key_eq_zero F, he, Nat.sub_zero, Nat.div_one]

/-! ## Part 3 — the frame residual is the reduction of the key; the key is an order-1 key -/

/-- `digPoly` at height `0` is reduction mod `π` (B.23's shape + B.22's `digAt_zero`;
no `hπ` — the height-`0` digit is total). -/
private theorem digPoly_zero (a : Polynomial O) :
    digPoly π 0 a = a.map (residue O) := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, Polynomial.coeff_map]
  split_ifs with h
  · rw [digAt_zero]
  · rw [a.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- **The frame residual at `h = 0` IS the reduction of the key**, base-changed along
`ResidueField O → resField X` (B.59a's iso, whose coe is the `algebraMap`). -/
theorem frameRes_eq_map (F : KeyFrame O π) (hh0 : F.h = 0) (H₀ : ℕ) (hpin : F.Pin H₀) :
    F.frameRes H₀ hpin
      = (F.key.map (residue O)).map
          (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))) := by
  have hH0 : H₀ = 0 := pin_eq_zero F hh0 hpin
  subst hH0
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  show (resPoly π Polynomial.X F.key F.h F.e₁ F.hne 0).coeff n = _
  rw [resPoly_coeff, sideDeg_key_eq F hh0]
  split_ifs with hn
  · show resMk π Polynomial.X (0 - F.h * n)
        (dev Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne + F.e₁ * n)) = _
    rw [sideMin_key_eq_zero F, e1_eq_one F hh0, zero_add, one_mul, Nat.zero_sub, dev_X]
    show AdjoinRoot.mk _ (digPoly π 0 (Polynomial.C (F.key.coeff n))) = _
    rw [digPoly_zero, Polynomial.map_C, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  · rw [F.key.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]

/-- Round trip `R[X] → S[X] → R[X]` along a ring equiv is the identity. -/
private theorem map_symm_map {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (a : Polynomial R) :
    (a.map (e : R →+* S)).map (e.symm : S →+* R) = a := by
  rw [Polynomial.map_map]
  have h : ((e.symm : S →+* R).comp (e : R →+* S)) = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [h, Polynomial.map_id]

/-- Irreducibility descends along `Polynomial.map` of a ring equiv. -/
private theorem irreducible_of_irreducible_map {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {p : Polynomial R} (hp : Irreducible (p.map (e : R →+* S))) :
    Irreducible p := by
  constructor
  · intro hu
    exact hp.not_isUnit (by simpa using hu.map (Polynomial.mapRingHom (e : R →+* S)))
  · intro a b hab
    rcases hp.isUnit_or_isUnit (show p.map (e : R →+* S)
          = a.map (e : R →+* S) * b.map (e : R →+* S) by rw [hab, Polynomial.map_mul])
        with h | h
    · left
      have h2 := h.map (Polynomial.mapRingHom (e.symm : S →+* R))
      simp only [Polynomial.coe_mapRingHom] at h2
      rwa [map_symm_map e a] at h2
    · right
      have h2 := h.map (Polynomial.mapRingHom (e.symm : S →+* R))
      simp only [Polynomial.coe_mapRingHom] at h2
      rwa [map_symm_map e b] at h2

/-- **The degenerate frame's key is an order-1 key** (B.01's `IsKey`) — the C.01-header
seam made a theorem: reduction irreducibility transports back from `hresirr` along
`frameRes_eq_map` and B.59a's iso. -/
theorem isKey_key (F : KeyFrame O π) (hh0 : F.h = 0) : IsKey F.key := by
  have hpin0 : F.Pin 0 := by
    show npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = ((0 : ℕ) : ℕ∞)
    rw [sideMin_key_eq_zero F, npHgt_key_zero F hh0, Nat.cast_zero]
  have hirr : Irreducible (F.frameRes 0 hpin0) := (F.hresirr 0 hpin0).1
  rw [frameRes_eq_map F hh0 0 hpin0] at hirr
  have hcoe : algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
      = ((resFieldXEquiv O :
            ResidueField O ≃+* resField (Polynomial.X : Polynomial O)) :
          ResidueField O →+* resField (Polynomial.X : Polynomial O)) := rfl
  rw [hcoe] at hirr
  exact ⟨F.hmonic, by rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁,
    irreducible_of_irreducible_map (resFieldXEquiv O) hirr⟩

/-! ## Part 4 — the C.05 dictionary, extended to the side objects -/

private theorem min'_congr {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

private theorem max'_congr {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst h; rfl

/-- **C.05's unsigned fourth clause, under the DELTA-mandated finiteness guard**: at the
degenerate frame the dv-side set IS chapter B's side set at the key, whenever the cleared
support is finite (the C.05 DELTA's refutation is exactly the `suppVal = ⊤` case). -/
theorem dvSideSet_eq_sideSet (F : KeyFrame O π) (hh0 : F.h = 0) {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hsupp : suppVal F.key f u ℓ ≠ ⊤) :
    dvSideSet F f u ℓ = sideSet F.key f u ℓ := by
  classical
  have hiff : ∀ j, DvOnSide F f u ℓ j ↔ OnSide F.key f u ℓ j := by
    intro j
    constructor
    · rintro ⟨heq, _⟩
      show ℓ • npHgt F.key f j + ((u * j : ℕ) : ℕ∞) = suppVal F.key f u ℓ
      rw [← dvSupp_degenerate F hh0, ← dvHgt_degenerate F hh0, heq, Nat.cast_mul]
    · intro hOn
      have hfin : npHgt F.key f j ≠ ⊤ := npHgt_ne_top_of_onSide hℓ hsupp hOn
      have heq : ℓ • npHgt F.key f j + ((u * j : ℕ) : ℕ∞) = suppVal F.key f u ℓ := hOn
      refine ⟨?_, ?_⟩
      · rw [dvSupp_degenerate F hh0, dvHgt_degenerate F hh0, ← heq, Nat.cast_mul]
      · rw [dvHgt_degenerate F hh0]
        exact hfin
  unfold dvSideSet sideSet
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right fun _ => hiff j

/-- Side minima agree under the dictionary. -/
theorem dvSideMin_eq_sideMin (F : KeyFrame O π) (hh0 : F.h = 0) {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hsupp : suppVal F.key f u ℓ ≠ ⊤)
    (hne : (dvSideSet F f u ℓ).Nonempty) (hneB : (sideSet F.key f u ℓ).Nonempty) :
    dvSideMin F f u ℓ hne = sideMin F.key f u ℓ hneB :=
  min'_congr (dvSideSet_eq_sideSet F hh0 hℓ hsupp) hne hneB

/-- Side degrees agree under the dictionary. -/
theorem dvSideDeg_eq_sideDeg (F : KeyFrame O π) (hh0 : F.h = 0) {f : Polynomial O}
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hsupp : suppVal F.key f u ℓ ≠ ⊤)
    (hne : (dvSideSet F f u ℓ).Nonempty) (hneB : (sideSet F.key f u ℓ).Nonempty) :
    dvSideDeg F f u ℓ hne = sideDeg F.key f u ℓ hneB := by
  have hmin : dvSideMin F f u ℓ hne = sideMin F.key f u ℓ hneB :=
    dvSideMin_eq_sideMin F hh0 hℓ hsupp hne hneB
  have hmax : dvSideMax F f u ℓ hne = sideMax F.key f u ℓ hneB :=
    max'_congr (dvSideSet_eq_sideSet F hh0 hℓ hsupp) hne hneB
  show (dvSideMax F f u ℓ hne - dvSideMin F f u ℓ hne) / ℓ = _
  rw [hmin, hmax]
  rfl

/-! ## Part 5 — the residual-read bridge -/

/-- **The degenerate carrier hom** `resField F.key →+* stageField`: `AdjoinRoot.lift`
over `frameRes_eq_map` (the root of `ψ` is a root of the reduced key). -/
noncomputable def h0Hom (F : KeyFrame O π) (hh0 : F.h = 0) (H₀ : ℕ) (hpin : F.Pin H₀) :
    resField F.key →+* F.stageField H₀ hpin :=
  AdjoinRoot.lift
    ((algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)).comp
      (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))))
    (AdjoinRoot.root (F.frameRes H₀ hpin))
    (by
      calc (F.key.map (residue O)).eval₂
            ((algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)).comp
              (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))))
            (AdjoinRoot.root (F.frameRes H₀ hpin))
          = ((F.key.map (residue O)).map
                (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O)))).eval₂
              (algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin))
              (AdjoinRoot.root (F.frameRes H₀ hpin)) := (Polynomial.eval₂_map _ _ _).symm
        _ = (F.frameRes H₀ hpin).eval₂
              (algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin))
              (AdjoinRoot.root (F.frameRes H₀ hpin)) := by
            rw [← frameRes_eq_map F hh0 H₀ hpin]
        _ = 0 := by
            rw [AdjoinRoot.algebraMap_eq]
            exact AdjoinRoot.eval₂_root _)

/-- **The ϖ-read collapses to the B.25 residual read at the degenerate frame**: for `A`
below the key's degree (every development coefficient), `twistRead k A` is `resMk` at the
same height, transported along `h0Hom`.  The twist factor is `η⁻¹ ^ 0 = 1`
(`twistExp_eq_zero`), and the slot window's junk tail vanishes coefficientwise. -/
theorem twistRead_eq_h0Hom_resMk (F : KeyFrame O π) (hπ : Irreducible π) (hh0 : F.h = 0)
    (H₀ : ℕ) (hpin : F.Pin H₀) (k : ℕ) {A : Polynomial O} (hA : A.degree < F.key.degree) :
    F.twistRead H₀ hpin k A = h0Hom F hh0 H₀ hpin (resMk π F.key k A) := by
  letI : Field (F.stageField H₀ hpin) := F.stageFieldInst H₀ hpin
  -- (1) the twist dies: `η⁻¹ ^ 0 = 1`
  have hL : F.twistRead H₀ hpin k A = F.slotRes H₀ hpin k A := by
    show (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A
        = F.slotRes H₀ hpin k A
    rw [twistExp_eq_zero F hh0, pow_zero, one_mul]
  -- (2) the slot read as the clean range sum
  have hL2 : F.slotRes H₀ hpin k A = (Finset.range F.f₁).sum fun t =>
      algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π k (A.coeff t)))
        * (F.stageLetter H₀ hpin) ^ t := by
    unfold KeyFrame.slotRes
    rw [slotWindow_eq_range F hh0 k]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hidx : F.slotIdx k + F.e₁ * t = t := by
      rw [slotIdx_eq_zero F hh0, e1_eq_one F hh0, zero_add, one_mul]
    rw [hidx]
    have hdig : (k - t * F.h) / F.e₁ = k := by
      rw [hh0, e1_eq_one F hh0, mul_zero, Nat.sub_zero, Nat.div_one]
    rw [hdig]
  -- (3) the lifted residual read is the same sum (`lift ∘ mk = eval₂`, junk tail kills)
  have hR : h0Hom F hh0 H₀ hpin (resMk π F.key k A)
      = Polynomial.eval₂
          ((algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)).comp
            (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))))
          (AdjoinRoot.root (F.frameRes H₀ hpin)) (digPoly π k A) :=
    AdjoinRoot.lift_mk _ _
  have hlt : (digPoly π k A).natDegree < F.f₁ := by
    by_cases h0 : digPoly π k A = 0
    · rw [h0, Polynomial.natDegree_zero]
      exact F.hf₁
    · have hdlt : (digPoly π k A).degree < F.key.degree :=
        lt_of_le_of_lt (degree_digPoly_le hπ k A) hA
      have := Polynomial.natDegree_lt_natDegree h0 hdlt
      rwa [F.hdeg, e1_eq_one F hh0, one_mul] at this
  rw [hL, hL2, hR, Polynomial.eval₂_eq_sum_range' _ hlt]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [digPoly_coeff hπ, RingHom.comp_apply]
  rfl

/-- **The level residual IS the order-1 residual at the degenerate frame**, transported
along `h0Hom` (C.25's `dvResPoly` = B.29's `resPoly` at the key, coefficientwise by
`twistRead_eq_h0Hom_resMk` on the development coefficients). -/
theorem dvResPoly_eq_map_resPoly (F : KeyFrame O π) (hπ : Irreducible π) (hh0 : F.h = 0)
    (H₀ : ℕ) (hpin : F.Pin H₀) {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hsupp : suppVal F.key f u ℓ ≠ ⊤)
    (hne : (dvSideSet F f u ℓ).Nonempty) (hneB : (sideSet F.key f u ℓ).Nonempty)
    (M₀ : ℕ) (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) :
    dvResPoly F H₀ hpin f u ℓ hne M₀ hp
      = (resPoly π F.key f u ℓ hneB M₀).map (h0Hom F hh0 H₀ hpin) := by
  have hDpos : 0 < F.key.natDegree := by
    rw [F.hdeg]
    exact Nat.mul_pos F.he₁ F.hf₁
  have hdeg := dvSideDeg_eq_sideDeg F hh0 hℓ hsupp hne hneB
  have hmin := dvSideMin_eq_sideMin F hh0 hℓ hsupp hne hneB
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_map]
  show ((Finset.range (dvSideDeg F f u ℓ hne + 1)).sum (fun t =>
      Polynomial.C (F.twistRead H₀ hpin (M₀ - t * u)
          (dev F.key f (dvSideMin F f u ℓ hne + t * ℓ)))
        * Polynomial.X ^ t)).coeff n
    = h0Hom F hh0 H₀ hpin ((resPoly π F.key f u ℓ hneB M₀).coeff n)
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, resPoly_coeff, hdeg, hmin]
  split_ifs with hn
  · rw [Nat.mul_comm n u, Nat.mul_comm n ℓ,
      twistRead_eq_h0Hom_resMk F hπ hh0 H₀ hpin _ (degree_dev_lt F.hmonic hDpos f _)]
    rfl
  · rw [map_zero]

/-! ## Part 6 — the degenerate leg -/

set_option linter.unusedVariables false in
/-- ★ **THE `h = 0` LEG**: the declared cite `fgmn_dv_exact_mul`'s statement at the
degenerate frame — hypothesis list matched plus the ONE case hypothesis `hh0 : F.h = 0`
(`hpos`/`hpos'` carried for the match, as in C133mh3).  The dv-calculus collapses to the
order-1 chain at the key: B39a's `resPoly_mul_gen` and side laws supply everything, with
`hfloor` degenerating to exactly B39a's `0 < u`. -/
theorem fgmn_dv_exact_mul_h0 {F : KeyFrame O π} (hh0 : F.h = 0) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ) :
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp
            * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp' := by
  classical
  have hkey : IsKey F.key := isKey_key F hh0
  have hu : 0 < u := by
    have h := hfloor
    rw [hh0, mul_zero, mul_zero] at h
    exact h
  have hDpos : 0 < F.key.natDegree := by
    rw [F.hdeg]
    exact Nat.mul_pos F.he₁ F.hf₁
  have hg0 : g ≠ 0 := hg.ne_zero
  have hg0' : g' ≠ 0 := hg'.ne_zero
  -- finiteness (B.43)
  have htf : suppVal F.key g u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero F.hmonic hDpos hg0
  have htz : suppVal F.key g' u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero F.hmonic hDpos hg0'
  have htfz : suppVal F.key (g * g') u ℓ ≠ ⊤ :=
    suppVal_ne_top_of_ne_zero F.hmonic hDpos (mul_ne_zero hg0 hg0')
  -- the dictionary on the three side sets
  have hsetg := dvSideSet_eq_sideSet F hh0 hℓ htf
  have hsetg' := dvSideSet_eq_sideSet F hh0 hℓ htz
  have hsetgz := dvSideSet_eq_sideSet F hh0 hℓ htfz
  -- B-side purity data
  have hmem0g : (0 : ℕ) ∈ sideSet F.key g u ℓ := hsetg ▸ hpg.1
  have hmemEg : g.natDegree / (F.e₁ * F.f₁) ∈ sideSet F.key g u ℓ := hsetg ▸ hpg.2
  have hmem0g' : (0 : ℕ) ∈ sideSet F.key g' u ℓ := hsetg' ▸ hpg'.1
  have hmemEg' : g'.natDegree / (F.e₁ * F.f₁) ∈ sideSet F.key g' u ℓ := hsetg' ▸ hpg'.2
  have hnfB : (sideSet F.key g u ℓ).Nonempty := ⟨0, hmem0g⟩
  have hnzB : (sideSet F.key g' u ℓ).Nonempty := ⟨0, hmem0g'⟩
  have hming : sideMin F.key g u ℓ hnfB = 0 := Nat.le_zero.mp (Finset.min'_le _ 0 hmem0g)
  have hming' : sideMin F.key g' u ℓ hnzB = 0 := Nat.le_zero.mp (Finset.min'_le _ 0 hmem0g')
  obtain ⟨Hf, hHf⟩ := exists_sideMin_height hℓ htf hnfB
  obtain ⟨Hz, hHz⟩ := exists_sideMin_height hℓ htz hnzB
  -- endpoint heights vanish (monic tops)
  have hng : g.natDegree = (g.natDegree / (F.e₁ * F.f₁)) * F.key.natDegree := by
    rw [F.hdeg]
    exact (Nat.div_mul_cancel hdg).symm
  have hng' : g'.natDegree = (g'.natDegree / (F.e₁ * F.f₁)) * F.key.natDegree := by
    rw [F.hdeg]
    exact (Nat.div_mul_cancel hdg').symm
  have htopg : npHgt F.key g (g.natDegree / (F.e₁ * F.f₁)) = 0 :=
    npHgt_top F.hmonic hDpos hg hng
  have htopg' : npHgt F.key g' (g'.natDegree / (F.e₁ * F.f₁)) = 0 :=
    npHgt_top F.hmonic hDpos hg' hng'
  -- the two reads of each support value pin `ℓ·H = u·(deg/D′)`
  have hOnEg : OnSide F.key g u ℓ (g.natDegree / (F.e₁ * F.f₁)) := onSide_of_mem_sideSet hmemEg
  have hOnEg' : OnSide F.key g' u ℓ (g'.natDegree / (F.e₁ * F.f₁)) :=
    onSide_of_mem_sideSet hmemEg'
  have hsuppg : suppVal F.key g u ℓ = ((u * (g.natDegree / (F.e₁ * F.f₁)) : ℕ) : ℕ∞) := by
    have h1 := suppVal_eq_of_onSide (H := 0) (by exact_mod_cast htopg) hOnEg
    rwa [Nat.mul_zero, Nat.zero_add] at h1
  have hsuppg' : suppVal F.key g' u ℓ = ((u * (g'.natDegree / (F.e₁ * F.f₁)) : ℕ) : ℕ∞) := by
    have h1 := suppVal_eq_of_onSide (H := 0) (by exact_mod_cast htopg') hOnEg'
    rwa [Nat.mul_zero, Nat.zero_add] at h1
  have hOn0g : OnSide F.key g u ℓ 0 := onSide_of_mem_sideSet hmem0g
  have hOn0g' : OnSide F.key g' u ℓ 0 := onSide_of_mem_sideSet hmem0g'
  have hLHf : ℓ * Hf = u * (g.natDegree / (F.e₁ * F.f₁)) := by
    have hHf0 : npHgt F.key g 0 = (Hf : ℕ∞) := by
      rw [← hming]
      exact hHf
    have h1 := suppVal_eq_of_onSide hHf0 hOn0g
    rw [Nat.mul_zero, Nat.add_zero] at h1
    exact_mod_cast h1.symm.trans hsuppg
  have hLHz : ℓ * Hz = u * (g'.natDegree / (F.e₁ * F.f₁)) := by
    have hHz0 : npHgt F.key g' 0 = (Hz : ℕ∞) := by
      rw [← hming']
      exact hHz
    have h1 := suppVal_eq_of_onSide hHz0 hOn0g'
    rw [Nat.mul_zero, Nat.add_zero] at h1
    exact_mod_cast h1.symm.trans hsuppg'
  -- the product's endpoint arithmetic
  have hdeggz : (g * g').natDegree = g.natDegree + g'.natDegree :=
    Polynomial.natDegree_mul hg0 hg0'
  have hD0 : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hdgz : F.e₁ * F.f₁ ∣ (g * g').natDegree := by
    rw [hdeggz]
    exact dvd_add hdg hdg'
  have hngz : (g * g').natDegree / (F.e₁ * F.f₁)
      = g.natDegree / (F.e₁ * F.f₁) + g'.natDegree / (F.e₁ * F.f₁) := by
    obtain ⟨a, ha⟩ := hdg
    obtain ⟨b, hb⟩ := hdg'
    rw [hdeggz, ha, hb, ← Nat.mul_add, Nat.mul_div_cancel_left _ hD0,
      Nat.mul_div_cancel_left _ hD0, Nat.mul_div_cancel_left _ hD0]
  have hnggz : (g * g').natDegree
      = ((g * g').natDegree / (F.e₁ * F.f₁)) * F.key.natDegree := by
    rw [F.hdeg]
    exact (Nat.div_mul_cancel hdgz).symm
  have htopgz : npHgt F.key (g * g') ((g * g').natDegree / (F.e₁ * F.f₁)) = 0 :=
    npHgt_top F.hmonic hDpos (hg.mul hg') hnggz
  -- suppVal of the product (B39a) matches the endpoint's line
  have hsuppgz : suppVal F.key (g * g') u ℓ
      = ((u * ((g * g').natDegree / (F.e₁ * F.f₁)) : ℕ) : ℕ∞) := by
    have hsv := suppVal_mul_gen hπ hkey hu hℓ hcop htf htz hnfB hnzB hHf hHz
    rw [hming, hming'] at hsv
    rw [hsv]
    congr 1
    simp only [Nat.add_zero, Nat.mul_zero]
    rw [Nat.mul_add, hLHf, hLHz, hngz, Nat.mul_add]
  have hOnEgz : OnSide F.key (g * g') u ℓ ((g * g').natDegree / (F.e₁ * F.f₁)) := by
    show ℓ • npHgt F.key (g * g') ((g * g').natDegree / (F.e₁ * F.f₁))
        + ((u * ((g * g').natDegree / (F.e₁ * F.f₁)) : ℕ) : ℕ∞)
      = suppVal F.key (g * g') u ℓ
    rw [htopgz, smul_zero, zero_add, hsuppgz]
  have hmemEgz : (g * g').natDegree / (F.e₁ * F.f₁) ∈ sideSet F.key (g * g') u ℓ :=
    mem_sideSet_of_onSide F.hmonic hDpos hℓ htfz hOnEgz
  have hnPB : (sideSet F.key (g * g') u ℓ).Nonempty := ⟨_, hmemEgz⟩
  have hminsum := sideMin_mul_gen' hπ hkey hu hℓ hcop rfl htf htz hnfB hnzB hHf hHz hnPB
  have hmingz : sideMin F.key (g * g') u ℓ hnPB = 0 := by
    rw [hminsum, hming, hming']
  have hmem0gz : (0 : ℕ) ∈ sideSet F.key (g * g') u ℓ := by
    have hm := Finset.min'_mem (sideSet F.key (g * g') u ℓ) hnPB
    rwa [show (sideSet F.key (g * g') u ℓ).min' hnPB = 0 from hmingz] at hm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hsetgz]
    exact hmem0gz
  · rw [hsetgz]
    exact hmemEgz
  · intro hne hne' hne'' M₀ M₀' M₀'' hp hp' hp''
    -- convert the dv pins to B pins
    have hpB : npHgt F.key g (sideMin F.key g u ℓ hnfB) = (M₀ : ℕ∞) := by
      have h1 := hp
      rw [dvHgt_degenerate F hh0, dvSideMin_eq_sideMin F hh0 hℓ htf hne hnfB] at h1
      exact h1
    have hpB' : npHgt F.key g' (sideMin F.key g' u ℓ hnzB) = (M₀' : ℕ∞) := by
      have h1 := hp'
      rw [dvHgt_degenerate F hh0, dvSideMin_eq_sideMin F hh0 hℓ htz hne' hnzB] at h1
      exact h1
    have hpB'' : npHgt F.key (g * g') (sideMin F.key (g * g') u ℓ hnPB) = (M₀'' : ℕ∞) := by
      have h1 := hp''
      rw [dvHgt_degenerate F hh0, dvSideMin_eq_sideMin F hh0 hℓ htfz hne'' hnPB] at h1
      exact h1
    -- pin uniqueness
    have hMHf : M₀ = Hf := by exact_mod_cast hpB.symm.trans hHf
    have hMHz : M₀' = Hz := by exact_mod_cast hpB'.symm.trans hHz
    have hnp := npHgt_mul_gen' hπ hkey hu hℓ hcop rfl htf htz hnfB hnzB hHf hHz
    have hM'' : M₀'' = Hf + Hz := by
      rw [← hminsum] at hnp
      exact_mod_cast hpB''.symm.trans hnp
    -- transport and fire B39a's product law
    rw [dvResPoly_eq_map_resPoly F hπ hh0 H₀ hpin hℓ htfz hne'' hnPB M₀'' hp'',
      dvResPoly_eq_map_resPoly F hπ hh0 H₀ hpin hℓ htf hne hnfB M₀ hp,
      dvResPoly_eq_map_resPoly F hπ hh0 H₀ hpin hℓ htz hne' hnzB M₀' hp',
      ← Polynomial.map_mul]
    congr 1
    rw [hM'', hMHf, hMHz]
    exact resPoly_mul_gen' hπ hkey hu hℓ hcop rfl htf htz hnfB hnzB hHf hHz hnPB

/-! ## Part 7 — ★ THE FULL THEOREM: the axiom's statement, no `h` hypothesis -/

set_option linter.unusedVariables false in
/-- ★★ **THE RETIREMENT THEOREM — the declared cite `fgmn_dv_exact_mul` (C66b.lean:90),
statement BYTE-IDENTICAL, as a theorem of Lean core**: by cases on `F.h = 0` (this file's
degenerate leg) vs `0 < F.h` (C133mh3's landed `fgmn_dv_exact_mul_thm`).  The AxCheck
footer's print of this declaration at exactly `[propext, Classical.choice, Quot.sound]`
is the retirement's machine certificate. -/
theorem fgmn_dv_exact_mul_full {F : KeyFrame O π} (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree) (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ) :
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
          = dvResPoly F H₀ hpin g u ℓ hne M₀ hp
            * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp' := by
  rcases Nat.eq_zero_or_pos F.h with hh0 | hh
  · exact fgmn_dv_exact_mul_h0 hh0 hπ H₀ hpin hg hg' hℓ hcop hfloor hdg hdg'
      hpos hpos' hpg hpg'
  · exact C133mh3.fgmn_dv_exact_mul_thm hh hπ H₀ hpin hg hg' hℓ hcop hfloor hdg hdg'
      hpos hpos' hpg hpg'

end Uniformity.Density.Tower.C133h0leg

/-! ## AxCheck footer — `fgmn_dv_exact_mul_full` at Lean core is the retirement's
machine certificate -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133h0leg.isKey_key
#print axioms Uniformity.Density.Tower.C133h0leg.frameRes_eq_map
#print axioms Uniformity.Density.Tower.C133h0leg.dvSideSet_eq_sideSet
#print axioms Uniformity.Density.Tower.C133h0leg.dvResPoly_eq_map_resPoly
#print axioms Uniformity.Density.Tower.C133h0leg.fgmn_dv_exact_mul_h0
#print axioms Uniformity.Density.Tower.C133h0leg.fgmn_dv_exact_mul_full

end AxCheck
