/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10TauSupply

/-!
# Uniformity.ChapI.I10TauRows — TAU: the tau rows at abstract normalizers — the shared
vartheta gate of the capstone sockets [TAU 2026-08-31]

**Unit TAU** — what the two capstone sockets' quantification ranges ACTUALLY demand of the
tau rows (`UniversalKernelSpan` + `UniversalGeneratorDescent`, TWD), machine-checked.

## The scope verdict (charge 1)

* **(a) The deepTwist socket RECEIVES the realization abstractly**, exactly like the
  ladder guard: `CanonicalDeepTwistConfig`'s body is C130s18's
  `DeepTwistRealizationData` — an EXISTENTIAL over `ChainRealization` (`∃ E fE core Aℛ X
  eK eG, core.r = r ∧ views`).  Nothing in the body pins `Aℛ.normalizer`.
* **(b) The received normalizer is NOT constrained by the config's other laws.**  The
  view equations (`SlotViewEq`/`BlockViewEq`/`GaugeFamilyViewEq`/`ArenaFamilyViewEq`) are
  PRODUCING equalities — they pin the EXTERNAL socket data to the witness's own exports
  and hold at every realization (`RealizedInput.gaugeFamilyViewEq` etc.); `RealizedInput`'s
  five fields never mention the normalizer.  This unit MACHINE-CHECKS the freedom: TWD's
  index-2 normalizer twist (prose in `verdict_TWD.md`, BUILT here) yields a realization
  that (i) admits the verbatim `RealizedInput`, (ii) fires the LITERAL capstone I.10b
  socket body through the landed general application (`realizedInput_deepTwistConfigData`)
  — i.e. satisfies ALL the config's laws — and (iii) REFUTES `KernelSpanAt` at the
  deep-live level 3.  ★ CONSEQUENCE (stop-line): given any instance of the depth-4
  keystone parameters, **`UniversalKernelSpan n` is FALSE** — TWD's universal lattice row
  cannot be discharged as stated; the honest path to the capstone vartheta half is the
  normalizer-pinning restriction (owner amendment, flagged NOT enacted, §6).
* **Honesty pin**: the twist does NOT refute the READ-level row — at the q = 2 keystone
  the twisted witness still satisfies `CanonicalTauWordAt` (the card-2 collapse read ≡ 1,
  `m = 0, t = 0`).  What dies universally is the LATTICE route (`KernelSpanAt`), not the
  read row at the landed witnesses.

## The mechanism (the index-2 twist, machine form)

`LaurentNormalizer` carries NO additivity law — only `norm_zero` + `exact_height` — so
multiplying `norm i k` pointwise by level-kernel elements is legal (§1 `twist`).  Twisting
the canonical normalizer at level 3 at the single input `k₀ = e₃·((ê₃/ê₃)·u₃)` (the top
letter's height) by `Λ_top⁻¹` replaces the top letter class by `Λ_top²` while fixing the
other letter (its height input `e₂·((ê₃/ê₂)·u₂)` differs from `k₀` — hypothesis `hsep`,
`20 ≠ 42` at the S2 depth-4 tower) and the wrap (normalizer-free).  The top-exponent
coordinate `P` then separates: `P(Λ_top) = e₃ ∉ 2e₃ℤ = P(twisted span)` (§2).

## Charge 2 (`WrapDescentAt` vs RUNG's carrier machinery): NO reduction — machine form

RUNG's carrier packs (`I10RungPacks`) live at `LevelDatum`/polynomial carriers and consume
`normalizer`/`keys`/`receiver`-side data only; `WrapDescentAt` speaks of the node's
`canonicalRead`.  §5 machine-checks the separation at the sharpest landed altitude:
C130s18's χ-twist FIXES every field outside `node.canonicalRead` — normalizer (canonical!),
keys, receiver, arena read — yet moves the wrap value off the embedded subfield.  So no law
of the {canonical-normalizer realization + config} vocabulary (a fortiori no carrier read
law) can derive `WrapDescentAt`: it is genuinely per-realization supply (OPEN-LETTERS core,
exactly as TWD graded it).

## Post-unit tau boundary (charge 3) — see §6 and `runs/wave-c/verdict_TAU2.md`

**Flagged for human review** (trust boundary — new statements): `NormalizerPinned`,
`UniversalNormalizerPinning`, `UniversalPinnedGeneratorDescent`,
`UniversalPinnedTauWordDescentSupply` (supplier-side interface `Prop`s below the signed
surface; no leanspec name touched).  Owner items are FLAGGED, not enacted.

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_TAU2.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

/-! ## §0 The level-3 top-exponent character -/

namespace Uniformity.Density.Tower

open scoped BigOperators
open Uniformity.Density.Leaf

universe uE uG uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- **[TAU §0] The top-exponent coordinate of the level-3 Laurent lattice**: the exponent
of the top letter `Φ₂`, as a character `LevelExponentLattice 3 →* Multiplicative ℤ`.  The
separating functional of the index-2 refutation. -/
def topCoord3 : LevelExponentLattice 3 →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd ((Multiplicative.toAdd g).2.2 (Fin.last 1))
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Anti-drift pin: the character reads the top coordinate, nothing else. -/
theorem topCoord3_ofAdd (v : ℤ × ℤ × (Fin 2 → ℤ)) :
    topCoord3 (Multiplicative.ofAdd v) = Multiplicative.ofAdd (v.2.2 (Fin.last 1)) := rfl

/-- The top coordinate kills the top-zero inclusion. -/
theorem topCoord3_levelSnocHom (g : LevelExponentLattice 2) :
    topCoord3 (levelSnocHom 1 g) = 1 := by
  show Multiplicative.ofAdd
    ((Fin.snoc (Multiplicative.toAdd g).2.2 0 : Fin 2 → ℤ) (Fin.last 1)) = 1
  rw [Fin.snoc_last]
  rfl

/-- The top coordinate of the top key letter is `1`. -/
theorem topCoord3_keyLetter_last :
    topCoord3 (keyLetter 3 (Fin.last 1)) = Multiplicative.ofAdd (1 : ℤ) := by
  show Multiplicative.ofAdd
    ((Pi.single (Fin.last 1) (1 : ℤ) : Fin 2 → ℤ) (Fin.last 1)) = _
  rw [Pi.single_eq_same]

/-- The top coordinate kills the wrap generator. -/
theorem topCoord3_wrapGen (T : DeepTower F H₀ hpin r) : topCoord3 (T.wrapGen 3) = 1 := rfl

/-- The top coordinate of the CANONICAL top letter class is exactly `e₃` (via the landed
resolution `letterClass_top_coe`). -/
theorem topCoord3_letterClass_top (T : DeepTower F H₀ hpin r) (h3 : StageLive r 3) :
    topCoord3 ((T.laurentNormalizer.letterClass h3 (Fin.last 1) :
        LevelExponentLattice 3)) = Multiplicative.ofAdd (T.e 3 : ℤ) := by
  rw [T.letterClass_top_coe h3, map_mul, map_pow, map_inv, topCoord3_keyLetter_last,
    topCoord3_levelSnocHom, inv_one, mul_one, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

/-- The top coordinate kills the CANONICAL non-top letter class (via the landed inclusion
transport `levelSnocHom_letterClass`). -/
theorem topCoord3_letterClass_castSucc (T : DeepTower F H₀ hpin r)
    (h2l : StageLive r 2) (h3 : StageLive r 3) (a : Fin 1) :
    topCoord3 ((T.laurentNormalizer.letterClass h3 a.castSucc :
        LevelExponentLattice 3)) = 1 := by
  rw [← T.levelSnocHom_letterClass h2l h3 a]
  exact topCoord3_levelSnocHom _

/-! ## §1 The normalizer twist

`LaurentNormalizer` (C130k) has exactly three fields — `norm`, `norm_zero`,
`exact_height` — and NO additivity/coherence law in the height, so any pointwise
kernel-element multiple of a legal normalizer is again a legal normalizer.  This is the
freedom TWD's charge-1 finding names; here it is a CONSTRUCTION. -/

/-- **[TAU §1] The pointwise kernel twist of a normalizer**: multiply `norm i k` by a
kernel-valued family `t i k` with `t i 0 = 1`.  Legal because the interface demands only
`norm_zero` + `exact_height`. -/
def LaurentNormalizer.twist {W : DeepTower.{0, uKt} F H₀ hpin r}
    (N : LaurentNormalizer W) (t : (i : ℕ) → ℤ → LevelExponentLattice i)
    (ht0 : ∀ i, t i 0 = 1)
    (htker : ∀ i, StageLive r i → ∀ k, levelExponentHeight W i (t i k) = 1) :
    LaurentNormalizer W where
  norm i k := N.norm i k * t i k
  norm_zero i := by rw [ht0 i, mul_one]; exact N.norm_zero i
  exact_height i hi k := by
    rw [map_mul, htker i hi k, mul_one]
    exact N.exact_height i hi k

/-- The level-3 single-input twist family: `z` at exactly `(3, k₀)`, trivial elsewhere. -/
def twistFamily3 (k₀ : ℤ) (z : LevelExponentLattice 3) :
    (i : ℕ) → ℤ → LevelExponentLattice i
  | 3 => fun k => if k = k₀ then z else 1
  | _ => fun _ => 1

theorem twistFamily3_zero (k₀ : ℤ) (hk₀ : k₀ ≠ 0) (z : LevelExponentLattice 3) :
    ∀ i, twistFamily3 k₀ z i 0 = 1 := by
  intro i
  rcases i with _ | _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · exact if_neg fun h => hk₀ h.symm
  · rfl

theorem twistFamily3_height {W : DeepTower.{0, uKt} F H₀ hpin r} (k₀ : ℤ)
    {z : LevelExponentLattice 3} (hz : levelExponentHeight W 3 z = 1) :
    ∀ i, StageLive r i → ∀ k, levelExponentHeight W i (twistFamily3 k₀ z i k) = 1 := by
  intro i hi k
  rcases i with _ | _ | _ | _ | i
  · exact map_one _
  · exact map_one _
  · exact map_one _
  · show levelExponentHeight W 3 (if k = k₀ then z else 1) = 1
    split
    · exact hz
    · exact map_one _
  · exact map_one _

/-- **[TAU §1] The level-3 single-input normalizer twist.** -/
def LaurentNormalizer.twistAt3 {W : DeepTower.{0, uKt} F H₀ hpin r}
    (N : LaurentNormalizer W) (k₀ : ℤ) (hk₀ : k₀ ≠ 0) (z : LevelExponentLattice 3)
    (hz : levelExponentHeight W 3 z = 1) : LaurentNormalizer W :=
  N.twist (twistFamily3 k₀ z) (twistFamily3_zero k₀ hk₀ z) (twistFamily3_height k₀ hz)

/-- The twisted norm at the twisted input (input-congruent form, so `rfl` discharges the
definitional-equality side condition at letter-height expressions). -/
theorem LaurentNormalizer.twistAt3_norm_eq {W : DeepTower.{0, uKt} F H₀ hpin r}
    (N : LaurentNormalizer W) (k₀ : ℤ) (hk₀ : k₀ ≠ 0) (z : LevelExponentLattice 3)
    (hz : levelExponentHeight W 3 z = 1) {k : ℤ} (hk : k = k₀) :
    (N.twistAt3 k₀ hk₀ z hz).norm 3 k = N.norm 3 k * z := by
  show N.norm 3 k * (if k = k₀ then z else 1) = N.norm 3 k * z
  rw [if_pos hk]

/-- The twisted norm away from the twisted input. -/
theorem LaurentNormalizer.twistAt3_norm_ne {W : DeepTower.{0, uKt} F H₀ hpin r}
    (N : LaurentNormalizer W) (k₀ : ℤ) (hk₀ : k₀ ≠ 0) (z : LevelExponentLattice 3)
    (hz : levelExponentHeight W 3 z = 1) {k : ℤ} (hk : k ≠ k₀) :
    (N.twistAt3 k₀ hk₀ z hz).norm 3 k = N.norm 3 k := by
  show N.norm 3 k * (if k = k₀ then z else 1) = N.norm 3 k
  rw [if_neg hk, mul_one]

/-! ## §2 The index-2 refutation at the lattice

The twisted normalizer's letter classes: the non-top letter is UNCHANGED (its height
input differs from the twist input — `hsep`), the top letter DOUBLES (`Λ_top ↦ Λ_top²`).
The top-exponent character then separates the canonical `Λ_top` from the twisted span:
`e₃ ∉ 2e₃ℤ`.  This is TWD's charge-1 prose finding ("index 2"), machine-checked. -/

/-- The level-3 letter-height input at letter `a` — the exact expression `letterClass`
feeds the normalizer (definitionally). -/
def letterInput3 (W : DeepTower.{0, uKt} F H₀ hpin r) (a : Fin 2) : ℤ :=
  (W.e (a.1 + 2) : ℤ) * ((W.ehat 3 : ℤ) / (W.ehat (a.1 + 2) : ℤ) * (W.u (a.1 + 2) : ℤ))

/-- `letterClass_coe` with the height input in `letterInput3` form (definitional). -/
theorem letterClass_coe3 {W : DeepTower.{0, uKt} F H₀ hpin r} (N : LaurentNormalizer W)
    (h3 : StageLive r 3) (a : Fin 2) :
    (N.letterClass h3 a : LevelExponentLattice 3)
      = keyLetter 3 a ^ W.e (a.1 + 2) * (N.norm 3 (letterInput3 W a))⁻¹ :=
  N.letterClass_coe h3 a

/-- **[TAU §2] The top-twisted canonical normalizer**: the CC-4 greedy normalizer twisted
at the single input `k₀ = letterInput3 T (Fin.last 1)` (the top letter's height) by
`Λ_top⁻¹`. -/
def DeepTower.topTwistedNormalizer (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0) :
    LaurentNormalizer T :=
  T.laurentNormalizer.twistAt3 (letterInput3 T (Fin.last 1)) hk₀
    ((T.laurentNormalizer.letterClass h3 (Fin.last 1) : LevelExponentLattice 3))⁻¹
    (by rw [map_inv, MonoidHom.mem_ker.mp
        (T.laurentNormalizer.letterClass h3 (Fin.last 1)).2, inv_one])

/-- The twisted norm away from the twist input, in `letterInput3` form. -/
theorem topTwistedNormalizer_norm_ne (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0) {k : ℤ}
    (hk : k ≠ letterInput3 T (Fin.last 1)) :
    (T.topTwistedNormalizer h3 hk₀).norm 3 k = T.laurentNormalizer.norm 3 k :=
  LaurentNormalizer.twistAt3_norm_ne _ _ _ _ _ hk

/-- The twisted norm at the twist input, in `letterInput3` form. -/
theorem topTwistedNormalizer_norm_eq (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0) :
    (T.topTwistedNormalizer h3 hk₀).norm 3 (letterInput3 T (Fin.last 1))
      = T.laurentNormalizer.norm 3 (letterInput3 T (Fin.last 1))
        * ((T.laurentNormalizer.letterClass h3 (Fin.last 1) :
            LevelExponentLattice 3))⁻¹ :=
  LaurentNormalizer.twistAt3_norm_eq _ _ _ _ _ rfl

/-- The twist misses the non-top letter: its class is the canonical one. -/
theorem topTwisted_letterClass_castSucc (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0)
    (hsep : letterInput3 T (Fin.castSucc 0) ≠ letterInput3 T (Fin.last 1)) :
    (((T.topTwistedNormalizer h3 hk₀).letterClass h3 (Fin.castSucc 0)) :
        LevelExponentLattice 3)
      = ((T.laurentNormalizer.letterClass h3 (Fin.castSucc 0)) :
        LevelExponentLattice 3) := by
  rw [letterClass_coe3, letterClass_coe3, topTwistedNormalizer_norm_ne T h3 hk₀ hsep]

/-- The twist DOUBLES the top letter: `Λ'_top = Λ_top · Λ_top`. -/
theorem topTwisted_letterClass_top (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0) :
    (((T.topTwistedNormalizer h3 hk₀).letterClass h3 (Fin.last 1)) :
        LevelExponentLattice 3)
      = ((T.laurentNormalizer.letterClass h3 (Fin.last 1)) : LevelExponentLattice 3)
        * ((T.laurentNormalizer.letterClass h3 (Fin.last 1)) :
            LevelExponentLattice 3) := by
  rw [letterClass_coe3, topTwistedNormalizer_norm_eq T h3 hk₀, mul_inv, inv_inv,
    ← mul_assoc, ← letterClass_coe3]

/-- ★★ **[TAU §2] THE INDEX-2 REFUTATION, lattice form** — the canonical top letter class
(a level-3 KERNEL element) is NOT a distinguished-generator word of the top-twisted
normalizer: applying the top-exponent character, the twisted span's top coordinates are
`2e₃ℤ` (wrap and the non-top letter contribute `0`; the twisted top letter contributes
`2e₃`), while `Λ_top` sits at `e₃ ≠ 0`.  TWD's prose "index 2" finding, machine-checked;
the hypotheses `hk₀`/`hsep` are numeric side conditions discharged at the S2 depth-4
tower (`42 ≠ 0`, `20 ≠ 42`). -/
theorem topTwisted_letterClass_not_generatorWord (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0)
    (hsep : letterInput3 T (Fin.castSucc 0) ≠ letterInput3 T (Fin.last 1)) :
    ¬ ∃ (m : ℤ) (t : Fin (3 - 1) → ℤ),
      T.laurentNormalizer.letterClass h3 (Fin.last 1)
        = (T.topTwistedNormalizer h3 hk₀).generatorWord h3 m t := by
  have h2l : StageLive r 2 := ⟨by omega, by
    have := h3.2
    omega⟩
  rintro ⟨m, t, hword⟩
  have hcoe := congrArg (fun w : MonoidHom.ker (levelExponentHeight T 3) =>
    topCoord3 (w : LevelExponentLattice 3)) hword
  simp only [LaurentNormalizer.generatorWord, MulMemClass.coe_mul,
    SubgroupClass.coe_zpow, SubmonoidClass.coe_finsetProd, DeepTower.wrapClass_coe,
    map_mul, map_zpow, map_prod] at hcoe
  rw [topCoord3_letterClass_top T h3, topCoord3_wrapGen T, one_zpow, one_mul] at hcoe
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_one,
    topTwisted_letterClass_castSucc T h3 hk₀ hsep,
    topCoord3_letterClass_castSucc T h2l h3 0, one_zpow, one_mul,
    topTwisted_letterClass_top T h3 hk₀, map_mul,
    topCoord3_letterClass_top T h3, ← ofAdd_add, ← ofAdd_zsmul] at hcoe
  have hint : (T.e 3 : ℤ) = t (Fin.last 1) • ((T.e 3 : ℤ) + (T.e 3 : ℤ)) :=
    Multiplicative.ofAdd.injective hcoe
  rw [smul_eq_mul] at hint
  have he3 : (0 : ℤ) < (T.e 3 : ℤ) := by
    exact_mod_cast T.he 3 (by omega) h3.2
  have h1 : (T.e 3 : ℤ) * 1 = (T.e 3 : ℤ) * (2 * t (Fin.last 1)) := by
    linear_combination hint
  have h2 : (1 : ℤ) = 2 * t (Fin.last 1) := mul_left_cancel₀ (ne_of_gt he3) h1
  omega

/-- The twisted normalizer is NOT the canonical one (the pin behind "the pinning cannot be
a free per-realization supply"): equality would force `Λ_top = 1`, whose top coordinate is
`e₃ > 0`. -/
theorem topTwistedNormalizer_ne_laurent (T : DeepTower.{0, uKt} F H₀ hpin r)
    (h3 : StageLive r 3) (hk₀ : letterInput3 T (Fin.last 1) ≠ 0) :
    T.topTwistedNormalizer h3 hk₀ ≠ T.laurentNormalizer := by
  intro heq
  have hnorm : (T.topTwistedNormalizer h3 hk₀).norm 3 (letterInput3 T (Fin.last 1))
      = T.laurentNormalizer.norm 3 (letterInput3 T (Fin.last 1)) := by rw [heq]
  rw [topTwistedNormalizer_norm_eq T h3 hk₀] at hnorm
  have hinv : ((T.laurentNormalizer.letterClass h3 (Fin.last 1) :
      LevelExponentLattice 3))⁻¹ = 1 :=
    mul_left_cancel (hnorm.trans (mul_one _).symm)
  have htop : topCoord3 ((T.laurentNormalizer.letterClass h3 (Fin.last 1) :
      LevelExponentLattice 3)) = 1 := by
    rw [← inv_inv ((T.laurentNormalizer.letterClass h3 (Fin.last 1) :
      LevelExponentLattice 3)), hinv, inv_one, map_one]
  rw [topCoord3_letterClass_top T h3] at htop
  have he3 : (0 : ℤ) < (T.e 3 : ℤ) := by exact_mod_cast T.he 3 (by omega) h3.2
  have h0 : (T.e 3 : ℤ) = 0 := ofAdd_eq_one.mp htop
  omega

/-! ## §3 Realization plumbing: the socket's laws never see the normalizer

`ChainRealization` = {receiver, keys, normalizer, node}; `RealizedInput`'s five fields
(`receiver_eq`/`stageKey_eq`/`stageDeg_eq`/`point`/`point_mem`) mention receiver, keys,
and node ONLY.  So replacing the normalizer transports the realized input VERBATIM — the
normalizer field is free at every received witness (the dual of C130s18's
`twistRealization`, which frees `canonicalRead` while fixing the normalizer). -/

/-- Replace ONLY the normalizer of a chain realization. -/
def ChainRealization.setNormalizer {W : DeepTower.{0, uKt} F H₀ hpin r}
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
    [Algebra Kt L] (A : ChainRealization W Kt E L) (N' : LaurentNormalizer W) :
    ChainRealization W Kt E L :=
  { A with normalizer := N' }

section SetNormalizer

variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]

@[simp] theorem setNormalizer_receiver (A : ChainRealization W Kt E L)
    (N' : LaurentNormalizer W) : (A.setNormalizer N').receiver = A.receiver := rfl

@[simp] theorem setNormalizer_keys (A : ChainRealization W Kt E L)
    (N' : LaurentNormalizer W) : (A.setNormalizer N').keys = A.keys := rfl

@[simp] theorem setNormalizer_normalizer (A : ChainRealization W Kt E L)
    (N' : LaurentNormalizer W) : (A.setNormalizer N').normalizer = N' := rfl

@[simp] theorem setNormalizer_node (A : ChainRealization W Kt E L)
    (N' : LaurentNormalizer W) : (A.setNormalizer N').node = A.node := rfl

end SetNormalizer

section InputTransport

variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {n : ℕ} {core : ArisingCore (O := O) Kt L n}

/-- **[TAU §3] The realized input survives ANY normalizer replacement verbatim** — no
field of `RealizedInput` mentions the normalizer. -/
def RealizedInput.setNormalizer
    {A : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core A) (N' : LaurentNormalizer core.T) :
    RealizedInput core (A.setNormalizer N') where
  receiver_eq := X.receiver_eq
  stageKey_eq := X.stageKey_eq
  stageDeg_eq := X.stageDeg_eq
  point := X.point
  point_mem := X.point_mem

end InputTransport

end Uniformity.Density.Tower

/-! ## §3b The per-realization refutation wrapper -/

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

section Wrapper

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}

/-- ★ **[TAU §3] `KernelSpanAt` is REFUTED at every realization carrying the top-twisted
normalizer** (numeric side conditions `hk₀`/`hsep` at the core's tower). -/
theorem not_kernelSpanAt_of_topTwisted
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (hj : GaugeLive core.r 3)
    (hk₀ : letterInput3 core.T (Fin.last 1) ≠ 0)
    (hsep : letterInput3 core.T (Fin.castSucc 0) ≠ letterInput3 core.T (Fin.last 1))
    (hN : Aℛ.normalizer = core.T.topTwistedNormalizer hj.stageLive hk₀) :
    ¬ KernelSpanAt Aℛ 3 hj := by
  intro hspan
  obtain ⟨m, t, hword⟩ :=
    hspan (core.T.laurentNormalizer.letterClass hj.stageLive (Fin.last 1))
  rw [hN] at hword
  exact topTwisted_letterClass_not_generatorWord core.T hj.stageLive hk₀ hsep
    ⟨m, t, hword⟩

end Wrapper

/-! ## §4 The keystone instantiation: the socket fires at the twisted witness

The S2 depth-4 tower has `e ≡ 2`, `u = (1, 5, 21, 85)`, `ê = (2, 4, 8, 16)`; the two
level-3 letter-height inputs are `20 = 2·((8/4)·5)` and `42 = 2·((8/8)·21)` — distinct,
so the twist at input `42` misses the non-top letter, and `e₃ = 2 > 0` powers the index-2
separation.  Everything below is exactly as conditional as the landed keystone theorems
(TWD §5, USUP §5): the S2 hypotheses + the four threshold datums + the R8/R8r payload. -/

section Keystone

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- Value pin: the S2 depth-4 TOP letter-height input is `42 = e₃·((ê₃/ê₃)·u₃) = 2·21`. -/
theorem s2Four_letterInput3_top_eq :
    letterInput3 (s2DepthFour h2 hq) (Fin.last 1) = 42 := by
  have he : (s2DepthFour h2 hq).e 3 = 2 := rfl
  have hu : (s2DepthFour h2 hq).u 3 = 21 := rfl
  have hh : (s2DepthFour h2 hq).ehat 3 = 8 := s2four_ehat_three h2 hq
  simp only [letterInput3, Fin.val_last, Nat.reduceAdd, he, hu, hh]
  norm_num

/-- Value pin: the S2 depth-4 non-top letter-height input is `20 = e₂·((ê₃/ê₂)·u₂) =
2·(2·5)`. -/
theorem s2Four_letterInput3_castSucc_eq :
    letterInput3 (s2DepthFour h2 hq) (Fin.castSucc 0) = 20 := by
  have he : (s2DepthFour h2 hq).e 2 = 2 := rfl
  have hu : (s2DepthFour h2 hq).u 2 = 5 := rfl
  have hh2 : (s2DepthFour h2 hq).ehat 2 = 4 := s2four_ehat_two h2 hq
  have hh3 : (s2DepthFour h2 hq).ehat 3 = 8 := s2four_ehat_three h2 hq
  simp only [letterInput3, Fin.val_castSucc, Fin.val_zero, Nat.reduceAdd, he, hu, hh2, hh3]
  norm_num

/-- Numeric side condition 1: the S2 depth-4 top letter-height input `42 ≠ 0`. -/
theorem s2Four_letterInput3_top_ne_zero :
    letterInput3 (s2DepthFour h2 hq) (Fin.last 1) ≠ 0 := by
  rw [s2Four_letterInput3_top_eq h2 hq]
  norm_num

/-- Numeric side condition 2: the two S2 depth-4 letter-height inputs are distinct
(`20 ≠ 42`), so the single-input twist misses the non-top letter. -/
theorem s2Four_letterInput3_sep :
    letterInput3 (s2DepthFour h2 hq) (Fin.castSucc 0)
      ≠ letterInput3 (s2DepthFour h2 hq) (Fin.last 1) := by
  rw [s2Four_letterInput3_top_eq h2 hq, s2Four_letterInput3_castSucc_eq h2 hq]
  norm_num

/-- **[TAU §4] The twisted keystone normalizer** (legal by construction; ≠ canonical by
`s2FourTwisted_not_pinned` below). -/
noncomputable def s2FourTwistedNormalizer : LaurentNormalizer (s2DepthFour h2 hq) :=
  (s2DepthFour h2 hq).topTwistedNormalizer ⟨by omega, by omega⟩
    (s2Four_letterInput3_top_ne_zero h2 hq)

variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)

/-- **[TAU §4] The TWISTED depth-four realization**: the landed keystone witness with
ONLY the normalizer replaced — every other field byte-shared. -/
noncomputable def s2FourTwistedRealization :
    ChainRealization (s2DepthFour h2 hq) ((s2DepthFour h2 hq).fld 4)
      (FractionRing (Polynomial O)) L :=
  (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).setNormalizer
    (s2FourTwistedNormalizer h2 hq)

variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

/-- The realized input at the twisted witness — VERBATIM transport (no `RealizedInput`
field mentions the normalizer). -/
noncomputable def s2FourTwistedInput :
    RealizedInput (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄) :=
  (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
    F₀ hF₀ μ hμ hdeg hblock hcop).setNormalizer (s2FourTwistedNormalizer h2 hq)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- The twisted witness is NOT canonically normalized — the pinning is genuinely violated
by a legal received witness, so it cannot be derived; making it a GUARD is the §6 owner
amendment. -/
theorem s2FourTwisted_not_pinned :
    (s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄).normalizer
      ≠ (s2DepthFour h2 hq).laurentNormalizer :=
  topTwistedNormalizer_ne_laurent (s2DepthFour h2 hq) ⟨by omega, by omega⟩
    (s2Four_letterInput3_top_ne_zero h2 hq)

/-- ★ **[TAU §4] `KernelSpanAt` is REFUTED at the twisted keystone witness** at the
deep-live level `3`. -/
theorem s2FourTwisted_not_kernelSpanAt (hj : GaugeLive 4 3) :
    ¬ KernelSpanAt (core := s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄) 3 hj :=
  not_kernelSpanAt_of_topTwisted _ hj (s2Four_letterInput3_top_ne_zero h2 hq)
    (s2Four_letterInput3_sep h2 hq) rfl

/-- ★★ **[TAU §4] THE SOCKET FIRES AT THE TWISTED WITNESS** — the LITERAL capstone I.10b
socket body `CanonicalDeepTwistConfig` (leanspec-typed, `uE = 0` profile) holds at the
twisted witness's own exports, through the landed general application
`realizedInput_deepTwistConfigData`.  The falsifying twist satisfies ALL the config's
laws: together with `s2FourTwisted_not_kernelSpanAt`, charge (b) is SETTLED — the view
equations do NOT constrain the received normalizer, and no proof of kernel-span from the
config laws can exist. -/
theorem s2FourTwisted_canonicalDeepTwistConfig :
    CanonicalDeepTwistConfig.{uG, 0, uL}
      ((s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).stageCarrierTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      ((s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).inputBlockTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      (GaugeLattice.{uG} 4) ((s2DepthFour h2 hq).fld 4) L
      ((s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (arenaFamily (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop)
        (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop))
      (towerReadFamily (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      ((s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily) 4 n :=
  realizedInput_deepTwistConfigData
    (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (RingEquiv.refl ((s2DepthFour h2 hq).fld 4))
    (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)

include h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop in
/-- ★★ **[TAU §4] STOP-LINE: `UniversalKernelSpan` is REFUTED** given any instance of the
depth-4 keystone parameters — TWD's universal lattice row (row C3 across the abstract
normalizer field) cannot be discharged as stated at any degree hosting a keystone
occurrence; the capstone vartheta half's honest route is the normalizer-pinning owner
amendment (§6).  Conditionality: exactly the landed keystone theorems'. -/
theorem s2Four_not_universalKernelSpan : ¬ UniversalKernelSpan.{0, uL} n := by
  intro h
  have hdeep : DeepLive 4 3 := ⟨by omega, by omega⟩
  exact s2FourTwisted_not_kernelSpanAt h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
    hdeep.gaugeLive
    (h O ((s2DepthFour h2 hq).fld 4) (FractionRing (Polynomial O)) L
      (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄)
      (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      3 hdeep)

/-- **[TAU §4] HONESTY PIN — the READ row SURVIVES the twist at the keystone**:
`CanonicalTauWordAt` holds at the TWISTED witness (`m = 0, t = 0`: the level-3 canonical
read is constantly `1` and the twist never touches the node).  The refutation kills the
LATTICE route (`KernelSpanAt`/`UniversalKernelSpan`), NOT the read-level row at `q = 2` —
at general residue cardinality the read row stays exactly as open as TWD graded it. -/
theorem s2FourTwisted_canonicalTauWordAt (hj : GaugeLive 4 3) :
    CanonicalTauWordAt.{uG, 0, uL}
      (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj := by
  intro s
  refine ⟨0, 0, (canonicalResFamily_eq_canonicalResAt
    (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj
    (canonical_tau_mem_family
      (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) hj _ _)
    (canonical_tau_mem
      (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
      hj _ _)).trans ?_⟩
  refine (s2Four_canonicalResAt_eq_one h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop
    hj _).trans ?_
  simp

end Keystone

/-! ## §5 Charge 2 — `WrapDescentAt` does NOT reduce to carrier-side laws

RUNG's carrier packs (`I10RungPacks`) live at `LevelDatum`/polynomial carriers; every law
they consume sits on the `normalizer`/`keys`/`receiver`/FGMN side.  `WrapDescentAt`
speaks of `node.canonicalRead` at the wrap class.  The separation, at the sharpest landed
altitude: C130s18's χ-twist FIXES every realization field except `node.canonicalRead` —
in particular the normalizer stays CANONICAL — and transports the `RealizedInput`
verbatim, yet moves the wrap value off the embedded subfield.  So no derivation UNIFORM
in {canonical-normalizer realization + realized input} — a fortiori none from carrier
read laws, which the twist does not touch — can produce `WrapDescentAt`.  It is genuinely
per-realization supply: the OPEN-LETTERS core, exactly as TWD graded row R5. -/

section WrapSeparation

open Uniformity.Density.Tower.C130s18

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}
  {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L}

/-- The χ-twist moves the wrap value by exactly the character's value at the wrap class
(the node-level pin the separation consumes). -/
theorem twistRealization_wrapValue
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    {j : ℕ} (hj : StageLive core.r j) :
    (twistRealization Aℛ χ).node.wrapValue hj
      = Aℛ.node.wrapValue hj * χ j (core.T.wrapClass hj) := rfl

/-- The χ-twist keeps the normalizer — a canonically-normalized realization stays
canonically normalized (the carrier side is FIXED while the wrap value moves). -/
theorem twistRealization_normalizer
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ) :
    (twistRealization Aℛ χ).normalizer = Aℛ.normalizer := rfl

/-- The χ-twist keeps the keys and the receiver (the other carrier-side fields). -/
theorem twistRealization_keys_receiver
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ) :
    (twistRealization Aℛ χ).keys = Aℛ.keys ∧
      (twistRealization Aℛ χ).receiver = Aℛ.receiver := ⟨rfl, rfl⟩

/-- ★ **[TAU §5] `WrapDescentAt` is NOT uniform over canonically-normalized realizations**
— the wrap clause cannot be derived from ANY law of the
{canonical normalizer + keys + receiver + realized input + config} vocabulary: the
χ-twisted realization satisfies every one of those laws with the SAME carrier data (pins
above; the twisted input exports the literal socket data by C130s18's
`twist_supplies_ladderConfigData`), yet if the character's value at the wrap class avoids
the embedded subfield, the untwisted and twisted witnesses cannot both satisfy
`WrapDescentAt`.  A fortiori NO carrier read law (RUNG's `LevelDatum` machinery included)
implies the wrap clause: row R5's wrap remainder is genuinely per-realization supply. -/
theorem wrapDescentAt_not_uniform (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j)
    (hN : Aℛ.normalizer = core.T.laurentNormalizer)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    (hχ : ∀ y : Kt, ((χ j (core.T.wrapClass hj.stageLive) : Lˣ) : L)
      ≠ algebraMap Kt L y)
    (huniform : ∀ (A' : ChainRealization (O := O) (π := core.π) (F := core.F)
        (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L),
      RealizedInput core A' → A'.normalizer = core.T.laurentNormalizer →
        WrapDescentAt A' j hj) :
    False := by
  obtain ⟨u₁, hu₁⟩ := huniform Aℛ X hN
  obtain ⟨u₂, hu₂⟩ := huniform (twistRealization Aℛ χ) (twistRealizedInput X χ)
    ((twistRealization_normalizer χ).trans hN)
  rw [twistRealization_wrapValue χ hj.stageLive, hu₁] at hu₂
  refine hχ ((u₂ : Kt) * (u₁ : Kt)⁻¹) ?_
  have hval : ((χ j (core.T.wrapClass hj.stageLive) : Lˣ) : L)
      = ((unitAlgebraMap u₂ * (unitAlgebraMap u₁)⁻¹ : Lˣ) : L) := by
    rw [← hu₂]
    simp [mul_comm]
  rw [hval]
  simp [unitAlgebraMap, map_mul, map_inv₀]

end WrapSeparation

/-! ## §6 The post-unit boundary: the minimal restriction, owner-flagged (NOT enacted)

After §4, `UniversalKernelSpan` is dead as stated, and `NormalizerPinned` (below) is
equally dead as an unguarded universal supply (`s2FourTwisted_not_pinned` exhibits a
legal received witness violating it).  The minimal restriction is therefore STRUCTURAL —
owner-amendment territory, exactly TWD's recorded recommendation, in either equivalent
form:

* **(O-TAU-1)** pin `ChainRealization.normalizer := W.laurentNormalizer` (drop the free
  field) — TWD's original recommendation; or
* **(O-TAU-2)** conjoin `NormalizerPinned` into `DeepTwistRealizationData`'s existential
  (the socket then RECEIVES only pinned witnesses).

Under either amendment the guarded forms below become the operative universal supplies:
the kernel-span leg is FREE under the guard (`kernelSpanAt_of_laurent`), so the
capstone's vartheta half reduces to `UniversalPinnedGeneratorDescent` — row R5 only
(wrap = §5's per-realization supply + the letter receiver equalities).  NEITHER amendment
is enacted here; no leanspec name is touched. -/

section Boundary

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}

/-- **[TAU §6] The pinning Prop** — the received realization's normalizer is the CC-4
canonical (Laurent) one.  True by `rfl` at every landed witness; violated by the §4
twisted witness, so it can only enter as a structural GUARD (owner amendment), never as
a universal supply.  NEW STATEMENT (review). -/
def NormalizerPinned
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L) : Prop :=
  Aℛ.normalizer = core.T.laurentNormalizer

/-- Under the pin, the whole tau supply needs only descent (the landed TWD compilation,
re-expressed at the guard). -/
theorem tauWordDescentSupply_of_pinned_descent
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hN : NormalizerPinned Aℛ)
    (hdesc : ∀ j, (hj : DeepLive core.r j) →
      CanonicalGeneratorDescent Aℛ j hj.gaugeLive) :
    TauWordDescentSupply.{uG, uKt, uL} X :=
  tauWordDescentSupply_of_laurent_descent X hN hdesc

end Boundary

/-- **[TAU §6] The pinning as an unguarded universal Prop** — recorded ONLY to be refuted
(`s2Four_not_universalPinning`): this shape is NOT the amendment.  NEW STATEMENT
(review). -/
def UniversalNormalizerPinning (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L),
    RealizedInput core Aℛ → NormalizerPinned Aℛ

/-- **[TAU §6] The pinned universal descent** — row R5 at every PINNED arising
realization: the operative supply under the owner amendment.  NEW STATEMENT (review). -/
def UniversalPinnedGeneratorDescent (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ), NormalizerPinned Aℛ →
    ∀ j, (hj : DeepLive core.r j) → CanonicalGeneratorDescent Aℛ j hj.gaugeLive

/-- **[TAU §6] The pinned universal tau supply** — the guarded form of USUP's
`UniversalTauWordDescentSupply`: what the capstone vartheta half consumes AFTER the owner
amendment.  NEW STATEMENT (review). -/
def UniversalPinnedTauWordDescentSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ), NormalizerPinned Aℛ →
    TauWordDescentSupply.{uG, uKt, uL} X

/-- ★ **[TAU §6] Under the guard, row C3 vanishes**: the pinned universal descent alone
gives the pinned universal tau supply — the kernel-span leg is FREE
(`kernelSpanAt_of_laurent`).  With the owner amendment enacted this is the capstone
vartheta half's whole remaining tau boundary: row R5. -/
theorem universalPinnedTauSupply_of_descent {n : ℕ}
    (hd : UniversalPinnedGeneratorDescent.{uKt, uL} n) :
    UniversalPinnedTauWordDescentSupply.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X hN
  exact tauWordDescentSupply_of_pinned_descent X hN
    (hd O Kt E L core Aℛ X hN)

section NotUniversalPinning

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

include h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop in
/-- ★ **[TAU §6] The unguarded pinning is REFUTED** at the §4 twisted witness — the
pinning can only be a structural guard (owner amendment), never a free per-realization
supply.  Conditionality: exactly the landed keystone theorems'. -/
theorem s2Four_not_universalPinning : ¬ UniversalNormalizerPinning.{0, uL} n := by
  intro h
  exact s2FourTwisted_not_pinned h2 hq L w₁ w₂ w₃ w₄
    (h O ((s2DepthFour h2 hq).fld 4) (FractionRing (Polynomial O)) L
      (s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop)
      (s2FourTwistedRealization h2 hq L w₁ w₂ w₃ w₄)
      (s2FourTwistedInput h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop))

end NotUniversalPinning

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint (incremental footer — extended as sections land) -/

section AxCheck

#print axioms Uniformity.Density.Tower.topCoord3
#print axioms Uniformity.Density.Tower.topCoord3_letterClass_top
#print axioms Uniformity.Density.Tower.topCoord3_letterClass_castSucc
#print axioms Uniformity.Density.Tower.LaurentNormalizer.twist
#print axioms Uniformity.Density.Tower.LaurentNormalizer.twistAt3
#print axioms Uniformity.Density.Tower.DeepTower.topTwistedNormalizer
#print axioms Uniformity.Density.Tower.topTwisted_letterClass_top
#print axioms Uniformity.Density.Tower.topTwisted_letterClass_not_generatorWord
#print axioms Uniformity.Density.Tower.topTwistedNormalizer_ne_laurent
#print axioms Uniformity.Density.Tower.ChainRealization.setNormalizer
#print axioms Uniformity.Density.Tower.RealizedInput.setNormalizer
#print axioms Uniformity.Density.DeepExport.not_kernelSpanAt_of_topTwisted
#print axioms Uniformity.Density.DeepExport.s2FourTwistedRealization
#print axioms Uniformity.Density.DeepExport.s2FourTwistedInput
#print axioms Uniformity.Density.DeepExport.s2FourTwisted_not_pinned
#print axioms Uniformity.Density.DeepExport.s2FourTwisted_not_kernelSpanAt
#print axioms Uniformity.Density.DeepExport.s2FourTwisted_canonicalDeepTwistConfig
#print axioms Uniformity.Density.DeepExport.s2Four_not_universalKernelSpan
#print axioms Uniformity.Density.DeepExport.s2FourTwisted_canonicalTauWordAt
#print axioms Uniformity.Density.DeepExport.twistRealization_wrapValue
#print axioms Uniformity.Density.DeepExport.wrapDescentAt_not_uniform
#print axioms Uniformity.Density.DeepExport.NormalizerPinned
#print axioms Uniformity.Density.DeepExport.tauWordDescentSupply_of_pinned_descent
#print axioms Uniformity.Density.DeepExport.UniversalNormalizerPinning
#print axioms Uniformity.Density.DeepExport.UniversalPinnedGeneratorDescent
#print axioms Uniformity.Density.DeepExport.UniversalPinnedTauWordDescentSupply
#print axioms Uniformity.Density.DeepExport.universalPinnedTauSupply_of_descent
#print axioms Uniformity.Density.DeepExport.s2Four_not_universalPinning

end AxCheck
