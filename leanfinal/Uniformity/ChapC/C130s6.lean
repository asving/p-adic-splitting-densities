/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B32a
import Uniformity.ChapB.B32b
import Uniformity.ChapB.B35a
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B41a
import Uniformity.ChapC.C118a
import Uniformity.ChapC.C130s2
import Uniformity.ChapC.C130st

/-!
# Uniformity.ChapC.C130s6 — the S2 level-2 stage-source fields (chain-carrier node CC-6)

**Chain-carrier node CC-6** (`CHAIN_CARRIER_DESIGN_2026-08-24.md` §4.2, §6 stage row, §10 row
CC-6: "Fill every stage-source field at the S2 level-2 occurrence"): the concrete stage
VALUE / DIGIT / FULL / LIFT source family at level 2 of the S2 depth-two tower
`s2DepthTwo h2 hq` (CC-2, C130s2), every `NodePointSource` stage law (C130k, node CC-1)
proved at `i = 2` in its exact field shape, and the concrete `Ladder.SlotCarrier` these
fields produce — the literal table-for-table image of CC-5's `stageCarrier` (C130st),
pinned by the `stageCarrier_*_eq_s2` ties below.

## The tables (what they are, and why they are not free)

* **VALUE** `s2Hgt₂ A` := the corpus's level-2 height `dv2Hgt` (NODE C.11, the tower
  recursion) at the LANDED S2 level datum (`(s2Tower h2 hq).levelDatum h2`, NODE C.44) —
  i.e. the `e₂`-cleared level-2 support `dvSupp (s2Frame h2 hq) A 5 2` (side `u₂ = 5`,
  `ℓ₂ = e₂ = 2`), coerced `ℕ∞ → WithTop ℤ` (E.10's D-E1 carrier type) by `toZ`.  Both
  identifications are `rfl` pins (`s2Hgt₂_eq_dvSupp`, `s2Hgt₂_eq_dv2Hgt`); nothing fresh is
  invented.  Its regression teeth: `s2Hgt₂ 1 = 0`, `s2Hgt₂ x = 2` (the cleared
  `v₂(x) = 1/2`), `s2Hgt₂ Φ′ = 5 = u₂` (the table sees the tower height), and
  `s2Hgt₂ f₅ = 10 = E₂` — the last read literally off C.80's landed probe value
  `dvsupp_f₅`.
* **DIGIT** `s2Dig₂ A` := `0` at `A = 0`, else `1`.  This is the `q = 2` collapse
  (PROJECT_STATE §5's standing instrument): `|K₂| = Nat.card ((s2DepthTwo).fld 2) = 2`
  (C.80's landed `card_K₁`, transported along the constant residue tower of C.97's
  witness — `s2Fld₂_card` IS `card_K₁`, definitionally), so `K₂^× = {1}` and EVERY lawful
  digit table is FORCED to this one on the slot range — that is `s2Dig₂_forced`, the
  "free tables" defense.  Off slot range the value `1` is a junk extension, exactly like
  C130s2's `keyAt` junk indices: no `NodePointSource` law and no future slot tie reads it.
* **FULL** `S2Full₂ k` := `k` is realized by a nonzero slot-range polynomial (the maximal
  honest instance of `EFF.T2.09`'s predicate; `EFF.T2.10`'s fullness *criteria* are
  consumer-side instances of `Full`, per E.10's own doctrine, so membership in `S2Full₂ k`
  still costs an explicit witness).  Teeth: `S2Full₂ 0/2/5` hold with named witnesses,
  `S2Full₂ k` FAILS for every `k < 0`, and `S2Full₂ ≠ fun _ => True` — the predicate is
  live and source-bound, not `True` (design §8 row C.130c's demand).
* **LIFT** `s2Lift₂` : at a full height every nonzero digit is realized on slot range.
  With `|K₂| = 2` the only nonzero digit is `1`, so `(LIFT)`'s content at this instance IS
  realizability — which is exactly what `S2Full₂` certifies; the lift is a theorem, not a
  hypothesis, at this occurrence.

## The generic `dvSupp` valuation-law layer (Part 2)

The level-2 laws ride a NEW generic law bank for C.06's `dvSupp` (the nested cleared
support), mirrored from B32b's `suppVal` bank one level up: `dvSupp_zero_eq_top`,
`dvSupp_eq_inf_range`, `dvSupp_ne_top_of_ne_zero` (via B.05's reconstruction
`sum_dev_eq`), the ultrametric inequality `min_dvSupp_le_dvSupp_add` (per-slot B32b
`min_suppVal_le_suppVal_add` at the key `X`, through B32a's `dev_add_of_monic`),
`dvSupp_neg`, and — the law E.10 needs that no landed file had at this level — the
ultrametric EQUALITY OFF TIES `dvSupp_add_eq`, derived from the inequality and
neg-invariance by the standard valuation argument (`A = (A + B) + (−B)`), with no new
attainment analysis.

## What this node does NOT claim (honesty scope)

* No `NodePointSource` is inhabited: the point fields (`Point`/`Pt`/`coord`/`valueOn`,
  CC-9), the slot ties `slot_value`/`slot_digit` (which quantify over legal points), the
  threshold/WINDOW (CC-7), and the reads (CC-10/11) are later CC nodes'.  The
  `stageCarrier_*_eq_s2` ties are therefore CONDITIONAL: any future instance whose stage
  tables at `i = 2` are these tables produces, via CC-5's `stageCarrier`, exactly
  `s2Slot₂` — table for table (the `D`/`eC`/`fC` ties are unconditional `rfl`s).
* The exactness of `dv2Hgt` at legal points (`hgt` = the point valuation of the actual
  evaluation, on slot range) is C.11's documented C.25/C.26-style obligation and lands
  with the points (CC-9); the tables here are the corpus's own level-2 reads, chosen so
  that obligation is stateable, not discharged.
* Consumption note (design §6 named C.46/C.47/C.127 as the S2 level-2 pieces): the stage
  TABLES ride C.02/C.06/C.11's `stageHeight`/`dvSupp`/`dv2Hgt` and C.80/C.35b's landed S2
  probe values; C.46/C.47's `composedKey` slot computations are the KEY-side rows
  (consumed by CC-2) and will feed CC-9's point ties; C.127's law E-W operates at the
  trinomial frame (`e₂ = 1`), which the S2 tower (`e₂ = 2`) does not instantiate —
  neither is needed for the stage family itself.  Recorded here so the verdict is
  checkable.

**DEPENDS.** C130s2 (CC-2: `s2DepthTwo`, `s2DepthTwo_Dcum_two`) · C130st (CC-5:
`stageCarrier` + pins, `fhat`, `Dcum_pos`, `Dcum_eq_ehat_mul_fhat`) · C130k (CC-1:
`NodePointSource`, `StageLive`) · C.80 (`s2Tower`, `card_K₁`, `dvsupp_f₅`, `f₅`) · C.97
(`s2Frame`, `s2Witness`) · C.35b (`sh_C`, `sh_X`, `sh_zero`, `key_eq`, `s2Key_deg`,
frame numerals) · C.44 (`levelDatum`) · C.11 (`dv2Hgt`) · C.06 (`dvHgt`, `dvSupp`) ·
C.02 (`stageHeight`) · C118a (`inf_range_ext`, `smul_top_pos`, `dvHgt_top_of_gt`) ·
C.87 (`ehat_pos`) · B.05 (`sum_dev_eq`) · B32a (`dev_add_of_monic`) · B32b
(`min_suppVal_le_suppVal_add`, `suppVal_zero_eq_top`) · B35a (`dev_of_zero`,
`dev_mul_pow`, `dev_mul_pow_of_lt`) · B39b (`dev_neg`, `suppVal_neg`) · B41a
(`eq_zero_of_suppVal_eq_top`) · E.10 (`Ladder.SlotCarrier`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement touched.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130s6

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

universe uL

/-! ## Part 1 — the carrier-type dictionary `toZ : ℕ∞ → WithTop ℤ`

E.10's D-E1 ruling makes carrier heights `WithTop ℤ`; the corpus's cleared supports are
`ℕ∞` (GC-2, C-H14 discharged by construction).  `toZ` is the evident embedding (E.55's
private `nv`, made public here in the C130s6 namespace so CC-17 can reason through it). -/

/-- `ℕ∞ → WithTop ℤ`, top to top, `↑n` to `↑(n : ℤ)`. -/
noncomputable def toZ : ℕ∞ → WithTop ℤ := fun x => x.map (fun n : ℕ => (n : ℤ))

@[simp] theorem toZ_top : toZ ⊤ = ⊤ := rfl

@[simp] theorem toZ_coe (n : ℕ) : toZ (n : ℕ∞) = ((n : ℤ) : WithTop ℤ) := rfl

theorem toZ_eq_top_iff {x : ℕ∞} : toZ x = ⊤ ↔ x = ⊤ := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => simp [toZ_coe]

theorem toZ_le_toZ_iff {x y : ℕ∞} : toZ x ≤ toZ y ↔ x ≤ y := by
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => simp
    | coe n => simp [toZ_coe]
  | coe m =>
    induction y using ENat.recTopCoe with
    | top => simp
    | coe n => simp [toZ_coe, Nat.cast_le]

theorem toZ_min (x y : ℕ∞) : toZ (min x y) = min (toZ x) (toZ y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (toZ_le_toZ_iff.mpr h)]
  · rw [min_eq_right h, min_eq_right (toZ_le_toZ_iff.mpr h)]

theorem toZ_inj {x y : ℕ∞} (h : toZ x = toZ y) : x = y :=
  le_antisymm (toZ_le_toZ_iff.mp h.le) (toZ_le_toZ_iff.mp h.ge)

theorem toZ_eq_intCast_iff {x : ℕ∞} {k : ℤ} :
    toZ x = (k : WithTop ℤ) ↔ ∃ n : ℕ, x = (n : ℕ∞) ∧ (n : ℤ) = k := by
  induction x using ENat.recTopCoe with
  | top =>
    simp only [toZ_top]
    constructor
    · intro h
      exact absurd h.symm WithTop.coe_ne_top
    · rintro ⟨n, hn, -⟩
      exact absurd hn (by simp)
  | coe m =>
    rw [toZ_coe]
    constructor
    · intro h
      exact ⟨m, rfl, WithTop.coe_inj.mp h⟩
    · rintro ⟨n, hn, hk⟩
      have hmn : m = n := by exact_mod_cast hn
      rw [hmn, hk]

/-! ## Part 2 — the generic `dvSupp` valuation laws (B32b's bank, one level up)

C.06's `dvSupp F A u ℓ = inf_j (ℓ·dv(A_j) + u·j)` is the NESTED cleared support (its slot
heights are `stageHeight = suppVal X`, not `gaussVal`), so B32b's `suppVal` bank does not
apply verbatim; this section proves the same laws at the `dvSupp` level, per-slot through
B32b at the key `X`.  All statements are over any frame and any side `(u, ℓ)`, with
`0 < ℓ` where clearing needs it. -/

section DvSuppLaws

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `dvSupp` of `0` is `⊤` (mirror of B32b's `suppVal_zero_eq_top`). -/
theorem dvSupp_zero_eq_top (F : KeyFrame O π) (u : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    dvSupp F (0 : Polynomial O) u ℓ = ⊤ := by
  rw [dvSupp]
  simp only [Polynomial.natDegree_zero, Nat.zero_add, Finset.range_one, Finset.inf_singleton]
  rw [dvHgt, dev_of_zero, KeyFrame.stageHeight, suppVal_zero_eq_top F.he₁ F.h,
    C118a.smul_top_pos hℓ, top_add]

/-- `dvSupp` read over any range past the degree (mirror of B32b's `suppVal_eq_inf_range`;
the added abscissae have `dvHgt = ⊤` by C118a's `dvHgt_top_of_gt`). -/
theorem dvSupp_eq_inf_range (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (A : Polynomial O)
    {M : ℕ} (hM : A.natDegree < M) :
    dvSupp F A u ℓ = (Finset.range M).inf (fun j => ℓ • dvHgt F A j + (u * j : ℕ∞)) := by
  rw [dvSupp]
  have h := C118a.inf_range_ext (m := A.natDegree) (M := M - 1) (by omega)
      (fun j => ℓ • dvHgt F A j + (u * j : ℕ∞)) (fun i hi1 _ => by
        rw [C118a.dvHgt_top_of_gt F A hi1, C118a.smul_top_pos hℓ, top_add])
  rw [h, show M - 1 + 1 = M by omega]

/-- a nonzero polynomial has finite `dvSupp` — B.05's reconstruction `sum_dev_eq` makes an
all-`⊤` slot column impossible. -/
theorem dvSupp_ne_top_of_ne_zero (F : KeyFrame O π) (u ℓ : ℕ) {A : Polynomial O}
    (hA : A ≠ 0) : dvSupp F A u ℓ ≠ ⊤ := by
  intro htop
  have hkeypos : 0 < F.key.natDegree := by
    rw [F.hdeg]; exact Nat.mul_pos F.he₁ F.hf₁
  rw [dvSupp] at htop
  have hall : ∀ j ∈ Finset.range (A.natDegree + 1), dev F.key A j = 0 := by
    intro j hj
    have hle := Finset.inf_le (f := fun j => ℓ • dvHgt F A j + (u * j : ℕ∞)) hj
    rw [htop] at hle
    have hterm : ℓ • dvHgt F A j + ((u : ℕ∞) * (j : ℕ∞)) = ⊤ := top_le_iff.mp hle
    have hleft : ℓ • dvHgt F A j = ⊤ := by
      rcases WithTop.add_eq_top.mp hterm with h | h
      · exact h
      · rw [← Nat.cast_mul] at h
        exact absurd h (ENat.coe_ne_top _)
    have hdvtop : dvHgt F A j = ⊤ := by
      by_contra hx
      rw [nsmul_eq_mul] at hleft
      exact WithTop.mul_ne_top (ENat.coe_ne_top ℓ) hx hleft
    rw [dvHgt, KeyFrame.stageHeight] at hdvtop
    exact eq_zero_of_suppVal_eq_top Polynomial.monic_X
      (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) hdvtop
  have hrec : ∑ j ∈ Finset.range (A.natDegree + 1), dev F.key A j * F.key ^ j = A :=
    sum_dev_eq F.hmonic hkeypos A
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hkeypos))
  refine hA ?_
  rw [← hrec]
  exact Finset.sum_eq_zero fun j hj => by rw [hall j hj, zero_mul]

/-- **the `dvSupp` ultrametric inequality** (mirror of B32b's `min_suppVal_le_suppVal_add`):
per-slot, `dev` is additive (B32a) and `stageHeight = suppVal X` is ultrametric (B32b). -/
theorem min_dvSupp_le_dvSupp_add (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (A B : Polynomial O) :
    min (dvSupp F A u ℓ) (dvSupp F B u ℓ) ≤ dvSupp F (A + B) u ℓ := by
  set M := max (max A.natDegree B.natDegree) (A + B).natDegree + 1 with hMdef
  rw [dvSupp_eq_inf_range F hℓ A (M := M) (by omega),
    dvSupp_eq_inf_range F hℓ B (M := M) (by omega),
    dvSupp_eq_inf_range F hℓ (A + B) (M := M) (by omega)]
  refine Finset.le_inf fun j hj => ?_
  have hmono : Monotone fun x : ℕ∞ => ℓ • x + ((u : ℕ∞) * (j : ℕ∞)) := by
    intro x y hxy
    exact add_le_add (nsmul_le_nsmul_right hxy ℓ) le_rfl
  have hs : min (dvHgt F A j) (dvHgt F B j) ≤ dvHgt F (A + B) j := by
    rw [dvHgt, dvHgt, dvHgt, dev_add_of_monic F.hmonic A B j]
    exact min_suppVal_le_suppVal_add Polynomial.monic_X
      (by rw [Polynomial.natDegree_X]; exact Nat.one_pos) F.he₁ F.h _ _
  calc min ((Finset.range M).inf fun i => ℓ • dvHgt F A i + (u * i : ℕ∞))
        ((Finset.range M).inf fun i => ℓ • dvHgt F B i + (u * i : ℕ∞))
      ≤ min (ℓ • dvHgt F A j + (u * j : ℕ∞)) (ℓ • dvHgt F B j + (u * j : ℕ∞)) :=
        min_le_min (Finset.inf_le hj) (Finset.inf_le hj)
    _ = ℓ • min (dvHgt F A j) (dvHgt F B j) + (u * j : ℕ∞) := (hmono.map_min).symm
    _ ≤ ℓ • dvHgt F (A + B) j + (u * j : ℕ∞) := hmono hs

/-- `dvSupp` is negation-invariant (per-slot B39b's `dev_neg` + `suppVal_neg`). -/
theorem dvSupp_neg (F : KeyFrame O π) (A : Polynomial O) (u ℓ : ℕ) :
    dvSupp F (-A) u ℓ = dvSupp F A u ℓ := by
  rw [dvSupp, dvSupp, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun j _ => ?_
  rw [dvHgt, dvHgt, dev_neg F.hmonic, KeyFrame.stageHeight, KeyFrame.stageHeight,
    suppVal_neg Polynomial.monic_X]

/-- the strict half of equality off ties: the lower side wins outright.  Standard
valuation argument through `A = (A + B) + (−B)`; no attainment analysis needed. -/
theorem dvSupp_add_eq_of_lt (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {A B : Polynomial O} (hlt : dvSupp F A u ℓ < dvSupp F B u ℓ) :
    dvSupp F (A + B) u ℓ = dvSupp F A u ℓ := by
  have hge : dvSupp F A u ℓ ≤ dvSupp F (A + B) u ℓ := by
    have h := min_dvSupp_le_dvSupp_add (u := u) F hℓ A B
    rwa [min_eq_left hlt.le] at h
  refine le_antisymm ?_ hge
  have h2 : min (dvSupp F (A + B) u ℓ) (dvSupp F B u ℓ) ≤ dvSupp F A u ℓ := by
    have h3 := min_dvSupp_le_dvSupp_add (u := u) F hℓ (A + B) (-B)
    rw [dvSupp_neg] at h3
    calc min (dvSupp F (A + B) u ℓ) (dvSupp F B u ℓ)
        ≤ dvSupp F ((A + B) + -B) u ℓ := h3
      _ = dvSupp F A u ℓ := by rw [add_neg_cancel_right]
  by_contra hcon
  exact absurd h2 (not_le.mpr (lt_min (not_le.mp hcon) hlt))

/-- ★ **the `dvSupp` ultrametric EQUALITY OFF TIES** — the E.10 `hgt_add_eq` law at the
`dvSupp` level.  New here; no landed file carried it at any level above `suppVal`. -/
theorem dvSupp_add_eq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) {A B : Polynomial O}
    (hne : dvSupp F A u ℓ ≠ dvSupp F B u ℓ) :
    dvSupp F (A + B) u ℓ = min (dvSupp F A u ℓ) (dvSupp F B u ℓ) := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le]
    exact dvSupp_add_eq_of_lt F hℓ h
  · rw [min_eq_right h.le, add_comm]
    exact dvSupp_add_eq_of_lt F hℓ h

end DvSuppLaws

/-! ## Part 3 — the S2 level-2 stage-source fields -/

section S2

open Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ### 3a. The VALUE table (`EFF.T2.04`/`.05` at level 2) -/

/-- **the S2 level-2 stage VALUE table**: the corpus's `e₂`-cleared level-2 support at the
S2 side `(u₂, e₂) = (5, 2)`, in E.10's `WithTop ℤ` carrier type. -/
noncomputable def s2Hgt₂ (A : Polynomial O) : WithTop ℤ :=
  toZ (dvSupp (s2Frame h2 hq) A 5 2)

/-- Anti-drift pin: the table IS `dvSupp` at the S2 numerals — nothing fresh. -/
theorem s2Hgt₂_eq_dvSupp (A : Polynomial O) :
    s2Hgt₂ h2 hq A = toZ (dvSupp (s2Frame h2 hq) A 5 2) := rfl

/-- Anti-drift pin: the table IS C.11's level-2 height `dv2Hgt` at the LANDED S2 level
datum (C.44's `levelDatum` of C.80's `s2Tower`) — the corpus's own level-2 read. -/
theorem s2Hgt₂_eq_dv2Hgt (A : Polynomial O) :
    s2Hgt₂ h2 hq A = toZ (dv2Hgt ((C80.s2Tower h2 hq).levelDatum h2) A) := rfl

/-- the `hgt_zero` SOURCE FIELD at `i = 2` (`EFF.T2.05`: `h(0) = +∞`). -/
theorem s2Hgt₂_zero : s2Hgt₂ h2 hq (0 : Polynomial O) = ⊤ := by
  rw [s2Hgt₂, dvSupp_zero_eq_top _ _ (by norm_num), toZ_top]

/-- `EFF.T2.04` at level 2: every nonzero polynomial has finite height (stronger than the
slot-fenced field shape; see `s2Hgt₂_ne_top_slot`). -/
theorem s2Hgt₂_ne_top {A : Polynomial O} (hA : A ≠ 0) : s2Hgt₂ h2 hq A ≠ ⊤ := by
  rw [s2Hgt₂, ne_eq, toZ_eq_top_iff]
  exact dvSupp_ne_top_of_ne_zero (s2Frame h2 hq) 5 2 hA

/-- the `hgt_ne_top` SOURCE FIELD at `i = 2`, in its exact `NodePointSource` shape. -/
theorem s2Hgt₂_ne_top_slot :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 2 →
      s2Hgt₂ h2 hq A ≠ ⊤ :=
  fun _ hA _ => s2Hgt₂_ne_top h2 hq hA

/-- the `hgt_add_ge` SOURCE FIELD at `i = 2` (`EFF.T2.04`, the ultrametric inequality). -/
theorem s2Hgt₂_add_ge (A B : Polynomial O) :
    min (s2Hgt₂ h2 hq A) (s2Hgt₂ h2 hq B) ≤ s2Hgt₂ h2 hq (A + B) := by
  rw [s2Hgt₂, s2Hgt₂, s2Hgt₂, ← toZ_min]
  exact toZ_le_toZ_iff.mpr (min_dvSupp_le_dvSupp_add (s2Frame h2 hq) (by norm_num) A B)

/-- the `hgt_add_eq` SOURCE FIELD at `i = 2` (`EFF.T2.04`, equality off ties). -/
theorem s2Hgt₂_add_eq (A B : Polynomial O) (hne : s2Hgt₂ h2 hq A ≠ s2Hgt₂ h2 hq B) :
    s2Hgt₂ h2 hq (A + B) = min (s2Hgt₂ h2 hq A) (s2Hgt₂ h2 hq B) := by
  have hne' : dvSupp (s2Frame h2 hq) A 5 2 ≠ dvSupp (s2Frame h2 hq) B 5 2 :=
    fun h => hne (congrArg toZ h)
  rw [s2Hgt₂, s2Hgt₂, s2Hgt₂, ← toZ_min]
  exact congrArg toZ (dvSupp_add_eq (s2Frame h2 hq) (by norm_num) hne')

/-! ### 3b. The `q = 2` collapse: `|K₂| = 2` -/

/-- the level-2 residue field of the S2 depth-two tower has exactly two elements — C.80's
landed `card_K₁`, transported along the CONSTANT residue tower of C.97's witness
(`fld 2` is definitionally `K₁`). -/
theorem s2Fld₂_card : Nat.card ((s2DepthTwo h2 hq).fld 2) = 2 :=
  C80.card_K₁ h2 hq

/-- private copy of C.80's `eq_one_of_card_two` at `fld 2` (the private-copy pattern:
`private` does not export). -/
private theorem fld₂_eq_one_of_ne_zero {c : (s2DepthTwo h2 hq).fld 2} (hc : c ≠ 0) :
    c = 1 := by
  haveI : Finite ((s2DepthTwo h2 hq).fld 2) :=
    Nat.finite_of_card_ne_zero (by rw [s2Fld₂_card h2 hq]; norm_num)
  have hu : Nat.card ((s2DepthTwo h2 hq).fld 2)ˣ = 1 := by
    rw [Nat.card_units, s2Fld₂_card h2 hq]
  haveI : Subsingleton ((s2DepthTwo h2 hq).fld 2)ˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have h1 : hc.isUnit.unit = 1 := Subsingleton.elim _ _
  calc c = ((hc.isUnit.unit : ((s2DepthTwo h2 hq).fld 2)ˣ) : (s2DepthTwo h2 hq).fld 2) :=
        (hc.isUnit.unit_spec).symm
    _ = 1 := by rw [h1]; rfl

/-- `K₂` has characteristic 2: `1 + 1 = 0`.  This is what makes the level-2 `dig_add`
law's nonzero-sum hypothesis unsatisfiable on nonzero digits. -/
private theorem fld₂_one_add_one :
    (1 : (s2DepthTwo h2 hq).fld 2) + 1 = 0 := by
  by_contra h
  have h1 := fld₂_eq_one_of_ne_zero h2 hq h
  refine one_ne_zero (α := (s2DepthTwo h2 hq).fld 2) ?_
  linear_combination h1

/-! ### 3c. The DIGIT table (`EFF.T2.05` at level 2) -/

open Classical in
/-- **the S2 level-2 stage DIGIT table**: `0` at `0`, else `1` — the unique lawful table
over the 2-element `K₂` (see `s2Dig₂_forced`); the value off the slot range is a junk
extension no law and no future slot tie reads. -/
noncomputable def s2Dig₂ (A : Polynomial O) : (s2DepthTwo h2 hq).fld 2 :=
  if A = 0 then 0 else 1

/-- the `dig_zero` SOURCE FIELD at `i = 2` (`EFF.T2.05`: `dig(0) = 0`). -/
theorem s2Dig₂_zero : s2Dig₂ h2 hq (0 : Polynomial O) = 0 := if_pos rfl

/-- the table on nonzero polynomials. -/
theorem s2Dig₂_of_ne_zero {A : Polynomial O} (hA : A ≠ 0) : s2Dig₂ h2 hq A = 1 :=
  if_neg hA

/-- the `dig_ne_zero` SOURCE FIELD at `i = 2`, in its exact `NodePointSource` shape. -/
theorem s2Dig₂_ne_zero :
    ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 2 →
      s2Dig₂ h2 hq A ≠ 0 :=
  fun _ hA _ => by rw [s2Dig₂_of_ne_zero h2 hq hA]; exact one_ne_zero

/-- **the "free tables" defense**: over the 2-element `K₂`, ANY table satisfying the two
zero/nonzero digit laws agrees with `s2Dig₂` on the slot range and at `0` — the digit
table is forced, not chosen. -/
theorem s2Dig₂_forced (d : Polynomial O → (s2DepthTwo h2 hq).fld 2)
    (hd0 : d 0 = 0)
    (hdne : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < (s2DepthTwo h2 hq).Dcum 2 → d A ≠ 0) :
    ∀ A : Polynomial O, A.natDegree < (s2DepthTwo h2 hq).Dcum 2 →
      d A = s2Dig₂ h2 hq A := by
  intro A hdeg
  by_cases hA : A = 0
  · rw [hA, hd0, s2Dig₂_zero]
  · rw [s2Dig₂_of_ne_zero h2 hq hA]
    exact fld₂_eq_one_of_ne_zero h2 hq (hdne A hA hdeg)

/-- the `dig_add` SOURCE FIELD at `i = 2` (`EFF.HE7.96`(c)'s mechanism).  In
characteristic 2 with a single nonzero digit, the hypothesis `dig A + dig B ≠ 0` forces
one side to be `0`, whose height is `⊤ ≠ k` — the law holds with no residual case. -/
theorem s2Dig₂_add (A B : Polynomial O) (k : ℤ)
    (hA : s2Hgt₂ h2 hq A = (k : WithTop ℤ)) (hB : s2Hgt₂ h2 hq B = (k : WithTop ℤ))
    (hne : s2Dig₂ h2 hq A + s2Dig₂ h2 hq B ≠ 0) :
    s2Hgt₂ h2 hq (A + B) = (k : WithTop ℤ) ∧
      s2Dig₂ h2 hq (A + B) = s2Dig₂ h2 hq A + s2Dig₂ h2 hq B := by
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [s2Hgt₂_zero h2 hq] at hA
    exact WithTop.top_ne_coe hA
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [s2Hgt₂_zero h2 hq] at hB
    exact WithTop.top_ne_coe hB
  refine absurd ?_ hne
  rw [s2Dig₂_of_ne_zero h2 hq hA0, s2Dig₂_of_ne_zero h2 hq hB0, fld₂_one_add_one h2 hq]

/-! ### 3d. The FULL predicate and the LIFT law (`EFF.T2.09` at level 2) -/

/-- **the S2 level-2 FULL predicate**: `k` is realized by a nonzero slot-range polynomial —
the maximal honest instance of `EFF.T2.09`'s predicate (`EFF.T2.10`'s fullness criteria
stay consumer-side, per E.10).  Live and source-bound, NOT `True`: see
`not_s2Full₂_of_neg` / `s2Full₂_ne_trivial`. -/
def S2Full₂ (k : ℤ) : Prop :=
  ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthTwo h2 hq).Dcum 2 ∧
    s2Hgt₂ h2 hq A = (k : WithTop ℤ)

/-- the `lift` SOURCE FIELD at `i = 2` (`EFF.T2.09` `(LIFT)`): with `|K₂| = 2` the only
nonzero digit is `1`, so realizability of the height IS the lift. -/
theorem s2Lift₂ (k : ℤ) (hk : S2Full₂ h2 hq k) (c : (s2DepthTwo h2 hq).fld 2)
    (hc : c ≠ 0) :
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < (s2DepthTwo h2 hq).Dcum 2 ∧
      s2Hgt₂ h2 hq A = (k : WithTop ℤ) ∧ s2Dig₂ h2 hq A = c := by
  obtain ⟨A, hA0, hdeg, hgtA⟩ := hk
  exact ⟨A, hA0, hdeg, hgtA, by
    rw [s2Dig₂_of_ne_zero h2 hq hA0, fld₂_eq_one_of_ne_zero h2 hq hc]⟩

/-! ### 3e. Teeth — the table is the level-2 read, and `Full` is live

The value teeth are the S2 ladder read off the table: `h(1) = 0`, `h(x) = 2` (the
cleared `v₂(x) = 1/2`), `h(Φ′) = 5 = u₂` (the tower height itself), plus the landed
C.80 regression `h(f₅) = 10 = E₂`.  The `Full` teeth inhabit the predicate at `0, 2, 5`
and refute it on all negatives. -/

/-- `stageHeight 1 = 0` at the S2 frame (C.35b's `sh_C` at `a = 1`). -/
private theorem sh_one : (s2Frame h2 hq).stageHeight (1 : Polynomial O) = 0 := by
  rw [show (1 : Polynomial O) = Polynomial.C 1 by rw [map_one], C35b.sh_C h2 hq]
  simp

/-- `1 %ₘ Φ′ = 1` (degree `0 < 2`). -/
private theorem one_mod_key : (1 : Polynomial O) %ₘ (s2Frame h2 hq).key = 1 :=
  (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num)

/-- `1 /ₘ Φ′ = 0` (degree `0 < 2`). -/
private theorem one_div_key : (1 : Polynomial O) /ₘ (s2Frame h2 hq).key = 0 :=
  (Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).mpr
    (by rw [Polynomial.degree_one, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num)

/-- **tooth (value)**: `h(1) = 0`. -/
theorem s2Hgt₂_one : s2Hgt₂ h2 hq (1 : Polynomial O) = ((0 : ℤ) : WithTop ℤ) := by
  have hval : dvSupp (s2Frame h2 hq) (1 : Polynomial O) 5 2 = ((0 : ℕ) : ℕ∞) := by
    rw [dvSupp, Polynomial.natDegree_one, show Finset.range (0 + 1) = {0} by decide,
      Finset.inf_singleton, dvHgt]
    rw [show dev (s2Frame h2 hq).key (1 : Polynomial O) 0
        = (1 : Polynomial O) %ₘ (s2Frame h2 hq).key from rfl, one_mod_key h2 hq,
      sh_one h2 hq]
    simp
  rw [s2Hgt₂, hval, toZ_coe]
  norm_num

/-- **tooth (value)**: `h(x) = 2` — the cleared `v₂(x) = 1/2`. -/
theorem s2Hgt₂_X : s2Hgt₂ h2 hq (Polynomial.X : Polynomial O) = ((2 : ℤ) : WithTop ℤ) := by
  have hdev0 : dev (s2Frame h2 hq).key (Polynomial.X : Polynomial O) 0 = Polynomial.X :=
    (Polynomial.modByMonic_eq_self_iff (s2Frame h2 hq).hmonic).mpr
      (by rw [Polynomial.degree_X, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num)
  have hdev1 : dev (s2Frame h2 hq).key (Polynomial.X : Polynomial O) 1 = 0 := by
    show (Polynomial.X /ₘ (s2Frame h2 hq).key) %ₘ (s2Frame h2 hq).key = 0
    rw [(Polynomial.divByMonic_eq_zero_iff (s2Frame h2 hq).hmonic).mpr
      (by rw [Polynomial.degree_X, C35b.key_eq h2 hq, C35b.s2Key_deg]; norm_num),
      Polynomial.zero_modByMonic]
  have hval : dvSupp (s2Frame h2 hq) (Polynomial.X : Polynomial O) 5 2 = ((2 : ℕ) : ℕ∞) := by
    rw [dvSupp, Polynomial.natDegree_X, show Finset.range (1 + 1) = {0, 1} by decide,
      Finset.inf_insert, Finset.inf_singleton, dvHgt, dvHgt, hdev0, hdev1,
      C35b.sh_X h2 hq, C35b.sh_zero h2 hq, C118a.smul_top_pos (by norm_num), top_add,
      min_eq_left le_top]
    simp [nsmul_eq_mul]
  rw [s2Hgt₂, hval, toZ_coe]
  norm_num

/-- **tooth (value)**: `h(Φ′) = 5 = u₂` — the table sees the tower height. -/
theorem s2Hgt₂_key :
    s2Hgt₂ h2 hq ((s2Frame h2 hq).key : Polynomial O) = ((5 : ℤ) : WithTop ℤ) := by
  have hdev0 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 0 = 0 := by
    have h := dev_mul_pow_of_lt (s2Frame h2 hq).hmonic 1 1 0 Nat.one_pos
    rwa [one_mul, pow_one] at h
  have hdev1 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 1 = 1 := by
    have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (1 : Polynomial O) 0
    rw [Nat.add_zero, one_mul, pow_one] at h
    rw [h]
    exact one_mod_key h2 hq
  have hdev2 : dev (s2Frame h2 hq).key ((s2Frame h2 hq).key) 2 = 0 := by
    have h := dev_mul_pow (s2Frame h2 hq).hmonic 1 (1 : Polynomial O) 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, one_mul, pow_one] at h
    rw [h]
    show ((1 : Polynomial O) /ₘ (s2Frame h2 hq).key) %ₘ (s2Frame h2 hq).key = 0
    rw [one_div_key h2 hq, Polynomial.zero_modByMonic]
  have hdeg : ((s2Frame h2 hq).key).natDegree = 2 := by
    rw [(s2Frame h2 hq).hdeg, C35b.e1_eq h2 hq, C35b.f1_eq h2 hq]
  have hval : dvSupp (s2Frame h2 hq) ((s2Frame h2 hq).key) 5 2 = ((5 : ℕ) : ℕ∞) := by
    rw [dvSupp, hdeg, show Finset.range (2 + 1) = {0, 1, 2} by decide,
      Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton, dvHgt, dvHgt, dvHgt,
      hdev0, hdev1, hdev2, sh_one h2 hq, C35b.sh_zero h2 hq,
      C118a.smul_top_pos (by norm_num), top_add, top_add, min_eq_right le_top,
      min_eq_left le_top]
    simp
  rw [s2Hgt₂, hval, toZ_coe]
  norm_num

/-- **tooth (regression vs C.80)**: `h(f₅) = 10 = E₂`, read off the landed probe value
`dvsupp_f₅`. -/
theorem s2Hgt₂_f₅ : s2Hgt₂ h2 hq (C80.f₅ O) = ((10 : ℤ) : WithTop ℤ) := by
  rw [s2Hgt₂, C80.dvsupp_f₅ h2 hq, show (10 : ℕ∞) = ((10 : ℕ) : ℕ∞) by norm_num, toZ_coe]
  norm_num

/-- **tooth (Full)**: `0` is full, witnessed by `1`. -/
theorem s2Full₂_zero : S2Full₂ h2 hq (0 : ℤ) :=
  ⟨1, one_ne_zero,
    by rw [Polynomial.natDegree_one, s2DepthTwo_Dcum_two h2 hq]; norm_num,
    by rw [s2Hgt₂_one h2 hq]⟩

/-- **tooth (Full)**: `2` is full, witnessed by `x`. -/
theorem s2Full₂_two : S2Full₂ h2 hq (2 : ℤ) :=
  ⟨Polynomial.X, Polynomial.X_ne_zero,
    by rw [Polynomial.natDegree_X, s2DepthTwo_Dcum_two h2 hq]; norm_num,
    by rw [s2Hgt₂_X h2 hq]⟩

/-- **tooth (Full)**: `5 = u₂` is full, witnessed by the frame key `Φ′` itself. -/
theorem s2Full₂_five : S2Full₂ h2 hq (5 : ℤ) :=
  ⟨(s2Frame h2 hq).key, (s2Frame h2 hq).hmonic.ne_zero,
    by
      rw [(s2Frame h2 hq).hdeg, C35b.e1_eq h2 hq, C35b.f1_eq h2 hq,
        s2DepthTwo_Dcum_two h2 hq]
      norm_num,
    by rw [s2Hgt₂_key h2 hq]⟩

/-- **tooth (Full, negative)**: no negative height is full — the table's heights are
casts of naturals. -/
theorem not_s2Full₂_of_neg {k : ℤ} (hk : k < 0) : ¬ S2Full₂ h2 hq k := by
  rintro ⟨A, _hA0, _hdeg, hgtA⟩
  rw [s2Hgt₂] at hgtA
  obtain ⟨n, _hxn, hnk⟩ := toZ_eq_intCast_iff.mp hgtA
  omega

/-- **tooth (Full, non-vacuity)**: the predicate is NOT `True` (design §8 row C.130c). -/
theorem s2Full₂_ne_trivial : S2Full₂ h2 hq ≠ fun _ => True := by
  intro h
  exact not_s2Full₂_of_neg h2 hq (show (-1 : ℤ) < 0 by norm_num)
    (show S2Full₂ h2 hq (-1) by rw [h]; trivial)

/-! ### 3f. The concrete `SlotCarrier` at S2 level 2 — `stageCarrier`'s literal image -/

/-- ★ **NODE CC-6 — the concrete E.10 `SlotCarrier` at the S2 level-2 occurrence.**
Field for field the image CC-5's `stageCarrier` produces at `i = 2` from a
`NodePointSource` whose stage tables are the ones above (the `stageCarrier_*_eq_s2` ties
pin this): `D = Dcum 2`, `(eC, fC) = (ê₂, f̂₂)` with the PROVED `(DEG-EF)` split
(C130st), and the level-2 VALUE/DIGIT/FULL/LIFT family with every law proved — no
hypothesis, no socket, no `True` field. -/
noncomputable def s2Slot₂ : Ladder.SlotCarrier O ((s2DepthTwo h2 hq).fld 2) where
  D := (s2DepthTwo h2 hq).Dcum 2
  hD := (s2DepthTwo h2 hq).Dcum_pos (le_refl 2)
  eC := (s2DepthTwo h2 hq).ehat 2
  fC := (s2DepthTwo h2 hq).fhat 2
  hef := (s2DepthTwo h2 hq).Dcum_eq_ehat_mul_fhat 2
  heC := (s2DepthTwo h2 hq).ehat_pos (le_refl 2)
  hfC := (s2DepthTwo h2 hq).fhat_pos (le_refl 2)
  hgt := s2Hgt₂ h2 hq
  dig := s2Dig₂ h2 hq
  hgt_zero := s2Hgt₂_zero h2 hq
  dig_zero := s2Dig₂_zero h2 hq
  hgt_ne_top := s2Hgt₂_ne_top_slot h2 hq
  dig_ne_zero := s2Dig₂_ne_zero h2 hq
  hgt_add_ge := s2Hgt₂_add_ge h2 hq
  hgt_add_eq := s2Hgt₂_add_eq h2 hq
  dig_add := s2Dig₂_add h2 hq
  Full := S2Full₂ h2 hq
  hlift := s2Lift₂ h2 hq

/-- numeral pin: `D = 4` (C130s2's landed `Dcum` value). -/
theorem s2Slot₂_D : (s2Slot₂ h2 hq).D = 4 := s2DepthTwo_Dcum_two h2 hq

/-- numeral pin: `eC = ê₂ = 4`. -/
theorem s2Slot₂_eC : (s2Slot₂ h2 hq).eC = 4 := by
  change ∏ _j ∈ Finset.Icc 1 2, (2 : ℕ) = 4
  decide

/-- numeral pin: `fC = f̂₂ = 1`. -/
theorem s2Slot₂_fC : (s2Slot₂ h2 hq).fC = 1 := by
  change ∏ _j ∈ Finset.Icc 1 2, (1 : ℕ) = 1
  decide

/-- anti-drift pin: the carrier's tables ARE the level-2 source tables. -/
theorem s2Slot₂_hgt : (s2Slot₂ h2 hq).hgt = s2Hgt₂ h2 hq := rfl

/-- anti-drift pin: the carrier's digit table IS the level-2 source table. -/
theorem s2Slot₂_dig : (s2Slot₂ h2 hq).dig = s2Dig₂ h2 hq := rfl

/-- anti-drift pin: the carrier's `Full` IS the live level-2 predicate — not `True`. -/
theorem s2Slot₂_Full : (s2Slot₂ h2 hq).Full = S2Full₂ h2 hq := rfl

/-! ### 3g. The `stageCarrier` ties (the "via CC-5" clause, honestly conditional)

`stageCarrier` consumes a FULL `NodePointSource`, which no landed object inhabits (the
point/threshold/read fields are CC-7/9/10/11's).  What IS provable now, and what CC-17
will consume: the `D`/`eC`/`fC` fields of `stageCarrier` at `i = 2` over `s2DepthTwo`
equal `s2Slot₂`'s unconditionally (`rfl` — same tower bookkeeping), and any instance
whose stage tables at `i = 2` are this file's tables produces EXACTLY `s2Slot₂`'s
tables through `stageCarrier` (CC-5's own `rfl` pins make the proofs the hypotheses
themselves). -/

section StageCarrierTies

variable {Kt : Type} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
variable {receiver : TerminalReceiver (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2
  (s2DepthTwo h2 hq) Kt}
variable {K : KeyChain (s2DepthTwo h2 hq)}

/-- tie (unconditional): `stageCarrier`'s degree field at the S2 level 2 is `s2Slot₂`'s. -/
theorem stageCarrier_D_eq_s2
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 2) :
    (S.stageCarrier 2 hi).D = (s2Slot₂ h2 hq).D := rfl

/-- tie (unconditional): `stageCarrier`'s `(DEG-EF)` constants at the S2 level 2 are
`s2Slot₂`'s. -/
theorem stageCarrier_eC_fC_eq_s2
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 2) :
    (S.stageCarrier 2 hi).eC = (s2Slot₂ h2 hq).eC ∧
      (S.stageCarrier 2 hi).fC = (s2Slot₂ h2 hq).fC :=
  ⟨rfl, rfl⟩

/-- tie (conditional on the value table): an instance carrying this file's VALUE table
produces `s2Slot₂`'s height table through `stageCarrier`. -/
theorem stageCarrier_hgt_eq_s2
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 2)
    (hS : S.hgt 2 = s2Hgt₂ h2 hq) :
    (S.stageCarrier 2 hi).hgt = (s2Slot₂ h2 hq).hgt := hS

/-- tie (conditional on the digit table): an instance carrying this file's DIGIT table
produces `s2Slot₂`'s digit table through `stageCarrier`. -/
theorem stageCarrier_dig_eq_s2
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 2)
    (hS : S.dig 2 = s2Dig₂ h2 hq) :
    (S.stageCarrier 2 hi).dig = (s2Slot₂ h2 hq).dig := hS

/-- tie (conditional on the FULL predicate): an instance carrying this file's FULL
predicate produces `s2Slot₂`'s through `stageCarrier`. -/
theorem stageCarrier_Full_eq_s2
    (S : NodePointSource (L := L) (s2DepthTwo h2 hq) receiver K) (hi : StageLive 2 2)
    (hS : S.Full 2 = S2Full₂ h2 hq) :
    (S.stageCarrier 2 hi).Full = (s2Slot₂ h2 hq).Full := hS

end StageCarrierTies

end S2

end Uniformity.Density.Tower.C130s6

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130s6.toZ
#print axioms Uniformity.Density.Tower.C130s6.toZ_top
#print axioms Uniformity.Density.Tower.C130s6.toZ_coe
#print axioms Uniformity.Density.Tower.C130s6.toZ_eq_top_iff
#print axioms Uniformity.Density.Tower.C130s6.toZ_le_toZ_iff
#print axioms Uniformity.Density.Tower.C130s6.toZ_min
#print axioms Uniformity.Density.Tower.C130s6.toZ_inj
#print axioms Uniformity.Density.Tower.C130s6.toZ_eq_intCast_iff
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_zero_eq_top
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_eq_inf_range
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_ne_top_of_ne_zero
#print axioms Uniformity.Density.Tower.C130s6.min_dvSupp_le_dvSupp_add
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_neg
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_add_eq_of_lt
#print axioms Uniformity.Density.Tower.C130s6.dvSupp_add_eq
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_eq_dvSupp
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_eq_dv2Hgt
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_zero
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_ne_top
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_ne_top_slot
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_add_ge
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_add_eq
#print axioms Uniformity.Density.Tower.C130s6.s2Fld₂_card
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂_zero
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂_of_ne_zero
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂_ne_zero
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂_forced
#print axioms Uniformity.Density.Tower.C130s6.s2Dig₂_add
#print axioms Uniformity.Density.Tower.C130s6.S2Full₂
#print axioms Uniformity.Density.Tower.C130s6.s2Lift₂
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_one
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_X
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_key
#print axioms Uniformity.Density.Tower.C130s6.s2Hgt₂_f₅
#print axioms Uniformity.Density.Tower.C130s6.s2Full₂_zero
#print axioms Uniformity.Density.Tower.C130s6.s2Full₂_two
#print axioms Uniformity.Density.Tower.C130s6.s2Full₂_five
#print axioms Uniformity.Density.Tower.C130s6.not_s2Full₂_of_neg
#print axioms Uniformity.Density.Tower.C130s6.s2Full₂_ne_trivial
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_D
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_eC
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_fC
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_hgt
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_dig
#print axioms Uniformity.Density.Tower.C130s6.s2Slot₂_Full
#print axioms Uniformity.Density.Tower.C130s6.stageCarrier_D_eq_s2
#print axioms Uniformity.Density.Tower.C130s6.stageCarrier_eC_fC_eq_s2
#print axioms Uniformity.Density.Tower.C130s6.stageCarrier_hgt_eq_s2
#print axioms Uniformity.Density.Tower.C130s6.stageCarrier_dig_eq_s2
#print axioms Uniformity.Density.Tower.C130s6.stageCarrier_Full_eq_s2

end AxCheck
