/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Scaffold/DictIII/GDOrder1 — GD23's order-≤1 layer (BP_III §1.4)

E-phase transcription of `lean/blueprints/BP_III.md` §1.4 (module
`Scaffold/DictIII/GDOrder1.lean`, GD23's order-≤1 layer, Step 8, VERIFIED
leaf #4).  This file currently holds units III-G1 (`devCoeff` + the
O-coefficients lemma `devCoeff_map`/`devCoeff_map_mem_lifts` + the BP_III §3.2
bridge to the corpus `Moves.IsDevelopment`: `isDevelopment_devCoeff` and
`devCoeff_eq_of_isDevelopment`, with support lemmas `devCoeff_zero_left`,
`degree_devCoeff_lt`, `devCoeff_eq_zero_of_natDegree_lt`,
`sum_devCoeff_mul_pow`) and III-G2 (`devg_congr`), transcribed VERBATIM.  Unit III-G3a (`gaussW`) is BLOCKED —
its §1.4 display is ill-typed (`algebraMap ℤ (WithTop ℤ)`: no
`Semiring (WithTop ℤ)` exists) and statement changes are forbidden; see the
BLOCKED(III-G3a) record below for the verbatim display, the exact errors,
and the semantic-stub finding.  Unit III-G4 (`gaussW_mul`, GAUSS-g(ii)) is
BLOCKED downstream of it — unknown identifier `gaussW`; see the
BLOCKED(III-G4) record (verbatim display, exact error, provability notes
for the repaired def).  Unit III-G3b (`gaussW_dev_indep`, GAUSS-g(i)) is
BLOCKED downstream of III-G3a AND false-as-displayed at `Φ = 1` (missing
`hd` binder); its two gaussW-free inequality engines are landed proved
(`devCoeff_coeff_mem`, `devCoeff_sum_reconstruct`) — see the
BLOCKED(III-G3b) record.  Source of record: GD23 §3 GAUSS-g(i)/(ii).
-/

namespace LeanUrat.Scaffold.DictIII

/-- BP_III Wave-1 row III-G1 (GD23 §3 DEV-g): the Φ-adic development
coefficients, per the blueprint recipe "via `Polynomial.modByMonic` /
`divByMonic`": `devCoeff Φ B j` is the `j`-th coefficient `C_j` in
`B = Σ_j C_j Φ^j` — remainder at slot 0, then recurse on the monic quotient.
(Dependency def for unit III-G2; §1.4 displays only its use sites.) -/
noncomputable def devCoeff {O : Type*} [CommRing O] (Φ : Polynomial O) :
    Polynomial O → ℕ → Polynomial O
  | B, 0 => B %ₘ Φ
  | B, j + 1 => devCoeff Φ (B /ₘ Φ) j

/-- Helper for III-G2: development coefficients commute with ring-hom maps
when the key `Φ` is monic (division by a monic commutes with `map`). -/
theorem devCoeff_map {O S : Type*} [CommRing O] [CommRing S] (f : O →+* S)
    {Φ : Polynomial O} (hΦ : Φ.Monic) (B : Polynomial O) (j : ℕ) :
    (devCoeff Φ B j).map f = devCoeff (Φ.map f) (B.map f) j := by
  induction j generalizing B with
  | zero => simpa [devCoeff] using Polynomial.map_modByMonic f hΦ
  | succ j ih =>
    simp only [devCoeff]
    rw [ih (B /ₘ Φ), Polynomial.map_divByMonic f hΦ]

/-- Unit III-G1, the O-coefficients lemma in membership form (GD23 §3 DEV-g,
"monic division stays in `O[x]`"): the `Φ.map f`-adic development coefficients
of `B.map f` all lift back along `f` — each is the image of the corresponding
`O[x]`-computed development coefficient (`devCoeff_map`), hence lies in
`Polynomial.lifts f`. -/
theorem devCoeff_map_mem_lifts {O S : Type*} [CommRing O] [CommRing S]
    (f : O →+* S) {Φ : Polynomial O} (hΦ : Φ.Monic) (B : Polynomial O) (j : ℕ) :
    devCoeff (Φ.map f) (B.map f) j ∈ Polynomial.lifts f :=
  (Polynomial.mem_lifts _).mpr ⟨devCoeff Φ B j, devCoeff_map f hΦ B j⟩

/-- III-G1 support: developing `0` gives `0` in every slot. -/
@[simp] theorem devCoeff_zero_left {O : Type*} [CommRing O]
    (Φ : Polynomial O) (j : ℕ) : devCoeff Φ 0 j = 0 := by
  induction j with
  | zero => simp [devCoeff]
  | succ j ih => simp only [devCoeff, Polynomial.zero_divByMonic]; exact ih

/-- III-G1 support: every development coefficient has degree `< deg Φ`
(the corpus `IsDevelopment` degree clause). -/
theorem degree_devCoeff_lt {O : Type*} [CommRing O] [Nontrivial O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (B : Polynomial O) (j : ℕ) :
    (devCoeff Φ B j).degree < Φ.degree := by
  induction j generalizing B with
  | zero => simpa [devCoeff] using Polynomial.degree_modByMonic_lt B hΦ
  | succ j ih => simpa [devCoeff] using ih (B /ₘ Φ)

/-- III-G1 support: development slots beyond `natDegree B` vanish
(the corpus `IsDevelopment` finiteness clause). -/
theorem devCoeff_eq_zero_of_natDegree_lt {O : Type*} [CommRing O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (j : ℕ) :
    ∀ B : Polynomial O, B.natDegree < j → devCoeff Φ B j = 0 := by
  have hnt : Nontrivial O :=
    Polynomial.nontrivial_iff.mp (nontrivial_of_ne Φ 0 fun h => by simp [h] at hd)
  induction j with
  | zero => exact fun B hB => absurd hB (Nat.not_lt_zero _)
  | succ j ih =>
    intro B hB
    simp only [devCoeff]
    rcases eq_or_ne (B /ₘ Φ) 0 with h0 | h0
    · rw [h0, devCoeff_zero_left]
    · refine ih _ ?_
      have h1 : Φ.degree ≤ B.degree :=
        not_lt.mp fun hlt => h0 ((Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt)
      have h2 : Φ.natDegree ≤ B.natDegree := Polynomial.natDegree_le_natDegree h1
      have h3 := Polynomial.natDegree_divByMonic B hΦ
      omega

/-- III-G1 support: the development recomposes, `B = Σ_{j ≤ n} C_j Φ^j`
whenever `natDegree B ≤ n` (the corpus `IsDevelopment` sum clause). -/
theorem sum_devCoeff_mul_pow {O : Type*} [CommRing O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (n : ℕ) :
    ∀ B : Polynomial O, B.natDegree ≤ n →
      B = ∑ j ∈ Finset.range (n + 1), devCoeff Φ B j * Φ ^ j := by
  have hnt : Nontrivial O :=
    Polynomial.nontrivial_iff.mp (nontrivial_of_ne Φ 0 fun h => by simp [h] at hd)
  induction n with
  | zero =>
    intro B hB
    have hdeg : B.degree < Φ.degree := Polynomial.degree_lt_degree (by omega)
    simp [devCoeff, (Polynomial.modByMonic_eq_self_iff hΦ).mpr hdeg]
  | succ n ih =>
    intro B hB
    have hq : (B /ₘ Φ).natDegree ≤ n := by
      have h3 := Polynomial.natDegree_divByMonic B hΦ
      omega
    calc B = B %ₘ Φ + Φ * (B /ₘ Φ) := (Polynomial.modByMonic_add_div B Φ).symm
      _ = devCoeff Φ B 0 * Φ ^ 0
            + Φ * ∑ j ∈ Finset.range (n + 1), devCoeff Φ (B /ₘ Φ) j * Φ ^ j := by
          rw [← ih _ hq]
          simp [devCoeff]
      _ = ∑ j ∈ Finset.range (n + 1 + 1), devCoeff Φ B j * Φ ^ j := by
          have hterm : ∑ j ∈ Finset.range (n + 1),
                Φ * (devCoeff Φ (B /ₘ Φ) j * Φ ^ j)
              = ∑ j ∈ Finset.range (n + 1), devCoeff Φ B (j + 1) * Φ ^ (j + 1) :=
            Finset.sum_congr rfl fun j _ => by simp only [devCoeff]; ring
          simp only [Finset.sum_range_succ' (fun j => devCoeff Φ B j * Φ ^ j)
            (n + 1), pow_zero, mul_one]
          rw [Finset.mul_sum, hterm, add_comm (devCoeff Φ B 0)]

/-- Unit III-G1, bridge lemma dev → `Moves.IsDevelopment` (BP_III §3.2 row
`IsDevelopment`, `Moves/Defs.lean`): for a monic key of positive degree,
`devCoeff Φ B` IS a Φ-adic development of `B` in the corpus sense, with slot
count `B.natDegree + 1`.  Together with `devCoeff_eq_of_isDevelopment` (the
converse slotwise identification) this is the dev ↔ `IsDevelopment` bridge. -/
theorem isDevelopment_devCoeff {O : Type*} [CommRing O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (B : Polynomial O) :
    Moves.IsDevelopment Φ B (devCoeff Φ B) (B.natDegree + 1) := by
  have hnt : Nontrivial O :=
    Polynomial.nontrivial_iff.mp (nontrivial_of_ne Φ 0 fun h => by simp [h] at hd)
  exact ⟨fun j => degree_devCoeff_lt hΦ B j,
    fun j hj => devCoeff_eq_zero_of_natDegree_lt hΦ hd j B (by omega),
    sum_devCoeff_mul_pow hΦ hd B.natDegree B le_rfl⟩

/-- Unit III-G1, bridge lemma `Moves.IsDevelopment` → dev (Fact A uniqueness,
monic keys): ANY corpus development of `f` along a monic key `Φ` agrees
slotwise with `devCoeff Φ f` — so the corpus predicate pins exactly the
`modByMonic`/`divByMonic` recursion.  (No positive-degree hypothesis needed:
for constant monic `Φ` the degree clause forces all slots to `0`.) -/
theorem devCoeff_eq_of_isDevelopment {O : Type*} [CommRing O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (N : ℕ) :
    ∀ (f : Polynomial O) (C : ℕ → Polynomial O),
      Moves.IsDevelopment Φ f C N → ∀ j, C j = devCoeff Φ f j := by
  induction N with
  | zero =>
    intro f C h j
    have hf : f = 0 := by simpa using h.2.2
    rw [h.2.1 j (Nat.zero_le j), hf, devCoeff_zero_left]
  | succ N ih =>
    intro f C h
    have hterm : ∑ j ∈ Finset.range N, Φ * (C (j + 1) * Φ ^ j)
        = ∑ j ∈ Finset.range N, C (j + 1) * Φ ^ (j + 1) :=
      Finset.sum_congr rfl fun j _ => by ring
    have hsum' : C 0 + Φ * ∑ j ∈ Finset.range N, C (j + 1) * Φ ^ j = f := by
      conv_rhs => rw [h.2.2]
      simp only [Finset.sum_range_succ' (fun j => C j * Φ ^ j) N, pow_zero,
        mul_one]
      rw [Finset.mul_sum, hterm, add_comm (C 0)]
    obtain ⟨hdiv, hmod⟩ := Polynomial.div_modByMonic_unique
      (∑ j ∈ Finset.range N, C (j + 1) * Φ ^ j) (C 0) hΦ ⟨hsum', h.1 0⟩
    have hdev' : Moves.IsDevelopment Φ (f /ₘ Φ) (fun k => C (k + 1)) N := by
      refine ⟨fun k => h.1 (k + 1), fun k hk => h.2.1 (k + 1) (by omega), ?_⟩
      simpa using hdiv
    intro j
    cases j with
    | zero => simp only [devCoeff]; exact hmod.symm
    | succ j =>
      simp only [devCoeff]
      exact ih (f /ₘ Φ) (fun k => C (k + 1)) hdev' j

set_option linter.unusedVariables false in
/-- BP_III §1.4, unit III-G2 (GD23 §3 DEV-g): if `B ≡ B'` coefficientwise
mod `π^L` then every development-coefficient slot is congruent mod `π^L`,
for all `j` and all coefficient indices `k` (REV2 finding 9). VERBATIM.
(`hπ`/`hd` are verbatim-required binders, unused by this proof.) -/
theorem devg_congr {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal O)
    (Φ : Polynomial O) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (L : ℕ)
    {B B' : Polynomial O}
    (h : ∀ k, (B - B').coeff k ∈ (Ideal.span {π}) ^ L) :
    ∀ j k, (devCoeff Φ B j - devCoeff Φ B' j).coeff k ∈
      (Ideal.span {π}) ^ L := by
  intro j k
  set I : Ideal O := (Ideal.span {π}) ^ L with hI
  have hmap : B.map (Ideal.Quotient.mk I) = B'.map (Ideal.Quotient.mk I) := by
    ext n
    simp only [Polynomial.coeff_map]
    exact Ideal.Quotient.eq.mpr (by simpa using h n)
  have hdev : (devCoeff Φ B j - devCoeff Φ B' j).map (Ideal.Quotient.mk I)
      = 0 := by
    rw [Polynomial.map_sub, devCoeff_map _ hΦ, devCoeff_map _ hΦ, hmap,
      sub_self]
  have hz : (Ideal.Quotient.mk I)
      ((devCoeff Φ B j - devCoeff Φ B' j).coeff k) = 0 := by
    have := congrArg (fun P => Polynomial.coeff P k) hdev
    simpa [Polynomial.coeff_map] using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-! ## Unit III-G3b (`gaussW_dev_indep`) — BLOCKED record + its gaussW-free proof engines

BLOCKED(III-G3b): the §1.4 display

  theorem gaussW_dev_indep {O} [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] (Φ B : Polynomial O) (hΦ : Φ.Monic) :
      gaussW B = Finset.inf' (Finset.range (B.natDegree + 1))
        (by simp) fun j => gaussW (devCoeff Φ B j)

cannot compile as written; statement changes are forbidden, so NO declaration
is transcribed.  Two independent blocks:

1. MISSING DEP (fatal): dep III-G3a (`gaussW`) is BLOCKED — see the record
   below — so `gaussW` names no declaration.  Exact error at the verbatim
   transcription (both `gaussW` tokens): "Function expected at gaussW / but
   this term has type ?m.1 … The identifier `gaussW` is unknown".

2. FALSE AS DISPLAYED (needs an architect fix even after III-G3a lands): the
   display omits `hd : 1 ≤ Φ.natDegree` (which `devg_congr` carries).  At
   `Φ = 1` (monic, `natDegree 0`) EVERY development slot vanishes for every
   `B` — compiled witness: `devCoeff_one` below (from `p %ₘ 1 = 0`).  So for
   `B = 1` the RHS is `inf'` of `{gaussW 0} = {⊤}` (REV2 finding 10 pins
   `gaussW 0 = ⊤`), while the LHS `gaussW 1` is the coefficient-valuation of
   `1 ≠ 0`, hence `≠ ⊤` under any faithful GAUSS-g(i) reading: `0 ≠ ⊤`.  The
   architect fix must add the `hd` binder (GD23 §3 always has `deg Φ ≥ 1`).

So the unit's two mandated inequality engines are landed below gaussW-FREE, as
ideal-membership statements ready for one-line assembly once the repaired
`gaussW` display lands:

* `devCoeff_coeff_mem` — division transport: coefficientwise `B ∈ I` implies
  every development slot is coefficientwise in `I` (with `I := 𝔪^L` this is
  "coefficient-min ≤ development-min", the sound face of the barred `B' = 0`
  congruence; REV2 finding 25).
* `devCoeff_sum_reconstruct` — `B = Σ_{j ≤ natDegree B} devCoeff Φ B j · Φ^j`,
  the exact index range of the display's `inf'`; with `I := 𝔪^L` at an
  attained (`Finset.exists_mem_eq_inf'`) slot it gives the reverse inequality
  "development-min ≤ coefficient-min".
-/

/-- Helper for III-G3b: the development of `0` vanishes in every slot. -/
theorem devCoeff_zero {O : Type*} [CommRing O] (Φ : Polynomial O) :
    ∀ j, devCoeff Φ 0 j = 0
  | 0 => by simp [devCoeff, Polynomial.zero_modByMonic]
  | j + 1 => by
    simp only [devCoeff, Polynomial.zero_divByMonic]
    exact devCoeff_zero Φ j

/-- III-G3b refutation witness (block 2 of the BLOCKED(III-G3b) record): at
`Φ = 1` every development slot of every `B` vanishes, so the displayed
`gaussW_dev_indep` (no `1 ≤ Φ.natDegree` binder) is false at `Φ = B = 1`
under any faithful GAUSS-g(i) reading of `gaussW`. -/
theorem devCoeff_one {O : Type*} [CommRing O] (B : Polynomial O) :
    ∀ j, devCoeff (1 : Polynomial O) B j = 0
  | 0 => by simp [devCoeff, Polynomial.modByMonic_one]
  | j + 1 => by
    simp only [devCoeff, Polynomial.divByMonic_one]
    exact devCoeff_one B j

/-- III-G3b engine 1 (division transport, the sound face of DEV-g at `B' = 0`):
if every coefficient of `B` lies in the ideal `I`, then so does every
coefficient of every development slot.  With `I := 𝔪^L` this yields
"coefficient-min ≤ development-min" for the repaired GAUSS-g(i). -/
theorem devCoeff_coeff_mem {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (I : Ideal O) {B : Polynomial O}
    (h : ∀ k, B.coeff k ∈ I) :
    ∀ j k, (devCoeff Φ B j).coeff k ∈ I := by
  intro j k
  have hmap : B.map (Ideal.Quotient.mk I) = 0 := by
    ext n
    simpa [Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem] using h n
  have hdev : (devCoeff Φ B j).map (Ideal.Quotient.mk I) = 0 := by
    rw [devCoeff_map _ hΦ, hmap, devCoeff_zero]
  have hz : (Ideal.Quotient.mk I) ((devCoeff Φ B j).coeff k) = 0 := by
    have := congrArg (fun P => Polynomial.coeff P k) hdev
    simpa [Polynomial.coeff_map] using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-- III-G3b engine 2 (the Φ-adic development reconstructs `B`): for monic `Φ`
of degree ≥ 1, `B = Σ_{j < n} devCoeff Φ B j · Φ^j` whenever `natDegree B < n`
— in particular over the display's exact index range
`Finset.range (B.natDegree + 1)`.  Feeding an attained `inf'` slot
(`Finset.exists_mem_eq_inf'`) through it with `I := 𝔪^L` gives
"development-min ≤ coefficient-min" for the repaired GAUSS-g(i). -/
theorem devCoeff_sum_reconstruct {O : Type*} [CommRing O] [Nontrivial O]
    {Φ : Polynomial O} (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) :
    ∀ (n : ℕ) (B : Polynomial O), B.natDegree < n →
      ∑ j ∈ Finset.range n, devCoeff Φ B j * Φ ^ j = B := by
  intro n
  induction n with
  | zero => exact fun B hB => absurd hB (Nat.not_lt_zero _)
  | succ n ih =>
    intro B hB
    rcases lt_or_ge B.degree Φ.degree with hlt | hge
    · have hmod : B %ₘ Φ = B := (Polynomial.modByMonic_eq_self_iff hΦ).mpr hlt
      have hdiv : B /ₘ Φ = 0 := (Polynomial.divByMonic_eq_zero_iff hΦ).mpr hlt
      rw [Finset.sum_range_succ']
      simp [devCoeff, hmod, hdiv]
    · have hquot : (B /ₘ Φ).natDegree < n := by
        have hle := Polynomial.natDegree_le_natDegree hge
        rw [Polynomial.natDegree_divByMonic B hΦ]
        omega
      have key := ih (B /ₘ Φ) hquot
      rw [Finset.sum_range_succ']
      simp only [devCoeff, pow_succ, pow_zero, mul_one, ← mul_assoc,
        ← Finset.sum_mul, key]
      linear_combination Polynomial.modByMonic_add_div B Φ

/- BLOCKED(III-G3a): the §1.4 `gaussW` display cannot compile as written and
statement changes are forbidden, so NO declaration is transcribed here yet.
The verbatim display is

  def gaussW {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      (B : Polynomial O) : WithTop ℤ :=
    if hB : B = 0 then ⊤ else
      Finset.min' (B.support.image fun k => algebraMap ℤ (WithTop ℤ) 0)
        (by simpa [Polynomial.support_nonempty] using hB)

Two independent blocks, needing an architect fix of the display:
1. TYPE ERROR (fatal): `algebraMap ℤ (WithTop ℤ)` requires the instances
   `Semiring (WithTop ℤ)` + `Algebra ℤ (WithTop ℤ)`; neither exists
   (`#synth Semiring (WithTop ℤ)` fails — `WithTop ℤ` is genuinely not a
   semiring: `⊤ * (1 + (-1)) = 0` but `⊤ * 1 + ⊤ * (-1) = ⊤`). Exact error
   at the `algebraMap` token: "typeclass instance problem is stuck
   Algebra ℤ (WithTop ℤ)". Not a renamed-token issue — the map is ill-typed
   in every Mathlib — so the sanctioned same-function respelling convention
   (cf. Carriers.lean on `List.get?`) does not apply.
2. SEMANTIC STUB: the mapped function `fun k => algebraMap ℤ (WithTop ℤ) 0`
   ignores `k` (constant 0), so under ANY compiling respelling the def would
   give `gaussW B = 0` for every nonzero `B` — contradicting the unit row's
   own gloss ("nonzero = minimum over finite support" of coefficient
   valuations, GD23 §3 GAUSS-g(i)) and making downstream unit III-G5
   `gaussW_keyBlock` (`gaussW B ≠ gaussW Φ`) FALSE (`0 ≠ 0`). The intended
   body presumably reads the π-adic valuation of `B.coeff k` into `WithTop ℤ`
   at each support index `k`.

Minor (curable by modifiers alone, recorded for the repaired display):
`if hB : B = 0` needs `Decidable (B = 0)`, unavailable over arbitrary `O`
(exact error: "failed to synthesize instance of type class
Decidable (B = 0)"); cure = `open Classical in` + `noncomputable def`. -/

/- BLOCKED(III-G4): `gaussW_mul` (GD23 §3 GAUSS-g(ii), Gauss's lemma) cannot
compile as written — it consumes the BLOCKED III-G3a def above, so NO
declaration is transcribed for this unit yet.  The verbatim §1.4 display is

  theorem gaussW_mul {O} [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] (A B : Polynomial O) :
      gaussW (A * B) = gaussW A + gaussW B

Exact error (probed 2026-08-01 by appending the verbatim statement to this
file at HEAD): "The identifier `gaussW` is unknown … Function expected at
gaussW but this term has type ?m.1", at each of the three `gaussW` tokens.
Root cause = III-G3a's fatal type error recorded above, independently
reconfirmed by this unit's probes (`#synth Semiring (WithTop ℤ)` fails; in
def position the elaborator reports "typeclass instance problem is stuck
Algebra ℤ (WithTop ℤ)").

Provability notes for the architect's repaired display, so the repair lands
with eyes open:
1. Under ANY compiling respelling of the CURRENT stub body (constant 0 over
   the support), `gaussW_mul` is trivially TRUE and provable in ~10 lines:
   for `A, B ≠ 0` both sides are `0` (`mul_ne_zero` keeps `A * B` off the
   zero branch, both `min'`s collapse on the constant image, `0 = 0 + 0`);
   if either factor is `0` both sides are `⊤` (`WithTop.top_add`/`add_top`).
   But it would then carry NONE of GAUSS-g(ii)'s content while III-G5
   `gaussW_keyBlock` becomes FALSE (III-G3a semantic-stub note above) — so
   this unit deliberately does NOT land that vacuous transcription.
2. Under the INTENDED reading (`gaussW B` = min over the support of the
   π-adic valuations of the coefficients, zero ↦ ⊤), the statement is
   additivity of the Gauss valuation over the DVR `O`.  Quarry finding
   (BP §3.3 charge executed): `LeanUrat/L3Gauss.lean` is the necklace-count
   module (Möbius count of irreducibles over F_q) — nothing there
   transports; the Mathlib quarry is `Polynomial.content_mul :
   (p * q).content = p.content * q.content`
   (Mathlib.RingTheory.Polynomial.Content, needs `NormalizedGCDMonoid O`
   data — available on a DVR, noncomputably, via the UFD route), converting
   `content` to the min coefficient valuation by `multiplicity`/`addVal`
   additivity; alternatively the classical direct proof (clear π-powers,
   reduce mod π, use that `F[X̄]` is a domain over the residue field `F` —
   Gauss's lemma over `F[X̄]` per the unit row).  Both routes fit the
   repaired def; neither needs new axioms. -/

/- BLOCKED(III-G5): `gaussW_keyBlock` (GD23 §3 GAUSS-g(iii)) cannot compile
as written — it consumes the BLOCKED III-G3a def above, and statement changes
are forbidden, so NO declaration is transcribed for this unit.  The verbatim
§1.4 display is

  theorem gaussW_keyBlock {O} [CommRing O] [IsDomain O]
      [IsDiscreteValuationRing O] (Φ B : Polynomial O)
      (hΦ : Φ.Monic) (hdeg : B.natDegree < Φ.natDegree) (hB : B ≠ 0) :
      gaussW B ≠ gaussW Φ

Exact error (probed 2026-08-01 by transcribing the verbatim statement into
this file): "Function expected at gaussW / but this term has type ?m.1 …
The identifier `gaussW` is unknown", at both `gaussW` tokens — `autoImplicit`
(on in this package) does not rescue an APPLIED unknown identifier, and if
it did, `gaussW` would be silently ∀-auto-bound: a vacuity trap, not a
transcription.  Root cause = III-G3a's fatal type error, independently
reconfirmed by this unit's probes (`Semiring (WithTop ℤ)` unsynthesizable;
in def position "typeclass instance problem is stuck Algebra ℤ (WithTop ℤ)").

SEMANTIC FLAG for the architect's repair, one layer beyond III-G3a's
stub note (item 2 above, which already refutes THIS unit under any
respelling of the stub): even under the INTENDED GAUSS-g(i) definition —
`gaussW B` = min over `B.support` of `v_π(B.coeff k)`, zero ↦ `⊤` — the
III-G5 display stays mathematically FALSE.  Countermodel over any DVR:
`B = 1`, `Φ = Polynomial.X`.  All hypotheses hold (`X` monic,
`natDegree B = 0 < 1 = natDegree X`, `B ≠ 0`), yet `gaussW B = v_π(1) = 0`
and `gaussW Φ = 0` (monic ⇒ the leading coefficient is a unit and every
coefficient has `v_π ≥ 0`, so the support-min is 0) — EVERY monic `Φ` has
Gauss value 0 and every `B` with a unit coefficient ties it.  The
GAUSS-g(iii) content this row carries ("φ̄(X̄) prime; X̄-degree count blocks
divisibility below d₀") is a residual-DIVISIBILITY statement — the initial
form of `Φ` does not divide the initial form of `B` in the reduction grading
when `deg B < d₀` — not an inequality of the two Gauss VALUES.  The display
needs an architect restatement (e.g. `¬ (Φ.map (residue) ∣ B.map (residue))`
-shaped on initial forms, per GD23 §3) before III-G5 and its consumer
III-G12 can land. -/

/- Unit III-G9 (VAL-g step (3)). STATEMENT PROVENANCE: the BP_III §1.4 display
carries NO verbatim Lean statement for this unit (it displays G2–G7 and G10
only); per the unit brief the statement is drawn from the source of record,
GD23 rev 4 §3, Theorem VAL-g proof step (3):

  "Products of weight-0 coefficient classes multiply as in K₀:
   a_t·b_s = c_{ts} + d_{ts}·Φ₀ gives, modulo (π, Φ₀), [c_{ts}] = [a_t][b_s]
   — the field product — while the carry term d_{ts}·Φ̄₀ lands in strictly
   higher weight by (1) and so vanishes in the graded piece."

Rendering (a FORMULATED statement, flagged for division-lead review): K₀ is
carried as the literal quotient `Polynomial O ⧸ Ideal.span {C π, Φ₀}`;
weight-0 coefficient classes are classes of coefficient polynomials
(degree < d₀ := deg Φ₀; content-0 representatives after the π-unit clearing
steps (2)–(4) perform explicitly — content plays no role in the algebra
below, so no content binder appears). The blocked gaussW/w1 vocabulary
(III-G3a record above) is NOT consumed: the weight-side clause is rendered
slot-wise via the landed `devCoeff`, per the unit row's own gloss
("carry lands higher" = the carry occupies the strictly higher development
slot; the w₁-weight inequality itself is III-G7's `w1_submul_heavyCarry`,
blocked downstream of III-G3a). -/

set_option linter.unusedVariables false in
/-- BP_III Wave-1 row III-G9 (GD23 §3 VAL-g step (3)): weight-0 products
multiply as K₀. With c := (a·b) %ₘ Φ₀ and d := (a·b) /ₘ Φ₀:
(i) the division identity a·b = c + Φ₀·d ("a_t b_s = c_{ts} + d_{ts}Φ₀");
(ii) [c] = [a]·[b] in K₀ = O[x]/(π, Φ₀) — the K₀-multiplication law
("c_{ts} ≡ a_t·b_s mod (π, Φ₀)");
(iii)/(iv) deg c, deg d < d₀ — c and d are legitimate slot coefficients, so
(c, d) is THE two-slot Φ₀-development of a·b (uniqueness = III-G8);
(v) the carry d IS development slot 1 of a·b ("carry lands higher": slot
exponent t+s+1 vs t+s, hence w₁-weight heavier by h ≥ 1 — the weight
inequality is III-G7's clause, this unit supplies the slot placement).
(`hπ` pins π as THE uniformizer, so the quotient IS K₀; semantic pin,
unused by the algebra.) -/
theorem w0_mul_asK0 {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (π : O)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal O)
    (Φ₀ : Polynomial O) (hΦ : Φ₀.Monic) (hd : 1 ≤ Φ₀.natDegree)
    (a b : Polynomial O)
    (ha : a.natDegree < Φ₀.natDegree) (hb : b.natDegree < Φ₀.natDegree) :
    a * b = (a * b) %ₘ Φ₀ + Φ₀ * ((a * b) /ₘ Φ₀) ∧
    Ideal.Quotient.mk (Ideal.span {Polynomial.C π, Φ₀}) ((a * b) %ₘ Φ₀) =
      Ideal.Quotient.mk (Ideal.span {Polynomial.C π, Φ₀}) a *
        Ideal.Quotient.mk (Ideal.span {Polynomial.C π, Φ₀}) b ∧
    ((a * b) %ₘ Φ₀).natDegree < Φ₀.natDegree ∧
    ((a * b) /ₘ Φ₀).natDegree < Φ₀.natDegree ∧
    devCoeff Φ₀ (a * b) 1 = (a * b) /ₘ Φ₀ := by
  have hΦne : Φ₀.natDegree ≠ 0 := by omega
  have hdivdeg : ((a * b) /ₘ Φ₀).natDegree < Φ₀.natDegree := by
    have h1 : ((a * b) /ₘ Φ₀).natDegree = (a * b).natDegree - Φ₀.natDegree :=
      Polynomial.natDegree_divByMonic (a * b) hΦ
    have h2 : (a * b).natDegree ≤ a.natDegree + b.natDegree :=
      Polynomial.natDegree_mul_le
    omega
  refine ⟨(Polynomial.modByMonic_add_div (a * b) Φ₀).symm, ?_, ?_, hdivdeg, ?_⟩
  · -- (ii) the K₀-multiplication law: [c] = [a]·[b] mod (π, Φ₀)
    rw [← map_mul, Ideal.Quotient.eq]
    have h1 : (a * b) %ₘ Φ₀ - a * b = -(Φ₀ * ((a * b) /ₘ Φ₀)) := by
      linear_combination Polynomial.modByMonic_add_div (a * b) Φ₀
    rw [h1]
    exact neg_mem (Ideal.mem_span_pair.mpr ⟨0, (a * b) /ₘ Φ₀, by ring⟩)
  · -- (iii) c is a slot coefficient: deg c < d₀
    exact Polynomial.natDegree_modByMonic_lt (a * b) hΦ
      (by rintro rfl; rw [Polynomial.natDegree_one] at hd; omega)
  · -- (v) the carry occupies development slot 1
    show devCoeff Φ₀ ((a * b) /ₘ Φ₀) 0 = (a * b) /ₘ Φ₀
    show ((a * b) /ₘ Φ₀) %ₘ Φ₀ = (a * b) /ₘ Φ₀
    exact (Polynomial.modByMonic_eq_self_iff hΦ).mpr
      (Polynomial.degree_lt_degree hdivdeg)

/- Unit III-G8 (VAL-g step (2)). STATEMENT PROVENANCE: the BP_III §1.4 display
carries NO verbatim Lean statement for this unit (unit-table row III-G8 only);
per the unit brief the statement is transcribed from the source of record,
GD23 rev 4 §3, Theorem VAL-g proof step (2)
(`lean/notes/openmath/GD23_phaseB_verifybrief_rev4.md`):

  "The graded module. Weight-γ classes: by slot uniqueness of the
   development, a sum Σ_t π^{a_t} u_t Φ₀^t (u_t of content 0, e·a_t + t·h
   = γ) has w₁ > γ iff every [u_t] = 0; so gr_γ is the free K₀-module on
   the monomials π̄^a Φ̄₀^t with e·a + t·h = γ (a ∈ ℤ after clearing
   denominators by π-units, t ≥ 0), and the displayed in(A) formula holds."

Concrete slot-support rendering (FORMULATED statements, flagged for
division-lead review; the blocked gaussW/w1 vocabulary of the III-G3a
record above is NOT consumed):
* integral π-cleared form: exponents `a : ℕ → ℕ` — the brief's own "a ∈ ℤ
  after clearing denominators by π-units" (rev-4 clearing note), stated on
  the cleared representatives; the K[x] statement descends by that note;
* the K₀-class `[u] = 0` (K₀ = O[x]/(π, Φ₀), deg u < deg Φ₀ — III-G9's
  carrier above) is rendered COEFFICIENTWISE: every coefficient of `u` in
  `Ideal.span {π}` (a monic degree count kills any Φ₀-component: from
  u = π·v + Φ₀·w with deg u < deg Φ₀, reduce mod π — Φ̄₀ monic of degree
  d₀ forces w̄ = 0);
* `w₁(A) > γ` for a weight-γ lattice sum is rendered SLOTWISE: every
  development slot t sits strictly above the (e,h)-line, i.e. every
  coefficient of slot t lies in `Ideal.span {π} ^ (a t + 1)` (slot weight
  = e·(a t + w₀(u t)) + t·h > γ = e·a t + t·h ⇔ w₀(u t) ≥ 1) — the same
  span-pow vocabulary as `devg_congr` above.
Free K₀-module on the lattice monomials then reads: the digit tuple is
recoverable from the element (spanning/coordinates: `valg2_slot_eq`, via
the brief's own mechanism "slot uniqueness of the development" =
`devCoeff_slots`, a direct corollary of the landed Fact-A bridge
`devCoeff_eq_of_isDevelopment`), and the K₀-class tuple vanishes iff the
element sits strictly above weight γ (independence:
`valg2_gradedPiece_free`). -/

/-- Unit III-G8, part (a) — DEV SLOT UNIQUENESS (the proof-sketch column's
mechanism, "by slot uniqueness of the development"): the Φ-adic development
of a slot sum `Σ_{s<n} c_s Φ^s` with `deg c_s < deg Φ` (and `c_s = 0` for
`s ≥ n`) recovers each `c_j` exactly.  Direct corollary of the Fact-A
uniqueness bridge `devCoeff_eq_of_isDevelopment`. -/
theorem devCoeff_slots {O : Type*} [CommRing O] {Φ : Polynomial O}
    (hΦ : Φ.Monic) (n : ℕ) (c : ℕ → Polynomial O)
    (hdeg : ∀ s, (c s).degree < Φ.degree) (hvan : ∀ s, n ≤ s → c s = 0)
    (j : ℕ) :
    devCoeff Φ (∑ s ∈ Finset.range n, c s * Φ ^ s) j = c j :=
  (devCoeff_eq_of_isDevelopment hΦ n _ c ⟨hdeg, hvan, rfl⟩ j).symm

/-- Unit III-G8, part (b) — the SLOT READ of a weight-γ lattice sum (the
concrete "displayed in(A) formula holds" of GD23 §3 VAL-g (2)): development
slot t of `A = Σ_{s<n} π^{a_s}·u_s·Φ₀^s` is exactly its lattice digit
`π^{a_t}·u_t`, so the K₀-digit tuple `([u_t])_t` is well-defined from `A`
alone — the coordinate read of the free-module claim, slot-support form. -/
theorem valg2_slot_eq {O : Type*} [CommRing O]
    (π : O) (Φ₀ : Polynomial O) (hΦ : Φ₀.Monic)
    (n : ℕ) (a : ℕ → ℕ) (u : ℕ → Polynomial O)
    (hdeg : ∀ t, (u t).degree < Φ₀.degree) (hvan : ∀ t, n ≤ t → u t = 0)
    (t : ℕ) :
    devCoeff Φ₀ (∑ s ∈ Finset.range n, Polynomial.C (π ^ a s) * u s * Φ₀ ^ s) t
      = Polynomial.C (π ^ a t) * u t :=
  devCoeff_slots hΦ n (fun s => Polynomial.C (π ^ a s) * u s)
    (fun s =>
      lt_of_le_of_lt
        (calc (Polynomial.C (π ^ a s) * u s).degree
            ≤ (Polynomial.C (π ^ a s)).degree + (u s).degree :=
              Polynomial.degree_mul_le _ _
          _ ≤ 0 + (u s).degree := add_le_add_right Polynomial.degree_C_le _
          _ = (u s).degree := zero_add _)
        (hdeg s))
    (fun s hs => by rw [hvan s hs, mul_zero]) t

/-- Helper for III-G8: in a domain, `π^m·x` lies one π-step above its own
lattice height iff `x` lies in `(π)` — the slotwise class-vanishing test. -/
theorem pow_mul_mem_span_pow_succ_iff {O : Type*} [CommRing O] [IsDomain O]
    {π : O} (hπ0 : π ≠ 0) (m : ℕ) (x : O) :
    π ^ m * x ∈ Ideal.span {π} ^ (m + 1) ↔ x ∈ Ideal.span {π} := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero m hπ0)

set_option linter.unusedVariables false in
/-- BP_III Wave-1 row III-G8 (GD23 §3 VAL-g step (2)): the weight-γ graded
piece is the FREE K₀-module on the lattice monomials `π̄^a Φ̄₀^t` with
`e·a + t·h = γ` — concrete slot-support rendering (see the provenance block
above for the rendering conventions; FORMULATED statement, flagged for
review).  For a lattice sum `A = Σ_{t<n} π^{a_t}·u_t·Φ₀^t` on the weight-γ
line (`e·a_t + t·h = γ`, `deg u_t < deg Φ₀`): `w₁(A) > γ` — slotwise, every
development slot strictly above the line — IFF every K₀-digit class
`[u_t] = 0` — coefficientwise, every `u_t ≡ 0 mod π`.  (`hd`/`he`/`hh`/
`hlat` are the brief's weight-γ pins: they make the left side read
"w₁(A) > γ"; the slotwise criterion holds line-by-line, so the proof does
not consume them.) -/
theorem valg2_gradedPiece_free {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    (π : O) (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal O)
    (Φ₀ : Polynomial O) (hΦ : Φ₀.Monic) (hd : 1 ≤ Φ₀.natDegree)
    (e h γ : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (n : ℕ) (a : ℕ → ℕ) (u : ℕ → Polynomial O)
    (hdeg : ∀ t, (u t).degree < Φ₀.degree) (hvan : ∀ t, n ≤ t → u t = 0)
    (hlat : ∀ t, t < n → e * a t + t * h = γ) :
    (∀ t, t < n → ∀ k,
        (devCoeff Φ₀
            (∑ s ∈ Finset.range n, Polynomial.C (π ^ a s) * u s * Φ₀ ^ s)
            t).coeff k
          ∈ Ideal.span {π} ^ (a t + 1))
      ↔ ∀ t, t < n → ∀ k, (u t).coeff k ∈ Ideal.span {π} := by
  have hπ0 : π ≠ 0 := fun h0 =>
    IsDiscreteValuationRing.not_a_field O
      (by rw [← hπ, h0, Ideal.span_singleton_eq_bot])
  have hslot := valg2_slot_eq π Φ₀ hΦ n a u hdeg hvan
  constructor
  · intro H t ht k
    have hk := H t ht k
    rw [hslot t, Polynomial.coeff_C_mul] at hk
    exact (pow_mul_mem_span_pow_succ_iff hπ0 (a t) _).mp hk
  · intro H t ht k
    rw [hslot t, Polynomial.coeff_C_mul]
    exact (pow_mul_mem_span_pow_succ_iff hπ0 (a t) _).mpr (H t ht k)

end LeanUrat.Scaffold.DictIII
