/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H44
import Uniformity.ChapH.H46
import Uniformity.ChapH.H51
import Uniformity.ChapH.H89

/-!
# Uniformity.ChapH.H89w — the GENHN-3 general-consultation appendix (orchestrator item O-2)

**An H.89-adjacent appendix file, not a blueprint node** (the H09w precedent; registered by
blueprint AMENDMENT A-H.3, 2026-08-16, unit OM-6). It books CHAP-I's orchestrator item **O-2**:
*"book the `LEMMA GENHN-3` cap/consultation transcription (`EFF.GENHN.29` beyond the (c) bound
H.51 consumes) — the general window-pinning supplier; candidate: an H-appendix node next to
H.89"* — the supplier gap CHAP-I's honesty item I-11(ii) records for the COND resolution I.14
(`(H-e)-window-pinning` = ledger HYP.24's pinning half).

Source: `EFF.GENHN.29` (`LEMMA GENHN-3 (caps, raggedness, consultation)`,
`GENHN_PROOF_2026-08-08.md` L741–763), **as rider-corrected** by `[e2]` ERRATUM E1, the `[r2]`
annex, and R4 F-1 / `LEMMA GENHN-CAP-GEN` (`EFF.GENHN.79`, the TERMINAL wording): the "iff
`< e₁N`" is transcribed as the SUFFICIENT interior criterion only, and the band content is
transcribed at its arithmetic layer (comp geometry + census), never as the reader rule.
Numeric certification: `verification/om6_window_pinning_check.py` (26/26, both primes, both
characteristics, constructed-counterexample attacks).

## What is transcribed (per GENHN-3 clause)

* **(c), general `e₁`** — the displayed chain *"a consulted height m satisfies m < e₁N and
  m ≡ i(m)h mod e₁, hence m ≤ e₁N − e₁ + (i(m)h mod e₁) ≤ e₁(N−1) + i(m)h"*:
  `consulted_le_cap` + `cap_le_string_end`, and the occupied form `consulted_inside_string`.
  **⚠ SCOPE PIN (unit finding, machine-refuted reading):** the display's final *"— inside the
  string"* is FALSE without an occupancy pin: at `(e₁, h, m) = (3, 2, 1)` the congruence and
  cap hypotheses hold with `i(m) = 2`, yet `m` is not an occupied height of the class-2 string
  (`a(m) = −1` — the SAME defect `EFF.GENHN.28`'s second conditionality records for the
  normalizer display, governed there by the post-D2b `D′h < m` scope). The membership
  conclusion is therefore landed ONLY in the occupied form (`m = e₁v + ih`, `v ≥ 0`), where it
  is a theorem; the two INEQUALITIES are landed exactly as displayed (they survive the attack).
  Machine witness: `unoccupied_height_witness` below.
* **(b), general `e₁`** — *"the class-i slot string of a coordinate ends at e₁(N−1) + ih:
  RAGGED across classes"*: `string_end_le` + `string_end_mem` + `string_ends_ragged`, and the
  band count `bandCard` `= min(i·h / e₁, N)` — the general form of H.46's `raggedBand_card`
  (whose genre-E value `t` it reproduces at `(e₁, i) = (2, 1)`: gate section).
* **(a), interior, rider-corrected** — the SUFFICIENT criterion (R4 F-1: *"the previously
  proved stability below `e₁N` is unchanged"*): `out_window_dv_ge` (every out-of-window
  contribution has `dv ≥ e₁N`) + `interior_min_stable` (a computed value `< e₁N` is unchanged
  by adjoining any such contributions — lift-stability at the valuation layer). The undercut /
  no-tie computation: `no_tie_at_cap` (coprimality `gcd(h, e₁) = 1` is LOAD-BEARING — at
  `(e₁, h) = (2, 2)` an in-window value ties `e₁N`; certified attack CERT-3) + `cap_undercuts`
  (adjoining the class-0 out-of-window digit's value `e₁N` strictly lowers a min that sits
  above the cap — the instability half's witness pair).
* **(a), band `f₁ ≥ 2`, the `[r2]`/CAP-GEN arithmetic layer** — `compVis` (the visible-component
  count: component `t` of the height-`m` slot is in-window iff `m ≤ N − 1 + t·k`) with the
  `[r2]` display's three regimes (`compVis_interior` `= f₁`, `compVis_band_bounds`
  `∈ [1, f₁)`, `compVis_beyond` `= 0`), tied to landed H.44 `pinCensus` at the committed
  `(1, 3, 2)` instance numbers (`[r2]`(4) / `EFF.GENHN.32` / H.44's audit): the exhaustive
  partitions `3·2¹³ + 2¹³ = 2¹⁵` (N = 7) and `7·2¹⁸ + 2¹⁸ = 2²¹` (N = 8), machine-checked in
  the gate below.
* **(d), the update-map core** — *"every update (S6) determines new digits at height d from
  old digits at heights ≤ d: carries move upward only, both ring types"*:
  `recenter_descends` — the recentering `x ↦ x + s` descends to `R ⧸ I` for EVERY commutative
  ring `R` and ideal `I` (instantiate `I = (π^{d+1})`: the new state mod `π^{d+1}` — its digits
  at heights `≤ d` — is a function of the old state mod `π^{d+1}`); one statement, BOTH ring
  types at once. Plus the coefficient-axis triangularity `recenter_coeff_hasse` (the new
  `n`-th coefficient is the `n`-th Hasse derivative evaluated at `s` — GENIND-2(a)'s
  *"binomial update matrix is triangular with unit diagonal"*, displayed).

## What is NOT transcribed (fences carried unchanged)

* **`GENHN-CAP-GEN`'s three-clause reader rule** (`EFF.GENHN.79`) — chapter H's standing
  decision stands (§16 disposition item 3: *"the reader is not formalized … `CAP-GEN` has no
  node and its content sits in `StageInterface`'s `hwin`"*). This file lands the rule's
  ARITHMETIC substrate only; the dictionary-constancy clause 2 and the completion-test clauses
  remain math-language (CERTIFIED-OPEN at OM-6 §3).
* **`StageInterface.hwin`** — UNCHANGED, still HYP.36 CARRY per GC-5's table. Nothing here
  discharges, weakens, or re-fields it.
* **H.89's `e₁ = 2` fence** — H.89 stays `(OB-a)`'s discharge at `e₁ = 2` and only there; this
  file generalizes the HEIGHT ARITHMETIC, not the per-genre read ledger (which needs the genre
  reader). The `(OB-a)` disclosure at general stages is still carried.
* **GENHN-2's residue F_Q-independence** (the tie-breaking leg of the `[r2]` value-stability
  derivation) — consumed as the corpus consumes it (`EFF.GENHN.27`, H.51's source), not
  re-proved here.

DEPENDS: H.44 (`pinCensus`), H.46 (`slotOdd`, `raggedBand_card` — gate tie only), H.51
(`class_sep` neighborhood — coprimality vocabulary), H.89 (the `e₁ = 2` ledger — gate tie).

## Status

Sorry-free, axiom-free (Lean core only). Gate section + axiom footprint at the bottom.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- `e₁(N−1) = e₁N − e₁` in `ℕ` — the truncation-safe distribution both display
inequalities of (c) need (equality for `N ≥ 1`; both sides `0` at `N = 0`). -/
private theorem mul_pred_eq {e₁ N : ℕ} (hN : 1 ≤ N) : e₁ * (N - 1) = e₁ * N - e₁ := by
  rcases Nat.exists_eq_add_of_le hN with ⟨n, rfl⟩
  rw [Nat.add_comm 1 n, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]

/-- `e₁(N−v) = e₁N − e₁v` in `ℕ` for `v ≤ N`. -/
private theorem mul_sub_eq {e₁ N v : ℕ} (hv : v ≤ N) : e₁ * (N - v) = e₁ * N - e₁ * v := by
  rcases Nat.exists_eq_add_of_le hv with ⟨d, rfl⟩
  rw [Nat.add_sub_cancel_left, Nat.mul_add, Nat.add_sub_cancel_left]

/-! ## 1. GENHN-3(c) — the general-`e₁` consulted-height congruence bound -/

/-- **GENHN-3(c), first displayed inequality (general `e₁`).** A height `m < e₁N` in the
class-`i` residue class (`m ≡ i·h mod e₁`) satisfies `m ≤ e₁N − e₁ + (i·h mod e₁)` — the
consulted cap. (`e₁ = 0` is vacuous: no `m < 0`.) -/
theorem consulted_le_cap {e₁ h N i m : ℕ} (hm : m < e₁ * N)
    (hmod : m % e₁ = (i * h) % e₁) : m ≤ e₁ * N - e₁ + (i * h) % e₁ := by
  rcases Nat.eq_zero_or_pos e₁ with he | he
  · subst he; omega
  · have hN : 1 ≤ N := by
      by_contra hN
      have : N = 0 := by omega
      subst this
      omega
    have hdm : e₁ * (m / e₁) + m % e₁ = m := Nat.div_add_mod m e₁
    have hq : m / e₁ < N := Nat.div_lt_of_lt_mul (by omega)
    have h1 : e₁ * (m / e₁) ≤ e₁ * (N - 1) := Nat.mul_le_mul_left e₁ (by omega)
    have h2 : e₁ * (N - 1) = e₁ * N - e₁ := mul_pred_eq hN
    omega

/-- **GENHN-3(c), second displayed inequality (general `e₁`).**
`e₁N − e₁ + (i·h mod e₁) ≤ e₁(N−1) + i·h`. -/
theorem cap_le_string_end (e₁ h N i : ℕ) :
    e₁ * N - e₁ + (i * h) % e₁ ≤ e₁ * (N - 1) + i * h := by
  have h1 : (i * h) % e₁ ≤ i * h := Nat.mod_le _ _
  have h2 : e₁ * N - e₁ ≤ e₁ * (N - 1) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; omega
    · exact le_of_eq (mul_pred_eq hN).symm
  omega

/-- **GENHN-3(c), the "inside the string" conclusion — OCCUPIED form only** (scope pin, this
file's header): an occupied class-`i` height `m = e₁v + ih` with `m < e₁N` has `v ≤ N − 1`,
i.e. sits inside the class-`i` string of (b). The unoccupied reading is machine-refuted at
`unoccupied_height_witness`. -/
theorem consulted_inside_string {e₁ h N i v : ℕ} (hm : e₁ * v + i * h < e₁ * N) :
    v ≤ N - 1 := by
  by_contra hv
  have hNv : N ≤ v := by omega
  have : e₁ * N ≤ e₁ * v := Nat.mul_le_mul_left e₁ hNv
  omega

/-- **The occupancy scope pin is NECESSARY (machine-refuted reading).** At
`(e₁, h) = (3, 2)`, the height `m = 1` lies in the class-2 residue class
(`1 % 3 = (2·2) % 3`) and below every cap, yet is not an occupied height of the class-2
string: `1 = 3v + 4` has no solution. Same defect family as `EFF.GENHN.28`'s `a(m) ≥ 0`. -/
theorem unoccupied_height_witness :
    (1 % 3 = (2 * 2) % 3) ∧ ¬ ∃ v : ℕ, 3 * v + 2 * 2 = 1 := by
  constructor
  · rfl
  · rintro ⟨v, hv⟩; omega

/-! ## 2. GENHN-3(b) — general raggedness: string ends and the band count -/

/-- **GENHN-3(b), the string end as a bound.** Every occupied class-`i` height
(`v ≤ N − 1`) is at most `e₁(N−1) + ih`. -/
theorem string_end_le {e₁ h N i v : ℕ} (hv : v ≤ N - 1) :
    e₁ * v + i * h ≤ e₁ * (N - 1) + i * h := by
  have := Nat.mul_le_mul_left e₁ hv
  omega

/-- **GENHN-3(b), the string end is attained** (`v = N − 1` is occupied):
the class-`i` string ENDS at exactly `e₁(N−1) + ih`. -/
theorem string_end_mem (e₁ h i N : ℕ) :
    ∃ v ≤ N - 1, e₁ * v + i * h = e₁ * (N - 1) + i * h :=
  ⟨N - 1, le_refl _, rfl⟩

/-- **GENHN-3(b), "RAGGED across classes".** For `h ≥ 1`, distinct classes have distinct
(strictly increasing) string ends. -/
theorem string_ends_ragged {e₁ h N i i' : ℕ} (hh : 1 ≤ h) (hii' : i < i') :
    e₁ * (N - 1) + i * h < e₁ * (N - 1) + i' * h := by
  have h1 : (i + 1) * h ≤ i' * h := Nat.mul_le_mul_right h hii'
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- **GENHN-3(b), the general band count.** The class-`i` occupied heights at or above the
cap `e₁N` number exactly `min (i·h / e₁) N` — the general form of H.46's `raggedBand_card`
(genre E is `(e₁, i) = (2, 1)`, giving `⌊h/2⌋ = t`; gate below). Requires `e₁ ≥ 1`. -/
theorem bandCard {e₁ : ℕ} (h N i : ℕ) (he : 1 ≤ e₁) :
    ((Finset.range N).filter (fun v => e₁ * N ≤ e₁ * v + i * h)).card
      = min (i * h / e₁) N := by
  have hset : (Finset.range N).filter (fun v => e₁ * N ≤ e₁ * v + i * h)
      = Finset.Ico (N - i * h / e₁) N := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hvN, hcap⟩
      refine ⟨?_, hvN⟩
      -- e₁N ≤ e₁v + ih  ⟹  e₁(N−v) ≤ ih  ⟹  N−v ≤ ih/e₁
      have hd : e₁ * (N - v) = e₁ * N - e₁ * v := mul_sub_eq (le_of_lt hvN)
      have hle : e₁ * v ≤ e₁ * N := Nat.mul_le_mul_left e₁ (le_of_lt hvN)
      have hsub : (N - v) * e₁ ≤ i * h := by
        rw [Nat.mul_comm]
        omega
      have : N - v ≤ i * h / e₁ := (Nat.le_div_iff_mul_le he).2 hsub
      omega
    · rintro ⟨hlo, hvN⟩
      refine ⟨hvN, ?_⟩
      -- N−v ≤ ih/e₁  ⟹  e₁(N−v) ≤ ih  ⟹  e₁N ≤ e₁v + ih
      have h1 : N - v ≤ i * h / e₁ := by omega
      have h2 : (N - v) * e₁ ≤ i * h := (Nat.le_div_iff_mul_le he).1 h1
      have hd : e₁ * (N - v) = e₁ * N - e₁ * v := mul_sub_eq (le_of_lt hvN)
      have hle : e₁ * v ≤ e₁ * N := Nat.mul_le_mul_left e₁ (le_of_lt hvN)
      rw [Nat.mul_comm] at h2
      omega
  rw [hset, Nat.card_Ico]
  generalize i * h / e₁ = d
  omega

/-! ## 3. GENHN-3(a) — the interior criterion (rider-corrected, sufficient direction)
and the undercut / no-tie computation -/

/-- Every out-of-window contribution (`v ≥ N`) has `dv = e₁v + ih ≥ e₁N`. -/
theorem out_window_dv_ge {e₁ h N i v : ℕ} (hv : N ≤ v) : e₁ * N ≤ e₁ * v + i * h := by
  have := Nat.mul_le_mul_left e₁ hv
  omega

/-- **GENHN-3(a), interior stability (the R4 F-1 rider's "sufficient interior criterion").**
At the valuation layer: if the in-window value set `W` computes a value `< c` (read
`c = e₁N`), adjoining ANY set `B` of out-of-window contributions (each `≥ c`, by
`out_window_dv_ge`) leaves the computed minimum unchanged — the computed dv-value is a
function of the in-window data alone, i.e. LIFT-STABLE. -/
theorem interior_min_stable {W B : Finset ℕ} (hW : W.Nonempty) {c : ℕ}
    (hB : ∀ b ∈ B, c ≤ b) (hmin : W.min' hW < c) :
    (W ∪ B).min' (hW.mono Finset.subset_union_left) = W.min' hW := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_union_left _ (W.min'_mem hW))
  · rcases Finset.mem_union.1 ((W ∪ B).min'_mem (hW.mono Finset.subset_union_left)) with hw | hb
    · exact Finset.min'_le _ _ hw
    · have := hB _ hb
      omega

/-- **GENHN-3(a), the no-tie clause.** With `gcd(h, e₁) = 1` (H.51's separation
hypothesis), no OCCUPIED in-window height ties the cap: `e₁v + ih ≠ e₁N` for `i < e₁`,
`v ≤ N − 1`, `N ≥ 1`. (The out-of-window class-0 digit at `v = N` gives exactly `e₁N`,
"tying none below it".) Coprimality is LOAD-BEARING: at `(e₁, h) = (2, 2)` the in-window
value `2(N−1) + 1·2 = 2N` ties the cap — certified attack CERT-3; gate below. -/
theorem no_tie_at_cap {e₁ h N i v : ℕ} (hcop : Nat.Coprime h e₁) (hi : i < e₁)
    (hv : v ≤ N - 1) (hN : 1 ≤ N) : e₁ * v + i * h ≠ e₁ * N := by
  intro heq
  have hvN : v ≤ N := by omega
  have hd : e₁ * (N - v) = e₁ * N - e₁ * v := mul_sub_eq hvN
  have hle : e₁ * v ≤ e₁ * N := Nat.mul_le_mul_left e₁ hvN
  have hih : e₁ * (N - v) = i * h := by omega
  have hdvd : e₁ ∣ i * h := ⟨N - v, hih.symm⟩
  have hdvd_i : e₁ ∣ i := hcop.symm.dvd_of_dvd_mul_right hdvd
  have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_i hi
  subst hi0
  have hev : e₁ * v = e₁ * N := by omega
  have : v = N := Nat.eq_of_mul_eq_mul_left (by omega) hev
  omega

/-- **GENHN-3(a), the undercut (the instability half's witness pair).** If every in-window
value sits STRICTLY above the cap `c` (which `no_tie_at_cap` upgrades from `≥ c`), the
completion carrying the class-0 out-of-window digit at `v = N` (value exactly `c = e₁N`)
computes `c`, while the empty completion computes `W.min' > c`: two lifts, two values —
a computed value `≥ e₁N` is NOT lift-stable. -/
theorem cap_undercuts {W : Finset ℕ} (hW : W.Nonempty) {c : ℕ}
    (hstrict : ∀ w ∈ W, c < w) :
    (insert c W).min' (Finset.insert_nonempty c W) = c ∧ W.min' hW ≠ c := by
  constructor
  · apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_insert_self c W)
    · rcases Finset.mem_insert.1 ((insert c W).min'_mem (Finset.insert_nonempty c W)) with
        h | h
      · omega
      · exact le_of_lt (hstrict _ h)
  · have := hstrict _ (W.min'_mem hW)
    omega

/-! ## 4. GENHN-3(a), band `f₁ ≥ 2` — the `[r2]`/CAP-GEN arithmetic layer -/

/-- **The visible-component count** (`[r2]` annex, frame `μ = 2, e₁ = 1`, slope `k`):
component `t < f₁` of the height-`m` slot is in-window iff `m − tk ≤ N − 1`, i.e.
`m ≤ N − 1 + tk`. `compVis` is `CAP-GEN`'s `comp(m) = dim_{F_Q} V_m` at this frame; the
census of a nonzero readable pin is `pinCensus Q (compVis …) = Q^comp − 1` (H.44). -/
def compVis (f₁ k N m : ℕ) : ℕ :=
  ((Finset.range f₁).filter (fun t => m ≤ N - 1 + t * k)).card

/-- Interior heights (`m ≤ N − 1`) have all `f₁` components visible. -/
theorem compVis_interior {f₁ k N m : ℕ} (hm : m ≤ N - 1) : compVis f₁ k N m = f₁ := by
  unfold compVis
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro t _
  omega

/-- **The `[r2]` band bounds:** on the band `N ≤ m ≤ N − 1 + (f₁−1)k` (with `N ≥ 1`,
`f₁ ≥ 1`), the visible count satisfies `1 ≤ compVis < f₁` — "value readable, K-residue
needing an out-of-window component". -/
theorem compVis_band_bounds {f₁ k N m : ℕ} (hN : 1 ≤ N) (hf : 1 ≤ f₁)
    (hlo : N ≤ m) (hhi : m ≤ N - 1 + (f₁ - 1) * k) :
    1 ≤ compVis f₁ k N m ∧ compVis f₁ k N m < f₁ := by
  unfold compVis
  constructor
  · exact Finset.card_pos.2
      ⟨f₁ - 1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega⟩⟩
  · have h0 : (0 : ℕ) ∉ (Finset.range f₁).filter (fun t => m ≤ N - 1 + t * k) := by
      simp only [Finset.mem_filter, Finset.mem_range, not_and]
      intro _
      omega
    have hss : (Finset.range f₁).filter (fun t => m ≤ N - 1 + t * k) ⊂ Finset.range f₁ :=
      ⟨Finset.filter_subset _ _,
        fun hsub => h0 (hsub (Finset.mem_range.2 (by omega : (0 : ℕ) < f₁)))⟩
    have := Finset.card_lt_card hss
    rwa [Finset.card_range] at this

/-- Beyond the band (`m > N − 1 + (f₁−1)k`) nothing is visible. -/
theorem compVis_beyond {f₁ k N m : ℕ} (hm : N - 1 + (f₁ - 1) * k < m) :
    compVis f₁ k N m = 0 := by
  unfold compVis
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht
  have ht' : t ≤ f₁ - 1 := by
    have := Finset.mem_range.1 ht
    omega
  have : t * k ≤ (f₁ - 1) * k := Nat.mul_le_mul_right k ht'
  omega

end Uniformity.Density.Induction

/-! ## 5. GENHN-3(d) — the update-map core, both ring types at once -/

section Recentering

open Polynomial

variable {R : Type*} [CommRing R]

/-- **GENHN-3(d), the descent form.** The recentering update `x ↦ x + s` (S6's move)
descends to `R ⧸ I` for EVERY commutative ring and every ideal: instantiating
`I = (π^{d+1})`, the new state's digits at heights `≤ d` are a function of the old state's
digits at heights `≤ d` — "carries move upward only", and since `R` is arbitrary this is
**both ring types** (`ℤ_p` and `𝔽_q[[t]]`) in one statement. -/
theorem recenter_descends (I : Ideal R) (s : R) {f g : R[X]}
    (h : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) :
    (f.comp (X + C s)).map (Ideal.Quotient.mk I)
      = (g.comp (X + C s)).map (Ideal.Quotient.mk I) := by
  rw [Polynomial.map_comp, Polynomial.map_comp, h]

/-- **GENHN-3(d), the coefficient-axis triangularity** (GENIND-2(a)'s "binomial update
matrix is triangular with unit diagonal", displayed): the `n`-th coefficient of the
recentered polynomial is the `n`-th Hasse derivative evaluated at `s` — a function of the
old coefficients of index `≥ n` only (`Polynomial.hasseDeriv_coeff`). -/
theorem recenter_coeff_hasse (s : R) (f : R[X]) (n : ℕ) :
    (f.comp (X + C s)).coeff n = (Polynomial.hasseDeriv n f).eval s := by
  rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]

end Recentering

/-! ## 6. GATE — ties to the landed `e₁ = 2` ledger (H.46/H.89), the landed census (H.44),
and the committed `(1,3,2)` instance numbers -/

section OM6Gate

open Uniformity.Density.Induction

-- (b) gate: the general band count reproduces H.46's genre-E value `t` at `(e₁, i) = (2, 1)`,
-- `h = 2t + 1` — the `(t, N) = (1, 7)` cell of H.46's own header check (`h = 3, N = 7`,
-- band `{15}`, card `1`), and the `h = 1` empty band.
example : ((Finset.range 7).filter (fun v => 2 * 7 ≤ 2 * v + 1 * 3)).card = 1 := by decide
example : min (1 * 3 / 2) 7 = 1 := by decide          -- = t at h = 3
example : ((Finset.range 7).filter (fun v => 2 * 7 ≤ 2 * v + 1 * 1)).card = 0 := by decide
example : min (1 * 1 / 2) 7 = 0 := by decide          -- = 0 at h = 1 (H.46's empty band)

-- (c) gate: the general bound at `e₁ = 2` reproduces H.89's window ends: at odd `h` the
-- class-1 cap `e₁N − e₁ + (1·h % 2)` is the odd readable ceiling `2N − 1`.
example (N m : ℕ) (hm : m < 2 * N) (hmod : m % 2 = (1 * 3) % 2) : m ≤ 2 * N - 1 := by
  have := consulted_le_cap (e₁ := 2) (h := 3) (N := N) (i := 1) hm hmod
  omega

-- (a)-band gate: the committed `(1,3,2)` instance numbers, machine-checked through the
-- landed H.44 census (`pinCensus`) at `compVis`'s values.
example : compVis 3 1 7 7 = 2 := by decide            -- comp(N) = 2 at N = 7
example : compVis 3 1 7 8 = 1 := by decide            -- comp(N+1) = 1
example : compVis 3 1 8 7 = 3 := by decide            -- pin interior at N = 8
example : compVis 2 1 7 7 = 1 ∧ compVis 2 1 7 8 = 0 := by decide  -- (1,2,2): band = {N}
example : pinCensus 2 (compVis 3 1 7 7) = 3 := by decide
example : pinCensus 2 (compVis 3 1 7 7) * 2 ^ 13 + 2 ^ 13 = 2 ^ 15 := by decide
example : pinCensus 2 (compVis 3 1 8 7) = 7 := by decide
example : pinCensus 2 (compVis 3 1 8 7) * 2 ^ 18 + 2 ^ 18 = 2 ^ 21 := by decide

-- (a)-interior gate: the no-tie attack cell — at `(e₁, h) = (2, 2)` (NOT coprime) the
-- in-window value `2(N−1) + 1·2` DOES tie the cap `2N`: coprimality is load-bearing.
example (N : ℕ) (hN : 1 ≤ N) : 2 * (N - 1) + 1 * 2 = 2 * N := by omega

end OM6Gate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.consulted_le_cap
#print axioms Uniformity.Density.Induction.cap_le_string_end
#print axioms Uniformity.Density.Induction.consulted_inside_string
#print axioms Uniformity.Density.Induction.unoccupied_height_witness
#print axioms Uniformity.Density.Induction.string_end_le
#print axioms Uniformity.Density.Induction.string_end_mem
#print axioms Uniformity.Density.Induction.string_ends_ragged
#print axioms Uniformity.Density.Induction.bandCard
#print axioms Uniformity.Density.Induction.out_window_dv_ge
#print axioms Uniformity.Density.Induction.interior_min_stable
#print axioms Uniformity.Density.Induction.no_tie_at_cap
#print axioms Uniformity.Density.Induction.cap_undercuts
#print axioms Uniformity.Density.Induction.compVis_interior
#print axioms Uniformity.Density.Induction.compVis_band_bounds
#print axioms Uniformity.Density.Induction.compVis_beyond
#print axioms recenter_descends
#print axioms recenter_coeff_hasse

end AxCheck
