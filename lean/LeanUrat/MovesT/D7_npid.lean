/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesD.NPv_npid
import LeanUrat.MovesD.D8_bandShape
import LeanUrat.MovesD.D4a_chartBij
import LeanUrat.MovesD.L9s_Astable
import LeanUrat.MovesD.F1_enum

/-! # T-D7 `np_id` [hard, split D7a/D7b] — W4-4(a) (the ∀-jet quantifier is the
CONTRACT'S — REV 2, Codex 24) + `np_id_pin` (REV 7, W4-SYNC delta 6): the AS-BUILT
consumption target for MovesD's `NPIDPin`/`NthrSup`/`noteNP`/`D4R4_all_noteRange`
(imported BY NAME). `bandLevels`/`transportedLevels` are Defs carriers (CLOSED over
the built band vocabulary).

STATEMENT REPAIRS (adjudicated round-3 items, 2026-07-29; countermodels in the
campaign-ledger tail):
* `np_id` gains `hNP : (P : ShapePrefix).NPband n ≤ N` — **L12's own range, dropped
  in transcription**. The blueprint W4-4/T-D7 row keys the pin to L12 ("N(P̂) is
  finite, and for EVERY N ≥ N(P̂): …", quoted at `D4R4all_wrapper`; the W4-4 row's
  conclusion `D4R4_all_noteRange` quantifies `noteNP Nthr ≤ N`): the transported =
  band identity is priced only for presentations ON that range — a jet presented at
  `N < NPband` cannot see band levels ≥ N (`coordOf_lt` bounds every chart level
  below N), so the unguarded ∀-N form was refutable.
* `np_id_pin` gains the per-class jet-existence premise
  `hJex : ∀ i, Nonempty (JetSetup (reprOf i) n N m)` — **Wall B SEED-EXIST, fenced,
  typed as a hypothesis** (the blueprint's Wall-B row: MovesT riders take the
  jet/family AS GIVEN DATA — the hypothesis-not-axiom pattern; owner HC-2, never
  proved here). It also carries the SAME `hNP` range premise as `np_id` (its proof
  reads each class's threshold through a jet presented at N — the identical L12-range
  countermodel applies; recorded as a rider in MANIFEST "deviations").

PROOFS (per the escalation plan on record): D7a (⊆) via `fresh_band` + `band_shape`
+ `band_lt_Nshape` (de-privatized in MovesD/L9s_Astable — visibility-only, recorded);
D7b (⊇) via `chart_bij` + `fresh_cover`; the pin via the filters-agree identity
(`npband_eq_sup_bandLevels`: NPband's Nshape-grid filter = `bandLevels`' own grid,
both cut by the same `bandS` predicate). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-! ### foldr-union kernel (List-safe fold membership, both directions).
`mem_foldr_union` MOVED here from T-C2 (statement unchanged) — C2 imports D7, and
both units read `transportedLevels`' fold. -/

/-- List-safe union membership: an element of a listed Finset lies in the folded union
(`transportedLevels`'s REV-9 List-safe fold). [Moved from `C2_capIrr.lean` at the
round-3 repair — statement byte-identical.] -/
lemma mem_foldr_union {γ : Type*} [DecidableEq γ] {L : List (Finset γ)} {s : Finset γ}
    (hs : s ∈ L) {c : γ} (hc : c ∈ s) :
    c ∈ L.foldr (· ∪ ·) ∅ := by
  induction L with
  | nil => exact absurd hs List.not_mem_nil
  | cons t L ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hs with rfl | h
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (ih h)

/-- the elimination direction: a member of the folded union lies in some listed
Finset. -/
lemma exists_of_mem_foldr_union {γ : Type*} [DecidableEq γ] {L : List (Finset γ)}
    {c : γ} (hc : c ∈ L.foldr (· ∪ ·) ∅) : ∃ s ∈ L, c ∈ s := by
  induction L with
  | nil => simp at hc
  | cons t L ih =>
    rw [List.foldr_cons] at hc
    rcases Finset.mem_union.mp hc with h | h
    · exact ⟨t, List.mem_cons_self, h⟩
    · obtain ⟨s, hs, hcs⟩ := ih h
      exact ⟨s, List.mem_cons_of_mem _ hs, hcs⟩

/-! ### the shape-side band-grid kernel: membership faces + the filters-agree
identity (NPband's own Nshape-grid filter and `bandLevels` cut the SAME `bandS`
predicate; `band_lt_Nshape` collapses the two grid ranges). -/

/-- a `bandS`-satisfying in-box coordinate sits strictly below the geometric
threshold (via the de-privatized `band_lt_Nshape` height bound). -/
lemma level_lt_npband (R : ShapePrefix) (n : ℕ) (c : ℕ × ℕ) (hc2 : c.2 < n)
    {r : ℕ} (hr : r < R.reads.length) (hb : R.bandS n r c) : c.1 < R.NPband n := by
  classical
  have h1 : c.1 < R.Nshape := band_lt_Nshape R n r c hr hb
  unfold ShapePrefix.NPband
  rw [Nat.lt_one_add_iff]
  refine Finset.le_sup (f := fun c : ℕ × ℕ => c.1) ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨h1, hc2⟩, r, hr, hb⟩

/-- the `bandLevels` introduction face. -/
lemma mem_bandLevels (R : ShapePrefix) (n : ℕ) (c : ℕ × ℕ) (hc2 : c.2 < n)
    {r : ℕ} (hr : r < R.reads.length) (hb : R.bandS n r c) : c ∈ bandLevels R n := by
  classical
  unfold bandLevels
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨level_lt_npband R n c hc2 hr hb, hc2⟩, r, hr, hb⟩

/-- the `bandLevels` elimination face. -/
lemma bandLevels_mem_elim {R : ShapePrefix} {n : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ bandLevels R n) :
    (c.1 < R.NPband n ∧ c.2 < n) ∧ ∃ r < R.reads.length, R.bandS n r c := by
  classical
  unfold bandLevels at hc
  simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] using hc

/-- **the filters-agree identity** (the pin's kernel): the built `NPband` IS
1 + the largest `bandLevels` level — NPband's Nshape-grid filter and `bandLevels`'
NPband-grid filter carry the same `bandS` predicate, and `band_lt_Nshape` /
`level_lt_npband` place every satisfying coordinate inside BOTH grids. -/
lemma npband_eq_sup_bandLevels (R : ShapePrefix) (n : ℕ) :
    R.NPband n = 1 + (bandLevels R n).sup Prod.fst := by
  classical
  unfold ShapePrefix.NPband
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hc
    obtain ⟨⟨hc1, hc2⟩, r, hr, hb⟩ := hc
    exact Finset.le_sup (f := Prod.fst) (mem_bandLevels R n c hc2 hr hb)
  · apply Finset.sup_le
    intro c hc
    obtain ⟨⟨-, hc2⟩, r, hr, hb⟩ := bandLevels_mem_elim hc
    refine Finset.le_sup (f := fun c : ℕ × ℕ => c.1) ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨band_lt_Nshape R n r c hr hb, hc2⟩, r, hr, hb⟩

/-! ### D7a/D7b -/

/-- **D7a (⊆), premise-free**: every transported (level, base) pair is a shape band
coordinate — `fresh_band` places each consumed fresh-support coordinate in its read's
band, `band_shape` transfers to the shape side, `level_lt_npband` bounds the grid.
The ⊆ half needs NO range premise (a sub-threshold jet transports a SUBSET of the
grid); T-C2's `tbcap_irr_family` consumes exactly this half at its presented jets. -/
theorem np_id_sub {P : Shape n} (i : PrefIdx n pol P)
    (J : JetSetup (reprOf i) n N m) :
    transportedLevels J (topLocus p m) ⊆ bandLevels (P : ShapePrefix) n := by
  classical
  have hmatch : (P : ShapePrefix).MatchesHist (reprOf i) := (reprOf_mem i).1
  obtain ⟨hlen, -⟩ := id hmatch
  intro c hc
  unfold transportedLevels at hc
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range] at hc
  obtain ⟨j, ⟨⟨r, hr, hj⟩, -⟩, rfl⟩ := hc
  obtain ⟨s, hs, hjs⟩ := exists_of_mem_foldr_union hj
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  have hband : inFreshBand (reprOf i) n J.coordOf r ((reprOf i).nodes[r]'hr) j :=
    J.fresh_band r hr cl hcl j hjs
  have hbS : (P : ShapePrefix).bandS n r (J.coordOf j) :=
    (band_shape hmatch r hr j).mp hband
  have hr' : r < (P : ShapePrefix).reads.length := by omega
  exact mem_bandLevels _ n _ (J.coordOf_lt j).2 hr' hbS

/-- D7a/D7b: NP-ID — the transported level support IS the shape-side band grid.
[STATEMENT REPAIR, adjudicated round-3 item (4): the premise
`hNP : (P : ShapePrefix).NPband n ≤ N` is **L12's own range, dropped in
transcription** — cite the blueprint W4-4/T-D7 row ("for EVERY N ≥ N(P̂)", L12
quoted at `D4R4all_wrapper`; the row's own conclusion `D4R4_all_noteRange` ranges
over `noteNP Nthr ≤ N`). Countermodel without it: a jet presented at `N < NPband`
has every chart level `< N` (`coordOf_lt`), so band levels in `[N, NPband)` are
never transported and the ⊇ half fails.] -/
theorem np_id {P : Shape n} (i : PrefIdx n pol P)
    (hNP : (P : ShapePrefix).NPband n ≤ N)
    (J : JetSetup (reprOf i) n N m) :
    transportedLevels J (topLocus p m) = bandLevels (P : ShapePrefix) n := by
  classical
  have hmatch : (P : ShapePrefix).MatchesHist (reprOf i) := (reprOf_mem i).1
  obtain ⟨hlen, -⟩ := id hmatch
  apply Finset.Subset.antisymm (np_id_sub i J)
  -- D7b (⊇): chart_bij + fresh_cover
  intro c hc
  obtain ⟨⟨hc1, hc2⟩, r, hr, hb⟩ := bandLevels_mem_elim hc
  have hcbox : c ∈ Finset.range N ×ˢ Finset.range n := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hc1 hNP, hc2⟩
  obtain ⟨j, hj⟩ := (chart_bij J).2 c hcbox
  have hr2 : r < (reprOf i).nodes.length := by omega
  have hband : inFreshBand (reprOf i) n J.coordOf r ((reprOf i).nodes[r]'hr2) j := by
    refine (band_shape hmatch r hr2 j).mpr ?_
    rw [hj]
    exact hb
  obtain ⟨cl, hcl, hjcl⟩ := J.fresh_cover r hr2 j hband
  unfold transportedLevels
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
  refine ⟨j, ⟨⟨r, hr2, ?_⟩, ?_⟩, hj⟩
  · exact mem_foldr_union (List.mem_map_of_mem (f := fun cl => cl.support) hcl) hjcl
  · simp [topLocus]

/-- the BUILT pin supplied (REV 7): W4-4's as-built form.
[STATEMENT REPAIR, adjudicated round-3 item (4): gains the per-class jet-existence
premise `hJex` — **Wall B SEED-EXIST, fenced, typed as a hypothesis** (owner HC-2;
the blueprint Wall-B row's hypothesis-not-axiom pattern: `reprOf` is a classical
section, so the bare pin could read `hNthr` at NO jet and was unprovable without a
witness). RIDER (recorded in MANIFEST "deviations"): the pin also carries `np_id`'s
own `hNP` L12-range premise — its proof reads each class's `Nthr i` through a jet
presented AT N (`hNthr` + `hJex`), where the transported = band identity is priced
only on L12's range; the same sub-threshold countermodel refutes the unguarded
form.] Proof: all classes' transported level sets coincide with `bandLevels`
(`np_id`), so `NthrSup Nthr = 1 + max band level = NPband` — the filters-agree
identity `npband_eq_sup_bandLevels`. -/
theorem np_id_pin {P : Shape n}
    (hNP : (P : ShapePrefix).NPband n ≤ N)
    (hJex : ∀ i : PrefIdx n pol P, Nonempty (JetSetup (reprOf i) n N m))
    (Nthr : PrefIdx n pol P → ℕ)
    (hNthr : ∀ (i : PrefIdx n pol P) (J : JetSetup (reprOf i) n N m),
      Nthr i = 1 + (transportedLevels J (topLocus p m)).sup Prod.fst) :
    NPIDPin n pol P Nthr := by
  intro hne
  letI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  have hconst : ∀ i : PrefIdx n pol P, Nthr i = (P : ShapePrefix).NPband n := by
    intro i
    obtain ⟨J⟩ := hJex i
    rw [hNthr i J, np_id i hNP J, ← npband_eq_sup_bandLevels]
  have hsup : NthrSup Nthr = (P : ShapePrefix).NPband n := by
    unfold NthrSup
    apply le_antisymm
    · exact Finset.sup_le (fun i _ => le_of_eq (hconst i))
    · obtain ⟨i₀⟩ := hne
      calc (P : ShapePrefix).NPband n = Nthr i₀ := (hconst i₀).symm
        _ ≤ _ := Finset.le_sup (Finset.mem_univ i₀)
  exact hsup.symm

end LeanUrat.MovesT
