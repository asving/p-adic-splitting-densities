/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG5
import Uniformity.ChapC.C133mh11
import Uniformity.ChapC.C133mh15
import Uniformity.ChapC.C134csx

/-!
# Uniformity.ChapI.IFCG6 — [A0G7 2026-08-28] the engine binding and the child decrease
(nodes A0G-HE + A0G-CH)

**Uniform-a0 campaign, NODES A0G-HE and A0G-CH** (`docs/in-progress/A0_GENERAL_2026-08-28.md`
§6 rows `A0G-HE0`/`A0G-HE1`/`A0G-CH`, merged per the unit charge).  This file binds the
completed dv-graded Hensel engine (chapter C's MH corpus) to IFCG5's face-schema skeletons:
**every coprime residual split in a schema produces the declared pure factor blocks and
types**, and **every H.01-packageable residual child strictly decreases the cluster mass**.

## Node A0G-CH — the child decrease (§2; Lean-core, field-free arithmetic)

**Dedup record (per the standing dedup lesson, checked FIRST):** IFCG5 §5 already landed the
loop-conditioned decrease — `entry_snd_lt_mass_of_ne_loop`, `childEntry_lt_mass_or_loop`,
`childSizes_lt_mass_of_ne_loop`, and the cleared quotient bound
`two_mul_entry_snd_le_mass_of_two_le_den`.  This file does NOT restate any of them.  What the
row still owed, all field/citation-free:

* `entry_snd_lt_mass_of_fractional` — on a FRACTIONAL face (`b ≥ 2`) the decrease `μ < m` is
  UNCONDITIONAL: no `s ≠ loopSkeleton m` hypothesis (a fractional face can never be the loop
  face, so the per-skeleton side condition is redundant there).  This is the §6 row's literal
  statement "the repeated residual child has `μ < m` on every non-loop fractional face".
* `faceResDeg_le_mass_div_den` / `entry_snd_le_mass_div_den` / `decrease_chain_of_fractional`
  — §4.2's decrease chain `μ ≤ d ≤ m/b < m` VERBATIM, in exact `ℕ`-division form (IFCG5
  carried only the division-cleared form).
* `entry_snd_lt_mass_of_key` ★ — the sharpest form: `μ < m` for EVERY entry satisfying H.01's
  key condition `2 ≤ b·D` — fractional or not, loop hypothesis or not.  The sole entry of a
  valid skeleton violating `2 ≤ b·D` with `μ = m` is the loop's `(1, m)`
  (IFCG5's `eq_loopSkeleton_of_entry_snd_eq_mass`), and `loopFace_not_key` shows the loop face
  indeed carries NO key entry: together the two files give A0G-GC3's decrease tooth with the
  rescale as the sole same-mass edge.
* `genreDatumOfChildEntry_μ_lt_mass` ★ — the feed at the H.01 surface: every `GenreDatum`
  that IFCG5's `genreDatumOfChildEntry` can package from a valid mass-`m` skeleton has
  `μ < m`.  (H.01's `hkey` is exactly what excludes the loop child, so no loop side condition
  appears.)
* `childSizes_sum_le_mass` — bookkeeping: the TOTAL recursive child mass is at most `m`
  (each child of multiplicity `μ` controls face mass `b·D·μ ≥ μ`; sum = `m` by IFCG5's
  `mass_conservation`).

## Node A0G-HE — the engine binding (§3–§6)

The engine speaks (frame `F`, direction `u/ℓ`, dv-purity, `dvResPoly`); the skeleton speaks
(faces `(b, σ)`, entries `(D, μ)`).  The binding surfaces, in dependency order:

* `dv_multi_split` ★★ (§4) — **the n-ary Theorem A**: a monic dv-pure `g` whose level
  residual factors as a product of pairwise-coprime monic positive-degree `G_i` splits as
  `g = ∏ gᵢ` with each `gᵢ` monic, dv-pure, of EXACT degree `ℓ·D′·deg Gᵢ`, and EXACT
  residual `Gᵢ` (∀-pin form).  Iterates `C133mh9.theoremA` (the landed, Lean-core dv-graded
  Hensel existence) down the list; the constant-coefficient hypotheses Theorem A needs are
  DERIVED from `natDegree_dvResPoly` (the residual has nonzero constant coefficient), not
  assumed.  Lean-core.
* `schema_split` ★★ (§5) — the split AT A SCHEMA: the residual factors are powers
  `rᵢ^{μᵢ}` of distinct monic irreducibles matching a face pattern's entries `(Dᵢ, μᵢ)`
  (`deg rᵢ = Dᵢ`).  Each produced block additionally REALIZES its singleton sub-face
  `(ℓ, {(Dᵢ, μᵢ)})` in IFCG5's `RealizesFaceAt` sense — discharging exactly the residual
  binding IFCG5's scoping note deferred to this node.  Pairwise coprimality of the powers is
  DERIVED from distinctness + irreducibility (over the stage field); Lean-core.
* `levelDatumOfEntry` (§5) — the engine-side twin of IFCG5's `genreDatumOfChildEntry`: a
  pattern entry's residual data packaged as a C.09 `LevelDatum` (the numerator `u` and the
  stage-field irreducible `r` are explicit arguments, per IFCG5's D4).  With it,
  `hasLabel_of_block` + `block_natDegree_keyDeg₂` certify the TYPE contribution: the block
  carries `HasLabel L` and its degree is EXACTLY `L.keyDeg₂ · μ` — the stage's
  `(e, f) = (ℓ, deg r)` block with multiplicity exactly the pattern's `μ`, not merely a
  degree count (the A0G-HE1 gate).
* `face_split_unique` (§6) — `C133mh11.dv_oneSlope_split_unique` bound at the face surface:
  a `RealizesFaceAt` witness supplies the purity hypothesis, so the labelled/complement
  split of a face-realizing polynomial is UNIQUE.  The blocks of `schema_split` are therefore
  THE declared blocks.  Lean-core.
* `blockFactor_realizes_face` ★ / `context_split_face` ★ (§6) — the AMBIENT binding: under
  the signed `BlockContext`, C.35's selector `blockFactor L f` itself realizes the
  single-entry face `(L.ℓ, {(deg L.r, mult₂ L f)})` — the engine's ambient output IS a
  skeleton-face occupant (with `ValidFace`, `HasLabel`, divisibility, and positive
  multiplicity); and C134csx's full context split is re-exported with that face clause
  attached.  **These two are the file's ONLY cite carriers** (the allowlisted C.33 dissection
  `exists_dvDissection`, inherited through `C133mh15.blockFrontier_of_context` /
  `C134csx.context_split`).

## Design decisions (recorded per the unit charge)

* **D1 (no new predicates for HE0).**  The n-ary split is stated with raw `(u, ℓ)` data and
  `List.Forall₂` packaging — no new Prop wrapper — so A0G-GC3 can consume it pointwise
  without unfolding anything; the schema layer (`schema_split`) is where IFCG5's face types
  enter.
* **D2 (∃-pin in, ∀-pin out).**  Residual hypotheses are taken in the WEAK ∃-pin form and
  conclusions returned in the STRONG ∀-pin form (C.25's junk-total design makes them
  equivalent; Theorem A already pays the conversion cost).
* **D3 (hypothesis economy).**  Constant-coefficient nonvanishing of every residual factor is
  derived inside the proofs from the C.26 law `(dvResPoly).coeff 0 ≠ 0`; positivity of factor
  degrees is taken as a hypothesis because face validity (IFCG5 `ValidFace`) supplies it.
* **D4 (theoremC_placement enters transitively).**  The §6 HE1 row lists
  `C133mh13.theoremC_placement`; it is consumed INSIDE the two ambient bindings (it is the
  maximality step of `blockFrontier_of_context` and `context_split`).  A thin direct re-wrap
  would add a hypothesis relay with no new content, so it is deliberately not landed;
  per-face maximality is delivered through `face_split_unique` (mh11) instead.
* **D5 (cite isolation).**  Only the two ambient theorems touch the C.33-cite-bearing chain;
  every per-face theorem (the whole §2–§6 core) is Lean-core, so downstream consumers pay
  the cite exactly when they invoke the ambient dissection, never for the schema algebra.

## Landed inputs consumed

`C133mh9.theoremA` (via `C133mh14.TheoremAStatement`), `C133mh11.dv_oneSlope_split_unique`,
`C133mh15.blockFrontier_of_context`, `C134csx.context_split`, C.35's
`blockFactor_spec_of_frontier` + purity laws (`dvSideMin_eq_zero_of_isDvPure`,
`dvSideMax_eq_of_isDvPure`, `natDegree_div_eq_of_isDvPure`), C.26's `natDegree_dvResPoly`,
C.34's `dvSideSet_nonempty`, C.09's `LevelDatum`, and IFCG5's full face/child bank
(`RealizesFaceAt`, `ValidFace`, `stage_degree_le_mass`, `genreDatumOfChildEntry`, …).
Private plumbing (`isKey_X`, `localFieldStageField`, `dvOnSide_of_mem'`, `exists_pin`) is
re-declared byte-identical in mechanism from `C133mh14.lean` Part 0 / `C134csx.lean` Part 0
(private there, hence unreachable; credited per declaration; neither file edited).

## Status

Sorry-free.  AxCheck footer: every declaration Lean-core EXCEPT `blockFactor_realizes_face`
and `context_split_face`, which inherit exactly the allowlisted C.33 dissection cite
`Uniformity.Density.Tower.C33Cite.exists_dvDissection`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG6

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5

/-! ## §1 — Private list/multiset plumbing (Lean-core; no engine content) -/

private theorem forall₂_imp_of_mem {α β : Type*} {R S : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    (himp : ∀ a b, a ∈ l₁ → R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l₁' l₂' ha _ ih =>
      exact List.Forall₂.cons (himp a b List.mem_cons_self ha)
        (ih fun x y hx hR => himp x y (List.mem_cons_of_mem _ hx) hR)

private theorem multiset_list_sum_sum {l : List (Multiset ℕ)} :
    l.sum.sum = (l.map Multiset.sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [Multiset.sum_add, ih]

private theorem multiset_sum_le_of_le {s t : Multiset ℕ} (h : s ≤ t) : s.sum ≤ t.sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [Multiset.sum_add]
  exact Nat.le_add_right _ _

/-! ## §2 — NODE A0G-CH: the child decrease (field-free arithmetic on IFCG5's carrier)

Everything below is `ℕ`-arithmetic on IFCG5's `ValidSkeleton`/`FaceShape` data — no ring, no
field, no citation.  The dedup record is in the module header: the loop-conditioned forms are
IFCG5's and are NOT restated. -/

/-- **Unconditional decrease on fractional faces** (the A0G-CH row's literal statement): on a
face of denominator `b ≥ 2`, EVERY residual multiplicity satisfies `μ < m` — with no
`s ≠ loopSkeleton m` side condition (the loop face has `b = 1`).  From IFCG5's cleared bound
`2μ ≤ m` plus entry positivity. -/
theorem entry_snd_lt_mass_of_fractional {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s) (hb : 2 ≤ f.1)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) : p.2 < m := by
  have h2 := two_mul_entry_snd_le_mass_of_two_le_den hs hf hb hp
  have h1 : 1 ≤ p.2 := ((hs.1 f hf).2.2 p hp).2
  omega

/-- §4.2's `d ≤ m/b`, in exact `ℕ`-division form (IFCG5 carried only the cleared `b·d ≤ m`). -/
theorem faceResDeg_le_mass_div_den {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s) :
    faceResDeg f ≤ m / f.1 := by
  rw [Nat.le_div_iff_mul_le ((hs.1 f hf).1)]
  rw [Nat.mul_comm]
  exact faceLen_le_mass hs hf

/-- §4.2's `μ ≤ m/b`, in exact `ℕ`-division form. -/
theorem entry_snd_le_mass_div_den {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) : p.2 ≤ m / f.1 :=
  le_trans (entry_snd_le_resDeg (hs.1 f hf) hp) (faceResDeg_le_mass_div_den hs hf)

/-- **§4.2's decrease chain `μ ≤ d ≤ m/b < m`, verbatim** on a fractional face.  The mass
positivity `1 ≤ m` is DERIVED (the face itself has positive length), not assumed. -/
theorem decrease_chain_of_fractional {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s) (hb : 2 ≤ f.1)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) :
    p.2 ≤ faceResDeg f ∧ faceResDeg f ≤ m / f.1 ∧ m / f.1 < m := by
  have hm : 1 ≤ m := le_trans (faceLen_pos (hs.1 f hf)) (faceLen_le_mass' hs hf)
  exact ⟨entry_snd_le_resDeg (hs.1 f hf) hp, faceResDeg_le_mass_div_den hs hf,
    Nat.div_lt_self hm hb⟩

/-- ★ **The key-condition decrease** (A0G-CH's sharpest form): `μ < m` for EVERY residual
entry satisfying H.01's key condition `2 ≤ b·D` — no fractionality, no loop side condition.
(The loop's `(1, m)` entry is the sole full-mass entry of any valid skeleton, and it violates
`2 ≤ b·D`; see `loopFace_not_key`.) -/
theorem entry_snd_lt_mass_of_key {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s)
    {p : ℕ × ℕ} (hp : p ∈ f.2.data) (hkey : 2 ≤ f.1 * p.1) : p.2 < m := by
  have h1 : 1 ≤ p.2 := ((hs.1 f hf).2.2 p hp).2
  have h2 : f.1 * p.1 * p.2 ≤ m := stage_degree_le_mass hs hf hp
  have h3 : 2 * p.2 ≤ f.1 * p.1 * p.2 := Nat.mul_le_mul_right _ hkey
  omega

/-- The child-entry form of the key-condition decrease (A0G-GC3's consumable shape). -/
theorem childEntry_lt_mass_of_key {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s)
    {f : FaceShape} {p : ℕ × ℕ} (hc : IsChildEntry s f p) (hkey : 2 ≤ f.1 * p.1) :
    p.2 < m :=
  entry_snd_lt_mass_of_key hs hc.1 hc.2.1 hkey

/-- The loop face carries NO key entry: its sole entry `(1, m)` has `b·D = 1`.  Together with
`entry_snd_lt_mass_of_key` this is the decrease/loop dichotomy at the face level: key entries
strictly decrease, and the rescale child is never key-packageable. -/
theorem loopFace_not_key {m : ℕ} {p : ℕ × ℕ} (hp : p ∈ (loopFace m).2.data) :
    ¬ 2 ≤ (loopFace m).1 * p.1 := by
  have hpe : p = (1, m) := by simpa [loopFace] using hp
  subst hpe
  simp [loopFace]

/-- ★ **The A0G-CH feed at the H.01 surface**: every `GenreDatum` packaged by IFCG5's
`genreDatumOfChildEntry` from an entry of a valid mass-`m` skeleton has `μ < m` — H.01's
`hkey` hypothesis is exactly what excludes the loop child, so the decrease is unconditional. -/
theorem genreDatumOfChildEntry_μ_lt_mass {m : ℕ} {s : List FaceShape}
    (hs : ValidSkeleton m s) {f : FaceShape} (hf : f ∈ s)
    (Q h : ℕ) (hQ : 2 ≤ Q) (hh : 1 ≤ h) {p : ℕ × ℕ} (hp : p ∈ f.2.data)
    (hμ : 2 ≤ p.2) (hkey : 2 ≤ f.1 * p.1) (hcop : Nat.Coprime h f.1) :
    (genreDatumOfChildEntry Q h hQ hh (hs.1 f hf) hp hμ hkey hcop).μ < m := by
  rw [genreDatumOfChildEntry_μ]
  exact entry_snd_lt_mass_of_key hs hf hp hkey

/-- **Total child mass is bounded by the cluster mass**: the recursive child sizes of a valid
mass-`m` skeleton sum to at most `m` (each multiplicity-`μ` child controls face mass
`b·(D·μ) ≥ μ`; the controlled masses sum to `m` exactly by IFCG5's `mass_conservation`). -/
theorem childSizes_sum_le_mass {m : ℕ} {s : List FaceShape} (hs : ValidSkeleton m s) :
    (childSizes s).sum ≤ m := by
  have h2 : (childSizes s).sum
      = (s.map (fun f => (((f.2.data.map Prod.snd).filter (fun μ => 2 ≤ μ)).sum))).sum := by
    unfold childSizes
    rw [multiset_list_sum_sum, List.map_map]
    rfl
  have h1 : (s.map (fun f => (((f.2.data.map Prod.snd).filter (fun μ => 2 ≤ μ)).sum))).sum
      ≤ (s.map (fun f => (f.2.data.map (fun p => f.1 * (p.1 * p.2))).sum)).sum := by
    apply List.sum_le_sum
    intro f hf
    have hval := hs.1 f hf
    calc (((f.2.data.map Prod.snd).filter (fun μ => 2 ≤ μ)).sum)
        ≤ (f.2.data.map Prod.snd).sum :=
          multiset_sum_le_of_le (Multiset.filter_le _ _)
      _ ≤ (f.2.data.map (fun p => f.1 * (p.1 * p.2))).sum := by
          apply Multiset.sum_map_le_sum_map
          intro p hp
          obtain ⟨hD, hμ⟩ := hval.2.2 p hp
          have hb := hval.1
          calc p.2 = 1 * (1 * p.2) := by ring
            _ ≤ f.1 * (p.1 * p.2) := Nat.mul_le_mul hb (Nat.mul_le_mul hD le_rfl)
  rw [h2]
  exact le_trans h1 (le_of_eq (mass_conservation hs))

/-! ## §3 — NODE A0G-HE: engine plumbing

The four private declarations below are re-declared byte-identical in mechanism from
`C133mh14.lean` Part 0 / `C134csx.lean` Part 0 (private there, hence unreachable across
files; credited per declaration; neither file edited).  The list lemmas are fresh plumbing. -/

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-- Local D9 reconstruction (source: `C133mh14.lean`'s private `isKey_X`). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

/-- The stage field's `Field` instance (source: `C133mh14.lean`'s private
`localFieldStageField`). -/
@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- Membership in `dvSideSet` unpacks `DvOnSide` (source: `C133mh14.lean`'s private
`dvOnSide_of_mem'`). -/
private theorem dvOnSide_of_mem' {F : KeyFrame O π} {u ℓ j : ℕ} {f : Polynomial O}
    (hj : j ∈ dvSideSet F f u ℓ) : DvOnSide F f u ℓ j := by
  classical
  exact (Finset.mem_filter.mp (show j ∈ (Finset.range (f.natDegree + 1)).filter
    (DvOnSide F f u ℓ) from hj)).2

/-- Pin existence: the side-min abscissa of a nonempty side has FINITE level height
(source: `C133mh14.lean`'s private `exists_pin`). -/
private theorem exists_pin (F : KeyFrame O π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F f (dvSideMin F f u ℓ hne) = (M : ℕ∞) := by
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.1 (dvOnSide_of_mem' (Finset.min'_mem _ hne)).2
  exact ⟨M, hM.symm⟩

private theorem list_prod_monic {R : Type*} [CommSemiring R] :
    ∀ {l : List (Polynomial R)}, (∀ p ∈ l, p.Monic) → l.prod.Monic := by
  intro l
  induction l with
  | nil => intro _; exact Polynomial.monic_one
  | cons a t ih =>
      intro h
      rw [List.prod_cons]
      exact (h a List.mem_cons_self).mul (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

private theorem isCoprime_list_prod {R : Type*} [CommSemiring R] {a : R} :
    ∀ {l : List R}, (∀ b ∈ l, IsCoprime a b) → IsCoprime a l.prod := by
  intro l
  induction l with
  | nil => intro _; simpa using isCoprime_one_right
  | cons b t ih =>
      intro h
      rw [List.prod_cons]
      exact (h b List.mem_cons_self).mul_right (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- Distinct monic irreducibles over a field are coprime, and so are their powers. -/
private theorem pow_isCoprime_of_ne {k : Type*} [Field k] {r r' : Polynomial k}
    (hrm : r.Monic) (hr'm : r'.Monic) (hri : Irreducible r) (hr'i : Irreducible r')
    (hne : r ≠ r') (m m' : ℕ) : IsCoprime (r ^ m) (r' ^ m') := by
  have hnd : ¬ r ∣ r' := by
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    rcases hr'i.isUnit_or_isUnit hc with hu | hu
    · exact hri.not_isUnit hu
    · exact hne (Polynomial.eq_of_monic_of_associated hrm hr'm
        ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩)
  exact (hri.coprime_iff_not_dvd.mpr hnd).pow

/-! ## §4 — ★★ `dv_multi_split`: the n-ary Theorem A (A0G-HE0's core; Lean-core)

Iterating `C133mh9.theoremA` down a list of pairwise-coprime monic residual factors.  The
statement is arrow-chained in the list data (`Gs` first, then its hypotheses, then the
polynomial `g` and its hypotheses) so the induction motive needs no `generalizing`
bookkeeping. -/

set_option maxHeartbeats 1600000 in
/-- ★★ **The n-ary dv-graded Hensel split** (node A0G-HE0's core).  Let `g` be monic and
`(u, ℓ)`-dv-pure with `D′ ∣ deg g`, and let its level residual factor as `∏ Gᵢ` with the `Gᵢ`
monic, of positive degree, and pairwise coprime.  Then `g = ∏ gᵢ` with each `gᵢ` monic,
`(u, ℓ)`-dv-pure, of EXACT degree `ℓ·D′·deg Gᵢ`, and EXACT residual `Gᵢ` at every pin.
Constant-coefficient nonvanishing of the `Gᵢ` is DERIVED (C.26), not assumed.  Lean-core:
`C133mh9.theoremA` consumes no cite. -/
theorem dv_multi_split
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) :
    ∀ (Gs : List (Polynomial (F.stageField H₀ hpin))),
      (∀ G ∈ Gs, G.Monic) → (∀ G ∈ Gs, 0 < G.natDegree) → Gs.Pairwise IsCoprime →
    ∀ {g : Polynomial O}, g.Monic → (F.e₁ * F.f₁) ∣ g.natDegree → IsDvPure F g u ℓ →
      (∃ (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)),
        dvResPoly F H₀ hpin g u ℓ hne M₀ hp = Gs.prod) →
      ∃ gs : List (Polynomial O), g = gs.prod ∧
        List.Forall₂ (fun G g₁ => g₁.Monic ∧ IsDvPure F g₁ u ℓ ∧
          g₁.natDegree = ℓ * (F.e₁ * F.f₁) * G.natDegree ∧
          ∀ (hne₁ : (dvSideSet F g₁ u ℓ).Nonempty) (M₁ : ℕ)
            (hp₁ : dvHgt F g₁ (dvSideMin F g₁ u ℓ hne₁) = (M₁ : ℕ∞)),
            dvResPoly F H₀ hpin g₁ u ℓ hne₁ M₁ hp₁ = G) Gs gs := by
  intro Gs
  induction Gs with
  | nil =>
      intro _ _ _ g hg hgd hgpure hres
      obtain ⟨hne, M₀, hp, hR⟩ := hres
      -- `R(g) = 1` forces `dvSideDeg = 0`, hence `deg g = 0` (purity + divisibility), so `g = 1`
      have hRdeg := (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
      rw [hR] at hRdeg
      have hsd : dvSideDeg F g u ℓ hne = 0 := by simpa using hRdeg.symm
      have hdiv := natDegree_div_eq_of_isDvPure hℓ hcop hgpure hne
      rw [hsd, Nat.mul_zero] at hdiv
      have hg0 : g.natDegree = 0 := by
        have h1 := Nat.mul_div_cancel' hgd
        rw [hdiv, Nat.mul_zero] at h1
        exact h1.symm
      refine ⟨[], ?_, List.Forall₂.nil⟩
      rw [List.prod_nil]
      exact Polynomial.eq_one_of_monic_natDegree_zero hg hg0
  | cons G Gs' ih =>
      intro hmon hpos hpair g hg hgd hgpure hres
      obtain ⟨hne, M₀, hp, hR⟩ := hres
      have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
      have hGmon : G.Monic := hmon G List.mem_cons_self
      have hGpos : 0 < G.natDegree := hpos G List.mem_cons_self
      have hmon' : ∀ X ∈ Gs', X.Monic := fun X hX => hmon X (List.mem_cons_of_mem _ hX)
      have hpos' : ∀ X ∈ Gs', 0 < X.natDegree := fun X hX => hpos X (List.mem_cons_of_mem _ hX)
      obtain ⟨hcopG, hpair'⟩ := List.pairwise_cons.mp hpair
      have hPmon : Gs'.prod.Monic := list_prod_monic hmon'
      have hGP : IsCoprime G Gs'.prod := isCoprime_list_prod hcopG
      -- constant coefficients, derived from the C.26 law
      have hR0 := (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).2
      rw [hR, List.prod_cons, Polynomial.mul_coeff_zero] at hR0
      have hG0 : G.coeff 0 ≠ 0 := fun h0 => hR0 (by rw [h0, zero_mul])
      have hP0 : Gs'.prod.coeff 0 ≠ 0 := fun h0 => hR0 (by rw [h0, mul_zero])
      -- positive degree of `g`, from the pure degree law
      have hRdeg := (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1
      have hsd : dvSideDeg F g u ℓ hne = G.natDegree + Gs'.prod.natDegree := by
        rw [← hRdeg, hR, List.prod_cons, hGmon.natDegree_mul hPmon]
      have hdiv := natDegree_div_eq_of_isDvPure hℓ hcop hgpure hne
      have hgpos : 0 < g.natDegree := by
        have h1 := Nat.mul_div_cancel' hgd
        rw [hdiv, hsd] at h1
        have h2 : 0 < (F.e₁ * F.f₁) * (ℓ * (G.natDegree + Gs'.prod.natDegree)) :=
          Nat.mul_pos hDpos (Nat.mul_pos hℓ (by omega))
        omega
      -- THEOREM A (the landed Lean-core engine root), at `G` vs the tail product
      obtain ⟨g₁, g₂, hsplit, hg₁mon, hg₂mon, hdeg₁, hdeg₂, hpure₁, hpure₂, hhgt₁, hhgt₂,
          hres₁, hres₂⟩ :=
        C133mh9.theoremA π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g hg hgpos hgd hgpure hne M₀ hp
          G Gs'.prod hGmon hPmon hGP hG0 hP0 (by rw [hR, List.prod_cons])
      -- recurse on the co-block `g₂`
      have hgd₂ : (F.e₁ * F.f₁) ∣ g₂.natDegree := ⟨ℓ * Gs'.prod.natDegree, by rw [hdeg₂]; ring⟩
      have hne₂ : (dvSideSet F g₂ u ℓ).Nonempty := dvSideSet_nonempty F hg₂mon.ne_zero u hℓ
      obtain ⟨M₂, hp₂⟩ := exists_pin F hne₂
      obtain ⟨gs', hprod', hpkg'⟩ := ih hmon' hpos' hpair' hg₂mon hgd₂ hpure₂
        ⟨hne₂, M₂, hp₂, hres₂ hne₂ M₂ hp₂⟩
      exact ⟨g₁ :: gs', by rw [List.prod_cons, ← hprod']; exact hsplit,
        List.Forall₂.cons ⟨hg₁mon, hpure₁, hdeg₁, hres₁⟩ hpkg'⟩

/-! ## §5 — the schema layer: face-realizing blocks (A0G-HE0 × IFCG5, and the HE1 typing) -/

/-- A single-entry face is valid whenever its three components are positive. -/
theorem validFace_singleton {b D μ : ℕ} (hb : 1 ≤ b) (hD : 1 ≤ D) (hμ : 1 ≤ μ) :
    ValidFace (b, (⟨{(D, μ)}⟩ : FactorizationType)) := by
  refine ⟨hb, ?_, ?_⟩
  · show 1 ≤ faceResDeg (b, (⟨{(D, μ)}⟩ : FactorizationType))
    have h : faceResDeg (b, (⟨{(D, μ)}⟩ : FactorizationType)) = D * μ := by
      simp [faceResDeg, FactorizationType.degree]
    rw [h]
    exact Nat.mul_pos hD hμ
  · intro p hp
    have hpe : p = (D, μ) := by simpa using hp
    subst hpe
    exact ⟨hD, hμ⟩

/-- **The pure-block realization bridge**: a monic-free purity certificate plus the exact
degree law `deg g / D′ = ℓ·(pattern degree)` realizes the face `(ℓ, σ)` in IFCG5's sense —
`dvSideLen = faceLen` computed from `dvSideMin = 0` / `dvSideMax = deg/D′` (C.35). -/
theorem realizesFaceAt_of_pure {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}
    (hu : 1 ≤ u) {σ : FactorizationType} (hcopf : Nat.Coprime u ℓ)
    (hpure : IsDvPure F g u ℓ)
    (hdeg : g.natDegree / (F.e₁ * F.f₁) = ℓ * σ.degree) :
    RealizesFaceAt F g u (ℓ, σ) := by
  refine ⟨hu, hcopf, hpure, ?_⟩
  unfold dvSideLen
  rw [dvSideMax_eq_of_isDvPure hpure _, dvSideMin_eq_zero_of_isDvPure hpure _,
    Nat.sub_zero, hdeg]
  rfl

set_option maxHeartbeats 1600000 in
/-- ★★ **The schema split** (nodes A0G-HE0 + A0G-HE1's realization clause): every coprime
residual split IN A SCHEMA produces the declared pure factor blocks.  The residual of the
monic dv-pure `g` factors as `∏ rᵢ^{μᵢ}` along a list of pattern entries
`(Dᵢ, μᵢ)` with pairwise-DISTINCT monic irreducibles `rᵢ` of degree `Dᵢ` (pairwise
coprimality of the powers is DERIVED, not assumed).  Then `g = ∏ gᵢ` with each `gᵢ`:

* monic and `(u, ℓ)`-dv-pure,
* of EXACT degree `D′·(ℓ·(Dᵢ·μᵢ))` — the declared face-entry mass,
* of EXACT residual `rᵢ^{μᵢ}` at every pin (the entry's label data, multiplicity exactly
  `μᵢ`), and
* REALIZING the singleton sub-face `(ℓ, {(Dᵢ, μᵢ)})` in IFCG5's `RealizesFaceAt` sense —
  the residual-factorization binding IFCG5's scoping note deferred to this node.

Lean-core (no cite: the engine root `C133mh9.theoremA` is Lean-core). -/
theorem schema_split
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (ers : List ((ℕ × ℕ) × Polynomial (F.stageField H₀ hpin)))
    (hval : ∀ x ∈ ers, x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
      1 ≤ x.1.1 ∧ 1 ≤ x.1.2)
    (hdist : ers.Pairwise (fun x y => x.2 ≠ y.2))
    {g : Polynomial O} (hg : g.Monic) (hgd : (F.e₁ * F.f₁) ∣ g.natDegree)
    (hgpure : IsDvPure F g u ℓ)
    (hres : ∃ (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g u ℓ hne M₀ hp = (ers.map (fun x => x.2 ^ x.1.2)).prod) :
    ∃ gs : List (Polynomial O), g = gs.prod ∧
      List.Forall₂ (fun x g₁ => g₁.Monic ∧ IsDvPure F g₁ u ℓ ∧
        g₁.natDegree = (F.e₁ * F.f₁) * (ℓ * (x.1.1 * x.1.2)) ∧
        (∀ (hne₁ : (dvSideSet F g₁ u ℓ).Nonempty) (M₁ : ℕ)
          (hp₁ : dvHgt F g₁ (dvSideMin F g₁ u ℓ hne₁) = (M₁ : ℕ∞)),
          dvResPoly F H₀ hpin g₁ u ℓ hne₁ M₁ hp₁ = x.2 ^ x.1.2) ∧
        ValidFace (ℓ, (⟨{x.1}⟩ : FactorizationType)) ∧
        RealizesFaceAt F g₁ u (ℓ, (⟨{x.1}⟩ : FactorizationType))) ers gs := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hu : 1 ≤ u := lt_of_le_of_lt (Nat.zero_le _) hfloor
  -- feed `dv_multi_split` at the power list
  have hmon : ∀ G ∈ ers.map (fun x => x.2 ^ x.1.2), G.Monic := by
    intro G hG
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hG
    exact (hval x hx).1.pow _
  have hpos : ∀ G ∈ ers.map (fun x => x.2 ^ x.1.2), 0 < G.natDegree := by
    intro G hG
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hG
    obtain ⟨hxm, -, hxd, hx1, hx2⟩ := hval x hx
    rw [hxm.natDegree_pow, hxd]
    exact Nat.mul_pos hx2 hx1
  have hpair : (ers.map (fun x => x.2 ^ x.1.2)).Pairwise IsCoprime := by
    rw [List.pairwise_map]
    refine hdist.imp_of_mem ?_
    intro x y hx hy hne
    obtain ⟨hxm, hxi, -, -, -⟩ := hval x hx
    obtain ⟨hym, hyi, -, -, -⟩ := hval y hy
    exact pow_isCoprime_of_ne hxm hym hxi hyi hne _ _
  obtain ⟨gs, hprod, hpkg⟩ := dv_multi_split hπ hh H₀ hpin hℓ hcop hfloor
    (ers.map (fun x => x.2 ^ x.1.2)) hmon hpos hpair hg hgd hgpure hres
  refine ⟨gs, hprod, forall₂_imp_of_mem (List.forall₂_map_left_iff.1 hpkg) ?_⟩
  intro x g₁ hx hR4
  obtain ⟨hxm, hxi, hxd, hx1, hx2⟩ := hval x hx
  obtain ⟨hg₁m, hg₁p, hg₁d, hg₁r⟩ := hR4
  have hdeg2 : g₁.natDegree = (F.e₁ * F.f₁) * (ℓ * (x.1.1 * x.1.2)) := by
    rw [hg₁d, hxm.natDegree_pow, hxd]
    ring
  refine ⟨hg₁m, hg₁p, hdeg2, hg₁r, validFace_singleton hℓ hx1 hx2, ?_⟩
  refine realizesFaceAt_of_pure hu hcop hg₁p ?_
  have hσ : ((⟨{x.1}⟩ : FactorizationType)).degree = x.1.1 * x.1.2 := by
    simp [FactorizationType.degree]
  rw [hσ, hdeg2, Nat.mul_div_cancel_left _ hDpos]

/-! ### The engine-side entry datum (the `genreDatumOfChildEntry` twin) and the HE1 typing -/

/-- **The engine-side twin of IFCG5's `genreDatumOfChildEntry`**: a pattern entry's residual
data packaged as a C.09 `LevelDatum`.  Following IFCG5's D4, the numerator `u` and the
stage-field irreducible `r` — the data the skeleton deliberately does not store — enter as
explicit arguments. -/
def levelDatumOfEntry (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (r : Polynomial (F.stageField H₀ hpin)) (hrmonic : r.Monic) (hrirr : Irreducible r)
    (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree) : LevelDatum F H₀ hpin where
  u := u
  ℓ := ℓ
  r := r
  hℓ := hℓ
  hcop := hcop
  hκ := by rw [mul_assoc]; exact hfloor
  hrmonic := hrmonic
  hrirr := hrirr
  hr0 := hr0
  hrdeg := hrdeg

@[simp] theorem levelDatumOfEntry_u (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (r : Polynomial (F.stageField H₀ hpin)) (hrmonic : r.Monic) (hrirr : Irreducible r)
    (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree) :
    (levelDatumOfEntry F H₀ hpin hℓ hcop hfloor r hrmonic hrirr hr0 hrdeg).u = u := rfl

@[simp] theorem levelDatumOfEntry_ℓ (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (r : Polynomial (F.stageField H₀ hpin)) (hrmonic : r.Monic) (hrirr : Irreducible r)
    (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree) :
    (levelDatumOfEntry F H₀ hpin hℓ hcop hfloor r hrmonic hrirr hr0 hrdeg).ℓ = ℓ := rfl

@[simp] theorem levelDatumOfEntry_r (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (r : Polynomial (F.stageField H₀ hpin)) (hrmonic : r.Monic) (hrirr : Irreducible r)
    (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree) :
    (levelDatumOfEntry F H₀ hpin hℓ hcop hfloor r hrmonic hrirr hr0 hrdeg).r = r := rfl

/-- The entry datum's level-2 key degree is the declared `D″ = D′·ℓ·D` — the stage's
`(e, f) = (ℓ, deg r)` in one numeral. -/
theorem levelDatumOfEntry_keyDeg₂ (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (r : Polynomial (F.stageField H₀ hpin)) (hrmonic : r.Monic) (hrirr : Irreducible r)
    (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree) :
    (levelDatumOfEntry F H₀ hpin hℓ hcop hfloor r hrmonic hrirr hr0 hrdeg).keyDeg₂
      = (F.e₁ * F.f₁) * ℓ * r.natDegree := rfl

/-- **The type certification (A0G-HE1's gate, existence half)**: a `schema_split` block whose
entry carries the `LevelDatum` `L` is `HasLabel L` — it IS the `(λ = u/ℓ, r)`-labelled block,
with `HasLabel`'s multiplicity exactly the entry's `μ`. -/
theorem hasLabel_of_block {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {g₁ : Polynomial O} {μ : ℕ} (hμ : 0 < μ)
    (hg₁ : g₁.Monic) (hg₁pos : 0 < g₁.natDegree) (hpure : IsDvPure F g₁ L.u L.ℓ)
    (hres : ∀ (hne₁ : (dvSideSet F g₁ L.u L.ℓ).Nonempty) (M₁ : ℕ)
      (hp₁ : dvHgt F g₁ (dvSideMin F g₁ L.u L.ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin g₁ L.u L.ℓ hne₁ M₁ hp₁ = L.r ^ μ) :
    HasLabel L g₁ := by
  have hne₁ : (dvSideSet F g₁ L.u L.ℓ).Nonempty :=
    dvSideSet_nonempty F hg₁.ne_zero L.u L.hℓ
  obtain ⟨M₁, hp₁⟩ := exists_pin F hne₁
  exact ⟨hg₁, hg₁pos, hpure, hne₁, M₁, hp₁, μ, hμ, hres hne₁ M₁ hp₁⟩

/-- **The type certification, degree half**: the block's degree is EXACTLY
`keyDeg₂ · μ` — the stage block `(e, f) = (ℓ, deg r)` occurs with multiplicity exactly the
pattern entry's `μ`, not merely a total-degree count. -/
theorem block_natDegree_keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    {g₁ : Polynomial O} {μ : ℕ}
    (hdeg : g₁.natDegree = L.ℓ * (F.e₁ * F.f₁) * (L.r ^ μ).natDegree) :
    g₁.natDegree = L.keyDeg₂ * μ := by
  rw [hdeg, L.hrmonic.natDegree_pow, LevelDatum.keyDeg₂]
  ring

/-! ## §6 — uniqueness at the face, and the ambient bindings (the two cite carriers) -/

/-- **Uniqueness of the labelled/complement split at a realized face**
(`C133mh11.dv_oneSlope_split_unique` bound to IFCG5's surface): a `RealizesFaceAt` witness
supplies the purity hypothesis, so two labelled splits of a face-realizing polynomial agree.
Together with `schema_split`, the produced blocks are THE declared blocks.  Lean-core. -/
theorem face_split_unique {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {σ : FactorizationType} {g a b a' b' : Polynomial O}
    (hface : RealizesFaceAt F g L.u (L.ℓ, σ))
    (hgd : (F.e₁ * F.f₁) ∣ g.natDegree)
    (hab : g = a * b) (hab' : g = a' * b')
    (ha : a.Monic) (hb : b.Monic) (ha' : a'.Monic) (hb' : b'.Monic)
    (hapure : IsDvPure F a L.u L.ℓ) (ha'pure : IsDvPure F a' L.u L.ℓ)
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hares : ∃ (hne : (dvSideSet F a L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F a (dvSideMin F a L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin a L.u L.ℓ hne M₀ hp = L.r ^ m)
    (ha'res : ∃ (hne : (dvSideSet F a' L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F a' (dvSideMin F a' L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin a' L.u L.ℓ hne M₀ hp = L.r ^ m')
    (hbres : ∀ (hne : (dvSideSet F b L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F b (dvSideMin F b L.u L.ℓ hne) = (M₀ : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b L.u L.ℓ hne M₀ hp)
    (hb'res : ∀ (hne : (dvSideSet F b' L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F b' (dvSideMin F b' L.u L.ℓ hne) = (M₀ : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin b' L.u L.ℓ hne M₀ hp) :
    a' = a ∧ b' = b := by
  obtain ⟨-, -, hgpure, -⟩ := hface
  exact C133mh11.dv_oneSlope_split_unique L hπ hh hgpure hgd hab hab' ha hb ha' hb'
    hapure ha'pure hm hm' hares ha'res hbres hb'res

set_option maxHeartbeats 1600000 in
/-- ★ **The ambient block realizes its face** (A0G-HE1's placement clause; CITE CARRIER):
under the signed `BlockContext`, C.35's selector `blockFactor L f` realizes the single-entry
face `(L.ℓ, {(deg L.r, mult₂ L f)})` — the engine's ambient output IS a valid skeleton-face
occupant, with the label, the divisibility, and the positive multiplicity attached.
Footprint: Lean core + the allowlisted C.33 dissection cite
(`Uniformity.Density.Tower.exists_dvDissection`), inherited through
`C133mh15.blockFrontier_of_context`. -/
theorem blockFactor_realizes_face {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    RealizesFaceAt F (blockFactor L f) L.u
        (L.ℓ, (⟨{(L.r.natDegree, mult₂ L f)}⟩ : FactorizationType)) ∧
      ValidFace (L.ℓ, (⟨{(L.r.natDegree, mult₂ L f)}⟩ : FactorizationType)) ∧
      HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧ 0 < mult₂ L f := by
  have hfr := C133mh15.blockFrontier_of_context L hπ hh hctx
  obtain ⟨hlab, hdvd, hdeg, hpos⟩ := blockFactor_spec_of_frontier L hπ hfr
  have hu : 0 < L.u := lt_of_le_of_lt (Nat.zero_le _) L.hκ
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hpure : IsDvPure F (blockFactor L f) L.u L.ℓ := hlab.2.2.1
  refine ⟨?_, validFace_singleton L.hℓ L.hrdeg hpos, hlab, hdvd, hpos⟩
  refine realizesFaceAt_of_pure hu L.hcop hpure ?_
  have hσ : ((⟨{(L.r.natDegree, mult₂ L f)}⟩ : FactorizationType)).degree
      = L.r.natDegree * mult₂ L f := by
    simp [FactorizationType.degree]
  rw [hσ, hdeg, LevelDatum.keyDeg₂,
    show (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree * mult₂ L f
      = (F.e₁ * F.f₁) * (L.ℓ * (L.r.natDegree * mult₂ L f)) from by ring,
    Nat.mul_div_cancel_left _ hDpos]

set_option maxHeartbeats 1600000 in
/-- ★ **The ambient context split, face-bound** (CITE CARRIER): C134csx's full internal
split `f = blockFactor L f · g₂ · Wf` re-exported with the face-realization clause attached —
the declared block realizes its face, the complement's residual avoids `L.r` at every pin,
and the junk factor is point-sided.  Footprint: Lean core + the C.33 dissection cite. -/
theorem context_split_face {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hπ : Irreducible π) (hh : 0 < F.h)
    {f : Polynomial O} (hctx : BlockContext L f) :
    ∃ g₂ Wf : Polynomial O,
      f = blockFactor L f * g₂ * Wf ∧ g₂.Monic ∧ Wf.Monic ∧
      (∀ hneW : (dvSideSet F Wf L.u L.ℓ).Nonempty, dvSideDeg F Wf L.u L.ℓ hneW = 0) ∧
      (∀ (hne₂ : (dvSideSet F g₂ L.u L.ℓ).Nonempty) (M₂ : ℕ)
        (hp₂ : dvHgt F g₂ (dvSideMin F g₂ L.u L.ℓ hne₂) = (M₂ : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g₂ L.u L.ℓ hne₂ M₂ hp₂) ∧
      RealizesFaceAt F (blockFactor L f) L.u
        (L.ℓ, (⟨{(L.r.natDegree, mult₂ L f)}⟩ : FactorizationType)) := by
  obtain ⟨g₂, Wf, hsplit, hg₂, hWf, hWpt, hg₂res⟩ := C134csx.context_split L hπ hh hctx
  exact ⟨g₂, Wf, hsplit, hg₂, hWf, hWpt, hg₂res,
    (blockFactor_realizes_face L hπ hh hctx).1⟩

end Uniformity.Density.IFCG6

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only,
EXCEPT the two ambient bindings `blockFactor_realizes_face` and `context_split_face`, which
additionally inherit exactly the allowlisted C.33 dissection cite
`Uniformity.Density.Tower.exists_dvDissection`. -/

-- Node A0G-CH (all Lean-core; field/citation-free arithmetic)
#print axioms Uniformity.Density.IFCG6.entry_snd_lt_mass_of_fractional
#print axioms Uniformity.Density.IFCG6.faceResDeg_le_mass_div_den
#print axioms Uniformity.Density.IFCG6.entry_snd_le_mass_div_den
#print axioms Uniformity.Density.IFCG6.decrease_chain_of_fractional
#print axioms Uniformity.Density.IFCG6.entry_snd_lt_mass_of_key
#print axioms Uniformity.Density.IFCG6.childEntry_lt_mass_of_key
#print axioms Uniformity.Density.IFCG6.loopFace_not_key
#print axioms Uniformity.Density.IFCG6.genreDatumOfChildEntry_μ_lt_mass
#print axioms Uniformity.Density.IFCG6.childSizes_sum_le_mass

-- Node A0G-HE, per-face core (all Lean-core)
#print axioms Uniformity.Density.IFCG6.dv_multi_split
#print axioms Uniformity.Density.IFCG6.validFace_singleton
#print axioms Uniformity.Density.IFCG6.realizesFaceAt_of_pure
#print axioms Uniformity.Density.IFCG6.schema_split
#print axioms Uniformity.Density.IFCG6.levelDatumOfEntry
#print axioms Uniformity.Density.IFCG6.levelDatumOfEntry_keyDeg₂
#print axioms Uniformity.Density.IFCG6.hasLabel_of_block
#print axioms Uniformity.Density.IFCG6.block_natDegree_keyDeg₂
#print axioms Uniformity.Density.IFCG6.face_split_unique

-- Node A0G-HE, ambient bindings (Lean core + the C.33 dissection cite ONLY)
#print axioms Uniformity.Density.IFCG6.blockFactor_realizes_face
#print axioms Uniformity.Density.IFCG6.context_split_face
