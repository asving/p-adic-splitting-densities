/-
Unit NPv.npid  (MovesD campaign, ratification repair D5, 2026-07-28)
[Finding D5 ACCEPTED: `D4R4_all` uses the GEOMETRIC threshold `NPband` on the inhabited
branch, while L12's own threshold is "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅,
N(P̂) := 1 if Pref(P̂) = ∅"; the identification NPband = max-η N(η,⊤) was the W4-4 seam
pin NP-ID, a ledger comment with no Lean object. THIS unit types it.]
moves_ref: L12 (quoted at D4R4all_wrapper): "N(P̂) is finite, and for EVERY N ≥ N(P̂): …
(D4R.4-SUM) ∧ (D4R.4-EV)". §2.5 W4-4 NP-ID: "every transported-system equation level is a
band level and conversely" — the per-class thresholds' max IS the geometric band
threshold. Here: `NPIDPin n pol P Nthr` is that identity as a typed premise over an
ABSTRACT per-class threshold family `Nthr : PrefIdx → ℕ` (the classifier-side N(η,⊤) is
wave-4/HC-2 vocabulary — the pin is stated over whatever family the tree corpus
supplies); `noteNP` is L12's OWN piecewise threshold over that family; and
`D4R4_all_noteRange` restates D4R4_all with the quantifier on L12's own range,
derived by rewriting the threshold through the pin. W4-4's ledger pin is thereby
DISCHARGED TO A TYPED PREMISE; its proof (at the HC-2 Nthr) remains wave-4.
deps: Defs, D2a (instPrefIdxFinite), D4R4all_wrapper (D4R4_all), NPu (NP_pos).
sketch: Fintype.ofFinite; if_pos/if_neg; proof-irrelevant transport into T.jets.
difficulty: easy.  hypothesis_fields: `hpin : NPIDPin n pol P Nthr` (the typed pin);
`hne`/`T` as on D4R4_all.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D2a_finite
import LeanUrat.MovesD.NPu_threshold
import LeanUrat.MovesD.D4R4all_wrapper

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- The max of a per-class threshold family over the (finite — D2a) class index:
L12's `max_{η ∈ Pref(P̂)} N(η,⊤)` shape, over an abstract family. -/
noncomputable def NthrSup (Nthr : PrefIdx n pol P → ℕ) : ℕ :=
  letI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  Finset.univ.sup Nthr

/-- **W4-4 NP-ID, now a Lean object** — the ledger pin discharged to a typed premise:
on the inhabited branch, the GEOMETRIC band threshold `NPband` (what `Shape.NP` and hence
`D4R4_all` consume) IS the max of the per-class thresholds (§2.5 W4-4: "every
transported-system equation level is a band level and conversely"). Stated over an
abstract `Nthr`; the HC-2/wave-4 tree corpus instantiates `Nthr i := N(η_i, ⊤)` and
proves the pin. -/
noncomputable def NPIDPin (n : ℕ) (pol : CanonPolicy p F) (P : Shape n)
    (Nthr : PrefIdx n pol P → ℕ) : Prop :=
  Nonempty (PrefIdx n pol P) → (P : ShapePrefix).NPband n = NthrSup Nthr

open Classical in
/-- **L12's OWN threshold**, verbatim piecewise over the abstract family: "N(P̂) :=
max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if Pref(P̂) = ∅". -/
noncomputable def noteNP (Nthr : PrefIdx n pol P → ℕ) : ℕ :=
  if Nonempty (PrefIdx n pol P) then NthrSup Nthr else 1

/-- Under the pin, the corpus threshold IS L12's own threshold (both branches). -/
theorem NP_eq_noteNP {Nthr : PrefIdx n pol P → ℕ} (hpin : NPIDPin n pol P Nthr) :
    P.NP pol = noteNP Nthr := by
  unfold Shape.NP noteNP
  by_cases hInh : Nonempty (PrefIdx n pol P)
  · rw [if_pos hInh, if_pos hInh, hpin hInh]
  · rw [if_neg hInh, if_neg hInh]

/-- The range transport: L12-range membership gives corpus-range membership. -/
theorem NP_le_of_noteNP_le {Nthr : PrefIdx n pol P → ℕ} (hpin : NPIDPin n pol P Nthr)
    {N : ℕ} (hN : noteNP Nthr ≤ N) : P.NP pol ≤ N := by
  rw [NP_eq_noteNP hpin]; exact hN

/-- The bridge to the guarded form: `noteNP ≤ N` iff the per-class thresholds clear N
whenever any class exists AND N ≥ 1 on the empty branch (L12's N(∅) := 1 convention).
[CHARGE DEVIATION, recorded: the charge displayed the quantifier as the bare guarded form
`Nonempty → sup Nthr ≤ N`, which is strictly WEAKER than L12's range on the EMPTY branch
(at Pref = ∅, N = 0 it holds while L12 demands N ≥ N(∅) = 1, and `Threshold.jets` needs
NP ≤ N with NP = 1 there) — so `D4R4_all_noteRange` quantifies over `noteNP ≤ N`, L12's
own range verbatim; THIS lemma is the exact unfolding of that range. -/
theorem noteNP_le_iff {Nthr : PrefIdx n pol P → ℕ} {N : ℕ} :
    noteNP Nthr ≤ N ↔ (Nonempty (PrefIdx n pol P) → NthrSup Nthr ≤ N) ∧
      (IsEmpty (PrefIdx n pol P) → 1 ≤ N) := by
  classical
  unfold noteNP
  by_cases hInh : Nonempty (PrefIdx n pol P)
  · rw [if_pos hInh]
    exact ⟨fun h => ⟨fun _ => h, fun he => absurd hInh (not_nonempty_iff.mpr he)⟩,
           fun h => h.1 hInh⟩
  · rw [if_neg hInh]
    exact ⟨fun h => ⟨fun hc => absurd hc hInh, fun _ => h⟩,
           fun h => h.2 (not_nonempty_iff.mp hInh)⟩

/-- **D4R4 on L12's own range** (the finding-D5 repair): the SUM equality ∧ the EV bound
for EVERY N ≥ N(P̂) with N(P̂) the note's OWN piecewise threshold `noteNP` — derived from
`D4R4_all` by rewriting the threshold through the typed pin `NPIDPin`. The quantifier
range is now EXACTLY L12's display (D4R4all_wrapper's moves_ref), not the geometric
substitute. -/
theorem D4R4_all_noteRange (hne : (P : ShapePrefix).reads ≠ [])
    (T : Threshold p F n pol P) (Nthr : PrefIdx n pol P → ℕ)
    (hpin : NPIDPin n pol P Nthr) :
    ∀ (N : ℕ) (hNP : noteNP Nthr ≤ N),
      ((∑ᶠ i : PrefIdx n pol P,
          Nat.card ↥((T.jets N (NP_le_of_noteNP_le hpin hNP)).fiber i))
          * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N)) ∧
      (Nat.card ↥(T.jets N (NP_le_of_noteNP_le hpin hNP)).event
          * p ^ ((P : ShapePrefix).A' n) ≤ P.CD pol * p ^ (n * N)) := by
  intro N hNP
  exact D4R4_all hne T N (NP_le_of_noteNP_le hpin hNP)

end LeanUrat.MovesD
