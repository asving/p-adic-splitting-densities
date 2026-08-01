/-
HDISCHARGE_H3 §1.4 — unit ADM-U1 (wave 0): the (ADM) per-class carrier layer.
Defs `classCount` / `maxClassWeight` transcribed VERBATIM from the blueprint
(compile-probed there), plus the two non-vacuity lemmas assigned to this unit
by ADM-U2's duties (v1)/(v2): `classFilter_nonempty_of_mem_onLineSlots` and
`d_pos`, and mod-period simp lemmas.  Consumers: ADM-U2
(`admFull_iff_maxClassWeight`), ADM-U3, ADM-U4.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.CensusCore

/-!
# (ADM) per-class carrier defs [HDISCHARGE_H3 unit ADM-U1]

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §1.4 (ADM-U1: the two defs
  verbatim; the two non-vacuity lemmas named in ADM-U2's duties (v1)/(v2),
  Codex pass-1 finding 11, landed here so U2's proof consumes them).
* Math source of record: O-9 rev5 §2 (the class ledger; (CLASS-d)) — see
  HDISCHARGE_H3 §1.3.  NOTE (F-ADM-2): (CLASS-d) itself is NOT a carrier
  theorem at r ≥ 2; nothing here claims it.
* Carrier: `LeanUrat.Scaffold.CensusData` (BP_IV §1.2, `CensusCore.lean`).
-/

namespace LeanUrat.Scaffold.HD3

/-- unit ADM-U1 (blueprint-verbatim) — the per-class ledger count: the number
    of φ-monomial slots `j ∈ J` whose weight lies in the residue class
    `c (mod e)` (O-9 §2's `#{𝐣 : wt(𝐣) ≡ c}`; (CLASS-d) asserts this `= d`,
    supplied as a HYPOTHESIS at general order per F-ADM-2). -/
noncomputable def classCount (D : CensusData) (c : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : D.J => D.wt j % D.period = c % D.period)).card

/-- unit ADM-U1 (blueprint-verbatim) — the maximum ledger weight in the
    residue class of `β (mod e)` (O-9 §2's `max{wt(𝐣) : wt(𝐣) ≡ β}`; a
    genuine max whenever the class is nonempty — see
    `classFilter_nonempty_of_mem_onLineSlots`). -/
noncomputable def maxClassWeight (D : CensusData) (β : ℕ) : ℕ :=
  ((Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = β % D.period)) : Finset D.J).sup D.wt

/-- `classCount` depends on `c` only through `c % period`. -/
@[simp] theorem classCount_mod_period (D : CensusData) (c : ℕ) :
    classCount D (c % D.period) = classCount D c := by
  have h : c % D.period % D.period = c % D.period := Nat.mod_mod_of_dvd c dvd_rfl
  simp only [classCount, h]

/-- `maxClassWeight` depends on `β` only through `β % period`. -/
@[simp] theorem maxClassWeight_mod_period (D : CensusData) (β : ℕ) :
    maxClassWeight D (β % D.period) = maxClassWeight D β := by
  have h : β % D.period % D.period = β % D.period := Nat.mod_mod_of_dvd β dvd_rfl
  simp only [maxClassWeight, h]

/-- Any slot in the class of `β` weighs at most `maxClassWeight D β`
    (the `Finset.sup` upper-bound law, packaged for ADM-U2). -/
theorem wt_le_maxClassWeight (D : CensusData) {β : ℕ} {j : D.J}
    (hj : D.wt j % D.period = β % D.period) :
    D.wt j ≤ maxClassWeight D β :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- ADM-U2 non-vacuity duty (v1) — for `β ∈ onLineSlots` the filtered class
    is NONEMPTY: `β = wt 𝐣` for some `𝐣` (the def of `onLineSlots`), and `𝐣`
    lies in its own class.  So `maxClassWeight`'s `Finset.sup` is a genuine
    max, never the empty-sup default `0`. -/
theorem classFilter_nonempty_of_mem_onLineSlots (D : CensusData) {β : ℕ}
    (hβ : β ∈ D.onLineSlots) :
    (Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = β % D.period)).Nonempty := by
  simp only [CensusData.onLineSlots, Finset.mem_image] at hβ
  obtain ⟨j, -, hj⟩ := hβ
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by rw [hj]⟩⟩

/-- ADM-U2 non-vacuity duty (v2) — `d ≥ 1` is a carrier fact: `d = ∏ f_i`
    with every `f_i ≥ 1` (the `hf` bounds).  Used where (CLASS-d) as a
    hypothesis forces class nonemptiness at arbitrary `c`. -/
theorem d_pos (D : CensusData) : 0 < D.d :=
  Finset.prod_pos fun i _ => D.hf i

end LeanUrat.Scaffold.HD3
