/-
Kernels/D4R0K/L1 — BP4-c6 E-phase skeletons for units KB4, KB5 (pre-approved
split KB5a/KB5b), KB6, KB7, KB8a, KB8b, KB9
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.B "D4R.0-K(a) — the L1
tower-totality induction" + §4 KB; adjudications per
BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block: Q2 ADJUDICATED — prove over the
TRANSCRIBED ENUM MODEL, the seam to HC-1's (S6b) vocabulary is the separate ⚑
unit KB11, sibling cluster).

PLACEMENT (recorded resolution R0): the blueprint's §2.3 assigns `wt`, `offP`,
`digRead` to Tower.lean; Tower.lean's own FILE-SCOPE NOTE (BP4-c2) delegates
them to this file ("the sibling cluster should place them in
Kernels/D4R0K/L1.lean (importing this file)").  This file therefore carries
the model's realizer carrier + `wt`/`digRead`/`offP` defs AND the BP4-c6 unit
theorems; Tower.lean is NOT modified.

THE TRANSCRIBED MODEL AT GENERAL STAGE (verification/l1_boundary_enum.py,
generalized from its stage-2/stage-3 instances exactly along the script's own
MODEL paragraph).  Levels are indexed bottom-up: a LEVEL-0 realizer is a base
scalar (script: an integer coefficient of Z[x], weight v_p); a LEVEL-(r+1)
realizer is its tuple of Φ-adic digits at the e·g positions of the coefficient
space governed by stage data S r (script stage 2: C = {t ∈ Z[x] : deg t < eg}
with position j the x^j slot; script stage 3: position j the Φ₂^j slot with
digit B_j, deg B_j < deg Φ₂).  Weight: w(t) = min over positions j of
(e·w(t_j) + j·h), w_base = v_p (script `read2`/`read3` vals).  The digit read
is the script's INDEPENDENT from-scratch reading: minimizing slots, forced
class j₀ = (least minimizing slot) mod e, k-th residual digit read
recursively at position j₀ + e·k.

RECORDED RESOLUTIONS (statement transcription against the blueprint):
R1 (tuple carrier / degree invariant): per Q2 the tuple model is the default;
   `RealCarrier` stores ONLY the digit tuple, so the per-digit degree bound
   "< deg Φ_prev" of KB8a's invariant is carried by the carrier TYPING, and
   the transcribable residue of the invariant is the SUPPORT LAW (digits
   occupy only the designated slots — `offP_support`/`slotAssemble_support`)
   plus the positional read (REV 2 F1: k ↦ j₀+ek injective, all slots in the
   single class j₀ mod e; positions never mix under componentwise addition —
   in this carrier the no-mixing clause is definitional, which is exactly
   what the tuple transcription buys; the raw-Z[x] realization through the
   Ore lifts Φ is KB11-seam business).
R2 (weight codomain): `wt` is ℕ∞-valued and TOTAL — wt(zero) = ⊤ replaces the
   script's Partial-on-zero; "exact weight W" = `wt t = (W : ℕ∞)`; the min
   over positions is `Finset.inf` (zero digits contribute ⊤).
R3 (KB4's "at exact-weight t_k"): in the model `wt` IS the weight, so the
   slot-summand law is stated unconditionally in ℕ∞ (the exact-weight
   hypothesis of the note is absorbed by R2's junk-free totalization).
R4 (m = 0 convention): the script's CONVENTION paragraph fixes the slot-j₀
   monomial generator, absorbing the note's forced offset z^m (m = 0); the
   class map τ ↦ P is then the IDENTITY on digit tuples, so KB6's residue is
   representative uniqueness + z̄-invertibility + anchored nonvanishing over
   the KB1b `ExtCarrier` layer (the "bijectivity onto F′^×" clause is the
   identity's bijectivity — nothing to state beyond the anchored membership).
R5 (zero-class digits): the script SKIPS zero digits P_k = 0; here `offP`
   maps the zero class to the zero realizer (`offP_zero_class`), same result.
R6 (base stage): no threshold at the base (script: "digits are F_Q-unit
   lifts with no threshold") — `Eligible S 0 W = True`, KB7 quantifies over
   EVERY W including 0.
R7 (stream form): the tower enters as a stage STREAM `S : ℕ → StageData`
   with the (I-aug) chain `∀ i, IAug (S i) (S (i+1))` as hypothesis; only the
   prefix below the working level is consumed, and every finite `TowerData`
   extends to such a stream (append stages with h large), so no generality
   is lost against Tower.lean's finite records.
R8 (KB5b's τ ≠ 0): stated in the directly-consumable existential form
   `∃ k, τ k ≠ resZero` (equivalent to function inequality via funext).
R9 (computability): `offP` is a COMPUTABLE def (determinism witnessed at the
   compiler level); `wt`/`digRead` and their helpers are `noncomputable` ONLY
   because ℕ∞'s lattice instances are (instCompleteLinearOrderENat) — no
   choice enters their logic; KB9's spot rows therefore close by
   simp-unfolding + norm_num rather than bare `decide`.

E-phase discipline: all defs compile sorry-free; unit theorems have sorry
bodies except pure assemblies (l1_totality/l1_coverage/toPoly_injective/
offP_calls_eligible/offP_deterministic), whose bodies are the blueprint's own
assembly and compile against sorried deps.
Build: cd lean && lake build LeanUrat.Kernels.D4R0K.L1
-/
import LeanUrat.Kernels.D4R0K.Tower

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels.D4R0K

open Polynomial

/-! ## The model carriers (KB4/KB8a preamble — the `wt`/`digRead`/`offP`
vocabulary delegated to this file by Tower.lean's file-scope note) -/

/-- The realizer carrier of the transcribed enum model (resolution R1): a
level-0 realizer is a base scalar (ℤ — the script's integer coefficient); a
level-(r+1) realizer is its tuple of Φ-adic digits at the e·g coefficient-space
positions of stage data `S r`.  Per-digit degree bounds are carried by the
typing (R1). -/
def RealCarrier (S : ℕ → StageData) : ℕ → Type
  | 0 => ℤ
  | r + 1 => Fin ((S r).e * (S r).g) → RealCarrier S r

/-- The zero realizer at every level (all digits zero). -/
def realZero (S : ℕ → StageData) : ∀ r, RealCarrier S r
  | 0 => (0 : ℤ)
  | r + 1 => fun _ => realZero S r

/-- The residue-class carrier of the transcribed model (tuple presentation,
per Q2): F₀ = F_p; F_{r+1} = length-g_r tuples over F_r (the deg < g
representative's coefficients — script `Ext` elements, low → high).  The
multiplicative structure lives on the KB1b `ExtCarrier` layer (KB6); the
model statements need only the carrier, its zero, and equality. -/
def ResCarrier (p : ℕ) (S : ℕ → StageData) : ℕ → Type
  | 0 => ZMod p
  | r + 1 => Fin ((S r).g) → ResCarrier p S r

/-- The zero class at every level. -/
def resZero (p : ℕ) (S : ℕ → StageData) : ∀ r, ResCarrier p S r
  | 0 => (0 : ZMod p)
  | r + 1 => fun _ => resZero p S r

/-- Base weight: v_p on nonzero integers, ⊤ at 0 (resolution R2 — the
script's Partial-on-zero junk-totalized). -/
def wtBase (p : ℕ) (c : ℤ) : ℕ∞ :=
  if c = 0 then ⊤ else ((padicValInt p c : ℕ) : ℕ∞)

/-- The model weight `wt` (KB4 vocabulary; script `read2`/`read3` vals):
level 0 is `wtBase` (= v_p); at level r+1,
`wt t = min over positions j of (e·wt(t_j) + j·h)` with (e, h) = stage data
`S r` — the parent-scale development weight, ℕ∞-valued and total (R2). -/
noncomputable def wt (p : ℕ) (S : ℕ → StageData) : ∀ r, RealCarrier S r → ℕ∞
  | 0, c => wtBase p c
  | r + 1, t =>
    Finset.univ.inf fun j : Fin ((S r).e * (S r).g) =>
      ((S r).e : ℕ∞) * wt p S r (t j) + (((j : ℕ) * (S r).h : ℕ) : ℕ∞)

/-- The per-position weight contribution e·wt(t_j) + j·h (the `vals` map of
the script's independent reader, l1_boundary_enum.py:223). -/
noncomputable def slotWt (p : ℕ) (S : ℕ → StageData) (r : ℕ) (t : RealCarrier S (r + 1))
    (j : Fin ((S r).e * (S r).g)) : ℕ∞ :=
  ((S r).e : ℕ∞) * wt p S r (t j) + (((j : ℕ) * (S r).h : ℕ) : ℕ∞)

/-- Definitional tie: the level-(r+1) weight is the position-wise inf of
`slotWt`. -/
theorem wt_succ (p : ℕ) (S : ℕ → StageData) (r : ℕ) (t : RealCarrier S (r + 1)) :
    wt p S (r + 1) t = Finset.univ.inf (slotWt p S r t) := rfl

/-- The minimizing-slot set of the independent reader (script `mins`,
l1_boundary_enum.py:225): positions whose contribution attains the weight. -/
noncomputable def minSlots (p : ℕ) (S : ℕ → StageData) (r : ℕ) (t : RealCarrier S (r + 1)) :
    Finset (Fin ((S r).e * (S r).g)) :=
  Finset.univ.filter fun j => slotWt p S r t j = wt p S (r + 1) t

/-- The reader's forced slot class: (least minimizing slot) mod e (script
`j0 = mins[0] % e`, l1_boundary_enum.py:226; junk 0 when no slot minimizes,
i.e. at the zero realizer). -/
noncomputable def j0read (p : ℕ) (S : ℕ → StageData) (r : ℕ) (t : RealCarrier S (r + 1)) : ℕ :=
  if h : (minSlots p S r t).Nonempty then
    (((minSlots p S r t).min' h : Fin ((S r).e * (S r).g)) : ℕ) % (S r).e
  else 0

/-- Base digit read: the unit-part residue res(c / p^{v_p c}) (script
`(slots[j] // p ** ...) % p`, l1_boundary_enum.py:234; junk 0 at c = 0). -/
def digBase (p : ℕ) (c : ℤ) : ZMod p :=
  ((c / (p : ℤ) ^ padicValInt p c : ℤ) : ZMod p)

/-- The model digit read `digRead` — the script's INDEPENDENT from-scratch
reading (`read2`/`read3`): at level r+1 the k-th residual digit is the
recursive read of the digit at position j₀read + e·k when that position is a
minimizing slot, and 0 otherwise (script: `R` initialized to zeros, written
only at `mins`).  Level 0 reads the unit-part residue. -/
noncomputable def digRead (p : ℕ) (S : ℕ → StageData) : ∀ r, RealCarrier S r → ResCarrier p S r
  | 0, c => digBase p c
  | r + 1, t => fun k : Fin ((S r).g) =>
    if hj : j0read p S r t + (S r).e * (k : ℕ) < (S r).e * (S r).g then
      if (⟨j0read p S r t + (S r).e * (k : ℕ), hj⟩ : Fin ((S r).e * (S r).g)) ∈
          minSlots p S r t then
        digRead p S r (t ⟨j0read p S r t + (S r).e * (k : ℕ), hj⟩)
      else resZero p S r
    else resZero p S r

/-! ## KB4 — weight of a slot summand (the parent-scale weight law) -/

/-- The slot summand t_k·Φ^j of the development, in the tuple carrier: the
realizer supported at the single position j with digit tk. -/
def slotSummand (S : ℕ → StageData) (r : ℕ) (j : Fin ((S r).e * (S r).g))
    (tk : RealCarrier S r) : RealCarrier S (r + 1) :=
  fun i => if i = j then tk else realZero S r

/-- KB4 (helper). The zero realizer has weight ⊤ at every level (resolution
R2 — this is the law that makes empty positions invisible to the min).
deps: —.  Sketch: induction on r; level 0 is the `if`'s positive branch;
level r+1: every position's digit is `realZero`, so every `slotWt` is
e·⊤ + jh = ⊤ (e ≥ 1 from `e_pos`), and the inf of the constant-⊤ family
is ⊤. -/
theorem wt_realZero (p : ℕ) (S : ℕ → StageData) (r : ℕ) :
    wt p S r (realZero S r) = (⊤ : ℕ∞) := by
  induction r with
  | zero => simp [realZero, wt, wtBase]
  | succ r ih =>
    rw [wt_succ]
    refine le_antisymm le_top (Finset.le_inf fun j _ => ?_)
    have hj : slotWt p S r (realZero S (r + 1)) j = ⊤ := by
      change ((S r).e : ℕ∞) * wt p S r (realZero S r)
          + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) = ⊤
      rw [ih, ENat.mul_top (by exact_mod_cast (S r).e_pos.ne'), top_add]
    rw [hj]

/-- KB4 — weight of a slot summand: w(t_k·Φ^j) = e·w(t_k) + j·h, the
parent-scale weight law of the development (blueprint §4 KB4; the note's
"at exact-weight t_k" hypothesis is absorbed per resolution R3 — in ℕ∞ the
law is unconditional, with both sides ⊤ at t_k = 0).
deps: KB1a-b (Tower.lean records; the model `wt` def above).
Sketch: `wt_succ` + `Finset.inf`: position j contributes e·wt(tk) + j·h;
every other position holds `realZero`, contributing ⊤ (`wt_realZero`,
e ≥ 1); inf against ⊤ is the j-th value (`Finset.inf_eq_iff`/`le_top`
bookkeeping). -/
theorem wt_slotSummand (p : ℕ) (S : ℕ → StageData) (r : ℕ)
    (j : Fin ((S r).e * (S r).g)) (tk : RealCarrier S r) :
    wt p S (r + 1) (slotSummand S r j tk)
      = ((S r).e : ℕ∞) * wt p S r tk + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) := by
  rw [wt_succ]
  have hj : slotWt p S r (slotSummand S r j tk) j
      = ((S r).e : ℕ∞) * wt p S r tk + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) := by
    change ((S r).e : ℕ∞) * wt p S r (slotSummand S r j tk j)
        + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) = _
    rw [show slotSummand S r j tk j = tk from if_pos rfl]
  refine le_antisymm ?_ (Finset.le_inf fun i _ => ?_)
  · rw [← hj]
    exact Finset.inf_le (Finset.mem_univ j)
  · by_cases hij : i = j
    · subst hij
      rw [hj]
    · have hi : slotWt p S r (slotSummand S r j tk) i = ⊤ := by
        change ((S r).e : ℕ∞) * wt p S r (slotSummand S r j tk i)
            + (((i : ℕ) * (S r).h : ℕ) : ℕ∞) = ⊤
        rw [show slotSummand S r j tk i = realZero S r from if_neg hij, wt_realZero,
          ENat.mul_top (by exact_mod_cast (S r).e_pos.ne'), top_add]
      rw [hi]
      exact le_top

/-! ## KB5 — leading-form nonvanishing / weight exactness + read recovery
(pre-approved split KB5a/KB5b; REV 2, F1: the TRUE mechanism is positional —
k ↦ j₀+ek is INJECTIVE, all slots lie in the SINGLE class j₀ mod e
(l1_boundary_enum.py:227), and the tuple carrier never mixes positions (R1);
the one genuinely delicate content is that the designated slots are exactly
the minimizing slots, so the read recovers each prescribed digit and the min
is attained: no cancellation at weight W.
GATE (REV 2, F5): KB10's negative controls — the gate's teeth for this unit —
are ON RECORD as Tower.lean's `nc1_corrupted_slot`/`s2Bad_iaug_violated`/
`nc3_guard_trips`; per the cross-area adjudication the gate is SEQUENCED
BEFORE the KB5 prover (a scheduling constraint recorded here, not a logical
import). -/

/-- The slot assembly Σ_k d_k·Φ^{j₀+ek} of the offset-P development, in the
tuple carrier: position j₀+e·k holds digit d_k (k < g); every non-designated
position holds zero.  `offP`'s level-(r+1) branch is definitionally this
assembly (see `offP_succ`). -/
def slotAssemble (S : ℕ → StageData) (r W : ℕ)
    (d : Fin ((S r).g) → RealCarrier S r) : RealCarrier S (r + 1) :=
  fun j =>
    if hk : j0 (S r) W ≤ (j : ℕ) ∧ (S r).e ∣ ((j : ℕ) - j0 (S r) W) ∧
        ((j : ℕ) - j0 (S r) W) / (S r).e < (S r).g then
      d ⟨((j : ℕ) - j0 (S r) W) / (S r).e, hk.2.2⟩
    else realZero S r

/-- KB5 (mechanism, designated-slot value): the assembly holds digit d_k at
the designated position j₀+e·k — the positional half of REV 2 F1's slot
separation (k ↦ j₀+ek injective makes the position arithmetic exact).
deps: KB2 (`j0`/`slot` arithmetic).  Sketch: the dite's guard holds at
j = slot k ((j−j₀)/e = k by `Nat.mul_div_cancel_left`, e > 0); `Fin.ext`. -/
theorem slotAssemble_designated (S : ℕ → StageData) (r W : ℕ)
    (d : Fin ((S r).g) → RealCarrier S r) (k : Fin ((S r).g))
    (hlt : slot (S r) W (k : ℕ) < (S r).e * (S r).g) :
    slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hlt⟩ = d k := by
  have he : 0 < (S r).e := (S r).e_pos
  have hsub : slot (S r) W (k : ℕ) - j0 (S r) W = (S r).e * (k : ℕ) := by
    simp [slot]
  have hguard : j0 (S r) W ≤ slot (S r) W (k : ℕ) ∧
      (S r).e ∣ (slot (S r) W (k : ℕ) - j0 (S r) W) ∧
      (slot (S r) W (k : ℕ) - j0 (S r) W) / (S r).e < (S r).g := by
    refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
    · rw [hsub]; exact dvd_mul_right _ _
    · rw [hsub, Nat.mul_div_cancel_left _ he]; exact k.isLt
  change dite _ (fun hk => d ⟨_, hk.2.2⟩) _ = d k
  rw [dif_pos hguard]
  congr 1
  apply Fin.ext
  change (slot (S r) W (k : ℕ) - j0 (S r) W) / (S r).e = (k : ℕ)
  rw [hsub, Nat.mul_div_cancel_left _ he]

/-- KB5 (mechanism, support): the assembly vanishes off the designated slots
(the transcribable residue of KB8a's degree invariant, resolution R1).
deps: KB2.  Sketch: if the dite guard held, j would BE `slot (S r) W ((j−j₀)/e)`
(`Nat.div_mul_cancel` on the dvd leg), contradicting hj. -/
theorem slotAssemble_support (S : ℕ → StageData) (r W : ℕ)
    (d : Fin ((S r).g) → RealCarrier S r) (j : Fin ((S r).e * (S r).g))
    (hj : ∀ k : Fin ((S r).g), (j : ℕ) ≠ slot (S r) W (k : ℕ)) :
    slotAssemble S r W d j = realZero S r := by
  have hne : ¬(j0 (S r) W ≤ (j : ℕ) ∧ (S r).e ∣ ((j : ℕ) - j0 (S r) W) ∧
      ((j : ℕ) - j0 (S r) W) / (S r).e < (S r).g) := by
    rintro ⟨h1, h2, h3⟩
    refine hj ⟨((j : ℕ) - j0 (S r) W) / (S r).e, h3⟩ ?_
    have hc := Nat.mul_div_cancel' h2
    change (j : ℕ) = j0 (S r) W + (S r).e * (((j : ℕ) - j0 (S r) W) / (S r).e)
    omega
  change dite _ (fun hk => d ⟨_, hk.2.2⟩) _ = realZero S r
  rw [dif_neg hne]

/-- KB5a — min ≥ W (the lower half of weight exactness): if every prescribed
digit weighs at least its required parent-parent-scale weight u_k, the
assembled realizer weighs at least W.
deps: KB2 (`uk_spec` via `slot_mul_h_lt` at hW), KB4 (`wt_realZero` for the
off-slot positions), KB10 gate on record.
Sketch: per position, either off-slot (slotWt = ⊤ ≥ W by `wt_realZero`) or
designated slot k (slotWt ≥ e·u_k + slot·h = W by `uk_spec`, whose `hle`
guard is `slot_mul_h_lt` from hW); conclude by `Finset.le_inf`. -/
theorem slotAssemble_wt_ge (p : ℕ) (S : ℕ → StageData) (r : ℕ) {W : ℕ}
    (hW : (S r).thr < W) (d : Fin ((S r).g) → RealCarrier S r)
    (hd : ∀ k : Fin ((S r).g), ((uk (S r) W (k : ℕ) : ℕ) : ℕ∞) ≤ wt p S r (d k)) :
    (W : ℕ∞) ≤ wt p S (r + 1) (slotAssemble S r W d) := by
  have hfin : ∀ k : Fin ((S r).g), slot (S r) W (k : ℕ) < (S r).e * (S r).g := by
    intro k
    have h1 := slot_le (S r) W k.isLt
    have h2 : 0 < (S r).e * (S r).g := Nat.mul_pos (S r).e_pos (S r).g_pos
    omega
  rw [wt_succ]
  refine Finset.le_inf fun j _ => ?_
  by_cases hdes : ∃ k : Fin ((S r).g), (j : ℕ) = slot (S r) W (k : ℕ)
  · obtain ⟨k, hk⟩ := hdes
    have hjk : j = ⟨slot (S r) W (k : ℕ), hfin k⟩ := Fin.ext hk
    subst hjk
    have hval : slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hfin k⟩ = d k :=
      slotAssemble_designated S r W d k _
    have hle : slot (S r) W (k : ℕ) * (S r).h ≤ W := (slot_mul_h_lt (S r) hW k.isLt).le
    have hspec := uk_spec (S r) W (k : ℕ) hle
    calc (W : ℕ∞)
        = ((S r).e : ℕ∞) * ((uk (S r) W (k : ℕ) : ℕ) : ℕ∞)
          + ((slot (S r) W (k : ℕ) * (S r).h : ℕ) : ℕ∞) := by
          exact_mod_cast hspec.symm
      _ ≤ ((S r).e : ℕ∞) * wt p S r (d k)
          + ((slot (S r) W (k : ℕ) * (S r).h : ℕ) : ℕ∞) :=
          add_le_add (mul_le_mul_right (hd k) _) le_rfl
      _ = slotWt p S r (slotAssemble S r W d)
            ⟨slot (S r) W (k : ℕ), hfin k⟩ := by
          change _ = ((S r).e : ℕ∞) * wt p S r
              (slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hfin k⟩)
            + ((slot (S r) W (k : ℕ) * (S r).h : ℕ) : ℕ∞)
          rw [hval]
  · push_neg at hdes
    have hz := slotAssemble_support S r W d j hdes
    have htop : slotWt p S r (slotAssemble S r W d) j = ⊤ := by
      change ((S r).e : ℕ∞) * wt p S r (slotAssemble S r W d j)
          + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) = ⊤
      rw [hz, wt_realZero, ENat.mul_top (by exact_mod_cast (S r).e_pos.ne'), top_add]
    rw [htop]
    exact le_top

/-- KB5b — read = τ ∧ weight = W exactly (the leading-form nonvanishing,
REV 2 F1 mechanism): digits of exact weight u_k and prescribed reads τ_k at
the designated slots assemble to a realizer of weight EXACTLY W (min attained
— no cancellation: the nonzero digits sit at pairwise-distinct positions of
the single class j₀ mod e, and the tuple carrier never mixes positions) whose
independent read recovers τ.
deps: KB2 (`j0_lt`, `slot_mul_h`, `uk_spec`), KB4, KB5a, KB10 gate on record
(Tower.lean `nc1_corrupted_slot`: the corrupted class j₀+1 MUST fail this —
the gate's teeth).  hτ in the existential form of resolution R8.
Sketch: the minimizing slots are exactly {slot k : τ k ≠ 0} (designated slots
with nonzero digit have slotWt = e·u_k + slot·h = W by `uk_spec`; zero-class
slots and off-slots have slotWt = ⊤ by hz + `wt_realZero`); hence wt = W
(attained, KB5a for ≥); the reader's j₀read = (least such slot) mod e = j₀
(`j0_lt`), so the k-th read position is slot k: minimizing ⟹ recursive read
= τ k by hrd; non-minimizing ⟹ read 0 = τ k by the zero case. -/
theorem slotAssemble_total (p : ℕ) (S : ℕ → StageData) (r : ℕ) {W : ℕ}
    (hW : (S r).thr < W) (τ : ResCarrier p S (r + 1))
    (d : Fin ((S r).g) → RealCarrier S r)
    (hwt : ∀ k, τ k ≠ resZero p S r →
      wt p S r (d k) = ((uk (S r) W (k : ℕ) : ℕ) : ℕ∞))
    (hrd : ∀ k, τ k ≠ resZero p S r → digRead p S r (d k) = τ k)
    (hz : ∀ k, τ k = resZero p S r → d k = realZero S r)
    (hτ : ∃ k, τ k ≠ resZero p S r) :
    wt p S (r + 1) (slotAssemble S r W d) = (W : ℕ∞) ∧
      digRead p S (r + 1) (slotAssemble S r W d) = τ := by
  have he : 0 < (S r).e := (S r).e_pos
  have heE : ((S r).e : ℕ∞) ≠ 0 := by exact_mod_cast he.ne'
  have hfin : ∀ k : Fin ((S r).g), slot (S r) W (k : ℕ) < (S r).e * (S r).g := by
    intro k
    have h1 := slot_le (S r) W k.isLt
    have h2 : 0 < (S r).e * (S r).g := Nat.mul_pos (S r).e_pos (S r).g_pos
    omega
  have hdes : ∀ k : Fin ((S r).g),
      slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hfin k⟩ = d k :=
    fun k => slotAssemble_designated S r W d k (hfin k)
  have hle : ∀ k : Fin ((S r).g), slot (S r) W (k : ℕ) * (S r).h ≤ W :=
    fun k => (slot_mul_h_lt (S r) hW k.isLt).le
  -- per-slot weight at a designated slot with nonzero class: exactly W
  have hswt_des : ∀ k : Fin ((S r).g), τ k ≠ resZero p S r →
      slotWt p S r (slotAssemble S r W d) ⟨slot (S r) W (k : ℕ), hfin k⟩ = (W : ℕ∞) := by
    intro k hk
    change ((S r).e : ℕ∞) * wt p S r
        (slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hfin k⟩)
      + ((slot (S r) W (k : ℕ) * (S r).h : ℕ) : ℕ∞) = (W : ℕ∞)
    rw [hdes k, hwt k hk]
    exact_mod_cast uk_spec (S r) W (k : ℕ) (hle k)
  -- per-slot weight at a designated slot with zero class: ⊤
  have hswt_zero : ∀ k : Fin ((S r).g), τ k = resZero p S r →
      slotWt p S r (slotAssemble S r W d) ⟨slot (S r) W (k : ℕ), hfin k⟩ = ⊤ := by
    intro k hk
    change ((S r).e : ℕ∞) * wt p S r
        (slotAssemble S r W d ⟨slot (S r) W (k : ℕ), hfin k⟩)
      + ((slot (S r) W (k : ℕ) * (S r).h : ℕ) : ℕ∞) = ⊤
    rw [hdes k, hz k hk, wt_realZero, ENat.mul_top heE, top_add]
  -- per-slot weight off the designated slots: ⊤
  have hswt_off : ∀ j : Fin ((S r).e * (S r).g),
      (∀ k : Fin ((S r).g), (j : ℕ) ≠ slot (S r) W (k : ℕ)) →
      slotWt p S r (slotAssemble S r W d) j = ⊤ := by
    intro j hj
    change ((S r).e : ℕ∞) * wt p S r (slotAssemble S r W d j)
        + (((j : ℕ) * (S r).h : ℕ) : ℕ∞) = ⊤
    rw [slotAssemble_support S r W d j hj, wt_realZero, ENat.mul_top heE, top_add]
  obtain ⟨k₀, hk₀⟩ := hτ
  -- the weight conjunct
  have hwt_t : wt p S (r + 1) (slotAssemble S r W d) = (W : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · rw [wt_succ]
      refine le_trans
        (Finset.inf_le (Finset.mem_univ ⟨slot (S r) W (k₀ : ℕ), hfin k₀⟩)) ?_
      rw [hswt_des k₀ hk₀]
    · refine slotAssemble_wt_ge p S r hW d fun k => ?_
      by_cases hk : τ k = resZero p S r
      · rw [hz k hk, wt_realZero]
        exact le_top
      · rw [hwt k hk]
  -- the minimizing-slot characterization
  have hmem : ∀ j : Fin ((S r).e * (S r).g),
      j ∈ minSlots p S r (slotAssemble S r W d) ↔
        ∃ k : Fin ((S r).g), (j : ℕ) = slot (S r) W (k : ℕ) ∧ τ k ≠ resZero p S r := by
    intro j
    rw [minSlots, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [hwt_t]
    constructor
    · intro hj
      by_cases hdes' : ∃ k : Fin ((S r).g), (j : ℕ) = slot (S r) W (k : ℕ)
      · obtain ⟨k, hk⟩ := hdes'
        refine ⟨k, hk, fun hzk => ?_⟩
        rw [Fin.ext hk (b := ⟨slot (S r) W (k : ℕ), hfin k⟩), hswt_zero k hzk] at hj
        exact ENat.top_ne_coe W hj
      · push_neg at hdes'
        rw [hswt_off j hdes'] at hj
        exact absurd hj (ENat.top_ne_coe W)
    · rintro ⟨k, hk, hkne⟩
      rw [Fin.ext hk (b := ⟨slot (S r) W (k : ℕ), hfin k⟩)]
      exact hswt_des k hkne
  -- the reader's slot class is j₀
  have hne : (minSlots p S r (slotAssemble S r W d)).Nonempty :=
    ⟨⟨slot (S r) W (k₀ : ℕ), hfin k₀⟩, (hmem _).mpr ⟨k₀, rfl, hk₀⟩⟩
  have hj0read : j0read p S r (slotAssemble S r W d) = j0 (S r) W := by
    rw [j0read, dif_pos hne]
    obtain ⟨k, hk, -⟩ :=
      (hmem _).mp ((minSlots p S r (slotAssemble S r W d)).min'_mem hne)
    rw [hk]
    change (j0 (S r) W + (S r).e * (k : ℕ)) % (S r).e = j0 (S r) W
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (j0_lt (S r) W)
  -- slot positions are separated: k ↦ j₀ + e·k is injective (REV 2 F1)
  have hslot_inj : ∀ k k' : Fin ((S r).g),
      slot (S r) W (k : ℕ) = slot (S r) W (k' : ℕ) → k = k' := by
    intro k k' hkk
    have : (S r).e * (k : ℕ) = (S r).e * (k' : ℕ) := by
      have h1 : j0 (S r) W + (S r).e * (k : ℕ) = j0 (S r) W + (S r).e * (k' : ℕ) := hkk
      omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left he this)
  -- the read conjunct
  have hread : digRead p S (r + 1) (slotAssemble S r W d) = τ := by
    funext k
    have hdig : digRead p S (r + 1) (slotAssemble S r W d) k =
        if hj : j0read p S r (slotAssemble S r W d) + (S r).e * (k : ℕ)
            < (S r).e * (S r).g then
          if (⟨j0read p S r (slotAssemble S r W d) + (S r).e * (k : ℕ), hj⟩ :
              Fin ((S r).e * (S r).g)) ∈ minSlots p S r (slotAssemble S r W d) then
            digRead p S r (slotAssemble S r W d
              ⟨j0read p S r (slotAssemble S r W d) + (S r).e * (k : ℕ), hj⟩)
          else resZero p S r
        else resZero p S r := rfl
    rw [hdig]
    simp only [hj0read]
    have hlt' : j0 (S r) W + (S r).e * (k : ℕ) < (S r).e * (S r).g := hfin k
    rw [dif_pos hlt']
    by_cases hk : τ k = resZero p S r
    · rw [if_neg]
      · exact hk.symm
      · rw [hmem]
        rintro ⟨k', hk', hk'ne⟩
        have hkk : k = k' := hslot_inj k k' hk'
        exact hk'ne (hkk ▸ hk)
    · rw [if_pos ((hmem _).mpr ⟨k, rfl, hk⟩)]
      have hval : slotAssemble S r W d ⟨j0 (S r) W + (S r).e * (k : ℕ), hlt'⟩ = d k :=
        hdes k
      rw [hval]
      exact hrd k hk
  exact ⟨hwt_t, hread⟩

/-! ## KB6 — the class map (over the KB1b `ExtCarrier` layer)
Per resolution R4 (the script's m = 0 CONVENTION), the class map τ ↦ P is the
identity on digit tuples, so its "bijectivity onto F′^×" is the identity's;
the mathematical residue transcribed here: the deg < g representative is
UNIQUE (tuple ↔ polynomial round trip), z̄ is invertible since ψ(0) ≠ 0, and
the anchored targets τ = z̄^a·u are NONZERO classes — hence inside the
coverage domain F′^× that KB8b's totality sweeps.  deps: KB1a-b. -/

namespace ExtCarrier

variable {B : Type} [Field B] (E : ExtCarrier B)

/-- KB6 (vocabulary). Power in the tuple carrier (script `Ext.pow`,
l1_boundary_enum.py:122-127) — needed to STATE the anchored targets z̄^a·u. -/
noncomputable def pow (a : E.Carrier) : ℕ → E.Carrier
  | 0 => E.one
  | n + 1 => E.mul (pow a n) a

/-- Prover helper (KB6): the coefficient formula for a `Fin`-indexed
`Σ C(f i)·X^i` sum — serves `ofPoly_toPoly` and the ψpoly facts below. -/
private theorem sum_C_mul_X_pow_coeff {n : ℕ} (f : Fin n → B) (m : ℕ) :
    (∑ i : Fin n, C (f i) * X ^ (i : ℕ)).coeff m
      = if h : m < n then f ⟨m, h⟩ else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : m < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · simp
    · intro i _ hi
      have hmi : m ≠ (i : ℕ) := fun hmi => hi (Fin.ext (by simp [← hmi]))
      simp [hmi]
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hmi : m ≠ (i : ℕ) := fun hmi => h (hmi ▸ i.isLt)
    simp [hmi]

/-- KB6 (representative degree). The tuple's polynomial transcription has
degree < g — half of representative uniqueness.
deps: KB1b.  Sketch: `Polynomial.degree_sum_le` + `degree_C_mul_X_pow_le`
over i < g. -/
theorem toPoly_degree_lt (v : E.Carrier) :
    (E.toPoly v).degree < (E.g : WithBot ℕ) := by
  rw [toPoly]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe E.g)]
  intro i _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
    (by exact_mod_cast i.isLt)

/-- KB6 (representative uniqueness, round-trip form). Reading the tuple's own
polynomial back yields the tuple: the deg < g representative determines and is
determined by its coefficient tuple.
deps: KB1b.  Sketch: `coeff` of a sum of monomials of pairwise-distinct
degrees (`Polynomial.coeff_C_mul`, `coeff_X_pow`, `Finset.sum_eq_single`). -/
theorem ofPoly_toPoly (v : E.Carrier) : E.ofPoly (E.toPoly v) = v := by
  funext i
  change (E.toPoly v).coeff (i : ℕ) = v i
  rw [toPoly, sum_C_mul_X_pow_coeff, dif_pos i.isLt]

/-- KB6 (representative uniqueness, injective form) — assembly from
`ofPoly_toPoly`; no independent content. -/
theorem toPoly_injective : Function.Injective E.toPoly := fun v w h => by
  rw [← ofPoly_toPoly E v, ← ofPoly_toPoly E w, h]

/-- KB6 (z̄ ≠ 0). deps: KB1b.  Sketch: g ≥ 2 branch — the tuple has a 1 at
index 1; g = 1 branch — z̄ = −ψ₀ ≠ 0 by `ψ_const_ne`. -/
theorem zbar_ne_zero : E.zbar ≠ E.zero := by
  intro h
  by_cases hg : E.g = 1
  · have h0 := congrFun h ⟨0, E.g_pos⟩
    rw [zbar, if_pos hg] at h0
    exact E.ψ_const_ne (neg_eq_zero.mp h0)
  · have h2 : 1 < E.g := lt_of_le_of_ne E.g_pos (Ne.symm hg)
    have h1 := congrFun h ⟨1, h2⟩
    rw [zbar, if_neg hg] at h1
    exact one_ne_zero h1

/-- Prover helper (KB6): ψpoly's degree is at most g. -/
private theorem ψpoly_degree_le : E.ψpoly.degree ≤ (E.g : WithBot ℕ) := by
  rw [ψpoly]
  refine le_trans (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_le_iff]
  intro i _
  exact le_trans (Polynomial.degree_C_mul_X_pow_le _ _)
    (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt)

/-- Prover helper (KB6): ψpoly's top coefficient is 1 (the `ψ_monic` field). -/
private theorem ψpoly_coeff_g : E.ψpoly.coeff E.g = 1 := by
  rw [ψpoly, sum_C_mul_X_pow_coeff, dif_pos (Nat.lt_succ_self E.g)]
  exact E.ψ_monic

/-- Prover helper (KB6): ψpoly is monic. -/
private theorem ψpoly_monic : E.ψpoly.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one E.g
    (Polynomial.natDegree_le_iff_degree_le.mpr E.ψpoly_degree_le) E.ψpoly_coeff_g

/-- Prover helper (KB6): ψpoly has degree exactly g. -/
private theorem ψpoly_degree : E.ψpoly.degree = (E.g : WithBot ℕ) := by
  refine le_antisymm E.ψpoly_degree_le ?_
  refine Polynomial.le_degree_of_ne_zero ?_
  rw [E.ψpoly_coeff_g]
  exact one_ne_zero

/-- Prover helper (KB6): reducing a `C c·ψ + 1` combination mod ψ yields 1. -/
private theorem mod_C_mul_ψpoly_add_one (c : B) :
    (C c * E.ψpoly + 1) %ₘ E.ψpoly = 1 := by
  rw [Polynomial.add_modByMonic, Polynomial.mul_self_modByMonic E.ψpoly_monic, zero_add]
  refine (Polynomial.modByMonic_eq_self_iff E.ψpoly_monic).mpr ?_
  rw [Polynomial.degree_one, E.ψpoly_degree]
  exact_mod_cast E.g_pos

/-- Prover helper (KB6): `ofPoly` reads the constant polynomial 1 to the
tuple unit. -/
private theorem ofPoly_one : E.ofPoly 1 = E.one := by
  funext i
  change (1 : Polynomial B).coeff (i : ℕ) = if (i : ℕ) = 0 then 1 else 0
  rw [Polynomial.coeff_one]

/-- KB6 (z̄ invertible since ψ(0) ≠ 0 — the blueprint's sketch clause).
deps: KB1b.  Sketch: in B[z]/(ψ) the element z̄ is a unit iff z ∤ ψ, i.e.
ψ(0) ≠ 0 (`ψ_const_ne`); transport through the tuple presentation (the
`carrierField` route, or directly: gcd(z, ψ) = 1 gives a Bézout inverse whose
deg < g representative is the witness). -/
theorem zbar_isUnit : ∃ w : E.Carrier, E.mul E.zbar w = E.one := by
  by_cases hg : E.g = 1
  · -- z̄ = −ψ₀ is a nonzero constant; its inverse tuple is the witness
    refine ⟨fun _ => (-(E.ψ 0))⁻¹, ?_⟩
    have hz : E.toPoly E.zbar = C (-(E.ψ 0)) := by
      rw [toPoly, Finset.sum_eq_single (⟨0, E.g_pos⟩ : Fin E.g)]
      · rw [zbar, if_pos hg]
        simp
      · intro i _ hi
        exfalso
        refine hi (Fin.ext ?_)
        have := i.isLt
        omega
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have hw : E.toPoly (fun _ => (-(E.ψ 0))⁻¹) = C ((-(E.ψ 0))⁻¹) := by
      rw [toPoly, Finset.sum_eq_single (⟨0, E.g_pos⟩ : Fin E.g)]
      · simp
      · intro i _ hi
        exfalso
        refine hi (Fin.ext ?_)
        have := i.isLt
        omega
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have hne : -(E.ψ 0) ≠ 0 := neg_ne_zero.mpr E.ψ_const_ne
    have h1 : (1 : Polynomial B) %ₘ E.ψpoly = 1 := by
      have := E.mod_C_mul_ψpoly_add_one 0
      simpa using this
    change E.ofPoly ((E.toPoly E.zbar * E.toPoly fun _ => (-(E.ψ 0))⁻¹) %ₘ E.ψpoly)
        = E.one
    rw [hz, hw, ← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1, h1]
    exact E.ofPoly_one
  · -- g ≥ 2: z̄ = X and the Bézout inverse is −ψ₀⁻¹·(ψ − ψ₀)/X
    have hg2 : 2 ≤ E.g := by
      have := E.g_pos
      omega
    refine ⟨fun i => -(E.ψ 0)⁻¹ * E.ψ i.succ, ?_⟩
    have hz : E.toPoly E.zbar = X := by
      rw [toPoly, Finset.sum_eq_single (⟨1, by omega⟩ : Fin E.g)]
      · rw [zbar, if_neg hg]
        simp
      · intro i _ hi
        rw [zbar, if_neg hg]
        have hi1 : (i : ℕ) ≠ 1 := fun h => hi (Fin.ext (by simp [h]))
        simp [hi1]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    have hkey : C (-(E.ψ 0)⁻¹) * (C (E.ψ 0) * X ^ ((0 : Fin (E.g + 1)) : ℕ))
        = (-1 : Polynomial B) := by
      rw [show ((0 : Fin (E.g + 1)) : ℕ) = 0 from rfl, pow_zero, mul_one,
        ← Polynomial.C_mul, neg_mul, inv_mul_cancel₀ E.ψ_const_ne]
      simp
    have hw : X * E.toPoly (fun i => -(E.ψ 0)⁻¹ * E.ψ i.succ)
        = C (-(E.ψ 0)⁻¹) * E.ψpoly + 1 := by
      rw [toPoly, ψpoly, Fin.sum_univ_succ, Finset.mul_sum, mul_add, Finset.mul_sum]
      have hterm : ∀ i : Fin E.g, X * (C (-(E.ψ 0)⁻¹ * E.ψ i.succ) * X ^ (i : ℕ))
          = C (-(E.ψ 0)⁻¹) * (C (E.ψ i.succ) * X ^ ((i.succ : Fin (E.g + 1)) : ℕ)) := by
        intro i
        rw [Fin.val_succ, Polynomial.C_mul, pow_succ]
        ring
      simp only [hterm]
      rw [hkey]
      ring
    change E.ofPoly ((E.toPoly E.zbar * E.toPoly fun i => -(E.ψ 0)⁻¹ * E.ψ i.succ)
        %ₘ E.ψpoly) = E.one
    rw [hz, hw, E.mod_C_mul_ψpoly_add_one]
    exact E.ofPoly_one

/-- Prover helper (KB6): `toPoly` reflects zero — the injective form of the
round trip specialized at 0. -/
private theorem toPoly_eq_zero_iff (v : E.Carrier) :
    E.toPoly v = 0 ↔ v = E.zero := by
  constructor
  · intro h
    have hv := E.ofPoly_toPoly v
    rw [h] at hv
    rw [← hv]
    funext i
    change (0 : Polynomial B).coeff (i : ℕ) = 0
    simp
  · intro h
    rw [h, toPoly]
    refine Finset.sum_eq_zero fun i _ => ?_
    change C ((0 : B)) * X ^ (i : ℕ) = 0
    simp

/-- Prover helper (KB6): the tuple carrier has no zero divisors — the direct
route through ψ irreducible ⟹ prime in B[X] (avoiding the sorried
`carrierField` placeholder of Tower.lean): a vanishing product means
ψ ∣ toPoly a · toPoly b, so ψ (degree g) divides a factor of degree < g,
forcing that factor — hence its tuple — to vanish. -/
private theorem carrier_mul_ne_zero (x y : E.Carrier) (hx : x ≠ E.zero)
    (hy : y ≠ E.zero) : E.mul x y ≠ E.zero := by
  intro h
  -- the reduced remainder vanishes identically
  have hmod : (E.toPoly x * E.toPoly y) %ₘ E.ψpoly = 0 := by
    have hdeg : ((E.toPoly x * E.toPoly y) %ₘ E.ψpoly).degree < (E.g : WithBot ℕ) := by
      rw [← E.ψpoly_degree]
      exact Polynomial.degree_modByMonic_lt _ E.ψpoly_monic
    ext n
    rw [Polynomial.coeff_zero]
    by_cases hn : n < E.g
    · exact congrFun h ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hdeg (by exact_mod_cast Nat.le_of_not_lt hn))
  have hdvd : E.ψpoly ∣ E.toPoly x * E.toPoly y :=
    (Polynomial.modByMonic_eq_zero_iff_dvd E.ψpoly_monic).mp hmod
  have hprime : Prime E.ψpoly :=
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp E.ψ_irred)
  have hfactor : (E.ψpoly ∣ E.toPoly x) ∨ (E.ψpoly ∣ E.toPoly y) :=
    hprime.2.2 _ _ hdvd
  have hcontra : ∀ v : E.Carrier, v ≠ E.zero → ¬ E.ψpoly ∣ E.toPoly v := by
    intro v hv hdv
    have hvne : E.toPoly v ≠ 0 := fun h0 => hv ((E.toPoly_eq_zero_iff v).mp h0)
    have := Polynomial.degree_le_of_dvd hdv hvne
    rw [E.ψpoly_degree] at this
    exact absurd (lt_of_le_of_lt this (E.toPoly_degree_lt v)) (lt_irrefl _)
  rcases hfactor with hf | hf
  · exact hcontra x hx hf
  · exact hcontra y hy hf

/-- KB6 (anchored targets are in F′^× — the coverage clause for the a > 0
boundary cases of the enumeration): z̄^a·u ≠ 0 for every unit-side u ≠ 0.
deps: KB1b, `zbar_ne_zero`/`zbar_isUnit`.  Sketch: F′ is a field
(`ψ_irred` through `carrierField`): products of nonzeros are nonzero; z̄ ≠ 0.
Together with resolution R4 (class map = identity) this closes the
blueprint's "bijectivity onto F′^× including anchored τ = z̄^a·u". -/
theorem anchored_ne_zero (a : ℕ) (u : E.Carrier) (hu : u ≠ E.zero) :
    E.mul (E.pow E.zbar a) u ≠ E.zero := by
  have hp : ∀ n : ℕ, E.pow E.zbar n ≠ E.zero := by
    intro n
    induction n with
    | zero =>
      intro h
      have h0 := congrFun h ⟨0, E.g_pos⟩
      exact one_ne_zero h0
    | succ n ih => exact E.carrier_mul_ne_zero _ _ ih E.zbar_ne_zero
  exact E.carrier_mul_ne_zero _ _ (hp a) hu

end ExtCarrier

/-! ## KB8a — `offP`: construction, eligibility, degree invariant
(the def is placed before KB7 because KB7's statement consumes it; unit order
is KB7 → KB8a in the blueprint's dependency spine, file order is
vocabulary-first). -/

/-- Base realizer: the F_Q-unit lift c·p^W (script
`t[j] = Pk * p ** (num // e)`, l1_boundary_enum.py:212 — no threshold,
resolution R6). -/
def offBase (p W : ℕ) (c : ZMod p) : ℤ :=
  (ZMod.val c : ℤ) * (p : ℤ) ^ W

/-- KB8a — THE OFFSET-P CONSTRUCTION `offP` (a def, not a choice — L1-v
determinism is definitional; MOVES 4653-4671, (S6b′) 2436-2455, transcribed
from `offsetP2`/`offsetP3`): at the base, the unit lift c·p^W; at level r+1,
the slot assembly placing at position j₀+e·k the RECURSIVE realizer of digit
τ_k at parent-parent-scale weight u_k = (W − (j₀+ek)h)/e.  Zero-class digits
recurse to the zero realizer (resolution R5, `offP_zero_class`).
deps: KB1a-c, KB2 (`j0`/`uk`), KB3 (guard — consumed by the eligibility
theorem below, not by the def, which is total with junk below threshold). -/
def offP (p : ℕ) (S : ℕ → StageData) : ∀ r, ℕ → ResCarrier p S r → RealCarrier S r
  | 0, W, τ => offBase p W τ
  | r + 1, W, τ =>
    slotAssemble S r W fun k => offP p S r (uk (S r) W (k : ℕ)) (τ k)

/-- Definitional tie: `offP`'s level-(r+1) branch IS the slot assembly of its
recursive digit realizers. -/
theorem offP_succ (p : ℕ) (S : ℕ → StageData) (r W : ℕ)
    (τ : ResCarrier p S (r + 1)) :
    offP p S (r + 1) W τ
      = slotAssemble S r W fun k => offP p S r (uk (S r) W (k : ℕ)) (τ k) := rfl

/-- KB8a (zero-class law, resolution R5): the zero class recurses to the zero
realizer — the transcription of the script's skip-zero-digits branch.
deps: —.  Sketch: induction on r; base: val 0 = 0; step: every designated
slot holds `offP r _ resZero = realZero` by IH, off-slots are `realZero`
outright; funext. -/
theorem offP_zero_class (p : ℕ) (S : ℕ → StageData) (r W : ℕ) :
    offP p S r W (resZero p S r) = realZero S r := by
  induction r generalizing W with
  | zero =>
    change (ZMod.val (0 : ZMod p) : ℤ) * (p : ℤ) ^ W = 0
    rw [(ZMod.val_eq_zero (0 : ZMod p)).mpr rfl]
    simp
  | succ r ih =>
    funext j
    change slotAssemble S r W (fun k => offP p S r (uk (S r) W (k : ℕ)) (resZero p S r)) j
        = realZero S r
    simp only [ih]
    unfold slotAssemble
    split <;> rfl

/-- KB8a (slots in range — KB2's `slot_le` in the Fin-usable strict form;
the designated positions exist in the coefficient space).
deps: KB2 (`slot_le`).  Sketch: slot ≤ eg − 1 < eg (e·g ≥ 1 from
`e_pos`/`g_pos`); omega. -/
theorem slot_lt (s : StageData) (W : ℕ) {k : ℕ} (hk : k < s.g) :
    slot s W k < s.e * s.g := by
  have h1 := slot_le s W hk
  have h2 : 0 < s.e * s.g := Nat.mul_pos s.e_pos s.g_pos
  omega

/-- KB8a (eligibility of every recursive call — the L1-ii clause in stream
form): under (I-aug) at the consecutive pair, every digit's required weight
u_k clears the threshold one stage down, so the recursion into level r+1 is
eligible.  Assembly of Tower.lean's KB3 `guard_chain`; no independent
content. -/
theorem offP_calls_eligible (S : ℕ → StageData) (r : ℕ)
    (hIaug : IAug (S r) (S (r + 1))) {W : ℕ} (hW : (S (r + 1)).thr < W)
    (k : Fin ((S (r + 1)).g)) :
    (S r).thr < uk (S (r + 1)) W (k : ℕ) :=
  guard_chain (S r) (S (r + 1)) hIaug hW k.isLt

/-- KB8a (degree invariant, designated-slot half): `offP`'s digit at the
designated position j₀+e·k is the recursive realizer of τ_k at weight u_k.
deps: `offP_succ` + KB5's `slotAssemble_designated`.
Sketch: rw [offP_succ]; exact slotAssemble_designated …. -/
theorem offP_designated (p : ℕ) (S : ℕ → StageData) (r W : ℕ)
    (τ : ResCarrier p S (r + 1)) (k : Fin ((S r).g))
    (hlt : slot (S r) W (k : ℕ) < (S r).e * (S r).g) :
    offP p S (r + 1) W τ ⟨slot (S r) W (k : ℕ), hlt⟩
      = offP p S r (uk (S r) W (k : ℕ)) (τ k) := by
  rw [offP_succ]
  exact slotAssemble_designated S r W _ k hlt

/-- KB8a — THE DEGREE INVARIANT (support half, resolution R1; REV 2 F1's
explicit KB8a obligation): every stage-r realizer built by `offP` has its
Φ-adic digits ONLY at the designated slots j₀+e·k — no positional overflow
(the per-digit degree bound "< deg Φ_prev" is the carrier typing itself).
deps: `offP_succ` + KB5's `slotAssemble_support`.
Sketch: rw [offP_succ]; exact slotAssemble_support …. -/
theorem offP_support (p : ℕ) (S : ℕ → StageData) (r W : ℕ)
    (τ : ResCarrier p S (r + 1)) (j : Fin ((S r).e * (S r).g))
    (hj : ∀ k : Fin ((S r).g), (j : ℕ) ≠ slot (S r) W (k : ℕ)) :
    offP p S (r + 1) W τ j = realZero S r := by
  rw [offP_succ]
  exact slotAssemble_support S r W _ j hj

/-! ## KB7 — the base case -/

/-- Eligibility of a weight at a level (resolution R6): the base has NO
threshold (script: "digits are F_Q-unit lifts with no threshold"); level r+1
demands W strictly above the clean threshold e·h·g of its stage data. -/
def Eligible (S : ℕ → StageData) : ℕ → ℕ → Prop
  | 0, _ => True
  | r + 1, W => (S r).thr < W

/-- KB7 — base case: stage-1 realizers.  EVERY nonzero scalar c ∈ F_p^× is
realized at EVERY weight W (including W = 0 — no threshold, resolution R6) by
its unit lift c·p^W, with exact weight and correct read-back; determinism is
definitional (`offP` is a def).
deps: KB1a-b (vocabulary); p prime (the unit lift's valuation).
Sketch: v_p(val·p^W) = W since 0 < val < p and p is prime
(`padicValInt.mul`, `padicValNat.prime_pow_self`, `padicValNat.eq_zero_of_not_dvd`);
the unit part reads back to c (`ZMod.natCast_val`/`ZMod.intCast_cast`
round-trip; exact division by p^W). -/
theorem base_total (p : ℕ) [Fact p.Prime] (S : ℕ → StageData) (W : ℕ)
    (τ : ResCarrier p S 0) (hτ : τ ≠ resZero p S 0) :
    wt p S 0 (offP p S 0 W τ) = (W : ℕ∞) ∧
      digRead p S 0 (offP p S 0 W τ) = τ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hτ0 : τ ≠ (0 : ZMod p) := hτ
  have hval : ZMod.val τ ≠ 0 := fun h => hτ0 ((ZMod.val_eq_zero τ).mp h)
  have hvlt : ZMod.val τ < p := ZMod.val_lt τ
  have hnd : ¬ p ∣ ZMod.val τ :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hval) hvlt
  have hvz : (ZMod.val τ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hval
  have hpW : ((p : ℤ)) ^ W ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hprod : (ZMod.val τ : ℤ) * (p : ℤ) ^ W ≠ 0 := mul_ne_zero hvz hpW
  have hpv : padicValInt p ((ZMod.val τ : ℤ) * (p : ℤ) ^ W) = W := by
    rw [padicValInt.mul hvz hpW]
    have h1 : padicValInt p (ZMod.val τ : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      exact padicValNat.eq_zero_of_not_dvd hnd
    have h2 : padicValInt p ((p : ℤ) ^ W) = W := by
      rw [show ((p : ℤ)) ^ W = ((p ^ W : ℕ) : ℤ) by push_cast; ring,
        padicValInt.of_nat]
      exact padicValNat.prime_pow W
    rw [h1, h2, zero_add]
  constructor
  · change wtBase p ((ZMod.val τ : ℤ) * (p : ℤ) ^ W) = (W : ℕ∞)
    simp only [wtBase]
    rw [if_neg hprod, hpv]
  · change digBase p ((ZMod.val τ : ℤ) * (p : ℤ) ^ W) = τ
    simp only [digBase]
    rw [hpv, Int.mul_ediv_cancel _ hpW, Int.cast_natCast, ZMod.natCast_val,
      ZMod.cast_id]

/-! ## KB8b — `l1_totality`: THE INDUCTION
(pre-approved split executed NOW per REV 2 F13: exactness leg `l1_exactness`
and read leg `l1_read` are the two sorried units; `l1_totality` and
`l1_coverage` are their assemblies.  Each leg's prover may run the mutual
strong induction internally — the legs are separately true; the IH available
one stage down is exactly (S6b′)'s CLAIM = the conjunction, blueprint §3.B.) -/

/-- Prover helper (KB8b): the two legs share one induction — (S6b′)'s CLAIM
is the conjunction, so the IH one stage down must carry both conjuncts
(blueprint §3.B; the legs project out of this). -/
private theorem l1_main (p : ℕ) [Fact p.Prime] (S : ℕ → StageData)
    (hIaug : ∀ i, IAug (S i) (S (i + 1))) :
    ∀ r : ℕ, ∀ W : ℕ, Eligible S r W → ∀ τ : ResCarrier p S r,
      τ ≠ resZero p S r →
      wt p S r (offP p S r W τ) = (W : ℕ∞) ∧
        digRead p S r (offP p S r W τ) = τ := by
  intro r
  induction r with
  | zero => exact fun W _ τ hτ => base_total p S W τ hτ
  | succ r ih =>
    intro W hW τ hτ
    have hW' : (S r).thr < W := hW
    have helig : ∀ k : Fin ((S r).g), Eligible S r (uk (S r) W (k : ℕ)) := by
      cases r with
      | zero => exact fun _ => trivial
      | succ r' => exact fun k => offP_calls_eligible S r' (hIaug r') hW' k
    have hex : ∃ k, τ k ≠ resZero p S r := by
      by_contra hall
      push_neg at hall
      exact hτ (funext fun k => hall k)
    rw [offP_succ]
    exact slotAssemble_total p S r hW' τ _
      (fun k hk => (ih (uk (S r) W (k : ℕ)) (helig k) (τ k) hk).1)
      (fun k hk => (ih (uk (S r) W (k : ℕ)) (helig k) (τ k) hk).2)
      (fun k hk => by rw [hk]; exact offP_zero_class p S r _)
      hex

/-- KB8b (exactness leg): ∀ stage r, ∀ eligible W, ∀ τ ∈ F_r^×,
wt (offP r W τ) = W — the weight-exactness half of L1 totality (L1-iii).
deps: KB8a (`offP_succ`/`offP_calls_eligible`), KB4, KB5 (KB5a/KB5b), KB7
(base), KB2/KB3 (Tower.lean).  hIaug per resolution R7 (only the prefix
below r is consumed).
Sketch: strong induction on r.  Base: `base_total`.  Step: the digit family
d k := offP r (u_k) (τ k) satisfies KB5b's hypotheses — exact weight u_k and
read τ k at nonzero classes by the IH (each call eligible:
`offP_calls_eligible` needs `hIaug` at the pair (r−1, r) via the guard
chain; for r = 0 digits, the base case has no threshold), zero classes to
zero realizers by `offP_zero_class` + `wt_realZero`; hτ survives to some
nonzero digit (a nonzero tuple has a nonzero entry); conclude by
`slotAssemble_total`.1 through `offP_succ`. -/
theorem l1_exactness (p : ℕ) [Fact p.Prime] (S : ℕ → StageData)
    (hIaug : ∀ i, IAug (S i) (S (i + 1))) :
    ∀ r : ℕ, ∀ W : ℕ, Eligible S r W → ∀ τ : ResCarrier p S r,
      τ ≠ resZero p S r → wt p S r (offP p S r W τ) = (W : ℕ∞) := by
  intro r W hW τ hτ
  exact (l1_main p S hIaug r W hW τ hτ).1

/-- KB8b (read leg): ∀ stage r, ∀ eligible W, ∀ τ ∈ F_r^×,
digRead (offP r W τ) = τ — the class-read half of L1 totality (L1-iv, the
REV 2 F1 positional mechanism).
deps: as `l1_exactness` (the two legs share the mutual induction; KB5b
delivers both conjuncts at the step — a prover may prove the conjunction
once and project).
Sketch: same induction; the step is `slotAssemble_total`.2. -/
theorem l1_read (p : ℕ) [Fact p.Prime] (S : ℕ → StageData)
    (hIaug : ∀ i, IAug (S i) (S (i + 1))) :
    ∀ r : ℕ, ∀ W : ℕ, Eligible S r W → ∀ τ : ResCarrier p S r,
      τ ≠ resZero p S r → digRead p S r (offP p S r W τ) = τ := by
  intro r W hW τ hτ
  exact (l1_main p S hIaug r W hW τ hτ).2

/-- KB8b — `l1_totality`, THE KERNEL THEOREM (D4R.0-K(a) = L1 totality over
the transcribed enum model; MOVES 4653-4671): at every stage r, every
eligible weight W (strictly above the clean threshold; no threshold at the
base), and EVERY prescribed class τ ∈ F_r^× — anchored targets included, per
KB6/resolution R4 they are particular nonzero classes — the offset-P
construction returns a realizer with exact weight W and prescribed read τ.
Assembly of the two legs; no independent content.
deps: `l1_exactness`, `l1_read`.
CONVENTION FENCE (§3.B, binding on the KB11 seam): the note's own digit map
may differ from this model's by a data-determined slot-unit twist — a
bijection of nonzero classes; totality/weight/determinism transport, WHICH
class gets WHICH realizer is convention-relative. -/
theorem l1_totality (p : ℕ) [Fact p.Prime] (S : ℕ → StageData)
    (hIaug : ∀ i, IAug (S i) (S (i + 1))) (r : ℕ) (W : ℕ)
    (hW : Eligible S r W) (τ : ResCarrier p S r) (hτ : τ ≠ resZero p S r) :
    wt p S r (offP p S r W τ) = (W : ℕ∞) ∧
      digRead p S r (offP p S r W τ) = τ :=
  ⟨l1_exactness p S hIaug r W hW τ hτ, l1_read p S hIaug r W hW τ hτ⟩

/-- KB8b (coverage corollary): every class in F_r^× is covered at every
eligible weight — the bijectivity/coverage clause of the blueprint (the
witness is `offP` itself; with resolution R4's identity class map, coverage
IS totality).  deps: `l1_totality`. -/
theorem l1_coverage (p : ℕ) [Fact p.Prime] (S : ℕ → StageData)
    (hIaug : ∀ i, IAug (S i) (S (i + 1))) (r : ℕ) (W : ℕ)
    (hW : Eligible S r W) (τ : ResCarrier p S r) (hτ : τ ≠ resZero p S r) :
    ∃ t : RealCarrier S r, wt p S r t = (W : ℕ∞) ∧ digRead p S r t = τ :=
  ⟨offP p S r W τ, l1_totality p S hIaug r W hW τ hτ⟩

/-! ## KB9 — determinism + boundary corollaries (spot rows against the
probe's tallies — verification/l1_boundary_enum.py §4: 40,378 cases total;
the spot rows below are single enumerated corners, not the grid). -/

/-- KB9 (determinism, L1-v): the realizer is a FUNCTION of (stage data, W, τ)
— `offP` is a def, not a choice; congruence is definitional.  (The def is
also `Classical`-free by construction: `ZMod.val`, slot arithmetic, and the
tuple assembly are all explicit data.) -/
theorem offP_deterministic (p : ℕ) (S : ℕ → StageData) (r : ℕ)
    {W W' : ℕ} {τ τ' : ResCarrier p S r} (hw : W = W') (ht : τ = τ') :
    offP p S r W τ = offP p S r W' τ' := by
  subst hw; subst ht; rfl

/-- KB9 (spot data). The constant stage stream at (e,h,g) = (2,1,2) — the
probe's NC1/NC2 run point p = 3, thr = 4 (only stage 0 is consumed by the
level-1 spot row). -/
def spotStream32 : ℕ → StageData :=
  fun _ => ⟨2, 1, 2, by norm_num, by norm_num, by norm_num, by decide⟩

/-- KB9 (spot data). The all-ones target class τ = (1,1) ∈ F₉ = F₃[z]/ψ,
tuple presentation. -/
def spotTauA : ResCarrier 3 spotStream32 1 := fun _ => (1 : ZMod 3)

/-- KB9 (spot row: min-W + j₀ > 0 engaged, probe tallies (min-nu)/(j0>0)).
SEALED EXPECTED VALUES (hand-computed from the model, matching the probe's
PASS at p = 3, (e,h,g) = (2,1,2), W = thr+1 = 5): j₀ = 5 mod 2 = 1 > 0;
slots 1 and 3; u₀ = 2, u₁ = 1; realizer positions (0, 1·3², 0, 1·3¹);
weight min(⊤, 2·2+1, ⊤, 2·1+3) = 5; read (1,1) = τ.
deps: KB8a (`offP`), the model defs.  Sketch: decide/norm_num after
`simp [offP, wt, digRead, …]` unfolding (the terms are closed numerals). -/
theorem spot_minW_j0pos :
    wt 3 spotStream32 1 (offP 3 spotStream32 1 5 spotTauA) = (5 : ℕ∞) ∧
      digRead 3 spotStream32 1 (offP 3 spotStream32 1 5 spotTauA) = spotTauA := by
  sorry

/-- KB9 (spot data). The constant stage stream at (e,h,g) = (2,1,1), p = 2 —
the g = 1 single-slot corner with TRIVIAL unit group |F′^×| = 1
(F′ = F₂[z]/(z+1) ≅ F₂; probe tallies (g=1)/(trivial unit group)). -/
def spotStream21 : ℕ → StageData :=
  fun _ => ⟨2, 1, 1, by norm_num, by norm_num, by norm_num, by decide⟩

/-- KB9 (spot data). The unique unit target τ = (1) of the trivial-unit-group
corner. -/
def spotTauB : ResCarrier 2 spotStream21 1 := fun _ => (1 : ZMod 2)

/-- KB9 (spot row: g = 1 single slot, trivial unit group at p = 2).
SEALED EXPECTED VALUES (hand-computed, matching the probe's PASS at p = 2,
(e,h,g) = (2,1,1), W = thr+1 = 3): j₀ = 3 mod 2 = 1; single slot 1; u₀ = 1;
realizer positions (0, 1·2¹); weight min(⊤, 2·1+1) = 3; read (1) = τ.
deps/sketch: as `spot_minW_j0pos`. -/
theorem spot_g1_trivialUnit :
    wt 2 spotStream21 1 (offP 2 spotStream21 1 3 spotTauB) = (3 : ℕ∞) ∧
      digRead 2 spotStream21 1 (offP 2 spotStream21 1 3 spotTauB) = spotTauB := by
  sorry

end LeanUrat.Kernels.D4R0K
