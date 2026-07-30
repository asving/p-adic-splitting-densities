/-
Kernels/D4R0K/Tower — BP4-c2 E-phase skeletons for units KB1a, KB1b, KB1c,
KB2, KB3, KB10 (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.B + §4 KB;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

THE TRANSCRIBED ENUM MODEL (Q2 ADJUDICATED 2026-07-30: prove over the
transcribed l1_boundary_enum model; the seam to HC-1's (S6b) vocabulary is the
separate ⚑ unit KB11): verification/l1_boundary_enum.py — per-stage side data
(e, h, g, ψ) with gcd(e,h) = 1; clean threshold w_prev(Φ) = e·h·g;
j₀ := h⁻¹·W mod e (the forced slot class); slots j₀ + e·k ≤ eg−1; summand
parent-parent-scale weights u_k := (W − (j₀+ek)h)/e; recursion guard
u_k > e_prev·h_prev·g_prev, fed by (I-aug) h > e·(e_prev·h_prev·g_prev).

FILE-SCOPE NOTE (recorded resolution): the blueprint's §2.3 assigns `wt`,
`offP`, `digRead` to Tower.lean as well; those are units KB4/KB8a (a sibling
cluster) and are NOT here — this file carries exactly the BP4-c2 units. The
sibling cluster should place them in Kernels/D4R0K/L1.lean (importing this
file) or obtain orchestrator authorization to extend this one.

E-phase discipline: Defs are sorry-free where decidable (one recorded
exception: `ExtCarrier.carrierField`, see its docstring); theorems have sorry
bodies.  Build: cd lean && lake build LeanUrat.Kernels.D4R0K.Tower
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels.D4R0K

open Polynomial

/-! ## KB1a — `StageData`/`TowerData` records + arithmetic invariants only
(REV 2, F13 split of the retired KB1). -/

/-- KB1a (stage record). One OM stage's arithmetic side data (e, h, g) of the
transcribed enumeration model, with gcd(e,h) = 1 and positivity as fields.
RECORDED RESOLUTION: the blueprint's "(e, h, g, ψ-as-data)" splits across
KB1a/KB1b exactly at the tower dependency — ψ's TYPE depends on the residue
field one stage down, so ψ-as-data lives in KB1b's carrier record `ExtCarrier`
and the arithmetic-only record carries (e, h, g).
deps: —.  ⚑ interface ratification. -/
structure StageData where
  e : ℕ
  h : ℕ
  g : ℕ
  e_pos : 0 < e
  h_pos : 0 < h
  g_pos : 0 < g
  cop : Nat.Coprime e h

namespace StageData

/-- KB1a. The clean threshold w_prev(Φ) = e·h·g (MOVES (S6b′) 2436-2455). -/
def thr (s : StageData) : ℕ := s.e * s.h * s.g

end StageData

/-- KB1a ((I-aug) law). The (I-aug) inequality between consecutive stages:
h_cur > e_cur·(e_prev·h_prev·g_prev) (MOVES 2450-2455).  The script's grid
choice h₂ = e₂·e₁h₁g₁ + 1 satisfies it; its NC3 control h₂ = e₂·e₁h₁g₁ − 1
violates it (see KB10 below). -/
def IAug (prev cur : StageData) : Prop := cur.e * prev.thr < cur.h

instance (prev cur : StageData) : Decidable (IAug prev cur) :=
  inferInstanceAs (Decidable (cur.e * prev.thr < cur.h))

/-- KB1a (tower record). The stage tower with the (I-aug) chain as a field.
Stages are indexed bottom-up 0..len; stage 0 sits directly over the base field
F_p, whose scalar realizers are F_Q-unit lifts with no threshold (KB7's base
case, sibling cluster).
deps: —.  ⚑ interface ratification. -/
structure TowerData where
  len : ℕ
  stage : Fin (len + 1) → StageData
  iaug : ∀ i : Fin len, IAug (stage i.castSucc) (stage i.succ)

/-! ## KB1b — the residue-field carrier (the enumeration's tuple model). -/

/-- KB1b (layer record). One extension layer F′ = B[z]/(ψ) of the tuple-model
residue-field tower (script class `Ext`, l1_boundary_enum.py:92-133): ψ as data
(low → high coefficient tuple, length g+1) with the carrier laws as fields —
ψ monic, ψ(0) ≠ 0, ψ irreducible (the law is stated against the Polynomial B
transcription of the tuple; the CARRIER itself stays the script's tuple
`Fin g → B`).  Q2 ADJUDICATED: the tuple model is the default; AdjoinRoot only
if the seam unit KB11 demands it.
deps: KB1a (a layer's `g` instantiates a `StageData.g` at use sites — tied at
KB1c's gate and in the sibling cluster's KB4/KB8a). -/
structure ExtCarrier (B : Type) [Field B] where
  g : ℕ
  g_pos : 0 < g
  ψ : Fin (g + 1) → B
  ψ_monic : ψ (Fin.last g) = 1
  ψ_const_ne : ψ 0 ≠ 0
  ψ_irred : Irreducible (∑ i : Fin (g + 1), C (ψ i) * X ^ (i : ℕ))

namespace ExtCarrier

variable {B : Type} [Field B] (E : ExtCarrier B)

/-- KB1b. The tuple carrier (script `Ext` elements: length-g tuples of
base-field elements, low → high). -/
def Carrier : Type := Fin E.g → B

/-- KB1b. ψ as a polynomial — the transcription the `ψ_irred` field displays. -/
noncomputable def ψpoly : Polynomial B :=
  ∑ i : Fin (E.g + 1), C (E.ψ i) * X ^ (i : ℕ)

/-- KB1b. A tuple as a polynomial of degree < g. -/
noncomputable def toPoly (v : E.Carrier) : Polynomial B :=
  ∑ i : Fin E.g, C (v i) * X ^ (i : ℕ)

/-- KB1b. Truncating read-back (the deg < g representative's tuple). -/
def ofPoly (q : Polynomial B) : E.Carrier := fun i => q.coeff i

def zero : E.Carrier := fun _ => 0

def one : E.Carrier := fun i => if (i : ℕ) = 0 then 1 else 0

def add (a b : E.Carrier) : E.Carrier := fun i => a i + b i

def neg (a : E.Carrier) : E.Carrier := fun i => -(a i)

/-- KB1b. Multiplication: convolve and reduce mod ψ (script `Ext.mul`),
via the Polynomial transcription and `modByMonic`. -/
noncomputable def mul (a b : E.Carrier) : E.Carrier :=
  E.ofPoly ((E.toPoly a * E.toPoly b) %ₘ E.ψpoly)

/-- KB1b. z̄, the residue-class generator (script `Ext.zbar`,
l1_boundary_enum.py:100-103): (0,1,0,…) at g ≥ 2; −ψ₀ at g = 1. -/
def zbar : E.Carrier :=
  if E.g = 1 then fun _ => -(E.ψ 0) else fun i => if (i : ℕ) = 1 then 1 else 0

/-- KB1b (carrier-law placeholder — the ONE sorried def of this file,
recorded).  The field structure on the tuple carrier: the quotient field
F′ = B[z]/(ψ) transported to the tuple presentation (well-defined since
ψ_irred).  Deliberately a def, NOT an instance — no silent instance search
may route through a sorried term.  Filling it (AdjoinRoot transport along
toPoly/ofPoly, or direct verification of the script ops above) is the KB1b
prover's job; consumers `letI := E.carrierField` explicitly.  (`@[reducible]`
per the compiler's class-typed-def rule; reducibility does NOT register it
for instance search, so the no-silent-instance fence stands.) -/
@[reducible] noncomputable def carrierField : Field E.Carrier := sorry

end ExtCarrier

/-! ## KB1c — NON-VACUITY gate: the p = 2 stage-3 probe instance. -/

/-- KB1c (data). Stage-1 side data of the p = 2 stage-3 probe point:
(e₁,h₁,g₁) = (2,1,1) — the head of grid_s1, l1_boundary_enum.py:370. -/
def s1P2 : StageData :=
  ⟨2, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- KB1c (data). Stage-2 side data of the probe point: (e₂,g₂) = (2,1) with
h₂ = e₂·e₁h₁g₁ + 1 = 5, the script's (I-aug) grid choice
(l1_boundary_enum.py:378). -/
def s2P2 : StageData :=
  ⟨2, 5, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- KB1c (data). The two-stage tower at the probe point; the (I-aug) chain
field holds by evaluation (2·(2·1·1) = 4 < 5). -/
def towerP2 : TowerData := ⟨1, ![s1P2, s2P2], by decide⟩

/-- KB1c — NON-VACUITY GATE against KB1a+KB1b.  SEALED PREDICTION: PASSES —
the probe grid realizes this instance at p = 2, stage 3, with ψ₁ = z + 1 over
F₂ (degree 1, monic, ψ₁(0) = 1 ≠ 0, irreducible) and ψ₂ = z + 1̄ over
F₂[z]/(ψ₁); the record surface is inhabited at the p = 2 stage-3 probe point.
deps: KB1a, KB1b.  Sketch: exhibit the two layers; the degree-1 laws by
decide/norm_num (a monic degree-1 polynomial over a field is irreducible);
the stacking field instance through `ExtCarrier.carrierField`. -/
theorem stage3_instance_p2 :
    ∃ E1 : ExtCarrier (ZMod 2), E1.g = (towerP2.stage 0).g ∧
      ∃ inst : Field E1.Carrier, ∃ E2 : @ExtCarrier E1.Carrier inst,
        E2.g = (towerP2.stage 1).g := by
  sorry

/-! ## KB2 — slot arithmetic. -/

/-- KB2 (def). The forced slot class j₀ := h⁻¹·W mod e, via the unit
h ∈ (ZMod e)ˣ (gcd(e,h) = 1, `ZMod.unitOfCoprime`).  At e = 1 the ring ZMod 1
is trivial and j₀ = 0 — the script's `if e > 1 else 0` branch
(l1_boundary_enum.py:202) is absorbed by the ZMod typing.
deps: KB1a.  Sketch: ZMod.unitOfCoprime + omega (per blueprint §4 KB2). -/
def j0 (s : StageData) (W : ℕ) : ℕ :=
  ((((ZMod.unitOfCoprime s.h s.cop.symm)⁻¹ : (ZMod s.e)ˣ) : ZMod s.e)
    * (W : ZMod s.e)).val

/-- KB2. j₀ < e (so slot 0 sits inside the coefficient space).
Sketch: `ZMod.val_lt` with `NeZero s.e` from `e_pos`. -/
theorem j0_lt (s : StageData) (W : ℕ) : j0 s W < s.e := by
  sorry

/-- KB2. The defining congruence j₀·h ≡ W (mod e).
Sketch: cast the val back (`ZMod.natCast_val`/`ZMod.cast_id`), cancel the
unit `ZMod.unitOfCoprime s.h _` against its inverse. -/
theorem j0_mul_h (s : StageData) (W : ℕ) :
    ((j0 s W * s.h : ℕ) : ZMod s.e) = (W : ZMod s.e) := by
  sorry

/-- KB2 (def). The k-th slot j₀ + e·k of the offset-P development. -/
def slot (s : StageData) (W k : ℕ) : ℕ := j0 s W + s.e * k

/-- KB2. Slots stay in the coefficient space: slot ≤ eg − 1 for k < g.
Sketch: `j0_lt` + omega. -/
theorem slot_le (s : StageData) (W : ℕ) {k : ℕ} (hk : k < s.g) :
    slot s W k ≤ s.e * s.g - 1 := by
  sorry

/-- KB2. Every slot lies in the SINGLE class j₀ mod e and carries a
zero-class summand weight: (j₀+ek)·h ≡ W (mod e).  (REV 2, F1: all slots
share the one class j₀ mod e — single-class membership is the independent
reader's own check, l1_boundary_enum.py:227; slot SEPARATION is positional,
i.e. injectivity of k ↦ j₀+ek, and belongs to KB5/KB8a.)
Sketch: `j0_mul_h` + push_cast; e·k·h ≡ 0. -/
theorem slot_mul_h (s : StageData) (W k : ℕ) :
    ((slot s W k * s.h : ℕ) : ZMod s.e) = (W : ZMod s.e) := by
  sorry

/-- KB2. e ∣ W − (j₀+ek)·h (ℕ-subtraction guarded by `hle`; the guard is
discharged above threshold by KB3's `slot_mul_h_lt`).
Sketch: `slot_mul_h` + `ZMod.natCast_self_eq_zero` bookkeeping
(`Nat.modCast` sub lemmas). -/
theorem slot_weight_dvd (s : StageData) (W k : ℕ)
    (hle : slot s W k * s.h ≤ W) :
    s.e ∣ W - slot s W k * s.h := by
  sorry

/-- KB2 (def). u_k := (W − (j₀+ek)·h)/e — the required parent-parent-scale
weight of the k-th summand (exact by `uk_spec`; ℕ-valued by construction). -/
def uk (s : StageData) (W k : ℕ) : ℕ := (W - slot s W k * s.h) / s.e

/-- KB2. u_k is EXACT: e·u_k + (j₀+ek)·h = W under the `hle` guard — the
"u_k ∈ ℕ with e·u_k + (j₀+ek)h = W" clause of the blueprint.
deps: `slot_weight_dvd`.  Sketch: `Nat.div_mul_cancel` + omega. -/
theorem uk_spec (s : StageData) (W k : ℕ) (hle : slot s W k * s.h ≤ W) :
    s.e * uk s W k + slot s W k * s.h = W := by
  sorry

/-! ## KB3 — the guard chain (the two-line (I-aug) inequality,
MOVES 2450-2455). -/

/-- KB3 (eligibility of the `hle` guard).  Above the clean threshold every
slot weight clears W strictly: (j₀+ek)·h < W for k < g.
Sketch: slot ≤ eg−1 (KB2), so slot·h ≤ (eg−1)·h = egh − h < ehg < W. -/
theorem slot_mul_h_lt (s : StageData) {W : ℕ} (hW : s.thr < W) {k : ℕ}
    (hk : k < s.g) : slot s W k * s.h < W := by
  sorry

/-- KB3 (first line of the two-line chain).
e·u_k = W − (j₀+ek)·h ≥ W − (eg−1)·h > ehg − (eg−1)·h = h.
All in ℕ with the e-divisibility from KB2 — no rational division. -/
theorem h_lt_e_mul_uk (s : StageData) {W : ℕ} (hW : s.thr < W) {k : ℕ}
    (hk : k < s.g) : s.h < s.e * uk s W k := by
  sorry

/-- KB3 — THE GUARD CHAIN (second line).  W > ehg ⟹ every summand weight u_k
clears the threshold one stage down: (I-aug) h > e·thr_prev gives
e·u_k > h > e·thr_prev, hence u_k > thr_prev — the recursive calls are
ELIGIBLE (blueprint L1-ii).
deps: KB1a, KB2.  Sketch: `h_lt_e_mul_uk` + `Nat.lt_of_mul_lt_mul_left`. -/
theorem guard_chain (prev s : StageData) (hIaug : IAug prev s) {W : ℕ}
    (hW : s.thr < W) {k : ℕ} (hk : k < s.g) : prev.thr < uk s W k := by
  sorry

/-- KB3 (tower form). The guard along a `TowerData`'s own (I-aug) chain
field: at every consecutive pair of tower stages, weights above the upper
stage's threshold recurse eligibly into the lower stage. -/
theorem guard_chain_tower (T : TowerData) (i : Fin T.len) {W : ℕ}
    (hW : (T.stage i.succ).thr < W) {k : ℕ}
    (hk : k < (T.stage i.succ).g) :
    (T.stage i.castSucc).thr < uk (T.stage i.succ) W k := by
  sorry

/-! ## KB10 — negative controls as theorems (GATE UNIT; sequenced BEFORE the
KB5 prover, REV 2 F5).  SEALED PREDICTIONS (probe §3, all PASS on record):
NC1 — the corrupted slot class j₀+1 leaves the zero class at every summand;
NC3 — the (I-aug) violation h₂ = e₂·e₁h₁g₁ − 1 trips the recursion guard at
the minimal eligible W₃.  (NC2, reader class-distinction, needs the `digRead`
vocabulary — KB8a/KB9 territory, sibling cluster.) -/

/-- KB10/NC1 — GATE.  The corrupted slot class j₀+1 leaves the zero class:
((j₀+1)+ek)·h ≢ W (mod e) at every summand k < g — transcribed AT THE
SCRIPT'S OWN SCOPE e ≥ 2 (REV 2, F1: at e = 1 every weight is zero-class
mod 1 and the control is VACUOUS; never quantify over e = 1).  The script's
`(j0+1) % e` wrap (l1_boundary_enum.py:434) is absorbed by the ZMod typing;
the script's run point is (p,e,h,g) = (3,2,1,2), W = 5.
deps: KB2.  Sketch: `slot_mul_h` shifts the corrupted read to W + h mod e;
h ≢ 0 mod e since gcd(e,h) = 1 and e ≥ 2. -/
theorem nc1_corrupted_slot (s : StageData) (he : 2 ≤ s.e) (W : ℕ) {k : ℕ}
    (hk : k < s.g) :
    (((j0 s W + 1 + s.e * k) * s.h : ℕ) : ZMod s.e) ≠ (W : ZMod s.e) := by
  sorry

/-- KB10/NC3 (data). The (I-aug)-violating stage-2 side data:
h₂ = e₂·e₁h₁g₁ − 1 = 3 over stage 1 = `s1P2` (script NC3 verbatim,
l1_boundary_enum.py:448-459). -/
def s2Bad : StageData :=
  ⟨2, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- KB10/NC3 (violation record). `s2Bad` indeed violates (I-aug) over
`s1P2`: h₂ = 3 < 4 = e₂·(e₁h₁g₁).  Sketch: decide. -/
theorem s2Bad_iaug_violated : ¬ IAug s1P2 s2Bad := by
  sorry

/-- KB10/NC3 — GATE.  At the minimal eligible W₃ = e₂h₂g₂ + 1 = 7 the
recursion guard trips: u₀ = (7 − 1·3)/2 = 2 ≤ 2 = e₁h₁g₁ (the guard demands
u_k > e₁h₁g₁; script NC3 expects exactly this `Partial`).  Together with
`guard_chain` this is the gate's teeth: the guard PASSES under (I-aug)
(KB3) and TRIPS on its violation (here).
deps: KB2, KB3.  Sketch: decide/norm_num on the concrete numerals. -/
theorem nc3_guard_trips : uk s2Bad (s2Bad.thr + 1) 0 ≤ s1P2.thr := by
  sorry

end LeanUrat.Kernels.D4R0K
