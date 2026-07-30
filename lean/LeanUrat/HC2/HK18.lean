/-
Unit HK-18  (BRIDGE campaign, area BP2, cluster BP2-c2 — E-phase statement skeleton)
blueprint: lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md §4 Block G, unit HK-18.

INFORMAL STATEMENT (blueprint): "The quartic f + node ν₁ data: f := Φ̂² + 2·Φ̂ (or the
minimal variant making read 1 a clean ADJACENT side: s0₁ + wSide₁ = μ₀ = 1, e₁ = 1,
g₁ = 1); define ν₁'s fields (species increment, line/gam/ustar per the γ-tie at
STR₁ = 1, pat from the side digits of B₀ = 2·Φ̂); prove ν₁'s Node law fields."
Φ̂ := U31's landing key = `U31.fq` (`landingKey_ν₀ : LandingKey ν₀ fq` — the recorded
lift of ψ₂ = z² + z + 1 at the (1,1) read, g = 2).  deps: HK-15 (σ₁, the S9-built child
stage — NOT YET ON DISK, so σ₁ enters as a parameter here; see PARAMETERIZATION below).

E-PHASE RESOLUTIONS (recorded per the statement-writer charge; ALL THREE are forced by
the frozen MovesC `Node`/`HistoryCoherent` laws, not free choices — flagged for the
orchestrator/adjudication record):

(R-1) THE VARIANT IS TAKEN: `fgate := Φ̂² + 2·Φ̂ + 16`, NOT the primary `Φ̂² + 2·Φ̂`.
  The primary has NO coherent read 1: its Φ̂-development (0, 2, 1) has child-polygon
  side (e,h) = (1,1) through slots 1–2 (child weights 1, 0), which fails BOTH IAug
  (1 > 1·bStage.w Φ̂ = 2 is false) and coherence's strict line steepening
  (slope₁ = 1/2 < slope₀ = 1); at the steep pair (1,3) the minimizing set degenerates
  to the single slot 1 (wSide₁ = 0), whose recorded Ranch is a nonzero CONSTANT,
  contradicting `Node.hOrd`/`Node.hμ` (ψ^μ ∤ const at μ ≥ 1). Adding the slot-0
  coefficient C 16 (child weight 1·bw(16) + 0·3 = 4) realizes the blueprint's OWN
  parenthetical: a clean ADJACENT side s0₁ + wSide₁ = 0 + 1 = 1 = μ₀ at the steep pair
  (e₁, h₁) = (1, 3), γ₁ = 4, with slot 2 strictly above (0 + 2·3 = 6 > 4). The
  Φ̂-development becomes (16, 2, 1); HK-20's displayed "(0, 2, 1)" updates accordingly
  (the 2·Φ̂ digit at the vertex slot is unchanged — the (HV)-relevant datum).

(R-2) ν₁.species := recentering, NOT the sketch's word "increment". At read 1 the
  window containment s0₁ + wSide₁ ≤ μ₀ = 1 forces wSide₁ ≤ 1; wSide₁ = 0 dies by (R-1)'s
  hOrd argument, so wSide₁ = 1, e₁ = 1 (e ∣ wSide), deg Ranch₁ = 1, hence g₁ = 1
  (hOrd: ψ₁^μ ∥ Ranch₁ at μ₁ ≥ 1 forces deg ψ₁ = 1). So e₁·g₁ = 1 and `Node.hspecInc`
  (increment → 1 < e·g) EXCLUDES increment; recentering is the unique legal non-root
  species (hspecRec: e = g = 1 ✓; hspecRecCenter realized: ψ₁ = z − 1 over char 2,
  center₁ = 1 = zbar₁). NOTE the gate's de-vacuification target is UNAFFECTED: the
  (NEW) transition at i = 0 keys on the PARENT'S species (ν₀ root ≠ recentering) with
  e₀·g₀ = 2 — the steep non-recentering leg fires exactly as Block G intends.

(R-3) The gate ROOT node `ν₀gate` is NOT `U31.ν₀` verbatim: fgate's base-development
  coefficient valuations are (3, 2, 1, 2, 0), so the (1,1) root side has total weight
  γ₀ = 3 attained at slots 0–2 (fq's was γ = 2). ν₀gate re-dresses U31's node at
  (gam, ustar, line) := (3, 1, ⟨3, 1⟩); every other datum (σ = bStage, (e,h) = (1,1),
  (s,t) = (1,0), g = 2, μ = 1, a = 0, s0 = 0, wSide = 2, Dwidth = 1, ψ = Ranch = ψ₂,
  pat ≡ 1, zbar = U31.ν₀.zbar, lift = 0) is U31.ν₀'s. γ-tie: 3 = 1·(1·1) + 2·1 ✓;
  hLineU: 3 − 1·2 = 1 ✓; slope law: 1·(1·1·1) = 1 ✓.

PARAMETERIZATION (dep HK-15 not yet on disk): ν₁'s frame is HK-15's child stage σ₁
(built by S9c at bStage/ψ₂/Φ̂ = fq at the NEXT pair (1,3), zbar₀ = U31.ν₀.zbar). Here
σ₁ is a `Stage 2 F4` parameter together with the single pin its law fields consume,
`hΦ : σ₁.Φ = U31.fq` (only `hDwidth` needs it). P-phase re-binds to HK-15's concrete σ₁
(whose `TransitionData.child_key` supplies hΦ).

PROOF SKETCH for the sorried Node law fields (all verified by hand-computation above):
ν₀gate: ψ₂ laws = U31's private `ψ₂_monic/ψ₂_natDegree/ψ₂_irr/ord_ψ₂/root_eval₂ ∘ r₀_prop`
(de-privatize or reprove); hRanch = U31.mkNode's `hRanch` verbatim; hLineU/hAnchor
arithmetic. ν₁gate: ψ₁ = X − C 1 linear (monic/deg/irr routine); hOrd: (X+1)¹ ∥ X + 1
over the char-2 field ↥σ₁.K; hzbarRoot: eval₂ 1 (X − C 1) = 1 − 1 = 0; hDwidth from hΦ
+ `U31.fq_natDegree`; hspecRecCenter second conjunct: both sides are 1 (map_one).
`ν₁gate` carries the polOM lift via the aux-node pattern (polOM is `blind`, so
`liftOf ν₁gate = liftOf ν₁aux` and SideReads clause (v) closes — HK-20's duty).

Estimated laws difficulty: routine-opus (~80 per blueprint).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U31_gateReadsOf

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK18

/-- **The gate quartic** (HK-18, resolution R-1): `fgate := Φ̂² + 2·Φ̂ + 16` at
Φ̂ = `U31.fq` = X² + 2X + 4 — the minimal adjacent-side variant of the blueprint's
`Φ̂² + 2·Φ̂` (see the file header for the forcing computation). In X-coordinates:
`fgate = X⁴ + 4X³ + 14X² + 20X + 40`, coefficient 2-valuations (3, 2, 1, 2, 0). -/
noncomputable def fgate : Polynomial ℤ_[2] :=
  U31.fq ^ 2 + Polynomial.C 2 * U31.fq + Polynomial.C 16

/-- fgate is monic (consumed by HK-22's `ReadsOf` head clause). -/
theorem fgate_monic : fgate.Monic := by
  sorry

/-- fgate is quartic (consumed by HK-22's `ReadsOf` head clause at n = 4). -/
theorem fgate_natDegree : fgate.natDegree = 4 := by
  sorry

/-- **The gate root node** (HK-18, resolution R-3): U31's inert root read, re-dressed
for fgate's base side — γ₀ = 3 at slots 0–2 of the (1,1) side, ustar = 1,
line = ⟨3, 1⟩ (intercept 3, slope 1). All other data are `U31.ν₀`'s. -/
noncomputable def ν₀gate : Node 2 F4 where
  species := ReadSpecies.root
  σ := U31.bStage
  e := 1
  h := 1
  s := 1
  t := 0
  g := 2
  μ := 1
  a := 0
  s0 := 0
  wSide := 2
  Dwidth := 1
  line := ⟨3, 1⟩
  ustar := 1
  gam := 3
  zbar := U31.ν₀.zbar
  center := 0
  lift := 0
  ψ := U31.ψ₂
  pat := fun _ => 1
  Ranch := U31.ψ₂
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := by norm_num
  hμ := le_refl 1
  hEdvd := one_dvd 2
  hDwidth := natDegree_X.symm
  hψmonic := sorry
  hψdeg := sorry
  hψirr := sorry
  hRanch := sorry
  hpat0 := sorry
  hpatTop := sorry
  hAnchor := by norm_num
  hLineU := sorry
  hOrd := sorry
  hzbarRoot := sorry
  hspecInc := by intro h; simp at h
  hspecRec := by intro h; simp at h
  hspecRecCenter := by intro h; simp at h

/-- **The read-1 node, pre-lift** (HK-18, resolutions R-1/R-2): the ADJACENT
recentering-species read of fgate in the child frame σ₁ (HK-15's stage, here a
parameter with the `σ₁.Φ = fq` pin) — steep pair (e₁, h₁) = (1, 3), Bézout (1, 0),
side slots 0–1 (s0 = 0, wSide = 1, adjacent to μ₀ = 1), γ₁ = 4, ustar₁ = 1,
line₁ = ⟨4, 3/2⟩ (slope law: (3/2)·(1·1·2) = 3), descend data ψ₁ = z − 1 (char 2:
= z + 1), g₁ = 1, μ₁ = 1, a₁ = 0, pattern (1, 1), Ranch₁ = z + 1, zbar₁ = center₁ = 1,
Dwidth₁ = 2 = deg fq. The `lift` field is the junk 0 — `ν₁gate` below installs the
polOM lift (the blind-policy aux pattern; SideReads (v) needs `lift = liftOf`). -/
noncomputable def ν₁aux (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) : Node 2 F4 where
  species := ReadSpecies.recentering
  σ := σ₁
  e := 1
  h := 3
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 2
  line := ⟨4, 3/2⟩
  ustar := 1
  gam := 4
  zbar := 1
  center := 1
  lift := 0
  he := le_refl 1
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := sorry
  ψ := Polynomial.X - Polynomial.C 1
  pat := fun _ => 1
  Ranch := Polynomial.X + 1
  hψmonic := sorry
  hψdeg := sorry
  hψirr := sorry
  hRanch := sorry
  hpat0 := sorry
  hpatTop := sorry
  hAnchor := by norm_num
  hLineU := sorry
  hOrd := sorry
  hzbarRoot := sorry
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, sorry⟩

/-- **The read-1 node** ν₁ (HK-18): `ν₁aux` carrying the polOM lift. Since `polOM` is
`blind` (reads only (σ, center), never the lift field), `(polOM 2 F4).liftOf (ν₁gate …)
= (polOM 2 F4).liftOf (ν₁aux …) = (ν₁gate …).lift` — SideReads clause (v)'s lift leg
(HK-20) closes by `CanonPolicy.blind`. -/
noncomputable def ν₁gate (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) : Node 2 F4 :=
  { ν₁aux σ₁ hΦ with lift := (polOM 2 F4).liftOf (ν₁aux σ₁ hΦ) }

/-- The recorded read-1 pair is the steep gate pair (1, 3) — the pair HK-47's
`TransHyp` assembly and HK-15's S9c instantiation are keyed at (rfl-grade; the
blueprint's `(ν₁.e, ν₁.h)` binders resolve to these literals). -/
theorem ν₁gate_pair (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) :
    (ν₁gate σ₁ hΦ).e = 1 ∧ (ν₁gate σ₁ hΦ).h = 3 :=
  ⟨rfl, rfl⟩

/-- The read-1 window is ADJACENT to the root vertex: s0₁ + wSide₁ = 1 = μ₀ —
coherence's window-containment clause at the gate holds with equality (the HK-21
certificate's adjacency leg; also the (SAE)/(HV) branch selector). -/
theorem ν₁gate_adjacent (σ₁ : Stage 2 F4) (hΦ : σ₁.Φ = U31.fq) :
    (ν₁gate σ₁ hΦ).s0 + (ν₁gate σ₁ hΦ).wSide = ν₀gate.μ :=
  rfl

end HK18

end LeanUrat.MovesJ
