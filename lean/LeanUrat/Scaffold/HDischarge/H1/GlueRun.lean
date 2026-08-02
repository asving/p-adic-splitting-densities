/-
SITE-EXH EXTENSION — `H1/GlueRun.lean`: **E-3, THE COMPOSITION GLUE**
(the extension's "one genuinely new obligation" — `TruncatedRun.lean` header "WHAT IS
NOT CLAIMED" + deviation D-3; design display `SiteExhProbe.lean` header E-3; ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`).

## WHAT LANDS HERE

* **THE STRUCTURAL GLUE (E-3 main theorem)** — `truncRunFrom_glue`: a truncated run
  from σ₀ (`H₁`) followed by a truncated run from a stage σ₁ its ending read
  designated-lands (`H₂`) glues to a truncated run from σ₀ on the concatenated
  history, PROVED, with the junction packet `GlueJunction` carrying EXACTLY the
  clauses the `TruncRunFrom` definition forces and nothing else.  `readsOfFrom_glue`
  is the displayed (StageCoreL-tagged) form: the base tag σ₀ rides through; the
  junction tag hσ₁ is definitionally inert (kernel core-free, deviation D-2).
* **THE JUNCTION GEOMETRY (worked out from the definition, per the charge).**  Write
  L₁ := |H₁|, L₂ := |H₂|, S := the total stretch ∏ e of H₁ (`History.strTotal`).
  The glued object is `H₁.nodes ++ (H₂-shifted)` where the SHIFT is forced two ways:
  (α) **the stretch shift** — [T-1]/[T-2] read the accumulated stretch from the
  run's OWN base, so every H₂ node re-enters at `strFrame = S·(own strFrame)`; its
  line/ustar data rescale by 1/S (`Node.stretch`; the γ-weight `gam` is stage-scale
  and does NOT move — the scale-invariance is the [T-2] proof).  (β) **the
  re-speciing shift** — `History.root_iff` forces every base node to ROOT species,
  and forces every NON-base node off it, so H₂'s base node re-enters re-specied
  (`Node.respec`, target species `sp'` ∈ {increment, recentering} with the node
  species-laws as packet obligations).  The packet then carries, exactly:
  (i) the five PAIR-FREE seam clauses ([T-4]/[T-3] frame-chain content at the seam
  index L₁−1: Bézout ties at the junction frame, window containment, width chain,
  strict steepening ON THE GLUED SCALE — the 1/S divisor is visible in `seam_steep`);
  (ii) the SPECIES-KEYED seam legs, forced ONLY when the seam is interior (L₁ ≥ 2) —
  **the RG-2 fence survives verbatim**: a non-recentering H₁-ending read with e ≥ 2
  admits NO interior seam (`seam_nonrec` demands e = 1), so an e ≥ 2 junction read is
  gluable ONLY as the BASE of the glued run (L₁ = 1, where [T-4] is pair-free) — the
  fence is NOT lifted (E-4), it is re-displayed at the seam;
  (iii) `ends_at` — H₁'s ending read re-designated at the junction key (its own [T-5]
  leaves the final Φnext free; the glue pins it to σ₁'s key);
  (iv) `junc_bundle` — **the promoted base read's FULL [T-5] bundle**: in the glued
  run H₂'s base read sits at interior index L₁ > 0, so the complete `SideReads`
  bundle is forced there.  H₂'s own runhood does NOT carry it (the E-1 base read
  deliberately dropped it — deviation D-1), so it is a genuine junction hypothesis:
  deviation D-1's open additive refinement, resurfacing as THE junction obligation.
  Its `LandingKey` re-species through the packet (the recentering face needs the
  recorded lift clauses; the increment face re-uses the root-face `IsNodeLift`);
  (v) the promoted transition legs out of the junction read (`junc_rec`/`junc_nonrec`,
  forced only at L₂ ≥ 2; the fence again: `junc_nonrec` demands e = 1).
* **THE CARRY-CONSTANT ADJUDICATION (the honest call the charge demanded).**  The
  glue is PURELY STRUCTURAL: no clause of `GlueJunction` computes a composite carry —
  the D-ITER constants do not enter the concatenation, because `TruncRunFrom`'s
  clauses are per-index and the junction bundle enters as a HYPOTHESIS.  Where the
  composite carry law genuinely lives: any general SUPPLIER of `junc_bundle` at a
  deep frame — deriving the classificand's deep-frame `SideReads` through the
  iterated development — must compute digits in the order-2 composite digit algebra,
  whose measured law is the two-constant ITER-LAW (strata probe 2026-08-08, row B2,
  0/804), NOT the single-ζ′ cyclic form (row B3-adj: ADJUDICATED FALSE at 22/28 mixed
  towers; kill-shot row N).  That obligation is displayed as the NAMED OPEN
  `DIterJunctionSupplier` below — stated, never asserted, cyclic form fenced out by
  the docstring.
* **E-3's f-tie (task 2), at the honest strength the definitions give.**  Two forms:
  (a) `readsOf_glue` — a coherent FULL run + a truncated run from a stage it reaches
  MERGE into a single truncated run from the full run's own root frame, conditional
  on the packet (for a full H₁ the seam legs at L₁ ≥ 2 force the ending read to
  e = 1 or recentering — full runs ending at an e ≥ 2 read do NOT merge; that IS the
  fence, disclosed);
  (b) `FTiedTruncLanding` + `ftie_extends` — the UNCONDITIONAL chain form: recorded
  coverage along f extends as the PAIR (full run on f reaching σ₁ at its ending
  read's designated landing) × (truncated run from σ₁ READING THE SAME f, landing
  Φ' at its base read).  What f-tied coverage NOW READS: recorded carriers ∪
  f-tied truncated landings (`FTiedTruncLanding`, the chain) ∪ merged truncated runs
  from the root (`readsOf_glue`, packet-conditional) — against the pre-E-3 state
  where the truncated leg was f-UNTIED (`OnTruncatedCarrier`'s f₀ existential).
* **GATES (all zero-sorry; the honest scoping of each is part of the record).**
  - `gate_truncRun_H₂rc` — a compiled truncated run from HK25's gate child σ₁rec
    READING U31's fq (= σ₁rec's own key, `σ₁rec_Φ`) whose base read is the RCW
    recentering read ν₁rc (root-respecied) with designated landing σ₂rc.Φ: the
    S10-fired recentering key, landed via a compiled `IsNodeLift` (realizer −rcLift,
    digit by `StageCore.R_neg` off the recorded `rcLift_R`).
  - `gate_ftie_chain` — **the f-tie chain FIRES END-TO-END on compiled tower data**:
    `FTiedTruncLanding 2 fq σ₁rec σ₂rc.Φ` — U31's full ReadsOf run on fq reaches
    σ₁rec (its root read's recorded `SideReads` designated-lands fq = σ₁rec.Φ), and
    the truncated continuation from σ₁rec lands the RCW recentering's fired key:
    the first f-TIED deep landing on file.  Honest scope: this is the RCW gate
    tower (junction read e = 1), NOT the BM2_TRACE §C-e p = 3 quartic — that tower
    is numerics-only (not formalized; `SiteExhProbe` header records this), so the
    C-e e = 2 escapee is hosted by THIS unit only in the theorem-schema sense: the
    glue theorem hosts any e ≥ 2 junction read at the glued BASE (L₁ = 1) given its
    packet, and no compiled e ≥ 2 instance exists on file to feed it.
  - `gate_glue_junction` + `gate_glue_conditional` — at the same tower data, EVERY
    `GlueJunction` field except `junc_bundle` is discharged concretely
    (`gate_glue_junction` builds the packet FROM a bundle hypothesis), and the glue
    theorem then fires (`gate_glue_conditional`), producing the 2-node merged run
    from U31's root frame.  The one leg carried as hypothesis is exactly deviation
    D-1's wall: at the choice-built σ₁rec the bundle's clause (iii) reads the
    residual of an out-of-carrier element (`σ.R f` at deg f = deg Φ), unprovable
    and irrefutable from the stage interface — the same wall that made D-1's
    clauses (i)–(iii)/(vi) not-retained-at-the-base.  A fully discharged merged
    gate therefore needs a genuinely deep compiled run (deg f > deg Φ₁ with real
    digit data) — a U31-scale follow-up unit, priced below with the named open.

## WHAT IS NOT CLAIMED

No general supplier of `junc_bundle` (the D-ITER transport — the named open, ITER-LAW
shape mandatory).  No claim that the p = 3 quartic C-e instance is compiled (numerics
only).  No fence lift anywhere: RG-2 appears VERBATIM in the seam/promotion legs
([E-4]).  `TruncRunFrom`/`ReadsOfFrom`/`ReadsOf`/`HistoryCoherent`/`SideReads` and all
of `TruncatedRun.lean`/`SiteExhProbe.lean` are byte-unchanged.  The glued object is a
TRUNCATED run — never claimed coherent/full (`HistoryCoherent`'s node-0 degree pin and
its own leg quantification are not asserted for it).
-/
import LeanUrat.Scaffold.HDischarge.H1.TruncatedRun

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

universe u

/-! ### §0 — carrier-side helpers (additive `MovesC` namespace extensions: head/last
node accessors, the total stretch, the stretch/respec node maps) -/

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- Every history has a node. -/
lemma History.hlen0 (H : History p F) : 0 < H.nodes.length := by
  cases h : H.nodes with
  | nil => exact absurd h H.nonempty
  | cons a l => simp

/-- The base node (index 0). -/
def History.headNode (H : History p F) : Node p F := H.nodes[0]'H.hlen0

/-- The ending node (index length − 1). -/
def History.lastNode (H : History p F) : Node p F :=
  H.nodes[H.nodes.length - 1]'(by have := H.hlen0; omega)

/-- The TOTAL accumulated stretch `S = ∏ᵢ eᵢ` of a history — the frame-scale factor a
continuation run acquires when glued behind it. -/
def History.strTotal (H : History p F) : ℕ := H.strFrame H.nodes.length

lemma History.strFrame_pos (H : History p F) (i : ℕ) : 0 < H.strFrame i := by
  refine List.prod_pos ?_
  intro x hx
  obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp hx
  exact ν.he

lemma History.strTotal_pos (H : History p F) : 0 < H.strTotal :=
  H.strFrame_pos _

/-- **The stretch shift** (glue shift (α)): re-express a node recorded at a run's own
frame scale on a scale stretched by `S` — line and side height divide by `S`; every
other field (the stage-scale weight `gam` included) is untouched.  Only `hLineU`
mentions the moved fields, and it rescales. -/
def Node.stretch (ν : Node p F) (S : ℕ) (hS : 0 < S) : Node p F :=
  { ν with
    line := ⟨ν.line.intercept / (S : ℚ), ν.line.slope / (S : ℚ)⟩
    ustar := ν.ustar / (S : ℚ)
    hLineU := by
      show ν.line.intercept / (S : ℚ) -
          ν.line.slope / (S : ℚ) * (((ν.s0 + ν.wSide) * ν.Dwidth : ℕ) : ℚ)
        = ν.ustar / (S : ℚ)
      have h : ν.line.intercept - ν.line.slope * (((ν.s0 + ν.wSide) * ν.Dwidth : ℕ) : ℚ)
          = ν.ustar := ν.hLineU
      rw [div_mul_eq_mul_div, div_sub_div_same, h] }

/-- **The re-speciing shift** (glue shift (β)): change a node's recorded species,
re-supplying the three species laws.  The glue uses it in both directions: a base node
promoted into the interior leaves ROOT species (obligations = the packet's `sp_*`
fields); a node cut out as a new base re-enters AT root (obligations vacuous). -/
def Node.respec (ν : Node p F) (sp : ReadSpecies)
    (hinc : sp = ReadSpecies.increment → 1 < ν.e * ν.g)
    (hrec : sp = ReadSpecies.recentering → ν.e = 1 ∧ ν.g = 1)
    (hrecC : sp = ReadSpecies.recentering →
      ν.ψ = Polynomial.X - Polynomial.C ν.center ∧
      ((ν.zbar : Fˣ) : F) = ((ν.center : ↥ν.σ.K) : F)) : Node p F :=
  { ν with species := sp, hspecInc := hinc, hspecRec := hrec, hspecRecCenter := hrecC }

@[simp] lemma Node.stretch_species (ν : Node p F) (S : ℕ) (hS : 0 < S) :
    (ν.stretch S hS).species = ν.species := rfl
@[simp] lemma Node.stretch_slope (ν : Node p F) (S : ℕ) (hS : 0 < S) :
    (ν.stretch S hS).line.slope = ν.line.slope / (S : ℚ) := rfl
@[simp] lemma Node.respec_slope (ν : Node p F) (sp) (h₁ h₂ h₃) :
    (ν.respec sp h₁ h₂ h₃ : Node p F).line.slope = ν.line.slope := rfl
@[simp] lemma Node.respec_species (ν : Node p F) (sp) (h₁ h₂ h₃) :
    (ν.respec sp h₁ h₂ h₃ : Node p F).species = sp := rfl

end LeanUrat.MovesC

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesJ

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ### §1 — the junction packet: EXACTLY the clauses `TruncRunFrom` forces at the seam -/

/-- **The E-3 junction packet** — the exact agreement hypotheses the `TruncRunFrom`
clauses force when `H₁ ++ H₂-shifted` must again satisfy them (header: THE JUNCTION
GEOMETRY).  Abbreviations: `ν₁ := H₁.lastNode` (the seam read), `ν₂ := H₂.headNode`
(the junction read), `S := H₁.strTotal`.  NOTE the two RG-2 re-displays
(`seam_nonrec`, `junc_nonrec`): the fence is retained VERBATIM — an e ≥ 2
non-recentering read survives gluing only where no interior transition touches it. -/
structure GlueJunction (f₀ : Polynomial ℤ_[p]) (H₁ H₂ : History p F)
    (sp' : ReadSpecies) : Prop where
  /-- the junction read enters the glued interior (index L₁ ≥ 1): never root. -/
  sp_ne_root : sp' ≠ ReadSpecies.root
  /-- re-speciing law (increment face): genuine stage growth. -/
  sp_inc : sp' = ReadSpecies.increment → 1 < H₂.headNode.e * H₂.headNode.g
  /-- re-speciing law (recentering face): pair (1, ·), degree 1. -/
  sp_rec : sp' = ReadSpecies.recentering → H₂.headNode.e = 1 ∧ H₂.headNode.g = 1
  /-- re-speciing law (recentering face): recorded center shape. -/
  sp_recCenter : sp' = ReadSpecies.recentering →
    H₂.headNode.ψ = Polynomial.X - Polynomial.C H₂.headNode.center ∧
    ((H₂.headNode.zbar : Fˣ) : F) = ((H₂.headNode.center : ↥H₂.headNode.σ.K) : F)
  /-- seam pair-free clause 1: the Bézout s-tie at the junction frame. -/
  seam_s_tie : H₂.headNode.σ.e = 1 → H₂.headNode.σ.s = H₂.headNode.s
  /-- seam pair-free clause 2: the Bézout t-tie at the junction frame. -/
  seam_t_tie : H₂.headNode.σ.e = 1 → H₂.headNode.σ.t = H₂.headNode.t
  /-- seam pair-free clause 3: window containment across the seam. -/
  seam_window : H₂.headNode.s0 + H₂.headNode.wSide ≤ H₁.lastNode.μ
  /-- seam pair-free clause 4: the width chain across the seam (the frame agreement:
  `deg σ₁.Φ = ` the seam read's child width). -/
  seam_width : H₂.headNode.Dwidth = H₁.lastNode.childWidth
  /-- seam pair-free clause 5: strict steepening across the seam, ON THE GLUED SCALE
  (the junction read's slope re-enters divided by H₁'s total stretch). -/
  seam_steep : H₁.lastNode.line.slope
      < H₂.headNode.line.slope / (H₁.strTotal : ℚ)
  /-- species-keyed seam leg (recentering face) — forced only when the seam transition
  is INTERIOR (L₁ ≥ 2): the recorded recentering relation into the junction frame. -/
  seam_rec : 1 < H₁.nodes.length → H₁.lastNode.species = ReadSpecies.recentering →
    IsRecenteringCore H₁.lastNode.σ H₂.headNode.σ H₁.lastNode.center H₁.lastNode.lift
  /-- species-keyed seam leg (non-recentering face), THE RG-2 FENCE INCLUDED: an
  interior seam demands stride 1 + the (S-a) two-step transition records. -/
  seam_nonrec : 1 < H₁.nodes.length → H₁.lastNode.species ≠ ReadSpecies.recentering →
    H₁.lastNode.e = 1 ∧
    ∃ σV : Stage p F,
      RegradeOf H₁.lastNode.σ H₁.lastNode.e H₁.lastNode.h σV ∧
      IsNodeLift H₁.lastNode H₂.headNode.σ.Φ ∧
      TransitionCoreL σV H₂.headNode.σ H₂.headNode.σ.Φ H₂.headNode.e H₂.headNode.h
        H₁.lastNode.zbar
  /-- H₁'s ending read, re-designated at the junction key (H₁'s own [T-5] leaves the
  final Φnext free; the glued [T-5] pins it to σ₁'s key): development + (at an
  interior seam) the full bundle + the landing, all at `H₂.headNode.σ.Φ`. -/
  ends_at : ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
    IsDevelopment H₁.lastNode.σ.Φ f₀ B Nd ∧
    (1 < H₁.nodes.length → SideReads H₁.lastNode B Nd H₂.headNode.σ.Φ) ∧
    (LandingKey H₁.lastNode H₂.headNode.σ.Φ ∨
      IsStandardLift H₁.lastNode.σ H₁.lastNode.ψ H₁.lastNode.g H₂.headNode.σ.Φ)
  /-- **the promoted junction bundle** — the full [T-5] content at the junction read
  (interior at glued index L₁ > 0, so `SideReads` is forced UNCONDITIONALLY; H₂'s own
  runhood does not carry it — deviation D-1 resurfacing as THE junction obligation).
  Stated on H₂'s recorded (root-species) node; the recentering-face lift clauses ride
  along so `LandingKey` re-species (the increment face re-uses the root-face
  `IsNodeLift`; see `DIterJunctionSupplier` for what a general discharge costs). -/
  junc_bundle : ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
    IsDevelopment H₂.headNode.σ.Φ f₀ B Nd ∧
    (∀ h1 : 1 < H₂.nodes.length, Φnext = (H₂.nodes[1]'h1).σ.Φ) ∧
    SideReads H₂.headNode B Nd Φnext ∧
    (sp' = ReadSpecies.recentering →
      inC H₂.headNode.σ.Φ H₂.headNode.lift ∧ H₂.headNode.lift ≠ 0 ∧
      H₂.headNode.σ.w H₂.headNode.lift = H₂.headNode.σ.w H₂.headNode.σ.Φ ∧
      H₂.headNode.σ.R H₂.headNode.lift
        = LaurentPolynomial.C H₂.headNode.center * LaurentPolynomial.T 0 ∧
      Φnext = H₂.headNode.σ.Φ - H₂.headNode.lift)
  /-- promoted transition leg out of the junction read (recentering face) — forced
  only when H₂ continues (L₂ ≥ 2). -/
  junc_rec : ∀ h1 : 1 < H₂.nodes.length, sp' = ReadSpecies.recentering →
    IsRecenteringCore H₂.headNode.σ (H₂.nodes[1]'h1).σ H₂.headNode.center
      H₂.headNode.lift
  /-- promoted transition leg (non-recentering face), THE RG-2 FENCE AGAIN: a
  continuing junction read must have stride 1 unless recentering. -/
  junc_nonrec : ∀ h1 : 1 < H₂.nodes.length, sp' ≠ ReadSpecies.recentering →
    H₂.headNode.e = 1 ∧
    ∃ σV : Stage p F,
      RegradeOf H₂.headNode.σ H₂.headNode.e H₂.headNode.h σV ∧
      IsNodeLift H₂.headNode (H₂.nodes[1]'h1).σ.Φ ∧
      TransitionCoreL σV (H₂.nodes[1]'h1).σ (H₂.nodes[1]'h1).σ.Φ
        (H₂.nodes[1]'h1).e (H₂.nodes[1]'h1).h H₂.headNode.zbar

/-! ### §2 — the glued history: `H₁ ++ H₂-shifted` -/

/-- Index congruence for `getElem` on lists, subst-based (motive-safe). -/
private lemma getElem_idx_congr {α : Type*} (l : List α) {i j : ℕ} (hij : i = j)
    {hi : i < l.length} : l[i]'hi = l[j]'(hij ▸ hi) := by
  subst hij
  rfl

section Glue

variable (H₁ H₂ : History p F) (sp' : ReadSpecies)
variable (hne : sp' ≠ ReadSpecies.root)
variable (hinc : sp' = ReadSpecies.increment → 1 < H₂.headNode.e * H₂.headNode.g)
variable (hrec : sp' = ReadSpecies.recentering → H₂.headNode.e = 1 ∧ H₂.headNode.g = 1)
variable (hrecC : sp' = ReadSpecies.recentering →
    H₂.headNode.ψ = Polynomial.X - Polynomial.C H₂.headNode.center ∧
    ((H₂.headNode.zbar : Fˣ) : F) = ((H₂.headNode.center : ↥H₂.headNode.σ.K) : F))

/-- The shifted junction node: H₂'s base node, stretch-shifted and re-specied. -/
def glueJnc : Node p F :=
  (H₂.headNode.stretch H₁.strTotal H₁.strTotal_pos).respec sp' hinc hrec hrecC

/-- The shifted H₂ node list: the junction node, then the tail stretch-shifted. -/
def glueTail : List (Node p F) :=
  glueJnc H₁ H₂ sp' hinc hrec hrecC ::
    (H₂.nodes.drop 1).map (fun ν => ν.stretch H₁.strTotal H₁.strTotal_pos)

lemma glueTail_length :
    (glueTail H₁ H₂ sp' hinc hrec hrecC).length = H₂.nodes.length := by
  simp only [glueTail, List.length_cons, List.length_map, List.length_drop]
  have := H₂.hlen0
  omega

/-- Tail transport at 0: the junction node. -/
lemma glueTail_get_zero {h : 0 < (glueTail H₁ H₂ sp' hinc hrec hrecC).length} :
    (glueTail H₁ H₂ sp' hinc hrec hrecC)[0]'h = glueJnc H₁ H₂ sp' hinc hrec hrecC :=
  rfl

/-- Tail transport at `k + 1`: H₂'s tail node, stretch-shifted. -/
lemma glueTail_get_succ (k : ℕ) (hk2 : k + 1 < H₂.nodes.length)
    {h : k + 1 < (glueTail H₁ H₂ sp' hinc hrec hrecC).length} :
    (glueTail H₁ H₂ sp' hinc hrec hrecC)[k+1]'h
      = (H₂.nodes[k+1]'hk2).stretch H₁.strTotal H₁.strTotal_pos := by
  have hk' : k < ((H₂.nodes.drop 1).map
      (fun ν => ν.stretch H₁.strTotal H₁.strTotal_pos)).length := by
    simp only [List.length_map, List.length_drop]
    omega
  show (((H₂.nodes.drop 1).map
      (fun ν => ν.stretch H₁.strTotal H₁.strTotal_pos))[k]'hk') = _
  rw [List.getElem_map, List.getElem_drop]
  exact congrArg (fun ν : Node p F => ν.stretch H₁.strTotal H₁.strTotal_pos)
    (getElem_idx_congr H₂.nodes (by omega))

include hne in
/-- Every shifted node is off root species (the junction node by re-speciing, the
tail nodes by H₂'s own `root_iff`). -/
lemma glueTail_species_ne_root (k : ℕ)
    (hk : k < (glueTail H₁ H₂ sp' hinc hrec hrecC).length) :
    ((glueTail H₁ H₂ sp' hinc hrec hrecC)[k]'hk).species ≠ ReadSpecies.root := by
  have hkH : k < H₂.nodes.length := by
    rw [glueTail_length] at hk
    exact hk
  rcases k with _ | k'
  · rw [glueTail_get_zero]
    show sp' ≠ ReadSpecies.root
    exact hne
  · rw [glueTail_get_succ H₁ H₂ sp' hinc hrec hrecC k' hkH]
    show (H₂.nodes[k'+1]'hkH).species ≠ ReadSpecies.root
    intro hcon
    have := (H₂.root_iff (k'+1) hkH).mp hcon
    omega

/-- **The glued history** `H₁ ++ H₂-shifted` (root_iff: H₁'s nodes keep their species;
the junction node is re-specied off root; H₂'s tail nodes were non-root already). -/
def glueHistory : History p F where
  nodes := H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC
  nonempty := by
    intro hcon
    rcases List.append_eq_nil_iff.mp hcon with ⟨h1, -⟩
    exact H₁.nonempty h1
  root_iff := by
    intro j hj
    by_cases hjlt : j < H₁.nodes.length
    · rw [List.getElem_append_left hjlt]
      constructor
      · intro hsp
        exact (H₁.root_iff j hjlt).mp hsp
      · intro h0
        subst h0
        exact (H₁.root_iff 0 hjlt).mpr rfl
    · have hle : H₁.nodes.length ≤ j := Nat.le_of_not_lt hjlt
      have hL1 : 0 < H₁.nodes.length := H₁.hlen0
      rw [List.getElem_append_right hle]
      exact iff_of_false
        (glueTail_species_ne_root H₁ H₂ sp' hne hinc hrec hrecC _ _) (by omega)

lemma glue_length :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes.length
      = H₁.nodes.length + H₂.nodes.length := by
  show (H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC).length = _
  rw [List.length_append, glueTail_length]

/-- Index transport, H₁ range. -/
lemma glue_node_lo (i : ℕ) (hi : i < H₁.nodes.length)
    {h : i < (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes.length} :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes[i]'h = H₁.nodes[i]'hi :=
  List.getElem_append_left hi

/-- Index transport, the junction index L₁. -/
lemma glue_node_mid
    {h : H₁.nodes.length < (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes.length} :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes[H₁.nodes.length]'h
      = glueJnc H₁ H₂ sp' hinc hrec hrecC := by
  show (H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC)[H₁.nodes.length]'h = _
  rw [List.getElem_append_right (le_refl _),
    getElem_idx_congr _ (show H₁.nodes.length - H₁.nodes.length = 0 by omega),
    glueTail_get_zero]

/-- Index transport, H₂'s tail range (`k ≥ 1`). -/
lemma glue_node_hi (k : ℕ) (hk0 : 0 < k) (hk : k < H₂.nodes.length)
    {h : H₁.nodes.length + k
        < (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes.length} :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).nodes[H₁.nodes.length + k]'h
      = (H₂.nodes[k]'hk).stretch H₁.strTotal H₁.strTotal_pos := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show (H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC)[H₁.nodes.length + (k'+1)]'h = _
  rw [List.getElem_append_right (by omega),
    getElem_idx_congr _
      (show H₁.nodes.length + (k' + 1) - H₁.nodes.length = k' + 1 by omega),
    glueTail_get_succ H₁ H₂ sp' hinc hrec hrecC k' hk]

/-- The e-profile of the shifted tail is H₂'s own (stretch/respec keep `e`). -/
lemma glue_tail_mapE :
    (glueTail H₁ H₂ sp' hinc hrec hrecC).map Node.e = H₂.nodes.map Node.e := by
  simp only [glueTail, List.map_cons, List.map_map]
  have h1 : (glueJnc H₁ H₂ sp' hinc hrec hrecC).e = H₂.headNode.e := rfl
  have h2 : (Node.e ∘ fun ν : Node p F => ν.stretch H₁.strTotal H₁.strTotal_pos)
      = Node.e := rfl
  rw [h1, h2]
  have h3 : H₂.headNode :: H₂.nodes.drop 1 = H₂.nodes := by
    simpa [History.headNode] using List.getElem_cons_drop (as := H₂.nodes) (i := 0) H₂.hlen0
  conv_rhs => rw [← h3]
  simp

/-- Stretch transport, H₁ range (`i ≤ L₁`). -/
lemma glue_str_lo (i : ℕ) (hi : i ≤ H₁.nodes.length) :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).strFrame i = H₁.strFrame i := by
  show ((((H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC).take i).map Node.e)).prod = _
  rw [List.take_append]
  have h0 : i - H₁.nodes.length = 0 := by omega
  rw [h0, List.take_zero, List.append_nil]
  rfl

/-- Stretch transport, junction/tail range: the glued stretch at `L₁ + k` is H₁'s
total stretch times H₂'s own stretch at `k`. -/
lemma glue_str_hi (k : ℕ) :
    (glueHistory H₁ H₂ sp' hne hinc hrec hrecC).strFrame (H₁.nodes.length + k)
      = H₁.strTotal * H₂.strFrame k := by
  show ((((H₁.nodes ++ glueTail H₁ H₂ sp' hinc hrec hrecC).take
      (H₁.nodes.length + k)).map Node.e)).prod = _
  rw [List.take_append]
  have h1 : H₁.nodes.length + k - H₁.nodes.length = k := by omega
  rw [h1, List.take_of_length_le (by omega), List.map_append, List.prod_append]
  congr 1
  · show _ = H₁.strFrame H₁.nodes.length
    show _ = (((H₁.nodes.take H₁.nodes.length).map Node.e)).prod
    rw [List.take_of_length_le (le_refl _)]
  · show (((glueTail H₁ H₂ sp' hinc hrec hrecC).take k).map Node.e).prod = _
    rw [List.map_take, glue_tail_mapE, ← List.map_take]
    rfl

end Glue

/-! ### §3 — arithmetic helpers for the two rescaled per-node laws -/

private lemma slope_rescale {sl e str D hval S : ℚ} (hS : S ≠ 0)
    (h1 : sl * (e * str * D) = hval) :
    sl / S * (e * (S * str) * D) = hval := by
  field_simp
  linear_combination h1

private lemma gam_rescale {gam e str u rest S : ℚ} (hS : S ≠ 0)
    (h1 : gam = e * (str * u) + rest) :
    gam = e * ((S * str) * (u / S)) + rest := by
  have hcancel : (S * str) * (u / S) = str * u := by
    field_simp
  rw [hcancel]
  exact h1

/-! ### §4 — E-3 MAIN: the composition glue -/

/-- **E-3 (the structural glue), PROVED**: a truncated run from σ₀ followed by a
truncated run from the stage σ₁ its ending read designated-lands glues — under
EXACTLY the junction packet the clauses force — to a truncated run from σ₀ on
`H₁ ++ H₂-shifted`.  Purely structural: no composite carry constant enters (header,
THE CARRY-CONSTANT ADJUDICATION); the RG-2 fence survives verbatim inside the
packet's seam/promotion legs (E-4 honored). -/
theorem truncRunFrom_glue (σ₀ σ₁ : Stage p F) (f₀ : Polynomial ℤ_[p])
    (H₁ H₂ : History p F) (sp' : ReadSpecies)
    (hrun₁ : TruncRunFrom σ₀ f₀ H₁) (hrun₂ : TruncRunFrom σ₁ f₀ H₂)
    (J : GlueJunction f₀ H₁ H₂ sp') :
    TruncRunFrom σ₀ f₀
      (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter) := by
  obtain ⟨hT0₁, hT1₁, hT2₁, hT3₁, hT4₁, hT5₁⟩ := hrun₁
  obtain ⟨hT0₂, hT1₂, hT2₂, hT3₂, hT4₂, hT5₂⟩ := hrun₂
  have hlenG : (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec
        J.sp_recCenter).nodes.length
      = H₁.nodes.length + H₂.nodes.length :=
    glue_length H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
  have hL1 : 0 < H₁.nodes.length := H₁.hlen0
  have hL2 : 0 < H₂.nodes.length := H₂.hlen0
  have hSposQ : (0 : ℚ) < (H₁.strTotal : ℚ) := by
    exact_mod_cast H₁.strTotal_pos
  have hSne : ((H₁.strTotal : ℕ) : ℚ) ≠ 0 := ne_of_gt hSposQ
  -- H₁'s last node at its index form
  have hlast : ∀ (h : H₁.nodes.length - 1 < H₁.nodes.length),
      H₁.nodes[H₁.nodes.length - 1]'h = H₁.lastNode := fun _ => rfl
  -- H₂'s head node at its index form
  have hhead : ∀ (h : 0 < H₂.nodes.length), H₂.nodes[0]'h = H₂.headNode := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- [T-0] the frame pin: the glued base is H₁'s base
    intro hj
    rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter 0 hL1]
    exact hT0₁ hL1
  · -- [T-1] the slope law
    intro i hi
    by_cases hilt : i < H₁.nodes.length
    · rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i hilt,
        glue_str_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
          (le_of_lt hilt)]
      exact hT1₁ i hilt
    · obtain ⟨k, rfl⟩ : ∃ k, i = H₁.nodes.length + k :=
        ⟨i - H₁.nodes.length, by omega⟩
      have hk : k < H₂.nodes.length := by rw [hlenG] at hi; omega
      rw [glue_str_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [Nat.add_zero]
        rw [glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter]
        have h2 := hT1₂ 0 hL2
        rw [hhead hL2] at h2
        show H₂.headNode.line.slope / (H₁.strTotal : ℚ) *
            ((H₂.headNode.e : ℚ) * ((H₁.strTotal * H₂.strFrame 0 : ℕ) : ℚ)
              * (H₂.headNode.Dwidth : ℚ))
          = (H₂.headNode.h : ℚ)
        push_cast
        exact slope_rescale hSne h2
      · rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k
          hk0 hk]
        have h2 := hT1₂ k hk
        show (H₂.nodes[k]'hk).line.slope / (H₁.strTotal : ℚ) *
            (((H₂.nodes[k]'hk).e : ℚ) * ((H₁.strTotal * H₂.strFrame k : ℕ) : ℚ)
              * ((H₂.nodes[k]'hk).Dwidth : ℚ))
          = ((H₂.nodes[k]'hk).h : ℚ)
        push_cast
        exact slope_rescale hSne h2
  · -- [T-2] the γ-tie (gam is stage-scale: the S-factor cancels against ustar/S)
    intro i hi
    by_cases hilt : i < H₁.nodes.length
    · rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i hilt,
        glue_str_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
          (le_of_lt hilt)]
      exact hT2₁ i hilt
    · obtain ⟨k, rfl⟩ : ∃ k, i = H₁.nodes.length + k :=
        ⟨i - H₁.nodes.length, by omega⟩
      have hk : k < H₂.nodes.length := by rw [hlenG] at hi; omega
      rw [glue_str_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [Nat.add_zero]
        rw [glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter]
        have h2 := hT2₂ 0 hL2
        rw [hhead hL2] at h2
        show ((H₂.headNode.gam : ℤ) : ℚ)
          = (H₂.headNode.e : ℚ) * (((H₁.strTotal * H₂.strFrame 0 : ℕ) : ℚ)
              * (H₂.headNode.ustar / (H₁.strTotal : ℚ)))
            + (((H₂.headNode.s0 + H₂.headNode.wSide : ℕ)) : ℚ) * (H₂.headNode.h : ℚ)
        push_cast
        push_cast at h2
        exact gam_rescale hSne h2
      · rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k
          hk0 hk]
        have h2 := hT2₂ k hk
        show (((H₂.nodes[k]'hk).gam : ℤ) : ℚ)
          = ((H₂.nodes[k]'hk).e : ℚ) * (((H₁.strTotal * H₂.strFrame k : ℕ) : ℚ)
              * ((H₂.nodes[k]'hk).ustar / (H₁.strTotal : ℚ)))
            + ((((H₂.nodes[k]'hk).s0 + (H₂.nodes[k]'hk).wSide : ℕ)) : ℚ)
              * ((H₂.nodes[k]'hk).h : ℚ)
        push_cast
        push_cast at h2
        exact gam_rescale hSne h2
  · -- [T-3] the interior transition legs (four ranges: inside H₁ / the seam /
    -- the promoted junction transition / inside H₂)
    intro i hi0 hi
    by_cases hcase1 : i + 1 < H₁.nodes.length
    · -- (a) inside H₁
      rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
          (by omega),
        glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter (i+1)
          hcase1]
      exact hT3₁ i hi0 hcase1
    · by_cases hcase2 : i + 1 = H₁.nodes.length
      · -- (b) THE SEAM (interior: 0 < i forces L₁ ≥ 2) — the packet's seam legs
        have hiL : i = H₁.nodes.length - 1 := by omega
        have h1L : 1 < H₁.nodes.length := by omega
        have hilt : i < H₁.nodes.length := by omega
        rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
          hilt]
        have hnodei : H₁.nodes[i]'hilt = H₁.lastNode := by
          subst hiL
          rfl
        have hnodei1 : ∀ (h : i + 1 < (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes.length),
            (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[i+1]'h = glueJnc H₁ H₂ sp' J.sp_inc J.sp_rec J.sp_recCenter := by
          intro h
          have : i + 1 = H₁.nodes.length := hcase2
          simp only [this]
          exact glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
        rw [hnodei, hnodei1]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hsp
          exact J.seam_rec h1L hsp
        · intro hsp
          exact J.seam_nonrec h1L hsp
        · intro he1
          exact J.seam_s_tie he1
        · intro he1
          exact J.seam_t_tie he1
        · exact J.seam_window
        · exact J.seam_width
        · exact J.seam_steep
      · -- i ≥ L₁
        have hge : H₁.nodes.length ≤ i := by omega
        obtain ⟨k, rfl⟩ : ∃ k, i = H₁.nodes.length + k :=
          ⟨i - H₁.nodes.length, by omega⟩
        have hk1 : k + 1 < H₂.nodes.length := by rw [hlenG] at hi; omega
        have hnodei1 : ∀ (h : H₁.nodes.length + k + 1 < (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes.length),
            (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[H₁.nodes.length + k + 1]'h
              = (H₂.nodes[k+1]'hk1).stretch H₁.strTotal H₁.strTotal_pos := by
          intro h
          have harr : H₁.nodes.length + k + 1 = H₁.nodes.length + (k + 1) := by omega
          simp only [harr]
          exact glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
            (k+1) (by omega) hk1
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · -- (c) THE PROMOTED JUNCTION TRANSITION — the packet's junc legs + H₂'s [T-4]
          subst hk0
          simp only [Nat.add_zero] at hnodei1 ⊢
          rw [glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter,
            hnodei1]
          have h1L2 : 1 < H₂.nodes.length := by omega
          obtain ⟨hs, ht, hwin, hwid, hsteep⟩ := hT4₂ h1L2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro hsp
            exact J.junc_rec h1L2 hsp
          · intro hsp
            exact J.junc_nonrec h1L2 hsp
          · intro he1
            exact hs he1
          · intro he1
            exact ht he1
          · exact hwin
          · exact hwid
          · show H₂.headNode.line.slope / (H₁.strTotal : ℚ)
              < (H₂.nodes[1]'h1L2).line.slope / (H₁.strTotal : ℚ)
            exact div_lt_div_of_pos_right hsteep hSposQ
        · -- (d) inside H₂ (k ≥ 1): H₂'s own interior legs, stretch-transported
          rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k
              hk0 (by omega), hnodei1]
          obtain ⟨hrec', hnonrec', hs, ht, hwin, hwid, hsteep⟩ := hT3₂ k hk0 hk1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro hsp
            exact hrec' hsp
          · intro hsp
            exact hnonrec' hsp
          · intro he1
            exact hs he1
          · intro he1
            exact ht he1
          · exact hwin
          · exact hwid
          · show (H₂.nodes[k]'(by omega)).line.slope / (H₁.strTotal : ℚ)
              < (H₂.nodes[k+1]'hk1).line.slope / (H₁.strTotal : ℚ)
            exact div_lt_div_of_pos_right hsteep hSposQ
  · -- [T-4] the glued base transition (L₁ = 1: the packet's pair-free seam clauses;
    -- L₁ ≥ 2: H₁'s own base transition)
    intro hi
    by_cases h1L : 1 < H₁.nodes.length
    · rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter 0
          (by omega),
        glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter 1 h1L]
      exact hT4₁ h1L
    · have hL1e : H₁.nodes.length = 1 := by omega
      have hnode1 : ∀ (h : 1 < (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes.length),
          (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[1]'h = glueJnc H₁ H₂ sp' J.sp_inc J.sp_rec J.sp_recCenter := by
        intro h
        have h1 : (1 : ℕ) = H₁.nodes.length := hL1e.symm
        simp only [h1]
        exact glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
      have hnode0 : ∀ (h : 0 < (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes.length),
          (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[0]'h = H₁.lastNode := by
        intro h
        rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter 0
          (by omega)]
        show H₁.nodes[0]'_ = H₁.nodes[H₁.nodes.length - 1]'_
        congr 1
        omega
      rw [hnode0, hnode1]
      exact ⟨fun he1 => J.seam_s_tie he1, fun he1 => J.seam_t_tie he1,
        J.seam_window, J.seam_width, J.seam_steep⟩
  · -- [T-5] the per-read bundle (four ranges: inside H₁ / the seam read / the
    -- junction read / inside H₂)
    intro i hi
    by_cases hcase1 : i + 1 < H₁.nodes.length
    · -- (a) inside H₁, with a successor still inside H₁: H₁'s bundle verbatim
      obtain ⟨B, Nd, Φnext, hdev, hpin, hside, hland⟩ := hT5₁ i (by omega)
      rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
        (by omega)]
      refine ⟨B, Nd, Φnext, hdev, ?_, hside, hland⟩
      intro hi1
      rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter (i+1)
        hcase1]
      exact hpin hcase1
    · by_cases hcase2 : i < H₁.nodes.length
      · -- (b) the SEAM read (i = L₁ − 1): the packet's `ends_at`
        have hiL : i = H₁.nodes.length - 1 := by omega
        obtain ⟨B, Nd, hdev, hside, hland⟩ := J.ends_at
        have hnodei : ∀ (h : i < (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes.length), (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[i]'h = H₁.lastNode := by
          intro h
          rw [glue_node_lo H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter i
            hcase2]
          subst hiL
          rfl
        rw [hnodei]
        refine ⟨B, Nd, H₂.headNode.σ.Φ, hdev, ?_, ?_, hland⟩
        · intro hi1
          have hip1 : i + 1 = H₁.nodes.length := by omega
          have := glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
            (h := by omega)
          show H₂.headNode.σ.Φ = ((glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[i+1]'hi1).σ.Φ
          simp only [hip1]
          rw [glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter]
          rfl
        · intro hi0
          exact hside (by omega)
      · -- i ≥ L₁
        obtain ⟨k, rfl⟩ : ∃ k, i = H₁.nodes.length + k :=
          ⟨i - H₁.nodes.length, by omega⟩
        have hk : k < H₂.nodes.length := by rw [hlenG] at hi; omega
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · -- (c) THE JUNCTION READ: the packet's bundle, LandingKey re-specied
          subst hk0
          simp only [Nat.add_zero]
          obtain ⟨B, Nd, Φnext, hdev, hpin, hside, hrecland⟩ := J.junc_bundle
          rw [glue_node_mid H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter]
          -- the head node's species is root (History.root_iff), so its recorded
          -- SideReads clause (iv) provides the non-recentering landing form
          have hheadroot : H₂.headNode.species = ReadSpecies.root :=
            (H₂.root_iff 0 hL2).mpr rfl
          obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hside
          have hnodelift : IsNodeLift H₂.headNode Φnext := by
            refine hs4.2 ?_
            rw [hheadroot]
            intro hcon
            exact ReadSpecies.noConfusion hcon
          have hlandJ : LandingKey
              (glueJnc H₁ H₂ sp' J.sp_inc J.sp_rec J.sp_recCenter) Φnext := by
            constructor
            · intro hsp
              have hspsp : sp' = ReadSpecies.recentering := hsp
              obtain ⟨ha, hb, hc, hd, he⟩ := hrecland hspsp
              exact ⟨ha, hb, hc, hd, he⟩
            · intro hsp
              exact hnodelift
          refine ⟨B, Nd, Φnext, hdev, ?_, ?_, Or.inl hlandJ⟩
          · intro hi1
            have hk1 : 1 < H₂.nodes.length := by rw [hlenG] at hi1; omega
            rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter 1
              (by omega) hk1]
            exact hpin hk1
          · intro hi0
            exact ⟨hs1, hs2, hs3, hlandJ, hs5, hs6⟩
        · -- (d) inside H₂ (k ≥ 1): H₂'s bundle, stretch-transported
          obtain ⟨B, Nd, Φnext, hdev, hpin, hside, hland⟩ := hT5₂ k hk
          rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter k
            hk0 hk]
          refine ⟨B, Nd, Φnext, hdev, ?_, ?_, hland⟩
          · intro hi1
            have hk1 : k + 1 < H₂.nodes.length := by rw [hlenG] at hi1; omega
            have harr : H₁.nodes.length + k + 1 = H₁.nodes.length + (k + 1) := by omega
            show Φnext = ((glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter).nodes[H₁.nodes.length + k + 1]'hi1).σ.Φ
            simp only [harr]
            rw [glue_node_hi H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter
              (k+1) (by omega) hk1]
            exact hpin hk1
          · intro hi0
            exact hside hk0

/-- **E-3, the DISPLAYED (StageCoreL-tagged) form**: `ReadsOfFrom` composes.  The base
tag `hσ₀` rides through to the glued run; the junction tag `hσ₁` is consumed here
only as display (the kernel is core-free — deviation D-2 — so the junction stage's
lawfulness is definitionally inert interior data of the glued run). -/
theorem readsOfFrom_glue (σ₀ σ₁ : Stage p F) (hσ₀ : StageCoreL σ₀)
    (hσ₁ : StageCoreL σ₁) (f₀ : Polynomial ℤ_[p])
    (H₁ H₂ : History p F) (sp' : ReadSpecies)
    (hrun₁ : ReadsOfFrom σ₀ hσ₀ f₀ H₁) (hrun₂ : ReadsOfFrom σ₁ hσ₁ f₀ H₂)
    (J : GlueJunction f₀ H₁ H₂ sp') :
    ReadsOfFrom σ₀ hσ₀ f₀
      (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter) :=
  truncRunFrom_glue σ₀ σ₁ f₀ H₁ H₂ sp' hrun₁ hrun₂ J

/-! ### §5 — the f-tie (task 2): the merged form and the unconditional chain form -/

/-- **The f-tie, MERGED form**: a coherent FULL run on `f` extends by a truncated run
from a stage σ₁, merging into a single truncated run FROM THE FULL RUN'S OWN ROOT
FRAME — conditional on the junction packet.  Honest strength: for a full H₁ with
L₁ ≥ 2 the packet's `seam_nonrec` leg forces the ending read to stride 1 (or
recentering) — a full run ending at an e ≥ 2 read does NOT merge; the e ≥ 2 shape is
hosted instead at the glued BASE (take H₁ the one-node truncated host of that read:
L₁ = 1, where the seam is the pair-free [T-4]). -/
theorem readsOf_glue (n : ℕ) (f : Polynomial ℤ_[p]) (σ₁ : Stage p F)
    (H₁ H₂ : History p F) (sp' : ReadSpecies)
    (hRO : ReadsOf p F n f H₁) (hrun₂ : TruncRunFrom σ₁ f H₂)
    (J : GlueJunction f H₁ H₂ sp') :
    TruncRunFrom ((H₁.nodes[0]'H₁.hlen0).σ) f
      (glueHistory H₁ H₂ sp' J.sp_ne_root J.sp_inc J.sp_rec J.sp_recCenter) :=
  truncRunFrom_glue _ σ₁ f H₁ H₂ sp'
    (truncRunFrom_of_readsOf n f H₁ hRO H₁.hlen0) hrun₂ J

/-- **f-TIED TRUNCATED LANDING** — what f-tied coverage now reads (the UNCONDITIONAL
chain form): the pair (site stage σ₁, produced key Φ') is f-tied when (left leg) a
coherent full `ReadsOf` run on f REACHES σ₁ — its ending read's recorded `SideReads`
designated-lands σ₁'s key — and (right leg) a truncated run from σ₁ READING THE SAME
f lands Φ' at its base read.  Against the pre-E-3 state this replaces
`OnTruncatedCarrier`'s free local classificand by the ambient f and anchors the base
stage on f's own recorded tower; no merge into one history is claimed here (that is
`readsOf_glue`, packet-conditional). -/
def FTiedTruncLanding (n : ℕ) (f : Polynomial ℤ_[p]) (σ₁ : Stage p F)
    (Φ' : Polynomial ℤ_[p]) : Prop :=
  (∃ H₁ : History p F, ReadsOf p F n f H₁ ∧
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment H₁.lastNode.σ.Φ f B Nd ∧ SideReads H₁.lastNode B Nd σ₁.Φ) ∧
  (∃ H₂ : History p F, TruncRunFrom σ₁ f H₂ ∧
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment H₂.headNode.σ.Φ f B Nd ∧
      (∀ h1 : 1 < H₂.nodes.length, Φ' = (H₂.nodes[1]'h1).σ.Φ) ∧
      (LandingKey H₂.headNode Φ' ∨
        IsStandardLift H₂.headNode.σ H₂.headNode.ψ H₂.headNode.g Φ'))

/-- **The f-tie, CHAIN form (unconditional)**: a full run reaching σ₁ and a truncated
run from σ₁ on the same f compose to an f-tied truncated landing — no junction packet
needed (nothing is merged; coverage extends as the chain). -/
theorem ftie_extends (n : ℕ) (f : Polynomial ℤ_[p]) (σ₁ : Stage p F)
    (Φ' : Polynomial ℤ_[p]) (H₁ H₂ : History p F)
    (hRO : ReadsOf p F n f H₁)
    (B₁ : ℕ → Polynomial ℤ_[p]) (Nd₁ : ℕ)
    (hdev₁ : IsDevelopment H₁.lastNode.σ.Φ f B₁ Nd₁)
    (hreach : SideReads H₁.lastNode B₁ Nd₁ σ₁.Φ)
    (hrun₂ : TruncRunFrom σ₁ f H₂)
    (B₂ : ℕ → Polynomial ℤ_[p]) (Nd₂ : ℕ)
    (hdev₂ : IsDevelopment H₂.headNode.σ.Φ f B₂ Nd₂)
    (hpin : ∀ h1 : 1 < H₂.nodes.length, Φ' = (H₂.nodes[1]'h1).σ.Φ)
    (hland : LandingKey H₂.headNode Φ' ∨
      IsStandardLift H₂.headNode.σ H₂.headNode.ψ H₂.headNode.g Φ') :
    FTiedTruncLanding n f σ₁ Φ' :=
  ⟨⟨H₁, hRO, B₁, Nd₁, hdev₁, hreach⟩, ⟨H₂, hrun₂, B₂, Nd₂, hdev₂, hpin, hland⟩⟩

/-! ### §6 — the ITER-LAW-shaped named open (task 3): the junction-bundle supplier -/

/-- **THE D-ITER JUNCTION SUPPLIER (named open — displayed, NEVER asserted).**  The
one leg of `GlueJunction` no compiled instance can discharge at a deep frame is
`junc_bundle`: the full `SideReads` of the ambient classificand f against its
development in the junction key.  A GENERAL supplier has the shape below: at a stage
σ₁ reached along f, SOME junction node hosts f's deep read with the full bundle.

THE ITER-LAW FENCE (strata probe `lean/notes/openmath/STRATA_PROBE_2026-08-08.md`,
Family B — binding on any future discharge): computing f's deep digits through the
iterated development is a computation in the order-2 COMPOSITE digit algebra of
gr(w₂), whose measured structure at the canonical (dig-consumed) alphabet is the
TWO-CONSTANT iterated law with the outer-wrap-feeds-inner-track fibration term

    (ITER-LAW)   c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀γ₂δ₂)/e₀},
                 δ₂ = ⌊(s₂(γ)+s₂(γ′))/e₁⌋

(row B2: 0/804 exact, 52 towers).  The single-constant CYCLIC presentation
`F′[u′]/(u′^{e_b′} − ζ′)` is ADJUDICATED FALSE at mixed stacked ramification (row
B3-adj: NOT-CYCLIC at 22/28 towers with e₀, e₁ ≥ 2; the kill-shot is designed row N,
where K₂ = K₁[z̄] is a genuine degree-2 extension and the cocycle value set
{z₁, z̄, z̄z₁^b} admits no single ζ′).  ANY Lean discharge of this supplier MUST
carry the two constants and the fibration term — a cyclic-form kernel is refuted at
nature and is fenced OUT of this obligation.  (The glue theorem itself never touches
these constants — header, THE CARRY-CONSTANT ADJUDICATION.) -/
def DIterJunctionSupplier (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] :
    Prop :=
  ∀ (n : ℕ) (f : Polynomial ℤ_[p]) (σ₁ : Stage p F) (H₁ : History p F),
    ReadsOf p F n f H₁ →
    (∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment H₁.lastNode.σ.Φ f B Nd ∧ SideReads H₁.lastNode B Nd σ₁.Φ) →
    σ₁.Φ.natDegree < n →
    ∃ (ν : Node p F), ν.σ = σ₁ ∧ ν.species = ReadSpecies.root ∧
      ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
        IsDevelopment σ₁.Φ f B Nd ∧ SideReads ν B Nd Φnext

/-! ### §7 — gates (compiled tower data: U31's fq-run into HK25/RCW's recentering) -/

section Gates

open RCW

private lemma fq_deg : U31.fq.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
  rfl

/-- The self-development of fq at the junction key σ₁rec.Φ (= fq): `fq = 0 + 1·Φ`. -/
private noncomputable def Bself : ℕ → Polynomial ℤ_[2] :=
  fun j => if j = 1 then 1 else 0

private lemma Bself_dev : IsDevelopment HK25.σ₁rec.Φ U31.fq Bself 2 := by
  rw [HK25.σ₁rec_Φ]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold Bself
    rw [fq_deg]
    split_ifs
    · exact lt_of_le_of_lt Polynomial.degree_one_le (by norm_num)
    · rw [Polynomial.degree_zero]
      decide
  · intro j hj
    unfold Bself
    rw [if_neg (by omega)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    unfold Bself
    norm_num

/-- The U31 development of fq at the base key, re-proved from the public `Bdev`
(the in-file `Bdev_dev` is private). -/
private lemma Bdev_dev' : IsDevelopment (X : Polynomial ℤ_[2]) U31.fq U31.Bdev 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [Polynomial.degree_X]
    unfold U31.Bdev
    split_ifs
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_one_le (by norm_num)
    · rw [Polynomial.degree_zero]; exact bot_lt_iff_ne_bot.mpr (by norm_num)
  · intro j hj
    unfold U31.Bdev
    split_ifs with h1 h2 h3
    · exact absurd h1 (by omega)
    · exact absurd h2 (by omega)
    · exact absurd h3 (by omega)
    · rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : U31.Bdev 0 = Polynomial.C 4 := rfl
    have h1 : U31.Bdev 1 = Polynomial.C 2 := rfl
    have h2 : U31.Bdev 2 = 1 := rfl
    rw [h0, h1, h2, U31.fq]
    ring

/-- U31's full run, re-assembled from the PUBLIC pieces (the in-file `readsOf_fq` is
private): the compiled coherent 1-node history H₀ with the recorded root read of fq,
designated landing fq itself. -/
theorem gate_readsOf_fq : ReadsOf 2 F4 2 U31.fq U31.H₀ := by
  refine ⟨U31.fq_monic, U31.fq_natDegree, U31.coherent_H₀, ?_⟩
  intro i hi
  have hi1 : i < 1 := hi
  have hi0 : i = 0 := by omega
  subst hi0
  refine ⟨U31.Bdev, 3, U31.fq, ?_, ?_, ?_⟩
  · show IsDevelopment (X : Polynomial ℤ_[2]) U31.fq U31.Bdev 3
    exact Bdev_dev'
  · intro h1
    exact absurd (show (1 : ℕ) < 1 from h1) (by omega)
  · show SideReads U31.ν₀ U31.Bdev 3 U31.fq
    exact U31.sideReads_ν₀

/-- **The junction node of the gate**: RCW's recentering read ν₁rc, re-specied to
ROOT so it can carry a one-node truncated run from σ₁rec (the base node of any
history is root by `root_iff`); the glue re-species it back to recentering. -/
noncomputable def ν₁rcRoot : Node 2 F4 :=
  ν₁rc.respec ReadSpecies.root
    (fun h => ReadSpecies.noConfusion h)
    (fun h => ReadSpecies.noConfusion h)
    (fun h => ReadSpecies.noConfusion h)

/-- The one-node truncated continuation history at σ₁rec. -/
noncomputable def H₂rc : History 2 F4 where
  nodes := [ν₁rcRoot]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hj1 : j < 1 := by simpa using hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact iff_of_true rfl rfl

lemma H₂rc_len : H₂rc.nodes.length = 1 := rfl

/-- **The compiled landing of the continuation run**: the recentering's fired key
σ₂rc.Φ is an `IsNodeLift` of the root-respecied read — realizer `−rcLift` at slot 0,
weight by `rcLift_w`/`hwΦ`/`hwmul`, digit by `StageCore.R_neg` (via the public
`score_σ₁rec`) off the recorded `rcLift_R`. -/
lemma landingKey_ν₁rcRoot : LandingKey ν₁rcRoot σ₂rc.Φ := by
  constructor
  · intro hcon
    exact absurd hcon (fun h => ReadSpecies.noConfusion h)
  · intro _
    show IsNodeLift ν₁rc σ₂rc.Φ
    -- w(−1) = 0 and w(1) = 0 from multiplicativity
    have hw1 : HK25.σ₁rec.w 1 = 0 := by
      have h := HK25.σ₁rec.hwmul 1 1 one_ne_zero one_ne_zero
      rw [mul_one] at h
      omega
    have hwm1 : HK25.σ₁rec.w (-1) = 0 := by
      have h := HK25.σ₁rec.hwmul (-1) (-1) (by norm_num) (by norm_num)
      rw [neg_mul_neg, one_mul] at h
      omega
    have hwneg : HK25.σ₁rec.w (-rcLift) = 3 := by
      have h := HK25.σ₁rec.hwmul (-1) rcLift (by norm_num) rcLift_ne
      rw [neg_one_mul] at h
      rw [h, hwm1, rcLift_w, HK25.σ₁rec.hwΦ, HK25.σ₁rec_pins.2.1]
      ring
    refine ⟨(fun k => if k = 0 then -rcLift else 0), ?_, ?_, ?_⟩
    · intro k hk
      by_cases h0 : k = 0
      · subst h0
        have hk' : ((Polynomial.X : Polynomial ↥HK25.σ₁rec.K)
            - Polynomial.C rcCenter).coeff 0 = 0 := hk
        simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub, neg_eq_zero] at hk'
        exact absurd hk' rcCenter_ne
      · show (if k = 0 then -rcLift else (0 : Polynomial ℤ_[2])) = 0
        rw [if_neg h0]
    · intro k hklt hkne
      have h0 : k = 0 := by
        have : ν₁rc.g = 1 := rfl
        omega
      subst h0
      simp only [reduceIte]
      refine ⟨neg_ne_zero.mpr rcLift_ne, ?_, ?_, ?_⟩
      · show (-rcLift).degree < HK25.σ₁rec.Φ.degree
        rw [Polynomial.degree_neg]
        exact rcLift_inC
      · show HK25.σ₁rec.w (-rcLift) = ((3 : ℕ) : ℤ) * (((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
        rw [hwneg]
        norm_num
      · show HK25.σ₁rec.R (-rcLift)
          = LaurentPolynomial.C ((Polynomial.X - Polynomial.C rcCenter).coeff 0)
            * LaurentPolynomial.T (- ν₁rc.σ.t * ν₁rc.σ.wPrev (-rcLift))
        have ht0 : ν₁rc.σ.t = 0 := HK25.σ₁rec_pins.2.2.2
        rw [ht0, neg_zero, zero_mul,
          score_σ₁rec.core.R_neg rcLift, rcLift_R,
          show ((Polynomial.X : Polynomial ↥HK25.σ₁rec.K)
            - Polynomial.C rcCenter).coeff 0 = -rcCenter by simp,
          map_neg, neg_mul]
    · show σ₂rc.Φ = HK25.σ₁rec.Φ ^ (1 * 1)
        + ∑ k ∈ Finset.range 1, (if k = 0 then -rcLift else 0) * HK25.σ₁rec.Φ ^ (1 * k)
      rw [Finset.sum_range_one, σ₂rc_Φ]
      simp only [if_pos, mul_one, pow_one, mul_zero, pow_zero]
      ring

/-- **GATE (the continuation run)**: a compiled truncated run from HK25's gate child
σ₁rec reading U31's fq (σ₁rec's own key), whose base read is the RCW recentering read
(root-respecied), designated landing = the S10-fired recentered key σ₂rc.Φ. -/
theorem gate_truncRun_H₂rc : TruncRunFrom HK25.σ₁rec U31.fq H₂rc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    rfl
  · intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    show (3 / 2 : ℚ) * (((1 : ℕ) : ℚ) * ((H₂rc.strFrame 0 : ℕ) : ℚ) * ((2 : ℕ) : ℚ))
        = ((3 : ℕ) : ℚ)
    have hstr : H₂rc.strFrame 0 = 1 := rfl
    rw [hstr]
    norm_num
  · intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    show (((3 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((H₂rc.strFrame 0 : ℕ) : ℚ) * (0 : ℚ))
        + (((0 + 1 : ℕ)) : ℚ) * ((3 : ℕ) : ℚ)
    have hstr : H₂rc.strFrame 0 = 1 := rfl
    rw [hstr]
    norm_num
  · intro i hi0 hi
    exact absurd (show i + 1 < 1 from hi) (by omega)
  · intro hi
    exact absurd (show (1 : ℕ) < 1 from hi) (by omega)
  · intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    refine ⟨Bself, 2, σ₂rc.Φ, Bself_dev, ?_, ?_, Or.inl landingKey_ν₁rcRoot⟩
    · intro h1
      exact absurd (show (1 : ℕ) < 1 from h1) (by omega)
    · intro h0
      exact absurd h0 (by omega)

/-- **GATE (the f-tie chain FIRES end-to-end, zero hypotheses)**: f-tied truncated
coverage is inhabited on compiled tower data — U31's full ReadsOf run on fq reaches
σ₁rec (its root read's recorded SideReads designated-lands fq = σ₁rec.Φ), and the
truncated continuation from σ₁rec lands the RCW recentering's fired key σ₂rc.Φ.
The first f-TIED deep landing on file. -/
theorem gate_ftie_chain : FTiedTruncLanding 2 U31.fq HK25.σ₁rec σ₂rc.Φ := by
  refine ftie_extends 2 U31.fq HK25.σ₁rec σ₂rc.Φ U31.H₀ H₂rc gate_readsOf_fq
    U31.Bdev 3 ?_ ?_ gate_truncRun_H₂rc Bself 2 Bself_dev
    (fun h1 => absurd (show (1:ℕ) < 1 from h1) (by omega))
    (Or.inl landingKey_ν₁rcRoot)
  · show IsDevelopment (X : Polynomial ℤ_[2]) U31.fq U31.Bdev 3
    exact Bdev_dev'
  · show SideReads U31.ν₀ U31.Bdev 3 HK25.σ₁rec.Φ
    rw [HK25.σ₁rec_Φ]
    exact U31.sideReads_ν₀

/-- **GATE (the junction packet, all structural legs discharged)**: at the compiled
seam U31.H₀ → σ₁rec → H₂rc, EVERY `GlueJunction` field is discharged concretely
EXCEPT `junc_bundle`, which enters as the displayed hypothesis — deviation D-1's wall
verbatim (its clause (iii) reads `σ.R f` at `deg f = deg Φ`, an out-of-carrier
residual, opaque at the choice-built σ₁rec; see `DIterJunctionSupplier`). -/
theorem gate_glue_junction
    (hbundle : ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
      IsDevelopment H₂rc.headNode.σ.Φ U31.fq B Nd ∧
      (∀ h1 : 1 < H₂rc.nodes.length, Φnext = (H₂rc.nodes[1]'h1).σ.Φ) ∧
      SideReads H₂rc.headNode B Nd Φnext ∧
      (ReadSpecies.recentering = ReadSpecies.recentering →
        inC H₂rc.headNode.σ.Φ H₂rc.headNode.lift ∧ H₂rc.headNode.lift ≠ 0 ∧
        H₂rc.headNode.σ.w H₂rc.headNode.lift = H₂rc.headNode.σ.w H₂rc.headNode.σ.Φ ∧
        H₂rc.headNode.σ.R H₂rc.headNode.lift
          = LaurentPolynomial.C H₂rc.headNode.center * LaurentPolynomial.T 0 ∧
        Φnext = H₂rc.headNode.σ.Φ - H₂rc.headNode.lift)) :
    GlueJunction U31.fq U31.H₀ H₂rc ReadSpecies.recentering := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbundle, ?_, ?_⟩
  · intro h
    exact ReadSpecies.noConfusion h
  · intro h
    exact ReadSpecies.noConfusion h
  · intro _
    exact ⟨rfl, rfl⟩
  · intro _
    exact ⟨rfl, rfl⟩
  · intro _
    exact HK25.σ₁rec_pins.2.2.1
  · intro _
    exact HK25.σ₁rec_pins.2.2.2
  · show (0 + 1 : ℕ) ≤ U31.ν₀.μ
    show (0 + 1 : ℕ) ≤ 1
    omega
  · show (2 : ℕ) = U31.ν₀.childWidth
    rfl
  · show (1 : ℚ) < (3 / 2 : ℚ) / ((U31.H₀.strTotal : ℕ) : ℚ)
    have hstr : U31.H₀.strTotal = 1 := rfl
    rw [hstr]
    norm_num
  · intro h1
    exact absurd (show (1:ℕ) < 1 from h1) (by omega)
  · intro h1
    exact absurd (show (1:ℕ) < 1 from h1) (by omega)
  · refine ⟨U31.Bdev, 3, ?_, ?_, ?_⟩
    · show IsDevelopment (X : Polynomial ℤ_[2]) U31.fq U31.Bdev 3
      exact Bdev_dev'
    · intro h1
      exact absurd (show (1:ℕ) < 1 from h1) (by omega)
    · refine Or.inl ?_
      show LandingKey U31.ν₀ HK25.σ₁rec.Φ
      rw [HK25.σ₁rec_Φ]
      exact U31.landingKey_ν₀
  · intro h1
    exact absurd (show (1:ℕ) < 1 from h1) (by omega)
  · intro h1
    exact absurd (show (1:ℕ) < 1 from h1) (by omega)

/-- **GATE (the glue theorem FIRES at the compiled seam, conditional on exactly the
D-1 wall)**: given the junction bundle, U31's full fq-run and the RCW continuation
merge into a single 2-node truncated run from U31's root frame carrying the interior
recentering read.  The hypothesis is the ONE undischargeable leg (header, GATES). -/
theorem gate_glue_conditional
    (hbundle : ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
      IsDevelopment H₂rc.headNode.σ.Φ U31.fq B Nd ∧
      (∀ h1 : 1 < H₂rc.nodes.length, Φnext = (H₂rc.nodes[1]'h1).σ.Φ) ∧
      SideReads H₂rc.headNode B Nd Φnext ∧
      (ReadSpecies.recentering = ReadSpecies.recentering →
        inC H₂rc.headNode.σ.Φ H₂rc.headNode.lift ∧ H₂rc.headNode.lift ≠ 0 ∧
        H₂rc.headNode.σ.w H₂rc.headNode.lift = H₂rc.headNode.σ.w H₂rc.headNode.σ.Φ ∧
        H₂rc.headNode.σ.R H₂rc.headNode.lift
          = LaurentPolynomial.C H₂rc.headNode.center * LaurentPolynomial.T 0 ∧
        Φnext = H₂rc.headNode.σ.Φ - H₂rc.headNode.lift)) :
    TruncRunFrom ((U31.H₀.nodes[0]'U31.H₀.hlen0).σ) U31.fq
      (glueHistory U31.H₀ H₂rc ReadSpecies.recentering
        (gate_glue_junction hbundle).sp_ne_root
        (gate_glue_junction hbundle).sp_inc
        (gate_glue_junction hbundle).sp_rec
        (gate_glue_junction hbundle).sp_recCenter) :=
  readsOf_glue 2 U31.fq HK25.σ₁rec U31.H₀ H₂rc ReadSpecies.recentering
    gate_readsOf_fq gate_truncRun_H₂rc (gate_glue_junction hbundle)

end Gates

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.truncRunFrom_glue
#print axioms LeanUrat.Scaffold.HDischarge.H1.readsOfFrom_glue
#print axioms LeanUrat.Scaffold.HDischarge.H1.readsOf_glue
#print axioms LeanUrat.Scaffold.HDischarge.H1.ftie_extends
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_readsOf_fq
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_truncRun_H₂rc
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_ftie_chain
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_glue_junction
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_glue_conditional
