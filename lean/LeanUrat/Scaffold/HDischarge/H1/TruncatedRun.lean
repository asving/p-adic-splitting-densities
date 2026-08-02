/-
SITE-EXH EXTENSION — `H1/TruncatedRun.lean`: THE TRUNCATED-RUN CARRIER (E-1/E-2/E-4)
(implementation of the probe-frozen design `H1/SiteExhProbe.lean` header §"THE MINIMAL
EXTENSION"; ASVIN SIGN-OFF 2026-08-08, ledger `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
commit 49b778e: "the additive ReadsOfFrom σ₀ truncated-run carrier; ReadsOf/HistoryCoherent
byte-unchanged; the D-ITER glue as the one new obligation").

## WHAT LANDS HERE

* **E-1** — `TruncRunFrom` (the kernel) + `ReadsOfFrom σ₀ hσ₀ f₀ H` (the displayed
  carrier, signature per the frozen design): truncated runs whose node-0 frame is the
  GIVEN stage (`(H.nodes[0]).σ = σ₀` REPLACES `HistoryCoherent`'s degree-1 base pin);
  the slope law, the γ-tie, and ALL interior transition legs — the RG-2 fence
  INCLUDED — are retained VERBATIM above the base read (E-4: no fence lift); the base
  read's own pair is free; every read is against a frame-development of the LOCAL
  classificand `f₀`, with the FULL `SideReads` bundle at every read ABOVE the base.
* **E-2** — `moveWitness_standardLift` + `standardLift_hosts` + `moveWitness_hosts`:
  every `HC1.MoveWitness σ σ'` is the base read of a ONE-NODE truncated run with the
  designated landing `Φnext := σ'.Φ`; `moveWitness_hosts_readsOfFrom` is the DISPLAYED
  (StageCoreL-tagged) form of the corollary.
* **THE WIDENED DISJUNCTION + THE DISCHARGE, TWO LAYERS** [layering per the pre-commit
  Codex adversarial pass — see THE CODEX FOLD below]:
  (kernel layer) `OnTruncatedCarrier` (core-free truncated base landing),
  `OnRecordedCarrier'`, `TowerMoveClosure'` — the residue row at the AS-BUILT widened
  target — is DISCHARGED (`towerMoveClosure'_discharged`), and
  `siteExh_elimination' : ∀ fl : FiredLift p F, fl.Lands'` fires UNCONDITIONALLY over
  the closed enumeration (junk-hostable `towerMove`s included).  What this closes is
  the engine-face escape ROUTE: every fired shape lands on a DISPLAYED carrier.
  (lawful layer) `OnTruncatedCarrierL` (the signed E-1 signature's core-BINDING
  carrier) and `TowerMoveClosureL` — the row at cored parents, the engine's own
  S9/S10 calling convention — is ALSO DISCHARGED (`towerMoveClosureL_discharged`).
  The two layers are ordered (`onTruncated_of_lawful`).  NEITHER discharges the
  ORIGINAL narrow-target row `TowerMoveClosure`, which stands open as displayed.
* **THE AGREEMENT LEMMA (one-way admission certificate)** — `truncRunFrom_of_readsOf`:
  every full `ReadsOf` run IS a truncated run from its own root frame; the truncated
  clauses are verbatim projections of `HistoryCoherent`/`SideReads` conjuncts (the
  task's "compiled agreement lemma on the overlap" — `HistoryCoherent` does not factor
  into named clause predicates, so the clauses are verbatim instances certified here).
  Scope [Codex fold]: this is ADMISSION (no full run is lost), not conservativity —
  the truncated carrier admits MORE runs by design; that widening IS the extension.
* **GATES** — `gate_mwRC_hosts` / `gate_mwRC_readsOfFrom` (the RCW recentering move
  hosts in a truncated run — the E-1/E-2 non-vacuity witnesses, positive) and
  `gate_flTower_lands'` (the SiteExhProbe towerMove gate instance re-fired through the
  new path, now landing UNconditionally).

## THE DEVIATIONS FROM THE E-1/E-2 DISPLAY (recorded here and in the ledger; the
## display was a design sketch — "nothing below implements it".  Adversarially
## audited pre-commit by Codex; scope of each claim per that audit — THE CODEX FOLD
## below.  STANDING RE-RATIFICATION ITEM for Asvin: the sign-off text demanded both
## the E-1 core-binding signature AND an elimination "unconditional at the engine
## face" over the existing junk-admitting `FiredLift`; those two demands are jointly
## unsatisfiable by one carrier, so BOTH layers are compiled — confirm the layering.)

* **(D-1) The base read's bundle is `IsDevelopment` + the designated-landing pair
  `(LandingKey ∨ IsStandardLift)`, NOT the full `SideReads` bundle.**
  COMPILED-ARGUMENT-BACKED for two clauses:
  (v) [choice-pin wall] clause (v) pins `ν.lift = (polOM p F).liftOf ν` — a
  classical choice — while clause (iv)'s recentering leg then pins the designated key
  to `σ.Φ − (polOM choice)`.  A recentering `MoveWitness` carries ITS OWN realizer
  `tt` (S10's choice) with `σ'.Φ = σ.Φ − tt`; the equation (polOM choice) = `tt` is
  not provable from the S10/polOM interfaces (choices from different existentials;
  `RecenterLiftSpec` realizers are non-unique at nature — deeper-weight perturbations
  preserve the spec via `w_strict`/`hRlt` — though the two-realizer separation
  instance is NOT compiled here), so the E-2 host construction has no route to the
  designated landing `σ'.Φ` with clause (v) at the base, the RCW gate included.
  (iv-as-sole-lander) [stage-scale/coprimality wall] every `History` forces node-0
  species = root (`root_iff`), so clause (iv) at the base lands through `IsNodeLift`,
  whose weight law reads the STAGE scale `ν.σ.w (t_k) = ν.h·(g−k)`.  An increment
  move's lift realizers carry `σ.wPrev (t_k) = σ.h·(g−k)` (D.5), hence by `hStretch`
  `σ.w (t_k) = σ.e·σ.h·(g−k)`: the base node's pair is forced to `(σ.e, σ.e·σ.h)` —
  violating the node's coprimality field `hcop` at every `σ.e ≥ 2` parent, i.e.
  exactly at the deep frames the extension exists to host (the C-e shape).
  NOT-FORCED-BUT-NOT-RETAINED, with reason [Codex: no forcing was supplied for
  these, correct]: clauses (i)/(ii)/(iii)/(vi) — the f₀-side/digit/anchor/vertex
  data.  They are not KEY-ASSERTING (the probe census names clause (iv) as the sole
  key-asserting `SideReads` clause), and no construction discharging them for an
  ARBITRARY `MoveWitness` is known (the attempted hS6a/hS6b realizer builds hit the
  `wPrev Φ`-threshold and coset-scalar walls; clause (vi) needs the Φnext-development
  carry).  Retaining any of them at the base is an OPEN ADDITIVE REFINEMENT (it
  would only strengthen the carrier) — E-3-adjacent, not prejudged here.
  `IsStandardLift` — D.5's displayed frame-pair formula on the `wPrev` scale,
  literally S9's `hlift` interface — hosts EVERY move (compiled below), so the base
  landing displays BOTH compiled firing forms of the census: the run-borne
  `LandingKey` (full-run truncations enter through it — the agreement lemma) and the
  stage-level `IsStandardLift` (engine moves enter through it — E-2).  Candid note
  [Codex]: at increment moves the truncated landing is close to a re-display of the
  move's own `TransHyp.hlift` — the carrier's value there is UNIFORMITY of the
  displayed target (+ the E-3 composition seam), not new per-move information.
* **(D-2) `hσ₀ : StageCoreL σ₀` rides on `ReadsOfFrom` as the displayed lawfulness
  interface; the kernel `TruncRunFrom` (and the kernel carrier `OnTruncatedCarrier`)
  is core-free.**  This IS a widening of the signed carrier at the kernel layer
  [Codex: correct] — junk parents host there.  Why compiled anyway: `HC1.MoveWitness`
  carries the CHILD core `core' : StageCoreL σ'` but NOT the parent's, and no parent
  core is derivable from it; an elimination over the EXISTING `FiredLift` (whose
  `towerMove` "quantifies over junk-hostable and unhostable moves alike" — the
  probe's header) can only be unconditional at a core-free target.  The SIGNED
  (core-binding) carrier is compiled as `OnTruncatedCarrierL`, its row
  `TowerMoveClosureL` DISCHARGED at cored parents — the engine's own S9/S10 calling
  convention, hence the whole engine-reachable perimeter (`Tower.base` cores the
  base; each move's `core'` cores the child).  Every clause of the E-2 host is
  discharged by BARE `Stage` fields (`hS5`, `hwmul`, `hStretch`, `he1t`, `hwΦ`,
  `hdeg`, `hmonic`); E-2's displayed "at a `StageCoreL σ`" form is compiled verbatim
  as `moveWitness_hosts_readsOfFrom`.
* (D-3, minor) The base read's own transition (i = 0 of a ≥ 2-node truncated run)
  retains the five PAIR-FREE frame-chain clauses of the interior leg (Bézout ties,
  window containment, width chain, strict steepening); its species-keyed stage-record
  legs at the free pair are E-3's to wire on the measured ITER-LAW shape — NOT
  prejudged here (E-3 is explicitly not this unit).

## THE CODEX FOLD (pre-commit adversarial pass, 2026-08-08)

Codex verdict on the draft: theorems sound for the as-built predicates (no
circularity; `OnTruncatedCarrier` NOT trivially true — the landing disjunction
forces monic stride-form/degree/weight (K0)-grade shape data), but two CRITICAL
description defects and two justification gaps, all folded in: (1) the core-free
carrier is a material widening of the signed E-1 — fixed by compiling the lawful
layer (`OnTruncatedCarrierL`/`TowerMoveClosureL`, discharged) alongside and scoping
every "discharge" claim to its layer; (2) "the signed SITE-EXH discharge" wording
conflated targets — all claims now name the AS-BUILT carrier explicitly, and the
open ORIGINAL row `TowerMoveClosure` is restated as untouched; (3) D-1(a)'s
"provably never" softened to interface-unprovability (the two-realizer separation
instance is not compiled); (4) "no-fork" re-scoped to one-way admission.

## THE BOX FACE (restated UNCHANGED — the disjoint displayed track)

`FiredLiftBox` (the classifier's own key producers `OM.B.liftKey` / `liftKeyExt`, in
the box coefficient rings) and `BoxKeyBridge` (the displayed key-transport residue)
are the SiteExhProbe §6 track: type-forced OFF this enumeration, owned by the M1
projective bridge.  Nothing here states, asserts, or discharges them; the engine-face
elimination `siteExh_elimination'` says NOTHING about box-face firings.

## WHAT IS NOT CLAIMED

E-3 (the composition glue: full run on f = truncated runs glued along the D-ITER
iterated development at interior e ≥ 2 reads) is its own follow-up unit on the
measured ITER-LAW — the extension's one genuinely new obligation, still open.
[E-3 LANDED 2026-08-08 — `H1/GlueRun.lean`: the STRUCTURAL glue is PROVED
(`truncRunFrom_glue`/`readsOfFrom_glue` + the f-tie `readsOf_glue`/`ftie_extends`,
junction packet `GlueJunction` = exactly the clauses this definition forces; the
RG-2 fence survives verbatim in its seam/promotion legs).  The composite carry
constants do NOT enter the glue itself; they live in the displayed junction-bundle
supplier, the named open `DIterJunctionSupplier` (ITER-LAW-shaped per the strata
probe; cyclic form fenced out) — which is deviation D-1's open additive refinement
resurfacing at the junction, as priced above.]  The
truncated carrier asserts landings of the pair (site stage, designated key) only; no
f-tied consumer strength is claimed.  `ReadsOf`/`HistoryCoherent`/`SideReads` and all
of `SiteExhProbe.lean`'s declarations are BYTE-UNCHANGED (E-4).
-/
import LeanUrat.Scaffold.HDischarge.H1.SiteExhProbe

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesJ

universe u

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-! ### §1 — E-1: the truncated-run kernel and the displayed carrier -/

/-- **The truncated-run KERNEL** (core-free — deviation D-2 of the header): a run whose
node-0 frame is the GIVEN stage.  Clause map (each `HistoryCoherent`/`ReadsOf` clause
verbatim or verbatim-instantiated; the agreement lemma `truncRunFrom_of_readsOf`
certifies the projections):
* [T-0] the node-0 FRAME PIN — replaces `HistoryCoherent`'s degree-1 base pin (E-1);
* [T-1] the slope law — VERBATIM `HistoryCoherent` conjunct 2, all nodes;
* [T-2] the γ-tie — VERBATIM `HistoryCoherent` conjunct 3, all nodes;
* [T-3] the interior transition legs ABOVE the base read (`0 < i`) — VERBATIM
  `HistoryCoherent` conjunct 4, the RG-2 fence `νᵢ.e = 1` INCLUDED (E-4);
* [T-4] the base read's own transition, PAIR-FREE: the five frame-chain clauses of the
  leg (ties, window, width chain, steepening); the species-keyed stage-record legs at
  the free base pair are E-3's (deviation D-3);
* [T-5] the per-read bundle: every read is against a frame-development of the LOCAL
  classificand `f₀` with an interior-pinned designated landing; FULL `SideReads` at
  every read ABOVE the base; every read's designated key is asserted by one of the two
  compiled landing forms — the run-borne `LandingKey` or the stage-level
  `IsStandardLift` at the frame pair (deviation D-1). -/
def TruncRunFrom (σ₀ : Stage p F) (f₀ : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  -- [T-0]
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ = σ₀) ∧
  -- [T-1]
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  -- [T-2]
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (((H.nodes[i]'hi).gam : ℤ) : ℚ)
      = ((H.nodes[i]'hi).e : ℚ) * ((H.strFrame i : ℚ) * (H.nodes[i]'hi).ustar)
        + ((((H.nodes[i]'hi).s0 + (H.nodes[i]'hi).wSide) : ℕ) : ℚ) * ((H.nodes[i]'hi).h : ℚ)) ∧
  -- [T-3]
  (∀ (i : ℕ) (hi0 : 0 < i) (hi : i + 1 < H.nodes.length),
    ((H.nodes[i]'(by omega)).species = ReadSpecies.recentering →
      IsRecenteringCore (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
        (H.nodes[i]'(by omega)).center (H.nodes[i]'(by omega)).lift) ∧
    ((H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering →
      (H.nodes[i]'(by omega)).e = 1 ∧
      ∃ σV : Stage p F,
        RegradeOf (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).e
            (H.nodes[i]'(by omega)).h σV ∧
        IsNodeLift (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi).σ.Φ ∧
        TransitionCoreL σV (H.nodes[i+1]'hi).σ
          (H.nodes[i+1]'hi).σ.Φ (H.nodes[i+1]'hi).e (H.nodes[i+1]'hi).h
          (H.nodes[i]'(by omega)).zbar) ∧
    ((H.nodes[i+1]'hi).σ.e = 1 → (H.nodes[i+1]'hi).σ.s = (H.nodes[i+1]'hi).s) ∧
    ((H.nodes[i+1]'hi).σ.e = 1 → (H.nodes[i+1]'hi).σ.t = (H.nodes[i+1]'hi).t) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope)) ∧
  -- [T-4]
  (∀ hi : 1 < H.nodes.length,
    ((H.nodes[1]'hi).σ.e = 1 → (H.nodes[1]'hi).σ.s = (H.nodes[1]'hi).s) ∧
    ((H.nodes[1]'hi).σ.e = 1 → (H.nodes[1]'hi).σ.t = (H.nodes[1]'hi).t) ∧
    ((H.nodes[1]'hi).s0 + (H.nodes[1]'hi).wSide ≤ (H.nodes[0]'(by omega)).μ) ∧
    ((H.nodes[1]'hi).Dwidth = (H.nodes[0]'(by omega)).childWidth) ∧
    ((H.nodes[0]'(by omega)).line.slope < (H.nodes[1]'hi).line.slope)) ∧
  -- [T-5]
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) (Φnext : Polynomial ℤ_[p]),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f₀ B Nd ∧
      (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
      (0 < i → SideReads (H.nodes[i]'hi) B Nd Φnext) ∧
      (LandingKey (H.nodes[i]'hi) Φnext ∨
        IsStandardLift (H.nodes[i]'hi).σ (H.nodes[i]'hi).ψ (H.nodes[i]'hi).g Φnext))

/-- **E-1 (the displayed carrier)** — the frozen-design signature: a truncated run from
the GIVEN lawful stage.  The lawfulness tag `hσ₀` is the carrier's interface for E-3
and (K0)-class consumers; the kernel is deliberately core-free (header deviation D-2 —
what makes the widened elimination unconditional), so the tag is definitionally
inert: `readsOfFrom_iff_kernel` is `Iff.rfl`. -/
def ReadsOfFrom (σ₀ : Stage p F) (hσ₀ : StageCoreL σ₀) (f₀ : Polynomial ℤ_[p])
    (H : History p F) : Prop :=
  TruncRunFrom σ₀ f₀ H

/-- The tag/kernel agreement, definitional. -/
theorem readsOfFrom_iff_kernel (σ₀ : Stage p F) (hσ₀ : StageCoreL σ₀)
    (f₀ : Polynomial ℤ_[p]) (H : History p F) :
    ReadsOfFrom σ₀ hσ₀ f₀ H ↔ TruncRunFrom σ₀ f₀ H := Iff.rfl

/-! ### §2 — the widened landing target -/

/-- **`OnTruncatedCarrier σ Φ'`** — the TRUNCATED-RUN BASE LANDING (the new displayed
carrier of the widened disjunction): the pair (site stage σ, produced key Φ') appears
at the base read of a truncated run — node 0 carries σ, the read is against a
frame-development of the run's local classificand, the designated key is Φ'
(interior-pinned), asserted by one of the two compiled landing forms.  Mirrors
`OnRecordedCarrier`'s leg (c) shape. -/
def OnTruncatedCarrier (σ : Stage p F) (Φ' : Polynomial ℤ_[p]) : Prop :=
  ∃ (f₀ : Polynomial ℤ_[p]) (H : History p F),
    TruncRunFrom σ f₀ H ∧
    ∃ h0 : 0 < H.nodes.length,
      (H.nodes[0]'h0).σ = σ ∧
      ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
        IsDevelopment (H.nodes[0]'h0).σ.Φ f₀ B Nd ∧
        (∀ h1 : 1 < H.nodes.length, Φ' = (H.nodes[1]'h1).σ.Φ) ∧
        (LandingKey (H.nodes[0]'h0) Φ' ∨
          IsStandardLift (H.nodes[0]'h0).σ (H.nodes[0]'h0).ψ (H.nodes[0]'h0).g Φ')

/-- **The WIDENED carrier disjunction** (E-2's landing target): recorded carriers ∪ the
truncated-run base landing. -/
def OnRecordedCarrier' (σ : Stage p F) (Φ' : Polynomial ℤ_[p]) : Prop :=
  OnRecordedCarrier σ Φ' ∨ OnTruncatedCarrier σ Φ'

/-- **The E-1-FAITHFUL (core-binding) truncated carrier** [CODEX FOLD, pre-commit
adversarial pass]: the signed signature's lawful form — the ∃ BINDS the parent core,
so this carrier admits exactly the `ReadsOfFrom`-hosted (lawful-stage) landings.
Strictly stronger than `OnTruncatedCarrier` (`onTruncated_of_lawful`); the row it
discharges is `TowerMoveClosureL` below, whose hypothesis is the engine's own S9/S10
calling convention (both take `StageCoreL σ`). -/
def OnTruncatedCarrierL (σ : Stage p F) (Φ' : Polynomial ℤ_[p]) : Prop :=
  ∃ (hσ : StageCoreL σ) (f₀ : Polynomial ℤ_[p]) (H : History p F),
    ReadsOfFrom σ hσ f₀ H ∧
    ∃ h0 : 0 < H.nodes.length,
      (H.nodes[0]'h0).σ = σ ∧
      ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
        IsDevelopment (H.nodes[0]'h0).σ.Φ f₀ B Nd ∧
        (∀ h1 : 1 < H.nodes.length, Φ' = (H.nodes[1]'h1).σ.Φ) ∧
        (LandingKey (H.nodes[0]'h0) Φ' ∨
          IsStandardLift (H.nodes[0]'h0).σ (H.nodes[0]'h0).ψ (H.nodes[0]'h0).g Φ')

/-- Monotonicity: the lawful (core-binding) landing implies the kernel landing. -/
theorem onTruncated_of_lawful (σ : Stage p F) (Φ' : Polynomial ℤ_[p])
    (h : OnTruncatedCarrierL σ Φ') : OnTruncatedCarrier σ Φ' := by
  obtain ⟨hσ, f₀, H, hrun, htail⟩ := h
  exact ⟨f₀, H, hrun, htail⟩

/-! ### §3 — the host construction (the E-2 base read) -/

/-- `ψ.coeff 0 ≠ 0` for a monic irreducible `ψ ≠ X` (the V10/HK05 pattern). -/
private lemma coeff_zero_ne_of_irr {K : Type*} [Field K] {ψ : Polynomial K}
    (hmon : ψ.Monic) (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X) :
    ψ.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := Polynomial.X_dvd_iff.mpr h0
  rcases hirr.isUnit_or_isUnit hu with hX | hUnit
  · exact Polynomial.not_isUnit_X hX
  · obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hUnit
    apply hne
    have hψX : ψ = Polynomial.C c * Polynomial.X := by rw [hu, ← hc.2]; ring
    have hlc : c = 1 := by
      have hm := hmon
      rw [hψX] at hm
      have hlead : (Polynomial.C c * Polynomial.X).leadingCoeff = c := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          Polynomial.leadingCoeff_X, mul_one]
      rw [Polynomial.Monic, hlead] at hm
      exact hm
    rw [hψX, hlc, map_one, one_mul]

/-- The frame key's self-development `Φ = 0 + 1·Φ` (the host's base-read development
of the local classificand `f₀ := σ.Φ`). -/
private lemma dev_self (σ : Stage p F) :
    IsDevelopment σ.Φ σ.Φ (fun j => if j = 1 then 1 else 0) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 1
    · simp only [hj, if_pos]
      rw [Polynomial.degree_one]
      exact Polynomial.natDegree_pos_iff_degree_pos.mp (by have := σ.hdeg; omega)
    · simp only [if_neg hj, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr
        (fun hb => σ.hmonic.ne_zero (Polynomial.degree_eq_bot.mp hb))
  · intro j hj
    dsimp only
    rw [if_neg (show ¬ j = 1 by omega)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num

/-- **The HOST READ** — the base read of the E-2 one-node truncated run at an arbitrary
stage σ: root species, read pair (1, 1), side `(s0, wSide) = (0, g₀)`, line of slope
`1/deg Φ` through `(g₀, 0)`, pattern := the residual `ψ₀`'s own coefficients
(`Ranch = ψ₀`, `ord_ψ₀ = 1`).  Every field is discharged by BARE `Stage` fields —
no `StageCoreL` (header deviation D-2). -/
noncomputable def hostNode (σ : Stage p F) (ψ₀ : Polynomial ↥σ.K) (g₀ : ℕ)
    (hmon : ψ₀.Monic) (hdeg : ψ₀.natDegree = g₀) (hirr : Irreducible ψ₀)
    (hg1 : 1 ≤ g₀) (hc0 : ψ₀.coeff 0 ≠ 0) (zb : Fˣ)
    (hzb : Polynomial.eval₂ σ.K.subtype ((zb : Fˣ) : F) ψ₀ = 0) : Node p F where
  species := ReadSpecies.root
  σ := σ
  e := 1
  h := 1
  s := 1
  t := 0
  g := g₀
  μ := 1
  a := 0
  s0 := 0
  wSide := g₀
  Dwidth := σ.Φ.natDegree
  line := ⟨(g₀ : ℚ), 1 / (σ.Φ.natDegree : ℚ)⟩
  ustar := 0
  gam := (g₀ : ℤ)
  zbar := zb
  center := 0
  lift := 0
  ψ := ψ₀
  pat := fun k => ψ₀.coeff k
  Ranch := ψ₀
  he := le_refl 1
  hh := le_refl 1
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := hg1
  hμ := le_refl 1
  hEdvd := one_dvd _
  hDwidth := rfl
  hψmonic := hmon
  hψdeg := hdeg
  hψirr := hirr
  hRanch := by
    simp only [Nat.div_one]
    conv_lhs => rw [ψ₀.as_sum_range' (g₀ + 1) (by rw [hdeg]; omega)]
    exact Finset.sum_congr rfl fun k _ => (Polynomial.C_mul_X_pow_eq_monomial).symm
  hpat0 := hc0
  hpatTop := by
    show ψ₀.coeff (g₀ / 1) ≠ 0
    rw [Nat.div_one, ← hdeg, hmon.coeff_natDegree]
    exact one_ne_zero
  hAnchor := by norm_num
  hLineU := by
    have hD : ((σ.Φ.natDegree : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by have := σ.hdeg; omega)
    show (g₀ : ℚ) - 1 / (σ.Φ.natDegree : ℚ) * (((0 + g₀) * σ.Φ.natDegree : ℕ) : ℚ) = 0
    push_cast
    field_simp
    ring
  hOrd := by
    constructor
    · rw [pow_one]
    · intro hdvd
      have hle := Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
      rw [Polynomial.natDegree_pow, hdeg] at hle
      omega
  hzbarRoot := hzb
  hspecInc := by intro hcontra; exact ReadSpecies.noConfusion hcontra
  hspecRec := by intro hcontra; exact ReadSpecies.noConfusion hcontra
  hspecRecCenter := by intro hcontra; exact ReadSpecies.noConfusion hcontra

/-- The one-node host history. -/
noncomputable def hostHist (ν : Node p F) (hroot : ν.species = ReadSpecies.root) :
    History p F where
  nodes := [ν]
  nonempty := by simp
  root_iff := by
    intro j hj
    have hj1 : j < 1 := by simpa using hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact iff_of_true hroot rfl

/-- **The master hosting lemma**: any stage-level standard lift `Φland` of an
irreducible rooted residual `(ψ₀, g₀)` at σ is the designated base landing of a
ONE-NODE truncated run on σ (local classificand `f₀ := σ.Φ`, its self-development).
Core-free. -/
theorem standardLift_hosts (σ : Stage p F) (ψ₀ : Polynomial ↥σ.K) (g₀ : ℕ)
    (hirr : Irreducible ψ₀) (hg1 : 1 ≤ g₀) (hc0 : ψ₀.coeff 0 ≠ 0)
    (zb : Fˣ) (hzb : Polynomial.eval₂ σ.K.subtype ((zb : Fˣ) : F) ψ₀ = 0)
    (Φland : Polynomial ℤ_[p]) (hland : IsStandardLift σ ψ₀ g₀ Φland) :
    ∃ (f₀ : Polynomial ℤ_[p]) (H : History p F),
      TruncRunFrom σ f₀ H ∧ H.nodes.length = 1 ∧
      ∃ h0 : 0 < H.nodes.length,
        (H.nodes[0]'h0).σ = σ ∧
        ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
          IsDevelopment (H.nodes[0]'h0).σ.Φ f₀ B Nd ∧
          (∀ h1 : 1 < H.nodes.length, Φland = (H.nodes[1]'h1).σ.Φ) ∧
          (LandingKey (H.nodes[0]'h0) Φland ∨
            IsStandardLift (H.nodes[0]'h0).σ (H.nodes[0]'h0).ψ (H.nodes[0]'h0).g Φland) := by
  have hD : ((σ.Φ.natDegree : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := σ.hdeg; omega)
  refine ⟨σ.Φ, hostHist (hostNode σ ψ₀ g₀ hland.1 hland.2.1 hirr hg1 hc0 zb hzb) rfl,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, Nat.one_pos, rfl, ?_⟩
  · -- [T-0] the frame pin
    intro h0
    rfl
  · -- [T-1] the slope law at the single node
    intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    show (1 / (σ.Φ.natDegree : ℚ)) *
        (((1 : ℕ) : ℚ) * ((1 : ℕ) : ℚ) * ((σ.Φ.natDegree : ℕ) : ℚ)) = ((1 : ℕ) : ℚ)
    push_cast
    field_simp
  · -- [T-2] the γ-tie at the single node
    intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    show (((g₀ : ℤ) : ℚ))
        = ((1 : ℕ) : ℚ) * (((1 : ℕ) : ℚ) * (0 : ℚ)) + (((0 + g₀ : ℕ)) : ℚ) * ((1 : ℕ) : ℚ)
    push_cast
    ring
  · -- [T-3] interior legs: vacuous at length 1
    intro i hi0 hi
    exact absurd (show i + 1 < 1 from hi) (by omega)
  · -- [T-4] base transition: vacuous at length 1
    intro h1
    exact absurd (show (1 : ℕ) < 1 from h1) (by omega)
  · -- [T-5] the single read: self-development + the designated standard-lift landing
    intro i hi
    have hi1 : i < 1 := hi
    have h0 : i = 0 := by omega
    subst h0
    exact ⟨(fun j => if j = 1 then 1 else 0), 2, Φland, dev_self σ,
      fun h1 => absurd (show (1 : ℕ) < 1 from h1) (by omega),
      fun hlt => absurd hlt (by omega),
      Or.inr hland⟩
  · -- the carrier tail: the base-read landing data, re-displayed
    exact ⟨(fun j => if j = 1 then 1 else 0), 2, dev_self σ,
      fun h1 => absurd (show (1 : ℕ) < 1 from h1) (by omega),
      Or.inr hland⟩

/-! ### §4 — E-2: every engine move is a hosted standard lift -/

/-- **The reduction lemma (E-2's compiled content)**: every `MoveWitness σ σ'` exhibits
its fired key `σ'.Φ` as a stage-level standard lift `IsStandardLift σ ψ₀ g₀ σ'.Φ` of an
irreducible rooted residual — the increment face through its own `TransHyp.hlift`
(`ψ₀ := ψ`, `TransitionData.child_key`), the recentering face through the realizer
`−tt` re-read as the standard lift of `ψ₀ := X + C c` at the frame pair (`c` the (S5)
digit unit of `−tt`; `σ.e = 1` and `σ.t = 0` at every recentering parent).  Discharged
by bare `Stage` fields only. -/
theorem moveWitness_standardLift (σ σ' : Stage p F) (mw : HC1.MoveWitness σ σ') :
    ∃ (ψ₀ : Polynomial ↥σ.K) (g₀ : ℕ) (zb : Fˣ),
      Irreducible ψ₀ ∧ 1 ≤ g₀ ∧ ψ₀.coeff 0 ≠ 0 ∧
      Polynomial.eval₂ σ.K.subtype ((zb : Fˣ) : F) ψ₀ = 0 ∧
      IsStandardLift σ ψ₀ g₀ σ'.Φ := by
  cases mw with
  | inc ψ g Φhat e' h' zbar hyp core core' =>
      refine ⟨ψ, g, zbar, hyp.hirr, hyp.hg,
        coeff_zero_ne_of_irr hyp.hmonic hyp.hirr hyp.hne_z, ?_, ?_⟩
      · -- the recorded root, `aeval`-to-`eval₂` converted
        have h := hyp.hroot
        rw [Polynomial.aeval_def, Polynomial.eval₂_map] at h
        simpa using h
      · rw [core.base.child_key]
        exact hyp.hlift
  | recenter cc tt core core' =>
      obtain ⟨he1, -, -, hinC, htt, hwt, -, hΦ', -⟩ := core.base
      have ht0 : σ.t = 0 := σ.he1t he1
      -- w 1 = 0 and w (−1) = 0 from the multiplicativity law alone
      have hw1 : σ.w 1 = 0 := by
        have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
        rw [mul_one] at h
        omega
      have hwm1 : σ.w (-1) = 0 := by
        have h := σ.hwmul (-1) (-1) (by norm_num) (by norm_num)
        rw [neg_mul_neg, one_mul] at h
        omega
      have hmtt : (-tt) ≠ 0 := neg_ne_zero.mpr htt
      have hinCm : inC σ.Φ (-tt) := by
        show (-tt).degree < σ.Φ.degree
        rw [Polynomial.degree_neg]
        exact hinC
      -- σ.w (−tt) = σ.h (the realizer sits at the key weight)
      have hwm : σ.w (-tt) = (σ.h : ℤ) := by
        have h := σ.hwmul (-1) tt (by norm_num) htt
        rw [neg_one_mul] at h
        rw [h, hwm1, hwt, σ.hwΦ]
        ring
      -- σ.wPrev (−tt) = σ.h (unramified stretch at σ.e = 1)
      have hwPm : σ.wPrev (-tt) = (σ.h : ℤ) := by
        have h := σ.hStretch (-tt) hmtt hinCm
        rw [he1] at h
        simp only [Nat.cast_one, one_mul] at h
        omega
      -- the (S5) digit unit of −tt, at the forced position 0 (σ.t = 0)
      obtain ⟨c, hc⟩ := σ.hS5 (-tt) hmtt hinCm
      rw [ht0] at hc
      simp only [neg_zero, zero_mul] at hc
      have hcne : (c : ↥σ.K) ≠ 0 := c.ne_zero
      have hcF : ((c : ↥σ.K) : F) ≠ 0 := by exact_mod_cast hcne
      have hcoeff0 : (Polynomial.X + Polynomial.C (c : ↥σ.K)).coeff 0 = (c : ↥σ.K) := by
        simp
      refine ⟨Polynomial.X + Polynomial.C (c : ↥σ.K), 1,
        Units.mk0 (-((c : ↥σ.K) : F)) (neg_ne_zero.mpr hcF), ?_, le_refl 1, ?_, ?_, ?_⟩
      · -- irreducibility of the linear residual
        have hXC : (Polynomial.X + Polynomial.C (c : ↥σ.K))
            = Polynomial.X - Polynomial.C (-(c : ↥σ.K)) := by
          rw [map_neg, sub_neg_eq_add]
        rw [hXC]
        exact Polynomial.irreducible_X_sub_C _
      · rw [hcoeff0]
        exact hcne
      · -- the root: −c
        show Polynomial.eval₂ σ.K.subtype
            ((Units.mk0 (-((c : ↥σ.K) : F)) (neg_ne_zero.mpr hcF) : Fˣ) : F)
            (Polynomial.X + Polynomial.C (c : ↥σ.K)) = 0
        rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
        show -((c : ↥σ.K) : F) + σ.K.subtype (c : ↥σ.K) = 0
        simp
      · -- IsStandardLift σ (X + C c) 1 σ'.Φ, realizer family (−tt at slot 0)
        refine ⟨Polynomial.monic_X_add_C _, Polynomial.natDegree_X_add_C _,
          (fun k => if k = 0 then -tt else 0), ?_, ?_, ?_⟩
        · intro k hk
          by_cases h0 : k = 0
          · subst h0
            rw [hcoeff0] at hk
            exact absurd hk hcne
          · simp only [if_neg h0]
        · intro k hklt hkne
          have h0 : k = 0 := by omega
          subst h0
          simp only [if_pos]
          refine ⟨hmtt, hinCm, ?_, ?_⟩
          · rw [hwPm]
            push_cast
            ring
          · rw [hcoeff0, ht0]
            simp only [neg_zero, zero_mul]
            simpa using hc
        · rw [hΦ', he1, Finset.sum_range_one]
          simp only [reduceIte, one_mul, mul_one, pow_one, pow_zero]
          exact sub_eq_add_neg σ.Φ tt

/-- **E-2, KERNEL form — UNCONDITIONAL over the junk-hostable `∀`** (what the widened
row discharge consumes): every `MoveWitness` lands its fired pair (σ, σ'.Φ) on the
truncated-run base carrier. -/
theorem moveWitness_hosts (σ σ' : Stage p F) (mw : HC1.MoveWitness σ σ') :
    OnTruncatedCarrier σ σ'.Φ := by
  obtain ⟨ψ₀, g₀, zb, hirr, hg1, hc0, hzb, hland⟩ := moveWitness_standardLift σ σ' mw
  obtain ⟨f₀, H, hrun, hlen, h0, hσ0, B, Nd, hdev, hpin, hlandK⟩ :=
    standardLift_hosts σ ψ₀ g₀ hirr hg1 hc0 zb hzb σ'.Φ hland
  exact ⟨f₀, H, hrun, h0, hσ0, B, Nd, hdev, hpin, hlandK⟩

/-- **E-2 VERBATIM (the displayed form)**: every `MoveWitness σ σ'` at a `StageCoreL σ`
is the base read of a ONE-NODE truncated run (`ReadsOfFrom`, the tagged carrier), with
the designated landing `Φnext := σ'.Φ`. -/
theorem moveWitness_hosts_readsOfFrom (σ σ' : Stage p F) (hσ : StageCoreL σ)
    (mw : HC1.MoveWitness σ σ') :
    ∃ (f₀ : Polynomial ℤ_[p]) (H : History p F),
      ReadsOfFrom σ hσ f₀ H ∧ H.nodes.length = 1 ∧
      ∃ h0 : 0 < H.nodes.length,
        (H.nodes[0]'h0).σ = σ ∧
        ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
          IsDevelopment (H.nodes[0]'h0).σ.Φ f₀ B Nd ∧
          (LandingKey (H.nodes[0]'h0) σ'.Φ ∨
            IsStandardLift (H.nodes[0]'h0).σ (H.nodes[0]'h0).ψ (H.nodes[0]'h0).g σ'.Φ) := by
  obtain ⟨ψ₀, g₀, zb, hirr, hg1, hc0, hzb, hland⟩ := moveWitness_standardLift σ σ' mw
  obtain ⟨f₀, H, hrun, hlen, h0, hσ0, B, Nd, hdev, hpin, hlandK⟩ :=
    standardLift_hosts σ ψ₀ g₀ hirr hg1 hc0 zb hzb σ'.Φ hland
  exact ⟨f₀, H, hrun, hlen, h0, hσ0, B, Nd, hdev, hlandK⟩

/-! ### §5 — the widened row, DISCHARGED; the unconditional elimination -/

/-- **The widened residue row** — `TowerMoveClosure` (SiteExhProbe §3) at the WIDENED
landing target.  Unlike the original row, this one is a THEOREM
(`towerMoveClosure'_discharged`). -/
def TowerMoveClosure' (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] : Prop :=
  ∀ (σ σ' : Stage p F), HC1.MoveWitness σ σ' → OnRecordedCarrier' σ σ'.Φ

/-- **THE DISCHARGE (kernel carrier)** — the adjudicated residue row, closed at the
AS-BUILT widened target: every stage-level engine move — junk parents included —
lands on the truncated leg.  What is discharged here is the row AT THE KERNEL
(core-free) carrier; the signed-signature (core-binding) form is
`towerMoveClosureL_discharged` below, at the engine's own calling convention. -/
theorem towerMoveClosure'_discharged : TowerMoveClosure' p F :=
  fun σ σ' mw => Or.inr (moveWitness_hosts σ σ' mw)

/-- **The widened row at the E-1-FAITHFUL carrier** [CODEX FOLD]: the residue row over
the engine's LAWFUL perimeter — parents with `StageCoreL`, exactly S9/S10's own
hypothesis (every engine-constructed move fires at a cored parent: `Tower.base` cores
the base, each move's `core'` cores the child).  Target: recorded carriers ∪ the
CORE-BINDING truncated landing. -/
def TowerMoveClosureL (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] : Prop :=
  ∀ (σ σ' : Stage p F), StageCoreL σ → HC1.MoveWitness σ σ' →
    OnRecordedCarrier σ σ'.Φ ∨ OnTruncatedCarrierL σ σ'.Φ

/-- **THE DISCHARGE (lawful carrier)** — the widened row at the signed E-1 signature,
closed on the engine's lawful perimeter. -/
theorem towerMoveClosureL_discharged : TowerMoveClosureL p F := by
  intro σ σ' hσ mw
  obtain ⟨f₀, H, hrun, h0, hσ0, B, Nd, hdev, hpin, hland⟩ := moveWitness_hosts σ σ' mw
  exact Or.inr ⟨hσ, f₀, H, hrun, h0, hσ0, B, Nd, hdev, hpin, hland⟩

/-- The widened landing predicate on the closed enumeration — `FiredLift.Lands` with
the widened carrier disjunction (per-constructor shapes unchanged). -/
def FiredLift.Lands' : FiredLift p F → Prop
  | .histNonrec H _ i hi1 _ =>
      OnRecordedCarrier' ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ)
  | .histRec H _ i hi1 _ =>
      OnRecordedCarrier' ((H.nodes[i]'(Nat.lt_of_succ_lt hi1)).σ) ((H.nodes[i+1]'hi1).σ.Φ)
  | .runLanding _ _ H _ i hi =>
      ∃ Φnext : Polynomial ℤ_[p],
        (∀ hi1 : i + 1 < H.nodes.length, Φnext = (H.nodes[i+1]'hi1).σ.Φ) ∧
        OnRecordedCarrier' ((H.nodes[i]'hi).σ) Φnext
  | .towerMove σ σ' _ => OnRecordedCarrier' σ σ'.Φ

/-- Monotonicity: the recorded landing implies the widened landing. -/
theorem lands'_of_lands (fl : FiredLift p F) (h : fl.Lands) : fl.Lands' := by
  cases fl with
  | histNonrec H hH i hi1 hspec => exact Or.inl h
  | histRec H hH i hi1 hspec => exact Or.inl h
  | runLanding n f H hRO i hi =>
      obtain ⟨Φn, hpin, hc⟩ := h
      exact ⟨Φn, hpin, Or.inl hc⟩
  | towerMove σ σ' mw => exact Or.inl h

/-- **THE ENGINE-FACE ELIMINATION AT THE AS-BUILT WIDENED CARRIER, unconditional**:
every fired lift of the closed engine-face enumeration lands on the widened
disjunction `Lands'` — the three run-borne shapes on the recorded carriers (as
before), the stage-level `towerMove` shape on the truncated-run base landing (kernel
carrier: junk parents included, per the header's D-2/Codex-fold scoping).  No
hypothesis row remains against THIS target; the ORIGINAL narrow-target row
`TowerMoveClosure` stands open as displayed, and the box face
(`FiredLiftBox`/`BoxKeyBridge`, SiteExhProbe §6) is the separate displayed track,
untouched. -/
theorem siteExh_elimination' : ∀ fl : FiredLift p F, fl.Lands' := by
  intro fl
  cases fl with
  | histNonrec H hH i hi1 hspec => exact Or.inl (histNonrec_lands H hH i hi1 hspec)
  | histRec H hH i hi1 hspec => exact Or.inl (histRec_lands H hH i hi1 hspec)
  | runLanding n f H hRO i hi =>
      obtain ⟨Φn, hpin, hc⟩ := readsOf_landing_lands n f H hRO i hi
      exact ⟨Φn, hpin, Or.inl hc⟩
  | towerMove σ σ' mw => exact towerMoveClosure'_discharged σ σ' mw

/-! ### §6 — the agreement lemma on the overlap (the no-fork certificate) -/

/-- **The compiled agreement lemma**: every full `ReadsOf` run is a truncated run from
its own root frame — [T-0] is `rfl`, [T-1]/[T-2]/[T-3] are the verbatim
`HistoryCoherent` conjuncts, [T-4] projects the pair-free clauses of the `i = 0` leg,
[T-5]'s landing is `SideReads` clause (iv).  This certifies the truncated clauses as
verbatim instances (no fork of `ReadsOf`/`HistoryCoherent` content). -/
theorem truncRunFrom_of_readsOf (n : ℕ) (f : Polynomial ℤ_[p]) (H : History p F)
    (hRO : ReadsOf p F n f H) (h0 : 0 < H.nodes.length) :
    TruncRunFrom ((H.nodes[0]'h0).σ) f H := by
  obtain ⟨hmon, hdegn, hHC, hreads⟩ := hRO
  obtain ⟨hdeg1, hslope, hgam, hleg⟩ := hHC
  refine ⟨fun _ => rfl, hslope, hgam, ?_, ?_, ?_⟩
  · intro i hi0 hi
    exact hleg i hi
  · intro hi
    obtain ⟨-, -, hs, ht, hwin, hDw, hsl⟩ := hleg 0 hi
    exact ⟨hs, ht, hwin, hDw, hsl⟩
  · intro i hi
    obtain ⟨B, Nd, Φnext, hdev, hpin, hside⟩ := hreads i hi
    exact ⟨B, Nd, Φnext, hdev, hpin, fun _ => hside, Or.inl hside.2.2.2.1⟩

/-! ### §7 — gates (non-vacuity, positive; the RCW instance re-fired through the new
path) -/

/-- `StageCoreL` for the RCW gate parent σ₁rec (re-derived from the HK-15 forged-child
supplier — `RCWitness`'s in-file derivation is private). -/
lemma score_σ₁rec : StageCoreL HK25.σ₁rec :=
  (gateChildStage_exists 1 3 (le_refl 1) (by norm_num) (by norm_num)
    HK47.transHyp_gate.hiaug).choose_spec.2.1

/-- **GATE (E-1/E-2 non-vacuity, kernel): the RCW recentering move HOSTS** — the
S10-fired `mwRC : MoveWitness σ₁rec σ₂rc` lands its pair (σ₁rec, σ₂rc.Φ) on the
truncated-run base carrier.  The recentering `MoveWitness` hosts in a truncated run:
E-1 is inhabited on a compiled engine instance. -/
theorem gate_mwRC_hosts : OnTruncatedCarrier HK25.σ₁rec RCW.σ₂rc.Φ :=
  moveWitness_hosts _ _ mwRC

/-- **GATE (E-2 verbatim, displayed form): the RCW move is the base read of a ONE-NODE
`ReadsOfFrom` run** at its `StageCoreL` parent, designated landing σ₂rc.Φ. -/
theorem gate_mwRC_readsOfFrom :
    ∃ (f₀ : Polynomial ℤ_[2]) (H : History 2 F4),
      ReadsOfFrom HK25.σ₁rec score_σ₁rec f₀ H ∧ H.nodes.length = 1 ∧
      ∃ h0 : 0 < H.nodes.length,
        (H.nodes[0]'h0).σ = HK25.σ₁rec ∧
        ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ),
          IsDevelopment (H.nodes[0]'h0).σ.Φ f₀ B Nd ∧
          (LandingKey (H.nodes[0]'h0) RCW.σ₂rc.Φ ∨
            IsStandardLift (H.nodes[0]'h0).σ (H.nodes[0]'h0).ψ (H.nodes[0]'h0).g
              RCW.σ₂rc.Φ) :=
  moveWitness_hosts_readsOfFrom HK25.σ₁rec RCW.σ₂rc score_σ₁rec mwRC

/-- **GATE (the towerMove shape, re-fired through the new path)**: the SiteExhProbe §5
gate instance `flTower` now lands UNconditionally on the widened disjunction — the
residue row that carried it is discharged. -/
theorem gate_flTower_lands' : flTower.Lands' :=
  siteExh_elimination' flTower

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.moveWitness_standardLift
#print axioms LeanUrat.Scaffold.HDischarge.H1.standardLift_hosts
#print axioms LeanUrat.Scaffold.HDischarge.H1.moveWitness_hosts
#print axioms LeanUrat.Scaffold.HDischarge.H1.moveWitness_hosts_readsOfFrom
#print axioms LeanUrat.Scaffold.HDischarge.H1.towerMoveClosure'_discharged
#print axioms LeanUrat.Scaffold.HDischarge.H1.towerMoveClosureL_discharged
#print axioms LeanUrat.Scaffold.HDischarge.H1.onTruncated_of_lawful
#print axioms LeanUrat.Scaffold.HDischarge.H1.siteExh_elimination'
#print axioms LeanUrat.Scaffold.HDischarge.H1.truncRunFrom_of_readsOf
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_mwRC_hosts
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_mwRC_readsOfFrom
#print axioms LeanUrat.Scaffold.HDischarge.H1.gate_flTower_lands'
