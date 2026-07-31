/-
Unit U21.readsOf_HV  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk:
exponent bookkeeping across two conventions — the MovesC F10 index lesson applies)
moves_ref: §C C.0 (HV) "the data IDENTITY pattern lead of ν_{i+1} = vtx(ν_i) with the
FULL transported vertex value".
deps: D4 (incl. the NEW clause (vi), N-4), Moves L5_landVertexDigit{,_repair} +
L5_landTransport_R4 + LandingCylinderL (PROVED — D.8's two-sided landing with the vertex
unit).  difficulty: medium-hard bookkeeping (post-N-4).
sketch: the adjacent read's hinge digit is the transported vertex digit by D.8's (VERTEX)
clause; unfold `Node.vtx`'s scalar bookkeeping (`z̄^{a−μm̂}` — the anchor/normalization
exponents match `LandingCylinderL`'s `T(μ·m̂ − a)` unit literally).
hypothesis_fields: none.
N-4 RESTATEMENT (2026-07-28, sign-off round — §9 F-3 executed; STATEMENT byte-unchanged,
the restatement is the DERIVATION ROUTE): the layer-2 TERMINAL interface gap is closed
by `SideReads` clause (vi) (Defs) — the vertex read-off `σ.digPrime zbar (Bh μ) = vtx`
at the designated next key's development. U21 is now a DERIVATION: at the transition
i → i+1, `ReadsOf` gives the frame-(i+1) development B' of f with the recorded child key
= read i's Φnext (the pin), so clause (vi) at read i fires on B' giving
`σ_i.digPrime zbar_i (B' μ_i) = vtx(ν_i)`; SideReads(i+1) clause (ii) at the top stride
`k = wSide'/e'` (adjacency puts `s0'+wSide' = μ_i`) reads the recorded pattern lead off
`B' μ_i` as a frame-(i+1) residual; the cross-frame digit bookkeeping
(`TransitionCoreL.child_dig_frame` + L5's z̄-exponent identities) ties the two. The
clause records only the minimal un-derivable fact — never (HV) itself. PROOF QUEUED
(fleet; medium-hard bookkeeping). U31's clause-(vi) gate re-run is the mandatory
non-vacuity companion (queued there).

═══════════════════════════════════════════════════════════════════════════════════════
U21.HV SPECIALIST ROUND (2026-07-28) — the D.7(v) warrant CHECKED against U21's mfun;
the reduction LANDED as a proved theorem; the residue is now EXACT and machine-scoped.

THE CHARGE. Since the last round, `mfun ≡ 0` gained a real warrant — D.7(v)'s D-map
DEFINITION (MOVES 2364–2367: "D(x) := R(x) mod ψ ∈ F′"; reduction mod ψ IS evaluation at
the root z̄, i.e. Lean's `digPrime` — recorded at HC1 blueprint §10.7(A) and
`HC1.DefsChild.ChildResData.hS5'`). Check whether that warrant pins U21's `mfun` (the
`child_dig_frame` existential); if yes close, if no deliver the exact residue.

FINDING: THE WARRANT DOES NOT REACH — different transition instance. Three grounds:
(1) INSTANCE MISMATCH. The warrant's Lean carriers (`ChildResData.hS5'`; `VertexPin` of
    HC1/K1_vertexPin; realized by `V8_childResidual.v8Rc_S5'`) pin the CONSTRUCTED child
    residual — the D-map `Rc` that HC1's S9/V8 chain BUILDS from parent data, where
    `mfun ≡ 0` holds by definition. U21's `mfun` is the existential inside the RECORDED
    `TransitionCoreL` that `HistoryCoherent` carries for an ARBITRARY `ReadsOf` history:
    the recorded child stage σ′ is constrained only by the clause set, and NO clause in
    `ReadsOf`'s cone (`HistoryCoherent`/`TransitionCoreL`/`SideReads`/`Node`/bare `Stage`
    laws) identifies σ′.R with the D-map or with any `ChildResData` carrier.
(2) CERTIFIED UNDERIVABILITY (unchanged by the warrant). The S8 dual-audited twist
    symmetry (HC1/S8_childS6.lean header certificate, Fable + Codex): with ẑ := z̄ ∈ ↥σ′.K
    and λ : ℤ, replacing ONLY σ′.R by `R̃ f := C (ẑ^{λ·σ′.w f}) · σ′.R f` preserves every
    `Stage` law (hRΦ iff ord z̄ ∣ λh′; hS6a if z̄^{λe′} ∈ FQ) and preserves
    `child_dig_frame` via `mfun ↦ mfun + λe′·id`; the recorded interface pins only
    `z̄^{λh′} = 1` and `z̄^{λe′} ∈ FQ` — never `z̄^λ = 1`. So no proof of the pin from the
    recorded class exists; the S7-escalation record (⋆) names the same twist as the wall.
    The warrant is NOTE-side justification that the intended model has no twist — it adds
    no Lean-side clause to the recorded class.
(3) WHAT THE WARRANT DOES LICENSE (sign-off item, NOT executed here — statement fence:
    `Moves/DefsL.lean` is frozen): the upstream repair the S7 scratch already named
    ("same honest fix, UPSTREAM: pin `child_dig_frame`'s mfun") is now note-warranted by
    D.7(v) itself, not merely by D.7(vi)'s V′ display. Pinning the recorded clause (or
    copying `RunVertexPin` below into the coherence record) is a Defs change for Asvin's
    queue; after it, `readsOf_HV` closes by `exact readsOf_HV_of_pin … (fun _ => pin)`.

WHAT IS PROVED THIS ROUND (in this file, zero new axioms):
* `readsOf_HV_of_pin` — THE FULL REDUCTION, a theorem (Lean-core footprint): (HV) from
  `ReadsOf` + adjacency + [non-recentering parents only] the vertex pin at the recorded
  (i, i+1) transition. Route exactly as the N-4 restatement bills it: clause (vi)@i fired
  on read (i+1)'s recorded development (the `Φnext` pin ties the keys), SideReads(ii)@i+1
  at the top stride k = wSide′/e′ with `hEdvd` + `hpatTop` (adjacency lands the slot on
  μ_i), then the frame change through the pin + `child_wPrev`, scalars extracted by
  Laurent-monomial equality.
* THE RECENTERING-PARENT LEG CLOSES UNCONDITIONALLY (no pin): coherence's recentering leg
  is `IsRecenteringCore`, whose `IsRecentering` base carries the residual-literal frame
  change — the digPrime-equality clause on parent coefficients (same K, same digits) —
  and `σ′.e = 1` forces `σ′.t = 0` (`he1t`), so the frame-(i+1) residual scalar of B′ μ_i
  IS its digPrime at every root. No twist freedom exists at a recentering.
THE EXACT RESIDUE (the one remaining sorry, at the pin): `RunVertexPin` at the recorded
transition of a run, non-recentering parents — HC1's `VertexPin` formula verbatim
(= `child_dig_frame` with `mfun ≡ 0`), needed only at the single element B′ μ_i (parent
weight w₀ = σ_i.w (B′ μ_i) = (gam′ − μ_i·h′)/e′; the ∀-form is stated because the run's
development is existential). Consumers: U23's (HV) leg via `readsOf_HV` (byte-unchanged).
═══════════════════════════════════════════════════════════════════════════════════════

QUEUE ITEM 21 EXECUTED (2026-07-31, Asvin sign-off): the residue is HOISTED — the sorry
is GONE. `readsOf_HV` is RE-TYPED to carry the named hypothesis `hpin` (the
`RunVertexPin` residue, exactly as `readsOf_HV_of_pin` bills it; hpin placed before
hadj so the (HV)-conjunct partial-application shape survives) and is discharged BY
`readsOf_HV_of_pin` — the unit is now sorry-free, Lean-core. Frozen `Moves/DefsL`
untouched. Consumer re-point: U23 `readsOf_realizable` gains the matching ∀-reads named
row and threads it (its own record there).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ## Laurent monomial scalar extraction (local; the HC1/K1_vertexPin `CT` calculus) -/

private lemma CT_apply' {K : Type*} [Field K] (c : K) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial K) q
      = if n = q then c else 0 := by
  have h1 : LaurentPolynomial.C c * LaurentPolynomial.T n
      = (Finsupp.single n c : LaurentPolynomial K) :=
    (LaurentPolynomial.single_eq_C_mul_T c n).symm
  have h0 := congrArg (fun t : ℤ →₀ K => t q) h1
  exact h0.trans Finsupp.single_apply

/-- Equal `C·T` monomials at the SAME position have equal scalars. -/
private lemma CT_eq_scalar {K : Type*} [Field K] {c c' : K} {n : ℤ}
    (h : LaurentPolynomial.C c * LaurentPolynomial.T n
       = LaurentPolynomial.C c' * LaurentPolynomial.T n) : c = c' := by
  have h1 := congrArg (fun t : ℤ →₀ K => t n) h
  rw [CT_apply', CT_apply', if_pos rfl, if_pos rfl] at h1
  exact h1

/-- Equal `C·T` monomials with a NONZERO right scalar have equal scalars at ANY pair of
positions (HK-06 wave supply, 2026-07-31: the σV regrade re-route shifts the recorded
position term — `child_wPrev` now lands on `σV.w`, the pin on `σᵢ.w` — but both
monomials are one and the same Laurent element, so the scalars agree regardless). -/
private lemma CT_eq_scalar_of_ne_zero {K : Type*} [Field K] {c c' : K} {m n : ℤ}
    (h : LaurentPolynomial.C c * LaurentPolynomial.T m
       = LaurentPolynomial.C c' * LaurentPolynomial.T n) (hc' : c' ≠ 0) : c = c' := by
  by_cases hmn : m = n
  · subst hmn; exact CT_eq_scalar h
  · exfalso
    have h1 := congrArg (fun t : ℤ →₀ K => t n) h
    rw [CT_apply', CT_apply', if_neg hmn, if_pos rfl] at h1
    exact hc' h1.symm

/-! ## The exact residue, named -/

/-- **THE U21 RESIDUE — the vertex pin at a recorded run transition** (HC1's
`K1_vertexPin.VertexPin` formula VERBATIM, transplanted to the HC-2 cone; =
`TransitionCoreL.child_dig_frame` with the frame-unit exponent pinned, `mfun ≡ 0`):
the child residual of every Φ̂-coefficient is the monomial unit at the forced position
whose scalar's F-image IS the parent ψ-digit `digPrime`. NOTE-WARRANT: D.7(v)'s D-map
definition (MOVES 2364–2367 — the child digit map is DEFINED as raw parent-residual
evaluation; blueprint §10.7(A), `ChildResData.hS5'`). LEAN STATUS: NOT derivable from
the recorded class (the S8 dual-audited twist symmetry `mfun ↦ mfun + λe′·id` moves it
while fixing every recorded hypothesis — see this file's header); realized BY
CONSTRUCTION on HC1's built child (`v8Rc_S5'`), so its discharge at run level is the
Wall A↔B seam: HC1-constructed histories, or the sign-off pin of `child_dig_frame`. -/
def RunVertexPin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (zbar : Fˣ) : Prop :=
  ∀ B : Polynomial ℤ_[p], B ≠ 0 → inC Φhat B →
    ∃ c' : (↥σ'.K)ˣ,
      σ'.R B = LaurentPolynomial.C ((c' : ↥σ'.K)) *
          LaurentPolynomial.T (- σ'.t * σ.w B) ∧
      ((c' : ↥σ'.K) : F) = σ.digPrime zbar B

/-! ## The reduction, PROVED -/

/-- **(HV) FROM THE PIN — the complete N-4 derivation route, machine-checked** (this
round; zero sorry): at an adjacent consecutive read of a run, the pattern LEAD equals
the transported vertex value, GIVEN the vertex pin at the recorded (i, i+1) transition
when the parent read is not a recentering. The RECENTERING-parent leg needs NO pin —
coherence's `IsRecenteringCore` base is residual-literal (digPrime-equality on parent
coefficients + `σ′.t = 0` via `he1t`). Route: clause (vi)@i on read (i+1)'s recorded
development + SideReads(ii)@i+1 at the top stride + adjacency + `child_wPrev` +
Laurent-monomial scalar extraction. -/
theorem readsOf_HV_of_pin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ)
    (hpin : (H.nodes[i]'(by omega : i < H.nodes.length)).species
        ≠ ReadSpecies.recentering →
      RunVertexPin (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi1).σ
        (H.nodes[i+1]'hi1).σ.Φ (H.nodes[i]'(by omega)).zbar) :
    (((H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
        : ↥(H.nodes[i+1]'hi1).σ.K) : F)
      = (H.nodes[i]'(by omega)).vtx := by
  classical
  have hi : i < H.nodes.length := by omega
  obtain ⟨hfmon, hfdeg, hcoh, hruns⟩ := h
  -- read i: the recorded run data; clause (vi) is the last SideReads conjunct
  obtain ⟨Bp, Ndp, Φp, hdevp, hpinp, hsidep⟩ := hruns i hi
  obtain ⟨-, -, -, -, -, hvi⟩ := hsidep
  -- read i+1: the recorded development realizing the child side
  obtain ⟨B, Nd, Φn, hdev, -, hside⟩ := hruns (i + 1) hi1
  obtain ⟨-, hdig, -, -, -, -⟩ := hside
  -- clause (vi)@i fired on read (i+1)'s development: the key pin ties Φp to the child key
  have hΦp : Φp = (H.nodes[i+1]'hi1).σ.Φ := hpinp hi1
  have hviB : (H.nodes[i]'hi).σ.digPrime (H.nodes[i]'hi).zbar (B (H.nodes[i]'hi).μ)
      = (H.nodes[i]'hi).vtx := by
    refine hvi B Nd ?_
    rw [← hdevp.2.2, hΦp]
    exact hdev
  -- adjacency lands the child top stride slot on the parent vertex slot μ_i
  have hslot : (H.nodes[i+1]'hi1).s0
      + (H.nodes[i+1]'hi1).e * ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
      = (H.nodes[i]'hi).μ := by
    rw [Nat.mul_div_cancel' (H.nodes[i+1]'hi1).hEdvd]
    exact hadj
  -- SideReads(ii)@i+1 at the top stride: the recorded pattern lead off B′ μ_i
  have hpt := hdig ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e) le_rfl
    (H.nodes[i+1]'hi1).hpatTop
  rw [hslot] at hpt
  obtain ⟨hBne, -, hres⟩ := hpt
  have hBin : inC (H.nodes[i+1]'hi1).σ.Φ (B (H.nodes[i]'hi).μ) :=
    hdev.1 (H.nodes[i]'hi).μ
  -- coherence's transition leg at (i, i+1)
  obtain ⟨-, -, -, htrans⟩ := hcoh
  obtain ⟨hrecleg, hncleg, -, -, -, -, -⟩ := htrans i hi1
  by_cases hsp : (H.nodes[i]'hi).species = ReadSpecies.recentering
  · -- RECENTERING parent: residual-literal frame change; NO pin needed
    have hrec := hrecleg hsp
    obtain ⟨-, he'1, -, hlift_in, -, -, -, hPhi', -, -, -, -, -, hdigeq⟩ := hrec.base
    have ht'0 : (H.nodes[i+1]'hi1).σ.t = 0 := (H.nodes[i+1]'hi1).σ.he1t he'1
    -- the vertex coefficient is a parent coefficient (the recentered key keeps the degree)
    have hdegΦ : (H.nodes[i+1]'hi1).σ.Φ.degree = (H.nodes[i]'hi).σ.Φ.degree := by
      rw [hPhi']
      exact Polynomial.degree_sub_eq_left_of_degree_lt hlift_in
    have hBinp : inC (H.nodes[i]'hi).σ.Φ (B (H.nodes[i]'hi).μ) := by
      show (B (H.nodes[i]'hi).μ).degree < (H.nodes[i]'hi).σ.Φ.degree
      rw [← hdegΦ]
      exact hBin
    -- at t′ = 0 the frame-(i+1) residual is the bare scalar…
    have hres0 : (H.nodes[i+1]'hi1).σ.R (B (H.nodes[i]'hi).μ)
        = LaurentPolynomial.C
            ((H.nodes[i+1]'hi1).pat
              ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)) := by
      rw [hres, ht'0, neg_zero, zero_mul, LaurentPolynomial.T_zero, mul_one]
    -- …so the pattern lead IS the child digPrime at the parent's root
    have hcomp : (H.nodes[i+1]'hi1).σ.digPrime (H.nodes[i]'hi).zbar (B (H.nodes[i]'hi).μ)
        = (((H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
            : ↥(H.nodes[i+1]'hi1).σ.K) : F) := by
      simp only [Stage.digPrime]
      rw [hres0, LaurentPolynomial.eval₂_C, Subfield.coe_subtype]
    calc (((H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
            : ↥(H.nodes[i+1]'hi1).σ.K) : F)
        = (H.nodes[i+1]'hi1).σ.digPrime (H.nodes[i]'hi).zbar (B (H.nodes[i]'hi).μ) :=
          hcomp.symm
      _ = (H.nodes[i]'hi).σ.digPrime (H.nodes[i]'hi).zbar (B (H.nodes[i]'hi).μ) :=
          hdigeq (B (H.nodes[i]'hi).μ) hBne hBinp (H.nodes[i]'hi).zbar
      _ = (H.nodes[i]'hi).vtx := hviB
  · -- ROOT/INCREMENT parent: the frame change through the pin
    -- (HK-06 wave: the leg's TransitionCoreL is now keyed through the σV regrade at the
    -- CHILD pair; the frame link `child_wPrev` lands on σV.w while the named pin's
    -- position is σᵢ.w — the scalar extraction is position-independent, see
    -- `CT_eq_scalar_of_ne_zero`.)
    obtain ⟨-, σV, -, -, htc⟩ := hncleg hsp
    obtain ⟨c', hc'R, hc'F⟩ := hpin hsp (B (H.nodes[i]'hi).μ) hBne hBin
    -- align the residual positions through the recorded frame link wPrev′ = σV.w
    rw [htc.base.child_wPrev] at hres
    -- extract the scalar: the recorded pattern lead IS the pinned child digit
    have hsc : (H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
        = (c' : ↥(H.nodes[i+1]'hi1).σ.K) :=
      CT_eq_scalar_of_ne_zero (hres.symm.trans hc'R) (Units.ne_zero c')
    rw [hsc]
    exact hc'F.trans hviB

/-- (HV) for runs: at an adjacent consecutive read of a run, the pattern LEAD equals the
transported vertex value in `F` (the (HV) conjunct of `TransitionAdmissible`).

QUEUE ITEM 21 EXECUTED (2026-07-31, Asvin sign-off on the consolidated queue — the
adjudicated NAMED-HYPOTHESIS HOIST, `readsOf_HV_of_pin` canonicalized; frozen
`Moves/DefsL` untouched): the statement now CARRIES the certified-underivable residue
as the named hypothesis `hpin : … → RunVertexPin …` (the S8 dual-audited twist symmetry
moves the pin while fixing every recorded hypothesis — see the header record; so the
hoist is the /goal-preferred repair: the reduction `readsOf_HV_of_pin`, PROVED
Lean-core, becomes the discharge). `hpin` sits BEFORE `hadj` so consumers' partial
application `readsOf_HV h i hi (hpin …)` still lands on the `TransitionAdmissible`
(HV) conjunct shape `hadj → concl`. Discharge routes for `hpin` at concrete runs stay
as recorded: (a) the Wall A↔B seam (HC1-constructed histories carry it by
`v8Rc_S5'`/`VertexPin`); (b) a future `child_dig_frame` Defs pin (a `Moves/DefsL`
statement change, NOT part of this item). Consumer re-point: U23's
`readsOf_realizable` gains the matching named row. -/
theorem readsOf_HV {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hpin : (H.nodes[i]'(by omega : i < H.nodes.length)).species
        ≠ ReadSpecies.recentering →
      RunVertexPin (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi1).σ
        (H.nodes[i+1]'hi1).σ.Φ (H.nodes[i]'(by omega)).zbar)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ) :
    (((H.nodes[i+1]'hi1).pat ((H.nodes[i+1]'hi1).wSide / (H.nodes[i+1]'hi1).e)
        : ↥(H.nodes[i+1]'hi1).σ.K) : F)
      = (H.nodes[i]'(by omega)).vtx :=
  readsOf_HV_of_pin h i hi1 hadj hpin

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.readsOf_HV_of_pin
#print axioms LeanUrat.MovesJ.readsOf_HV
