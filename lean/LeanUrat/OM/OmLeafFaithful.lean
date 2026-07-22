/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.WildMenuW3
import LeanUrat.OM.MultiSlopeMenu

/-!
# OmLeafFaithful — the Montes-paper semantic axiom `om_leaf_faithful` (Wave 2b,
`notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md` §2 W2b; **RE-SCOPED 2026-07-21, Wave 3c** to the
K-windowed menu per `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 4; **RE-SCOPED AGAIN
2026-07-22, Wave 4c** to the mixed-e menu `MultiSlopeMenu.omMenu4` with the per-family fiber
dispatch `fiberOf4`, per `notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §W4c)

Wave 1's σ-keying is DEFINITIONAL (`WildMenu.typeOfW` reads `(e,f)` off shape literals); Wave 2a
(`OM/QpType.lean`) built the genuine ℚ_p-factorization vocabulary (`LocalFactorData`,
`QpFactorization`, `qpType`). THIS module declares the ONE Wave-2 axiom tying the two together:

* `fiberOf4` — the UNIFIED per-family fiber predicate of the W4c re-scope: on multi-slope
  literals (head order-slot `1`) the genuine order-1 `classify1`/`InCell` fiber at the decoded
  menu cell; on every other shape the old `B.classify … = T` equation, byte-identical
  (unfolding lemmas `fiberOf4_mixed` / `fiberOf4_old`). This mirrors the PROVED Wave-4a
  counting fiber `MultiSlopeMenu.Fiber4` exactly (same discriminator `headOrd T = 1`, same
  decoded cell), so the axiom quantifies over the very fibers the Wave-4 counting model counts.
* `om_leaf_faithful` — **[CITE GMN]** every genuine monic `f : ℤ_[p][X]` that the level-`N`
  classifier ACTUALLY sends into the fiber of a shape of the Wave-4 σ-keyed menu
  `MultiSlopeMenu.omMenu4 n K σ` (∀ K — the K-windowed constant-e strata PLUS the one
  canonical mixed-e multi-slope stratum per mixed σ) has a genuine ℚ_p-factorization of type
  σ. MENU-FIBER-SCOPED; existence only; no uniformity / rationality / measure / density
  content. The W3 (omMenuW3, `B.classify`-fiber) instance is derived below as the THEOREM
  `om_leaf_faithful_w3`, and the `K = 1` Wave-2 form as `om_leaf_faithful_w1`
  (`WildMenuW3.omMenuW3_one`).
* `menuFiber_hasType` — the Wave-2 faithfulness theorem (footprint = core + the axiom; statement
  UNCHANGED by the W3c re-scope — routed through `om_leaf_faithful_w1`), and its σ-specialized
  corollary `gateFiber_hasType` at the Wave-1 wild gate
  (`T = Tselfloop 2 gateSide gateShape`, `σ = {(2,1)}`).
* **Mutation-consistency probe** (the axiom-safety evidence, blueprint §2 W2b last bullet):
  - `gateFiber_nonempty` — the gate fiber is INHABITED by a concrete named polynomial
    (`gatePoly = X² + 2X + 2` over `ℤ_[2]`, level `N = 3`), via the banked numeric gate
    `CellMenu.gate_S2C1` + the fiber characterization
    `ClassifierBridgeFiber2.classify_eq_selfloop_iff`. So the axiom's gate instance is NOT
    vacuous, and the mutation probe below genuinely fires.
  - the MUTATED axiom (same hypotheses, conclusion replaced by the SPLIT type `{(1,1),(1,1)}`)
    yields `False` against the PROVED Eisenstein irreducibility
    `QpType.wildGateFiber_eisenstein` — machine-checked in a scratch file (NOT committed; its
    verbatim text and output are recorded in the `Mutation probe evidence` comment block below).
  - `gate_axiom_coherent` — the POSITIVE coherence check: the real axiom's concrete gate instance
    (type `{(2,1)}`, a singleton factorization) COEXISTS with the proved irreducibility.

**Why `0 < N` (no decision-threshold hypothesis) is sound** (audit note; W3c: verbatim per
window leg): a nonempty `B.classify`-fiber of a menu shape forces the level to exceed the
shape's decision threshold. The wild k-leg literal
`Tselfloop n ((0, fSum σ · k), (n, 0)) (wShape σ)` carries its side in the emitted face payload,
and the classifier only emits sides read from the box Newton polygon, whose support dots have
box valuation `< N` (`PadicLift.zmodValuation_lt`); a left vertex `(0, fSum σ · k)` in the fiber
therefore forces `fSum σ · k < N`, i.e. exactly the `MenuPath` range in which
`classify_eq_selfloop_iff` proves the fiber IS the genuine stratum, whose digit conditions decode
to genuine `ℤ_[p]`-valuation data (`QpType.valuation_eq_of_zmodValuation_lt`). Below the leg's
own threshold the fiber is EMPTY (the banked count-level form is
`WildMenuW3.stratumCount_ramShapeAt_smallN`) and the axiom instance is vacuous. The order-0
separable leg reads only the mod-`p` reduction, decided at every `N ≥ 1`. **W4c addendum
(mixed branch)**: the mixed fiber hypothesis IS an `InCell` membership (`classify1`), which
carries its own threshold — `InCell` requires a level-`N` `MenuPath`, whose left vertex forces
`H_total = fSum σ ≤ N − 1`; below the canonical threshold the mixed fiber is EMPTY
(`MultiSlopeMenu.stratumCount4_mixed_smallN`) and the instance vacuous; in the readable range
the `Matches` digit conditions decode to genuine `ℤ_[p]`-valuation data exactly as above
(anchor: `OM/QpTypeMixed.lean`, `mixedGateFiber_valuation`).

Leaf module discipline (unchanged): exactly ONE axiom, zero `sorry`. **W3c change record
(2026-07-21)**: the axiom's menu hypothesis was re-scoped from `WildMenu.omMenuW n σ` (K = 1
only) to `(K : ℕ) … WildMenuW3.omMenuW3 n K σ`; everything else in the statement was
byte-identical. **W4c change record (2026-07-22)**: the menu hypothesis is re-scoped from
`WildMenuW3.omMenuW3 n K σ` to `MultiSlopeMenu.omMenu4 n K σ` and the fiber hypothesis from
the bare `B.classify … = T` equation to the per-family dispatch `fiberOf4` (see its docstring
for the vacuity trap this avoids); everything else is byte-identical. The W3 form survives as
the derived THEOREM `om_leaf_faithful_w3` (definitional on old shapes), and the Wave-2/W1 form
as `om_leaf_faithful_w1`, so all consumers compile unchanged. The H = 3 axiom-free anchor +
the W3c mutation probes live in `OM/QpTypeH3.lean`; the mixed-gate (n = 5) axiom-free anchor +
the W4c mutation probes live in `OM/QpTypeMixed.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.OmLeafFaithful

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## Block 1 — the unified fiber predicate and the axiom -/

/-- **The unified per-family fiber predicate** (W4c, blueprint `WILD_WAVE4` §W4c statement-design
point). The Wave-4 menu `MultiSlopeMenu.omMenu4` mixes TWO fiber notions, dispatched by the
family discriminator `headOrd T = 1` (which separates the multi-slope literals from every old
shape — `MultiSlopeMenu.headOrd_multiSideLit` vs `headOrd_of_mem_omMenuW3`):

* multi-slope literals (`headOrd T = 1`): the GENUINE order-1 fiber
  `classify1 p (toBox …) = some (mkCell n (decodePath T) (decodeShapes T))` — the
  `classify1`/`InCell` fiber at the decoded menu cell;
* every old shape: the old equation `B.classify p n N (toBox …) = T`, byte-identical to the
  W2/W3 axiom's hypothesis (`fiberOf4_old` is definitional).

**The vacuity trap this dispatch avoids** (the V1 failure mode): `B.classify` reads only the
FIRST Newton side and can never emit a multi-slope literal (recorded no-go, `WILD_WAVE4` §1),
so keeping the bare `B.classify … = T` hypothesis over the enlarged menu would make every
mixed instance of the axiom vacuously true — true but empty. The dispatch instead mirrors the
PROVED Wave-4a counting fiber `MultiSlopeMenu.Fiber4` exactly (same discriminator, same
decoded cell, `Fiber4` being its box-level `M9.realP` counterpart), so the axiom quantifies
over the very fibers the Wave-4 counting model counts. -/
def fiberOf4 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (T : ClusterShape)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n) : Prop :=
  if MultiSlopeMenu.headOrd T = 1 then
    classify1 p (PadicLift.toBox p n N hN f hf hdeg)
      = some (mkCell n (MultiSlopeMenu.decodePath T) (MultiSlopeMenu.decodeShapes T))
  else B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T

/-- `fiberOf4` on a multi-slope literal IS the genuine order-1 `classify1` fiber at the decoded
cell. -/
theorem fiberOf4_mixed (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T = 1) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf4 p n N hN T f hf hdeg
      ↔ classify1 p (PadicLift.toBox p n N hN f hf hdeg)
          = some (mkCell n (MultiSlopeMenu.decodePath T) (MultiSlopeMenu.decodeShapes T)) := by
  unfold fiberOf4
  rw [if_pos hT]

/-- `fiberOf4` on every old (non-multi-slope-headed) shape IS the old `B.classify` equation —
the W2/W3 fiber hypothesis, byte-identical. -/
theorem fiberOf4_old (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) {T : ClusterShape}
    (hT : MultiSlopeMenu.headOrd T ≠ 1) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = n) :
    fiberOf4 p n N hN T f hf hdeg
      ↔ B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T := by
  unfold fiberOf4
  rw [if_neg hT]

/-- **[CITE] GMN (Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
theory*, TAMS 364 (2012); arXiv:0807.2620v2) Thm 1.15 + Thm 1.19 + Cor 1.20 — the order-1
dissections with the explicit leaf `(e,f)` (Thm 1.15, Theorem of the polygon: one coprime
factor block per side of pairwise-distinct slope; Thm 1.19, Theorem of the residual polynomial:
one coprime factor per residual irreducible; Cor 1.20: `a_i = 1 ⟹ G_i` irreducible,
`f(L/K) = m·deg ψ_i`, `e(L/K) = e`) — these being the order-≤1 instances of Thm 3.1 / Thm 3.7 /
Cor 3.8 — plus Def 3.10 / eq. (37) (the assembled OM factorization `f = f_{r,∞} · ∏ f_t`),
TOGETHER WITH the standard structure theory of local fields the paper presupposes (the integer
ring of a finite extension of `ℚ_p` is a DVR, module-finite over `ℤ_p`, with the
residue/ramification bookkeeping; Serre, *Local Fields*, Ch. I–II) — packaged as the existence
of the `QpType.LocalFactorData` bundles (mathlib at the pin cannot prove DVR-ness of
`integralClosure ℤ_[p] L` for wild `L`; that existence content is exactly what this axiom
carries, cf. `OM/QpType.lean` header and `notes/GMN_citations.md` §§1–2).**

**MENU-FIBER-SCOPED** (the arising-shape restriction — the house discipline of
`B.omReadValuation_lt_of_certLevel_fkeyed`): quantified ONLY over genuine monic `f : ℤ_[p][X]`
that the level-`N` classifier ACTUALLY sends into the `fiberOf4`-fiber of a shape `T` of the
CURRENT Wave-4 σ-keyed menu `MultiSlopeMenu.omMenu4 n K σ` (order-0 separable `sepShape`s ∪
the constant-e `Tselfloop` window strata at all admissible heights `H = fSum σ · k`,
`gcd(k, e) = 1`, `1 ≤ k ≤ K`, ∪ — for mixed-all-e≥2 σ — the ONE canonical multi-slope literal
`multiSideLit n (mixedPath σ) (mixedSh σ)`; nothing else; ∀ K). A nonempty fiber forces the
level past the shape's own decision threshold (module docstring; small-N emptiness =
`WildMenuW3.stratumCount_ramShapeAt_smallN` resp. `MultiSlopeMenu.stratumCount4_mixed_smallN`),
where the banked fiber characterizations (`Order0`,
`ClassifierBridgeFiber2.classify_eq_selfloop_iff`, `CellMenu.inCell_mkCell_iff`) exhibit the
fiber as the genuine Ore/GMN stratum:

* squarefree order-0 residue with partition λ ⟹ Hensel factors, type `{(1, dᵢ)}`;
* single-side polygon `(0, fSum σ · k)–(n, 0)` with all-μ=1 residual of degrees `fᵢ` —
  **Cor 1.20 applies VERBATIM to every window leg**: each k-leg is single-slope all-μ=1 with
  the SAME side degree `sideDeg = gcd(fSum σ · k, n) = fSum σ` (`WildMenuW3.gcd_admissible`)
  and the SAME residual shape `wShape σ`, so the Thm 1.19/Cor 1.20 leaves carry type
  `{(n/fSum σ, fᵢ)} = σ` at every admissible height;
* NEW (W4c), the mixed multi-slope stratum: the `classify1`/`InCell` fiber pins (via
  `Matches`) the full multi-slope polygon — vertices exact, all dots on-or-above — with
  strictly increasing slopes `−1/e_j`, one side per distinct `e_j` of σ, and per-side all-μ=1
  separable residuals with parts of degrees `f`. **Thm 1.15 (slope dissection)** splits `f`
  into one coprime factor block per side; per side, **Thm 1.19 + Cor 1.20** (`a_i = 1`,
  `m = 1`, slope `−1/e_j` in lowest terms) make every residual part an irreducible leaf with
  `(e(L/K), f(L/K)) = (e_j, f)`; the assembled `(e,f)`-multiset is exactly
  `σ = ⋃_j {(e_j, f) : f a part of side j}` — the same multiset the definitional decoder
  recovers (`MultiSlopeMenu.typeOf4_multiSideLit`).

**W4c re-scope record (2026-07-22, blueprint `WILD_WAVE4` §W4c; third scope)**: hypothesis
`hT` re-scoped from `T ∈ WildMenuW3.omMenuW3 n K σ` to `T ∈ MultiSlopeMenu.omMenu4 n K σ`, and
hypothesis `hfib` from the bare `B.classify … = T` equation to the per-family dispatch
`fiberOf4 p n N hN T f hf hdeg` (see `fiberOf4`'s docstring for the vacuity trap the dispatch
avoids); everything else byte-identical. The W3 instance is EXACTLY the previously accepted
W3c form (derived below as `om_leaf_faithful_w3`, definitional on old shapes via
`fiberOf4_old`), and the `K = 1` Wave-2 form survives as `om_leaf_faithful_w1`.

**NO uniformity / rationality / measure / density term appears in the statement** (existence
only; no uniqueness clause — consumers need none). Deliberate NON-imports (blueprint §2 W2b,
unchanged): drainage (false of the truncated classifier), residual equidistribution (not
GMN-stated).

Mutation probes: `gateFiber_nonempty` + the recorded MUTATED-axiom `False` derivation (comment
block below) + the positive check `gate_axiom_coherent`; re-run at the H = 3 window stratum
after the W3c re-scope (split-type AND fine-(e,f)-swap — `OM/QpTypeH3.lean` evidence blocks);
re-run at the NEW mixed-gate stratum (n = 5, σ = {(2,1),(3,1)}) after the W4c re-scope
(all-unramified `{(1,1)}⁵` AND wrong-e singleton `{(2,1)}` — both against the AXIOM-FREE
`OM/QpTypeMixed.lean` anchors; evidence blocks there). -/
axiom om_leaf_faithful (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ)
    (hT : T ∈ MultiSlopeMenu.omMenu4 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : fiberOf4 p n N hN T f hf hdeg) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ

/-- **The Wave-3c form of the axiom, now a THEOREM** (W4c re-scope, 2026-07-22): the previously
accepted `om_leaf_faithful` statement over the K-windowed menu `WildMenuW3.omMenuW3 n K σ` with
the `B.classify` fiber equation is an instance of the re-scoped axiom — the menu leg by
`omMenu4 = omMenuW3 ∪ …` (left injection), the fiber leg definitionally (`fiberOf4_old`: every
W3 menu shape has an order-0 head, `MultiSlopeMenu.headOrd_of_mem_omMenuW3`). Every W3c
consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w3 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful p n N hN σ T K
    (by rw [MultiSlopeMenu.omMenu4]; exact Finset.mem_union_left _ hT) f hf hdeg
    ((fiberOf4_old p n N hN
      (by rw [MultiSlopeMenu.headOrd_of_mem_omMenuW3 hT]; exact zero_ne_one)
      f hf hdeg).mpr hfib)

/-- **The Wave-2 (K = 1) form of the axiom, a THEOREM since the W3c re-scope** (routed through
`om_leaf_faithful_w3` since the W4c re-scope): the originally accepted `om_leaf_faithful`
statement over the Wave-1 menu `WildMenu.omMenuW n σ` is the `K = 1` instance, via the
compatibility gate `WildMenuW3.omMenuW3_one : omMenuW3 n 1 σ = WildMenu.omMenuW n σ`. Every
Wave-2 consumer keeps compiling against this form. -/
theorem om_leaf_faithful_w1 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w3 p n N hN σ T 1 ((WildMenuW3.omMenuW3_one n σ).symm ▸ hT) f hf hdeg hfib

/-! ## Block 2 — the faithfulness theorem (the Wave-2 payoff) and the gate corollary -/

/-- **The Wave-2 semantic faithfulness theorem** (blueprint §2 W2c): a genuine monic
`f : ℤ_[p][X]` classified into the σ-keyed menu has a genuine ℚ_p-factorization of type σ —
its TRUE factorization type IS the type its menu shape is keyed by. Consumed footprint =
Lean core + `om_leaf_faithful` (see the census). Statement UNCHANGED by the W3c re-scope;
routed through the derived K = 1 form `om_leaf_faithful_w1`. -/
theorem menuFiber_hasType (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful_w1 p n N hN σ T hT f hf hdeg hfib

/-- The Wave-1 wild gate shape `Tselfloop 2 gateSide gateShape` is a member of the σ-keyed menu
at `σ = {(2,1)}` — via `WildMenu.omMenuW`'s ramified leg and `QpType.ramShape_gate` (itself
`WildMenu.ramShape_of_constERam` at the constant-e instance `e = 2, f = 1`). -/
theorem gate_mem_omMenuW :
    ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape
      ∈ WildMenu.omMenuW 2 (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) := by
  rw [WildMenu.omMenuW, QpType.ramShape_gate, Option.toFinset_some]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The σ-specialized faithfulness corollary at the Wave-1 wild gate**: every genuine monic
quadratic in the level-`N` classifier fiber of `Tselfloop 2 gateSide gateShape` has genuine
ℚ_p-factorization type `{(2,1)}` — one totally ramified quadratic factor. (Coheres with the
PROVED `QpType.wildGateFiber_eisenstein`: the same fiber is Eisenstein-irreducible.) -/
theorem gateFiber_hasType (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 0 < N)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : B.classify p 2 N (PadicLift.toBox p 2 N hN f hf hdeg)
      = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) :=
  menuFiber_hasType p 2 N hN _ _ gate_mem_omMenuW f hf hdeg hfib

/-! ## Block 3 — mutation probe leg 1: the gate fiber is INHABITED

Route (probe design note): `decide` on `B.classify` is structurally unavailable (`classifyAux`
is well-founded recursion — `WellFounded.fix` does not kernel-reduce — and `polyShape` carries
`Classical.decEq`), and extracting ℕ-positivity from the ℚ-valued `stratumCount_selfloop_R`
would still need a box→`ℤ_[p]` lift. Instead: the CONCRETE banked witness. `CellMenu.gate_S2C1`
(the W0 numeric gate, `p = 2, N = 3`) proves `InCell 2 gbox1 (mkCell 2 [(0,1),(2,0)] [[(1,1)]])`
for the box of `X² + 2X + 2`; `gatePoly` is its genuine `ℤ_[2]` lift (`toBox` sends one to the
other by direct coefficient computation), and `classify_eq_selfloop_iff` (mpr) converts `InCell`
into the classifier-fiber equation. -/

/-- The concrete gate-fiber witness: `X² + 2X + 2` over `ℤ_[2]` (Eisenstein at 2;
the `ℤ_[2]`-lift of the banked W0 gate box `CellMenu.gbox1`). -/
noncomputable def gatePoly : Polynomial ℤ_[2] := X ^ 2 + C 2 * X + C 2

theorem gatePoly_monic : gatePoly.Monic := by unfold gatePoly; monicity!

theorem gatePoly_natDegree : gatePoly.natDegree = 2 := by unfold gatePoly; compute_degree!

/-- `toBox` sends the genuine witness to the banked gate box: the level-3 reduction of
`X² + 2X + 2` is `gbox1`. -/
theorem toBox_gatePoly :
    PadicLift.toBox 2 2 3 (by norm_num) gatePoly gatePoly_monic gatePoly_natDegree
      = CellMenu.gbox1 := by
  apply Subtype.ext
  rw [PadicLift.toBox_val]
  show gatePoly.map (PadicInt.toZModPow 3) = (X ^ 2 + C 2 * X + C 2 : (ZMod (2 ^ 3))[X])
  unfold gatePoly
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat]

/-- **Mutation-probe leg 1 (fiber-nonemptiness).** The Wave-1 wild gate fiber is INHABITED by
the concrete `gatePoly = X² + 2X + 2` at `p = 2`, `N = 3`: the axiom's gate instance
quantifies over a genuinely nonempty fiber, so the mutation probe (comment block below) and the
coherence check `gate_axiom_coherent` have real force. Banked route: `CellMenu.gate_S2C1`
(`InCell`) + `ClassifierBridgeFiber2.classify_eq_selfloop_iff` (mpr). -/
theorem gateFiber_nonempty :
    ∃ (f0 : Polynomial ℤ_[2]) (hf : f0.Monic) (hdeg : f0.natDegree = 2),
      B.classify 2 2 3 (PadicLift.toBox 2 2 3 (by norm_num) f0 hf hdeg)
        = ClassifierBridgeFiber.Tselfloop 2 QpType.gateSide QpType.gateShape := by
  refine ⟨gatePoly, gatePoly_monic, gatePoly_natDegree, ?_⟩
  rw [toBox_gatePoly]
  exact (ClassifierBridgeFiber2.classify_eq_selfloop_iff 2 3 (by norm_num) (by norm_num)
    QpType.gatePath (QpType.menuPath_gate (by norm_num)) QpType.gateSide
    QpType.sidePairs_gatePath QpType.gateShape QpType.shapesFor_gate
    (by decide) (by decide) CellMenu.gbox1).mpr CellMenu.gate_S2C1.1

/-! ## Block 4 — mutation probe leg 2: the MUTATED axiom is refuted (evidence block)

**Mutation probe evidence (machine-checked 2026-07-21, scratch NOT committed; W2-era record —
the scratch below quotes the axiom's PRE-W3c hypotheses over `WildMenu.omMenuW`, which are now
exactly those of the derived theorem `om_leaf_faithful_w1`; the probes were RE-RUN against the
re-scoped W3 hypotheses at the H = 3 window stratum the same day, evidence blocks in
`OM/QpTypeH3.lean` — those W3-form hypotheses are, since the W4c re-scope of 2026-07-22,
exactly those of the derived theorem `om_leaf_faithful_w3`; the W4c probes at the NEW mixed
menu content live in `OM/QpTypeMixed.lean`).** The following scratch module — the (W2) axiom's hypotheses verbatim,
conclusion mutated to the SPLIT type `{(1,1),(1,1)}` — was compiled against this module and
`lake env lean` accepted it with zero errors, i.e. `False` DERIVES from the mutated axiom +
`gateFiber_nonempty` + `QpType.wildGateFiber_eisenstein`. A wrong-(e,f) payload at the gate is
therefore machine-refutable, not silently absorbable: the axiom's conclusion is load-bearing at
its concrete instances.

```lean
import Mathlib
import LeanUrat.OM.OmLeafFaithful

namespace LeanUrat.OM.OmLeafFaithfulScratch

open Polynomial
open LeanUrat LeanUrat.OM

/-- THE MUTATED AXIOM (scratch only): hypotheses of `om_leaf_faithful` verbatim, conclusion
replaced by the SPLIT type `{(1,1),(1,1)}`. -/
axiom om_leaf_faithful_MUTATED (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f,
      QpType.qpType p F = (⟨{((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))}⟩ : FactorizationType)

/-- The mutated axiom is REFUTED: at the inhabited gate fiber (`OmLeafFaithful.gateFiber_nonempty`)
it forces a 2-factor ℚ_2-factorization of a polynomial that is PROVEN irreducible over ℚ_2
(`QpType.wildGateFiber_eisenstein`). -/
theorem mutation_refuted : False := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := OmLeafFaithful.gateFiber_nonempty
  obtain ⟨F, hF⟩ := om_leaf_faithful_MUTATED 2 2 3 (by norm_num)
    (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) _ OmLeafFaithful.gate_mem_omMenuW
    f0 hf hdeg hfib
  have hirr : Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) :=
    QpType.wildGateFiber_eisenstein 2 (by norm_num) (by norm_num) hf hdeg hfib
  -- the mutated conclusion forces EXACTLY TWO factors
  have hlen : F.factors.length = 2 := by
    have hdata := congrArg FactorizationType.data hF
    have hcard := congrArg Multiset.card hdata
    simpa [QpType.qpType] using hcard
  obtain ⟨g₁, g₂, hfac⟩ := List.length_eq_two.mp hlen
  -- both factors are ℚ_2-irreducible, hence NON-UNITS after mapping
  have h1 : ¬ IsUnit (g₁.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₁ (by rw [hfac]; exact List.mem_cons_self ..)).not_isUnit
  have h2 : ¬ IsUnit (g₂.map (algebraMap ℤ_[2] ℚ_[2])) :=
    (F.irred g₂ (by rw [hfac]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).not_isUnit
  -- but their product is the irreducible f0.map — contradiction
  have hmap : f0.map (algebraMap ℤ_[2] ℚ_[2])
      = g₁.map (algebraMap ℤ_[2] ℚ_[2]) * g₂.map (algebraMap ℤ_[2] ℚ_[2]) := by
    rw [← F.prod_eq, hfac]
    simp [Polynomial.map_mul]
  rcases hirr.isUnit_or_isUnit hmap with h | h
  · exact h1 h
  · exact h2 h

end LeanUrat.OM.OmLeafFaithfulScratch

#print axioms LeanUrat.OM.OmLeafFaithfulScratch.mutation_refuted
```

`lake env lean` output on the scratch (2026-07-21): NO errors; the single info line

```
'LeanUrat.OM.OmLeafFaithfulScratch.mutation_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LeanUrat.OM.OmLeafFaithfulScratch.om_leaf_faithful_MUTATED]
```

i.e. `False` follows from the MUTATED axiom + Lean core + this module's PROVED theorems alone
(the real `om_leaf_faithful` does NOT appear in the refutation's cone). -/

/-! ## Block 5 — mutation probe leg 3: the POSITIVE coherence check -/

/-- **Mutation-probe leg 3 (positive coherence).** The REAL axiom's concrete gate instance
COEXISTS with the proved Eisenstein irreducibility: the inhabited gate fiber carries a
factorization of type `{(2,1)}` — a SINGLETON factorization — alongside
`Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2]))`. (Where the mutated split-type conclusion
yields `False`, the real conclusion is consistent — the two probe legs together pin the
axiom's (e,f) payload at the gate.) -/
theorem gate_axiom_coherent :
    ∃ (f0 : Polynomial ℤ_[2]) (F : QpType.QpFactorization 2 f0),
      QpType.qpType 2 F = (⟨{((2 : ℕ), (1 : ℕ))}⟩ : FactorizationType) ∧
      Irreducible (f0.map (algebraMap ℤ_[2] ℚ_[2])) := by
  obtain ⟨f0, hf, hdeg, hfib⟩ := gateFiber_nonempty
  obtain ⟨F, hF⟩ := gateFiber_hasType 2 (by norm_num) f0 hf hdeg hfib
  exact ⟨f0, F, hF, QpType.wildGateFiber_eisenstein 2 (by norm_num) (by norm_num) hf hdeg hfib⟩

/-! ## Block 6 — axiom census (this module declares EXACTLY ONE axiom, the W4c-re-scoped one)

Expected footprints: `om_leaf_faithful` = itself; `om_leaf_faithful_w3` /
`om_leaf_faithful_w1` / `menuFiber_hasType` / `gateFiber_hasType` / `gate_axiom_coherent` =
Lean core + `om_leaf_faithful`; `fiberOf4` / `fiberOf4_mixed` / `fiberOf4_old` /
`gate_mem_omMenuW` / `gatePoly*` / `toBox_gatePoly` / `gateFiber_nonempty` = Lean core ONLY.
The density capstones (`RealInstanceW.montes_unconditional_w`,
`RealInstanceV2.montes_unconditional`, `RealInstanceW3.montes_unconditional_w3`,
`RealInstanceW4.montes_unconditional_w4`) do NOT consume this module — their core-only
footprints are re-printed in `AxChk_baseline.lean`. -/

section AxCheck

#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_mixed
#print axioms LeanUrat.OM.OmLeafFaithful.fiberOf4_old
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w3
#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful_w1
#print axioms LeanUrat.OM.OmLeafFaithful.menuFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gate_mem_omMenuW
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_hasType
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly_monic
#print axioms LeanUrat.OM.OmLeafFaithful.gatePoly_natDegree
#print axioms LeanUrat.OM.OmLeafFaithful.toBox_gatePoly
#print axioms LeanUrat.OM.OmLeafFaithful.gateFiber_nonempty
#print axioms LeanUrat.OM.OmLeafFaithful.gate_axiom_coherent

end AxCheck

end LeanUrat.OM.OmLeafFaithful
