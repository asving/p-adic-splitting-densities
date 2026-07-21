/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpType
import LeanUrat.OM.WildMenuW3

/-!
# OmLeafFaithful — the Montes-paper semantic axiom `om_leaf_faithful` (Wave 2b,
`notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md` §2 W2b; **RE-SCOPED 2026-07-21, Wave 3c** to the
K-windowed menu per `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 4)

Wave 1's σ-keying is DEFINITIONAL (`WildMenu.typeOfW` reads `(e,f)` off shape literals); Wave 2a
(`OM/QpType.lean`) built the genuine ℚ_p-factorization vocabulary (`LocalFactorData`,
`QpFactorization`, `qpType`). THIS module declares the ONE Wave-2 axiom tying the two together:

* `om_leaf_faithful` — **[CITE GMN]** every genuine monic `f : ℤ_[p][X]` that the level-`N`
  classifier ACTUALLY sends to a shape of the K-windowed σ-keyed menu
  `WildMenuW3.omMenuW3 n K σ` (∀ K — all admissible heights `H = fSum σ · k`, `gcd(k, e) = 1`)
  has a genuine ℚ_p-factorization of type σ. MENU-FIBER-SCOPED; existence only; no uniformity /
  rationality / measure / density content. The `K = 1` instance is EXACTLY the previously
  accepted Wave-2 form (`WildMenuW3.omMenuW3_one`), derived below as the THEOREM
  `om_leaf_faithful_w1`.
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
separable leg reads only the mod-`p` reduction, decided at every `N ≥ 1`.

Leaf module discipline (unchanged): exactly ONE axiom, zero `sorry`. **W3c change record
(2026-07-21)**: the axiom's menu hypothesis was re-scoped from `WildMenu.omMenuW n σ` (K = 1
only) to `(K : ℕ) … WildMenuW3.omMenuW3 n K σ`; everything else in the statement is
byte-identical. The old form survives as the derived THEOREM `om_leaf_faithful_w1`, so all
Wave-2 consumers compile unchanged. The H = 3 axiom-free anchor + the re-run mutation probes
live in `OM/QpTypeH3.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.OmLeafFaithful

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## Block 1 — the axiom -/

/-- **[CITE] GMN (Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
theory*, TAMS 364 (2012); arXiv:0807.2620v2) Thm 1.15 + Thm 1.19 + Cor 1.20 — the order-1 leaf
dichotomy with explicit `(e,f)` (`a_i = 1 ⟹ G_i` irreducible, `f(L/K) = m·deg ψ_i`,
`e(L/K) = e`) — these being the order-≤1 instances of Thm 3.1 / Thm 3.7 / Cor 3.8 — plus
Def 3.10 / eq. (37) (the assembled OM factorization `f = f_{r,∞} · ∏ f_t`), TOGETHER WITH the
standard structure theory of local fields the paper presupposes (the integer ring of a finite
extension of `ℚ_p` is a DVR, module-finite over `ℤ_p`, with the residue/ramification bookkeeping;
Serre, *Local Fields*, Ch. I–II) — packaged as the existence of the `QpType.LocalFactorData`
bundles (mathlib at the pin cannot prove DVR-ness of `integralClosure ℤ_[p] L` for wild `L`;
that existence content is exactly what this axiom carries, cf. `OM/QpType.lean` header and
`notes/GMN_citations.md` §§1–2).**

**MENU-FIBER-SCOPED** (the arising-shape restriction — the house discipline of
`B.omReadValuation_lt_of_certLevel_fkeyed`): quantified ONLY over genuine monic `f : ℤ_[p][X]`
that the level-`N` classifier `B.classify` ACTUALLY sends to a shape `T` of the CURRENT
K-windowed σ-keyed menu `WildMenuW3.omMenuW3 n K σ` (order-0 separable `sepShape`s ∪ the
constant-e `Tselfloop` window strata at all admissible heights `H = fSum σ · k`,
`gcd(k, e) = 1`, `1 ≤ k ≤ K` — nothing else; ∀ K). A nonempty menu fiber forces the level past
the leg's own decision threshold (module docstring; per-leg small-N emptiness =
`WildMenuW3.stratumCount_ramShapeAt_smallN`), where the banked fiber characterizations
(`Order0`, `ClassifierBridgeFiber2.classify_eq_selfloop_iff`) exhibit the fiber as the genuine
Ore/GMN stratum: squarefree order-0 residue with partition λ (⟹ Hensel factors, type
`{(1, dᵢ)}`), resp. single-side polygon `(0, fSum σ · k)–(n, 0)` with all-multiplicity-1
residual of degrees `fᵢ`. **Cor 1.20 applies VERBATIM to every window leg**: each k-leg is
single-slope all-μ=1 with the SAME side degree `sideDeg = gcd(fSum σ · k, n) = fSum σ`
(`WildMenuW3.gcd_admissible`) and the SAME residual shape `wShape σ` as Wave 1's minimal-H
stratum, so the Thm 1.19/Cor 1.20 leaves carry type `{(n/fSum σ, fᵢ)} = σ` at every admissible
height.

**W3c re-scope record (2026-07-21, blueprint §2 item 4)**: hypothesis `hT` re-scoped from
`T ∈ WildMenu.omMenuW n σ` to `(K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)`; everything else
byte-identical. The `K = 1` instance is EXACTLY the previously accepted Wave-2 form (via
`WildMenuW3.omMenuW3_one`; derived below as `om_leaf_faithful_w1`).

**NO uniformity / rationality / measure / density term appears in the statement** (existence
only; no uniqueness clause — Wave 2 consumers need none). Deliberate NON-imports (blueprint §2
W2b, unchanged from Wave 1): drainage (false of the truncated classifier), residual
equidistribution (not GMN-stated).

Mutation probes: `gateFiber_nonempty` + the recorded MUTATED-axiom `False` derivation (comment
block below) + the positive check `gate_axiom_coherent`; re-run at the H = 3 window stratum
after the W3c re-scope (split-type AND fine-(e,f)-swap, both against the AXIOM-FREE
`OM/QpTypeH3.lean` anchors — evidence blocks there). -/
axiom om_leaf_faithful (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (K : ℕ) (hT : T ∈ WildMenuW3.omMenuW3 n K σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ

/-- **The Wave-2 (K = 1) form of the axiom, now a THEOREM** (W3c re-scope, 2026-07-21): the
previously accepted `om_leaf_faithful` statement over the Wave-1 menu `WildMenu.omMenuW n σ` is
the `K = 1` instance of the re-scoped axiom, via the compatibility gate
`WildMenuW3.omMenuW3_one : omMenuW3 n 1 σ = WildMenu.omMenuW n σ`. Every Wave-2 consumer keeps
compiling against this form. -/
theorem om_leaf_faithful_w1 (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (σ : FactorizationType) (T : ClusterShape) (hT : T ∈ WildMenu.omMenuW n σ)
    (f : Polynomial ℤ_[p]) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hfib : B.classify p n N (PadicLift.toBox p n N hN f hf hdeg) = T) :
    ∃ F : QpType.QpFactorization p f, QpType.qpType p F = σ :=
  om_leaf_faithful p n N hN σ T 1 ((WildMenuW3.omMenuW3_one n σ).symm ▸ hT) f hf hdeg hfib

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
`OM/QpTypeH3.lean`).** The following scratch module — the (W2) axiom's hypotheses verbatim,
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

/-! ## Block 6 — axiom census (this module declares EXACTLY ONE axiom, the W3c-re-scoped one)

Expected footprints: `om_leaf_faithful` = itself; `om_leaf_faithful_w1` / `menuFiber_hasType` /
`gateFiber_hasType` / `gate_axiom_coherent` = Lean core + `om_leaf_faithful`;
`gate_mem_omMenuW` / `gatePoly*` / `toBox_gatePoly` / `gateFiber_nonempty` = Lean core ONLY.
The density capstones (`RealInstanceW.montes_unconditional_w`,
`RealInstanceV2.montes_unconditional`, `RealInstanceW3.montes_unconditional_w3`) do NOT consume
this module — their core-only footprints are re-printed in `AxChk_baseline.lean`. -/

section AxCheck

#print axioms LeanUrat.OM.OmLeafFaithful.om_leaf_faithful
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
