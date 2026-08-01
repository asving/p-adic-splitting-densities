/-
HDISCHARGE_H1 §5.3 — `H1/SiteBlock.lean`: H1-U11 (`key1_along_history`), the
history-fold (blueprint §5.3, W3).

PROBE-FIRST RECORD (prover H1-U11, 2026-08-01; the blueprint gives U11 as PROSE
ONLY — no verbatim Lean statement exists for this unit, and the statement design
below IS the unit's probe duty, compile-probed green before landing):
* MODEL-CHAIN CARRIER (the flagged probe risk; candidates HC1
  `V1_readWPack`/`V34_readKernel` packagings): DECIDED for the DEPENDENT VECTOR
  `M : ∀ j (hj : j < H.nodes.length), GenuineStageModel (H.nodes[j]'hj).σ`.
  Reason: `Key1SiteBlock`/`KPBlock`/`GrBKeyLaws`/`DevBound` are all keyed to a
  `GenuineStageModel σ'` (Type-valued model data at the recorded stage), which
  the HC1 packs do NOT carry — `ReadFrame.pack`/`Stage.pack` are `ResValPack`
  read-functional carriers (`Moves/ResVal.lean`), a different face; routing
  through them would interpose an unratified pack→model bridge. The dependent
  vector threads the `getElem` proofs by proof irrelevance (probed: `i+1+1` and
  `i+2` slots unify definitionally).
* INDEX ENCODING: "every index ≥ 2" is carried as `i+2` (`i ≥ 0`), matching
  `HistoryCoherent`'s `i`/`i+1` successor pattern; the `j-1` subtraction form
  was rejected at probe (Nat `j-1+1` is not defeq to `j`, and the cast would
  ride through the dependent model slot). Site keying: the state at index `i+2`
  is read off against its CREATING read = node `i+1` (the (ν, σ') convention of
  the §5.1 rows).

H1-U11 honesty ledger (what is PROVED vs what is a ROW):
* The fold consumes the wave-2 units per step exactly as the blueprint
  disciplines them: U8 = `kp_step` FIRED (its `DevBound` input is the displayed
  per-step `hdev` row — STAGING ONLY, finding 11: nothing discharged until
  OP-B1 lands); U9 = `GrBKeyLaws` taken as the EXPLICIT per-step binder `hlaws`
  [REV 2, finding 12: U9 never lands sorry-backed; consumers carry the row];
  U10's assembly face = the intro rule `key1SiteBlock_base` (Order1).
* `hlaws` is quantified over ALL `KB : KPBlock` at the step (the row keyed to
  the SITE, not to a block representative): every `KPBlock` pins its `ψhom` to
  `in(Φ')` up to a `Gr`-unit (`kpa_init`), so the ∀-KB form is the
  unit-invariant rendering of the (GR-B-KEY) laws row.
* `hH : HistoryCoherent H` is NOT consumed by this proof (the kp_step precedent:
  unconsumed math-face keying, statement kept — the fold's charter is "along a
  HistoryCoherent chain"). Under the HK-06 re-key, `HistoryCoherent` pins the
  CHILD-pair ties (`σ'.e/s/t` at the child node's read pair) and supplies
  `IsNodeLift` only on non-recentering legs; `kp_step`'s verbatim binder block
  needs the PARENT-pair ties (`σ'.e = ν.e`, `σ'.h = ν.h`, `σ'.wPrev = ν.σ.w`,
  `IsNodeLift ν σ'.Φ`), so those enter as the displayed per-step `hlink` row —
  never silently read off coherence.
* At this packaging the induction over `H.nodes` DEGENERATES to indexed
  application (the wave-2 rows are supplied at every step, so no cross-step
  carry is needed); the fold's Lean content is the per-index assembly plus the
  dependent-slot threading. Never cite this theorem as evidence for (H1): the
  per-step rows are hypothesis content (A-M2/B-M1/OP-B1 open), and non-vacuity
  of the model chain is the open math-leaf chain.
-/
import LeanUrat.Scaffold.HDischarge.H1.TowerStep

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.Scaffold.HDischarge.H1

open LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesC

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

set_option linter.unusedVariables false in
/-- **H1-U11 (`key1_along_history`)** — the history-fold (blueprint §5.3): along a
`HistoryCoherent` chain `H` with per-level genuine stage models `M`, the (H1)(d)
site block `Key1SiteBlock` holds at every index ≥ 2 (encoded `i+2`; creating read
= node `i+1`), given the wave-2 units at each step: the `hlink` ν↔σ' tie row +
the `hdev` `DevBound` row (U8 `kp_step`'s verbatim inputs, the latter STAGING
ONLY per finding 11) and the `hlaws` (GR-B-KEY) laws row (U9's explicit binder,
finding 12). `hH` is the chain's math-face keying (unconsumed here — see the
module header ledger). Never cite this theorem alone as evidence for (H1). -/
theorem key1_along_history (H : History p F) (hH : HistoryCoherent H)
    (M : ∀ (j : ℕ) (hj : j < H.nodes.length), GenuineStageModel ((H.nodes[j]'hj).σ))
    (hlink : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      (H.nodes[i+1]'hi).σ.e = (H.nodes[i]'(by omega)).e ∧
      (H.nodes[i+1]'hi).σ.h = (H.nodes[i]'(by omega)).h ∧
      (H.nodes[i+1]'hi).σ.wPrev = (H.nodes[i]'(by omega)).σ.w ∧
      IsNodeLift (H.nodes[i]'(by omega)) (H.nodes[i+1]'hi).σ.Φ)
    (hdev : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
      DevBound (H.nodes[i]'(by omega)) ((H.nodes[i+1]'hi).σ) (M (i+1) hi))
    (hlaws : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length)
      (KB : KPBlock ((H.nodes[i+1]'hi).σ) (M (i+1) hi)),
      GrBKeyLaws (H.nodes[i]'(by omega)) ((H.nodes[i+1]'hi).σ) (M (i+1) hi) KB) :
    ∀ (i : ℕ) (hi : i + 2 < H.nodes.length),
      Key1SiteBlock (H.nodes[i+1]'(by omega)) ((H.nodes[i+2]'hi).σ) (M (i+2) hi) := by
  intro i hi
  have hi1 : (i + 1) + 1 < H.nodes.length := by omega
  obtain ⟨he, hh, hprev, hΦ⟩ := hlink (i+1) hi1
  obtain ⟨KB⟩ := kp_step (H.nodes[i+1]'(by omega)) ((H.nodes[i+2]'hi).σ) (M (i+2) hi)
    hΦ he hh hprev (hdev (i+1) hi1)
  exact key1SiteBlock_base _ _ _ KB (hlaws (i+1) hi1 KB)

/-!
## H1-U10 (`key1SiteBlock_step` + `key1SiteBlock_consume`) — the KEY1-SITE assembly
(blueprint §5.3/§4.2, W3; prover H1-U10, 2026-08-01)

STATEMENT PROVENANCE (honesty note, same footing as the U11 record above): the
blueprint gives H1-U10 in PROSE only — "`Key1SiteBlock` from U8+U9 (the KEY1-SITE
assembly, §4.2), PLUS the consumption lemma [REV 2, findings 7/8]: from
`Key1SiteBlock ν σ' M` and a `SideReads`-realized run of f at ν (which supplies
the `HasAnchorK (ν.σ.R f) ν.a ν.Ranch` witness per SideReads(iii)), conclude the
WGEO-shaped (d1)–(d3) at (f, ν.μ)".  The Lean statements below are shaped from
that prose per the U6/U7 precedent (`Order1.lean` header), flagged for the
semantic-guardian pass.  Shaping decisions, displayed:

* `key1SiteBlock_step` consumes U8 LITERALLY (`kp_step`'s hypothesis block
  VERBATIM: `hΦ`/`he`/`hh`/`hprev` + the `DevBound` row — STAGING ONLY, REV 2
  finding 11: nothing discharged until OP-B1 lands) and takes U9's output as the
  EXPLICIT BINDER `laws : ∀ KB, GrBKeyLaws ν σ' M KB` [REV 2, finding 12: U9
  never lands sorry-backed; consumers carry the row].  The ∀-KB form is forced
  by `kp_step`'s `Nonempty` conclusion (no canonical block exposed) and is the
  unit-invariant rendering of the laws row (every `KPBlock.ψhom` is `in(Φ')` up
  to a `Gr`-unit via `kpa_init`) — the same reading U11's `hlaws` row took.
* `key1SiteBlock_consume` renders "a `SideReads`-realized run of f at ν" as the
  per-read data of `ReadsOf` (HC2/Defs D4): `IsDevelopment ν.σ.Φ f B Nd` +
  `SideReads ν B Nd Φnext`.  `f ≠ 0` is NOT an extra hypothesis — it is DERIVED
  from the SideReads(iii) anchor (`anchored_ne_zero` below: `R 0 = 0` by
  `Stage.hR0`, while an anchored residual is a `T`-unit times the `toLaurent`
  image of a polynomial with nonzero constant coefficient).  The conclusion is
  the WGEO delivery shape of blueprint §4.1/§4.2 ((V2a) = (d1)+(d2), (V2c) =
  (d3)) at the RECORDED `ν.μ`, clause-for-clause the `KPBlock` +
  `GrBKeyLaws.faithful_at` content — so WGEO's Lean consumers fire with no
  restatement.

WHAT U10 DOES NOT CLAIM: both theorems are Lean-face ASSEMBLY (packaging plus
the anchor-nonvanishing derivation).  The step's mathematics lives in the open
leaves A-M2 (model non-vacuity at depth ≥ 2), B-M1 (KP-STEP), OP-B1 (the
`DevBound` derivation), and the GRB leaf behind U9's binder; nothing here
advances the §3.1 (H1) row (§6 honesty invariants).  Never cite these theorems
alone as evidence for (H1).
-/

section U10
open LeanUrat.MovesJ

/-- **Anchored residuals come from nonzero polynomials**: if `σ.R f` carries a
z-anchor (`HasAnchorK`, Moves/Defs: `R f = T a · toLaurent Ranch` with
`Ranch(0) ≠ 0`), then `f ≠ 0` — since `σ.R 0 = 0` (`Stage.hR0`) while the
anchored form is a Laurent unit times a nonzero polynomial image.  This is the
derivation that lets `key1SiteBlock_consume` fire `GrBKeyLaws.faithful_at`'s
`f ≠ 0` guard from the SideReads(iii) witness alone. -/
theorem anchored_ne_zero (σ : Stage p F) (f : Polynomial ℤ_[p]) {a : ℤ}
    {Ranch : Polynomial ↥σ.K} (h : HasAnchorK (σ.R f) a Ranch) : f ≠ 0 := by
  rintro rfl
  obtain ⟨h0, heq⟩ := h
  rw [σ.hR0] at heq
  have hRanch : Ranch ≠ 0 := fun hR => h0 (by rw [hR, Polynomial.coeff_zero])
  have hL : Polynomial.toLaurent Ranch ≠ 0 := fun hL =>
    hRanch (Polynomial.toLaurent_injective (by rw [map_zero]; exact hL))
  exact mul_ne_zero (LaurentPolynomial.isUnit_T _).ne_zero hL heq.symm

/-- **H1-U10 (`key1SiteBlock_step`) — the KEY1-SITE assembly at a tower step**
(blueprint §5.3/§4.2): `Key1SiteBlock` from U8 + U9.  U8 is consumed literally —
the hypothesis block is `kp_step`'s VERBATIM (`DevBound` is STAGING ONLY,
finding 11); U9's output enters as the EXPLICIT BINDER `laws` (finding 12; the
∀-KB form per the section header).  Pure packaging: the mathematics is the open
A-M2/B-M1/OP-B1/GRB leaves. -/
theorem key1SiteBlock_step (ν : Node p F) (σ' : Stage p F) (M : GenuineStageModel σ')
    (hΦ : IsNodeLift ν σ'.Φ) (he : σ'.e = ν.e) (hh : σ'.h = ν.h)
    (hprev : σ'.wPrev = ν.σ.w) (D : DevBound ν σ' M)
    (laws : ∀ KB : KPBlock σ' M, GrBKeyLaws ν σ' M KB) :
    Key1SiteBlock ν σ' M := by
  obtain ⟨KB⟩ := kp_step ν σ' M hΦ he hh hprev D
  exact ⟨KB, laws KB⟩

set_option linter.unusedVariables false in
/-- **H1-U10 consumption lemma (`key1SiteBlock_consume`)** [REV 2, findings 7/8]
— the lemma WGEO's Lean consumers actually fire: from `Key1SiteBlock ν σ' M` and
a `SideReads`-realized run of `f` at `ν` (clause (iii) supplies the
`HasAnchorK (ν.σ.R f) ν.a ν.Ranch` witness, whence `f ≠ 0` by
`anchored_ne_zero`), the WGEO-shaped (d1)–(d3) at `(f, ν.μ)` (blueprint §4.1,
the O-1thr rev-4 consumed form):
* (d1) `in(σ'.Φ) = u · ψ̂hom` with `u` a `Gr`-unit and `ψ̂hom` homogeneous prime;
* (d2) `ψ̂hom ∤ in(B)` for every nonzero `B` of degree `< deg σ'.Φ`;
* (d3) the two-sided ord tie at the RECORDED `ν.μ`:
  `ψ̂hom^ν.μ ∣ in(f)` and `¬ ψ̂hom^(ν.μ+1) ∣ in(f)`.
The site block is the CONSUMER-side hypothesis (Step-6 wiring supplies it — at a
step via `key1SiteBlock_step`, along a chain via `key1_along_history`); the
run-to-anchor identification is §4.2's obligation (iv), rendered exactly as the
finding-7 REALIZED-READ DATA hypothesis.  `Φnext` rides only through
`SideReads`'s descent clauses (unconsumed here — (d1)–(d3) are at the CURRENT
site). -/
theorem key1SiteBlock_consume (ν : Node p F) (σ' : Stage p F)
    (M : GenuineStageModel σ') (hSite : Key1SiteBlock ν σ' M)
    (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (Φnext : Polynomial ℤ_[p])
    (hdev : IsDevelopment ν.σ.Φ f B Nd) (hreads : SideReads ν B Nd Φnext) :
    letI := M.Rg.ring
    ∃ ψhom : M.S.Gr,
      (∃ (γ : ℤ) (x : M.S.grPiece γ),
        ψhom = DirectSum.of (fun γ => M.S.grPiece γ) γ x) ∧
      (∃ u : (M.S.Gr)ˣ, M.S.initialForm σ'.Φ = (u : M.S.Gr) * ψhom) ∧
      Prime ψhom ∧
      (∀ Bq : Polynomial ℤ_[p], Bq ≠ 0 → Bq.natDegree < σ'.Φ.natDegree →
        ¬ ψhom ∣ M.S.initialForm Bq) ∧
      (ψhom ^ ν.μ ∣ M.S.initialForm f ∧
        ¬ ψhom ^ (ν.μ + 1) ∣ M.S.initialForm f) := by
  letI := M.Rg.ring
  obtain ⟨KB, laws⟩ := hSite
  have hanch : HasAnchorK (ν.σ.R f) ν.a ν.Ranch := by
    have h3 := hreads.2.2.1.1
    rwa [← hdev.2.2] at h3
  have hf : f ≠ 0 := anchored_ne_zero ν.σ f hanch
  exact ⟨KB.ψhom, KB.homog, KB.kpa_init, KB.kpirr, KB.kpa_block,
    laws.faithful_at f hf hanch⟩

end U10

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.key1_along_history
#print axioms LeanUrat.Scaffold.HDischarge.H1.key1SiteBlock_step
#print axioms LeanUrat.Scaffold.HDischarge.H1.key1SiteBlock_consume
