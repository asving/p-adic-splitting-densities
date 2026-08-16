/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B29
import Uniformity.ChapB.B34

/-!
# Uniformity.ChapC.C01 — `KeyFrame`, the stage key frame

**Chapter C, NODE C.01** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. One signed declaration,
definitional.

*The stage key frame.* A **key frame** over the fixed bundle `O` consists of natural numbers
`e₁, f₁, h` and a polynomial `Φ′ ∈ O[X]` ("the key") subject to: `0 < e₁`, `0 < f₁`,
`Nat.Coprime h e₁` (the slope `h/e₁` in lowest terms); `Φ′` monic of degree `D′ = e₁·f₁`,
irreducible over `O`; `Φ′` is `(h, e₁)`-pure with respect to the order-0 key `X` (the
closure-free form of "the roots of `Φ′` have valuation `h/e₁`"); and the residual polynomial of
`Φ′` at that side — read under the GC-1 `sideMin` pin — is **irreducible** of degree `f₁` (the
frame's `ψ`). This is `EFF.HE6.08`'s frame `(O, Φ′, ψ, K = F_Q(η_θ), dv = e₁v)` with every
closure-dependent clause recast on chapter B's API.

The valuation normalization `dv := e₁·v` is C.02's `KeyFrame.stageHeight`; the pin proposition
`KeyFrame.Pin` is C.14a's (A-C.1(c)), not this node's.

GC-7 is in force: the bundle `O` is fixed once and a tower level is DATA over it, never a
re-quantified DVR. GC-2 is in force: the polygon objects are chapter B's landed
`sideSet`/`sideMin`/`resPoly`/`IsPure`, reused literally at the order-0 key `X`, with no new
polygon type.

## Faithfulness

**⚠ Mandatory, trust-boundary definition.** Three recasts against `EFF.HE6.08`'s verbatim frame,
each flagged for the chapter cross-read (blueprint §16):

* *"roots of `v = h/e₁`"* becomes the purity clause `hpure` together with `hne` — the two are
  equivalent through the polygon dictionary (a one-sided `X`-polygon of slope `h/e₁` IS the
  root-valuation statement, closure-free; chapter B's D-1 criterion C2).
* *"`ψ` irreducible with root `η_θ = res(θ^{e₁}π^{−h})`"* becomes `hresirr` — the residual read
  at the side, B.28/B.29's object. The `η_θ`-embedding `ι_ξ` of `EFF.HE6.08` is NOT carried
  (labels are transported by algebra maps of `AdjoinRoot` quotients, blueprint §4).
* The degenerate `h = 0` instance is admitted (the corpus has `h ≥ 1`) solely so that C.05's
  level-1 reconciliation can be definitional; every node needing positivity states `0 < F.h`
  explicitly (GC-6.4), and C.14a's carrier bridge to chapter H §8 takes `hh : 1 ≤ F.h` as an
  explicit hypothesis.

Note that `IsKey key` (B.01) does NOT hold at `h ≥ 1`: the reduction is `x^{D′}`, not
irreducible. The frame is genuinely disjoint from chapter B's key class except at the degenerate
instance, which is CHAP-B's H-1 seam made precise.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: B.01 (`IsKey`, for the contrast only) · B.16 (`sideSet`) · B.20 (`sideMin`) ·
B.28/B.29 (`resPoly`) · B.34 (`IsPure`) — all by committed node ID (GC-13(b)). The imports are
B.29 and B.34, which pull the rest of the chain.

**PROOF.** Definitional. The body is the gate-verified `leanspec/Leanspec/ChapC.lean` stub body
(`structure KeyFrame`, the §3 A-C.1 layer) verbatim.

SOURCE: `EFF.HE6.08` (the frame convention, verbatim); `EFF.HE6.10` (the development frame it
feeds); CHAP-B H-1 (the deferral of exactly this object to chapter C).

**TEETH.** Signed non-applicable (a definition; the frame audits fire at C.10 and blueprint §13).

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- The stage key frame `(e₁, f₁, h; Φ′)` of `EFF.HE6.08`: `Φ′` monic irreducible of degree
`D′ = e₁f₁`, one-sided of slope `h/e₁` over the order-0 key `X`, with irreducible residual
read `ψ` of degree `f₁`.  The valuation normalization is `dv := e₁·v` (C.02). -/
structure KeyFrame (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) where
  e₁ : ℕ
  f₁ : ℕ
  /-- The slope numerator.  `h = 0` (forcing `e₁ = 1`) is the DEGENERATE frame, admitted so
  that C.05's level-1 reconciliation is definitional; the corpus frame has `1 ≤ h`. -/
  h : ℕ
  key : Polynomial O
  he₁ : 0 < e₁
  hf₁ : 0 < f₁
  hcop : Nat.Coprime h e₁
  hmonic : key.Monic
  hdeg : key.natDegree = e₁ * f₁
  hirr : Irreducible key
  hpure : IsPure Polynomial.X key h e₁
  hne : (sideSet Polynomial.X key h e₁).Nonempty
  /-- The residual read of the key is irreducible of degree `f₁` (frame hypothesis
  `ψ ∈ F_Q[T]` irreducible, `EFF.HE6.08`) — pinned at `sideMin` per GC-1. -/
  hresirr : ∀ (H₀ : ℕ), npHgt Polynomial.X key (sideMin Polynomial.X key h e₁ hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π Polynomial.X key h e₁ hne H₀) ∧
    (resPoly π Polynomial.X key h e₁ hne H₀).natDegree = f₁

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.KeyFrame
#print axioms Uniformity.Density.Tower.KeyFrame.mk

end AxCheck
