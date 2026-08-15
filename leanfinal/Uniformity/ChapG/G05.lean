/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G05 — `CertFamily`, the certificate schema

**Chapter G, NODE G.05** (`blueprint/CHAP-G_base_cases_menus.md` §3). *The certificate schema.*
A level-`N` certified family over `O` consists of: a centre-modulus `m ≤ N`; a centre-indexed
certificate `cert : O → Coeff O n N → Prop`; a splitting type `σ`; a target type `D` with a
centre-indexed bijection `read : O → (Coeff O n N ≃ D)` and an admissible set `S : Set D`;
subject to (i) readability, (ii) shift-stability, (iii) centre-uniqueness, (iv) forcing. Its
certified set is `{c | ∃ γ, cert γ c}`.

DEPENDS: landed `Uniformity.Density.Coeff`, `Res`, `resFactor`, `proj`, `monicPoly`, `typeOf`,
`FactorizationType`.

Definitional, no proof obligation (a `structure` declares field *types*, not proofs of them).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- A level-`N` certified family: a centre-indexed certificate that (i) reads through a
bijection, (ii) survives centre moves inside a fixed coset, (iii) pins the centre's coset, and
(iv) forces one splitting type on every lift. -/
structure CertFamily (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n N : ℕ) where
  m : ℕ
  hm : m ≤ N
  D : Type
  cert : Res O N → Coeff O n N → Prop
  read : Res O N → (Coeff O n N ≃ D)
  S : Set D
  σ : FactorizationType
  hcert : ∀ γ c, cert γ c ↔ read γ c ∈ S
  hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c
  huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ
  hforce : ∀ γ (a : Fin n → O), cert γ (proj O n N a) → typeOf (monicPoly a) = σ

/-- The set of level-`N` classes certified by some centre. -/
def CertFamily.set {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {n N : ℕ} (F : CertFamily O n N) :
    Set (Coeff O n N) := {c | ∃ γ, F.cert γ c}

end Uniformity.Density.Menu
