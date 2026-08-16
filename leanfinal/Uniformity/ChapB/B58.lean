/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B55
import Uniformity.ChapB.B56
import Uniformity.ChapB.B57
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapB.B58 — THE LEAF THEOREM at residual degree `1` (unconditional)

**Chapter B, NODE B.58** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer),
ENV-C. One signed declaration, `typeOf_leaf_resDeg_one`, plus one non-contract corollary.

*THE LEAF THEOREM at residual degree 1.* Over the complete bundle, let `φ` be an order-1 key
with `m = φ.natDegree`, `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, and let `g` be monic, `(u,ℓ)`-pure
with `sideDeg φ g u ℓ = 1` and `ḡ = φ̄ ^ ℓ`. Then

```
typeOf g = ⟨{(ℓ, m)}⟩
```

and in particular `g` is irreducible over `O`.

**This is the chapter's unconditional `d = 1` row.** `B-BOX-1` (B.61's `hBOX`) is *not* used
anywhere below and must not be read into this node: at `d = 1` the residue-degree bracket
`m ∣ f(g) ∣ m·d` of B.55a is already an equality, so no pinning hypothesis is needed. The
`ℓ = 1, m ≥ 2, d ≥ 2` region that A-F.7 dropped to `B-BOX-1` is disjoint from this node's
hypotheses (`d = 1` at any `m`, any `ℓ` — blueprint §7's UNCONDITIONAL row).

DEPENDS: B.13 (through B.57's degree bookkeeping) · B.52 and B.55b
(`inertiaDegOf_eq_of_resDeg_one`, the bracket's collapse) · B.56b
(`factorizationType_eq_of_dvd`) · B.57 (`isPure_of_monic_factor`) · landed
`Uniformity.Density.typeOf_degree` (`Density/TypeOf.lean:372`), `typeOf_data`,
`monicFactors_spec`, `efPair_pos_of_mem` and `natDegree_pos_of_mem_monicFactors`
(`Density/TypePositivity.lean:55`, `:43`) · mathlib `Multiset.exists_cons_of_mem`,
`Polynomial.monic_multiset_prod_of_monic`, `Multiset.card_eq_one`.

## Which of the blueprint's two routes is taken

The blueprint records **two** routes deliberately (its ⚠ note) and requires the transcription to
say which it took, *because the DEPENDS differ*.

**This file takes the LONG route — step 4, via B.56b** (`EFF.HE3.34`'s orbit-counting shape):
the contract theorem never proves irreducibility on the way, it pins every member of
`(typeOf g).data` by divisibility and lets `factorizationType_eq_of_dvd` collapse the type.
Concretely the per-factor read is *stronger* than step 4 asks for — B.55b applied to a factor
returns `inertiaDegOf g' = m` and `ramIndexOf g' = ℓ` **as equalities**, not just `m ∣ f'` and
`ℓ ∣ e'` — but the interface fed to B.56b is the divisibility one it is signed for.

The SHORT route (step 3, `EFF.HE6.32` step 4's shape) is then recovered *as a corollary*:
`irreducible_of_resDeg_one` reads `monicFactors g = {g}` off the singleton type. It is **not**
contract text (the frozen SIGNATURE has only the `typeOf` conclusion); it is the blueprint
STATEMENT's "and in particular `g` is irreducible over `O`" clause, landed so that no consumer
has to re-derive it.

**PROOF.**
1. **The degree pin.** `g` is monic, so `deg g = deg ḡ = deg (φ̄ ^ ℓ) = ℓ·m` (`hres`,
   `Polynomial.natDegree_pow`, `Monic.natDegree_map`). Hence `0 < deg g` and `m ∣ deg g` —
   the latter is exactly B.57's load-bearing `hgd` (A-F.6), and it is *free* here, which is why
   this node needs no separate divisibility hypothesis.
2. **Every monic irreducible factor is a `d = 1` leaf.** Let `g' ∈ monicFactors g`. Splitting
   the factorization multiset as `g' ::ₘ F` gives `g = g' * F.prod` with both factors monic, so
   B.57 applies and returns: `g'` and `F.prod` are `(u,ℓ)`-pure,
   `sideDeg g' + sideDeg F.prod = sideDeg g = 1`, and `ḡ' = φ̄ ^ (ℓ · sideDeg g')`.
   If `sideDeg g' = 0` the residue clause degenerates to `ḡ' = 1`, forcing `deg g' = 0` and
   contradicting the positive degree of an irreducible factor. So `sideDeg g' = 1`.
3. **The `(e,f)` read.** B.55b at `g'` (hypotheses: monic, positive degree, pure, `sideDeg = 1`,
   residue clause — all from step 2) gives `inertiaDegOf g' = m` and `ramIndexOf g' = ℓ`, i.e.
   `efPair g' = (ℓ, m)`.
4. **Collapse.** `(typeOf g).degree = deg g = ℓ·m` (landed `typeOf_degree`); members are
   positive (landed `efPair_pos_of_mem`); `ℓ ∣ e` and `m ∣ f` for every member by step 3. B.56b
   `factorizationType_eq_of_dvd` with `a := ℓ`, `b := m` gives `typeOf g = ⟨{(ℓ, m)}⟩`.
5. **(Corollary.)** The type is a singleton, so `monicFactors g` has card `1`; its unique element
   has product `g`, hence equals `g`, hence `g` is irreducible.

## What each hypothesis pays for

`hu`, `hcop` and `hpure` enter only through B.57 and B.55b (`hcop` is B.54's gcd step inside
B.55a). `hℓ` is used three times: through B.57, through B.55b, and as `0 < a` for B.56b. `hg`
is used for the degree pin, for `monicFactors_spec`, and for `typeOf_degree`. `h1` is the node's
whole scope — it is what makes B.55's bracket an equality (step 3) and what forces the cofactor's
`sideDeg` to `0` (step 2). `hres` is consumed as the degree pin and, through B.57, as the source
of each factor's own residue clause. `hne` names the side whose degree `h1` measures.

Note that `hφ`'s three fields all do work: `monic` and `pos` in the degree arithmetic,
`irred` inside B.52/B.57 (unique factorization of `ḡ` in `(ResidueField O)[X]`).

## Environment note (0e type diff)

The elaborated signature carries ENV-C's `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]`, which the stub's `axiom` form drops because the *statement* names
neither. They reappear through B.55b and B.57. Exactly the artifact recorded at B.52, B.54 and
B.55; the mismatch is the blueprint's own declared ENV-C hypotheses reappearing, not a weakening.

## Signature provenance

`typeOf_leaf_resDeg_one` is the frozen stub (`leanspec/Leanspec/ChapB.lean`), verbatim — binder
names, order, implicitness and conclusion unchanged. `irreducible_of_resDeg_one` is new and
**NOT contract text**; it carries the contract theorem's binder list unchanged.

## Faithfulness

`docs/GMN_citations.md` Cor 1.20 ("in particular, if `a_i = 1` then `G_i` is irreducible,
`f(L/K) = m·deg ψ_i`, `e(L/K) = e`") — the corollary above is the first clause, the contract
theorem the second and third. `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md` NS-2 ([GN15] Thm 2.3's
last clause, `COVERS-ALL-O`); `EFF.HE6.32` step 4; `EFF.HE3.34`; `EFF.W12.27`.

The `(e,f)` read is over the **order** `AdjoinRoot g` (DECISION D-3): `inertiaDegOf`/`ramIndexOf`
are the norm-valuation invariants of `Density/TypeOf.lean`, and `HYP.01` (`typeOf` faithfulness)
and `HYP.12` (the `(e,f)` ordering convention) remain [CORE-SET] open — **disclosed here, not
discharged** (chapter-B honesty item H-7; the two `BP.B.58 → HYP.*` rows of the chapter ledger).

SOURCE: `docs/GMN_citations.md` Cor 1.20; `EFF.HE6.32`; `EFF.HE3.34`; `EFF.W12.27`.

**TEETH.** `W12-ORACLE` (`EFF.W12.56`, `[IND]`, 0 bad / 41,923 PARI checks) → **executable
regression** retained (PARI remains the independent engine); `HE-SIG` (`EFF.HE3.52`) →
**Lean theorem** at `d = 1`.

**No new axioms; no `sorry`.** In particular the 2026-08-16 B.42 axiom
(`exists_slope_factorization`) is **not** on this file's import path: B.55/B.56/B.57 predate it
and do not import `ChapB.B42`, so the footprints printed below are Lean-core only.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Both instances enter the
-- signature through B.55b and B.57 (see the environment note above).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.58 — THE LEAF THEOREM at residual degree `1`, unconditionally.** For an order-1 key `φ`
with `m = φ.natDegree`, a slope `−u/ℓ` in lowest terms with `0 < u < ∞`, `0 < ℓ`, and a monic
`(u,ℓ)`-pure `g` with residual degree `1` and reduction `φ̄ ^ ℓ`,

```
typeOf g = ⟨{(ℓ, m)}⟩.
```

No `B-BOX-1`: at `d = 1` B.55's bracket `m ∣ f(g) ∣ m·d` is already an equality. Route taken:
the blueprint's **long route** (step 4, via B.56b) — see the module docstring. -/
theorem typeOf_leaf_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (h1 : sideDeg φ g u ℓ hne = 1)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ ℓ) :
    typeOf g = ⟨{(ℓ, φ.natDegree)}⟩ := by
  classical
  -- STEP 1: the degree pin `deg g = ℓ * m`, and its two free consequences.
  have hdeg : g.natDegree = ℓ * φ.natDegree := by
    have hm1 : (g.map (IsLocalRing.residue O)).natDegree = g.natDegree :=
      hg.natDegree_map _
    rw [← hm1, hres, Polynomial.natDegree_pow, hφ.monic.natDegree_map]
  have hgd : φ.natDegree ∣ g.natDegree := ⟨ℓ, by rw [hdeg]; ring⟩
  have hspec := monicFactors_spec hg
  -- STEPS 2-3: every monic irreducible factor of `g` is itself a `d = 1` leaf, with the same
  -- `(e, f) = (ℓ, m)`.
  have hef : ∀ g' ∈ monicFactors g, efPair g' = (ℓ, φ.natDegree) := by
    intro g' hg'mem
    have hg'm : g'.Monic := (hspec.1 g' hg'mem).1
    have hg'pos : 0 < g'.natDegree := natDegree_pos_of_mem_monicFactors hg hg'mem
    -- peel `g'` off the factorization multiset to expose a monic cofactor
    obtain ⟨F, hF⟩ := Multiset.exists_cons_of_mem hg'mem
    have hFm : F.prod.Monic := by
      have hall : ∀ b ∈ F, (id b : Polynomial O).Monic := by
        intro b hb
        exact (hspec.1 b (by rw [hF]; exact Multiset.mem_cons_of_mem hb)).1
      simpa using Polynomial.monic_multiset_prod_of_monic F id hall
    have hprod : g = g' * F.prod := by
      rw [← hspec.2, hF, Multiset.prod_cons]
    -- B.57: both factors are pure, their residual degrees add up, and `ḡ' = φ̄ ^ (ℓ·d')`
    obtain ⟨hne₁, hne₂, hp₁, -, hsum, hr₁⟩ :=
      isPure_of_monic_factor hπ hφ hu hℓ hcop hg hg'm hFm hgd hprod hpure hne
    have hsum1 : sideDeg φ g' u ℓ hne₁ + sideDeg φ F.prod u ℓ hne₂ = 1 := by
      rw [hsum, h1]
    -- the factor's residual degree cannot vanish: `ḡ' = 1` would force `deg g' = 0`
    have hd'pos : 0 < sideDeg φ g' u ℓ hne₁ := by
      rcases Nat.eq_zero_or_pos (sideDeg φ g' u ℓ hne₁) with h0 | hpos
      · exfalso
        rw [h0, Nat.mul_zero, pow_zero] at hr₁
        have hz : g'.natDegree = 0 := by
          rw [← hg'm.natDegree_map (IsLocalRing.residue O), hr₁, Polynomial.natDegree_one]
        omega
      · exact hpos
    have hd'1 : sideDeg φ g' u ℓ hne₁ = 1 := by omega
    -- B.55b at `g'`: the bracket collapses to `f(g') = m`, `e(g') = ℓ`
    obtain ⟨hfeq, heeq⟩ :=
      inertiaDegOf_eq_of_resDeg_one hπ hφ hu hℓ hcop hg'm hg'pos hp₁ hne₁ hd'pos hr₁ hd'1
    simp [efPair, hfeq, heeq]
  -- STEP 4: the divisibility interface, and B.56b's collapse.
  refine factorizationType_eq_of_dvd hℓ hφ.pos ?_ ?_ ?_ ?_
  · rw [typeOf_degree hg, hdeg]
  · exact fun p hp => efPair_pos_of_mem hg hp
  · intro p hp
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg'mem, rfl⟩ := hp
    simp [hef g' hg'mem]
  · intro p hp
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg'mem, rfl⟩ := hp
    simp [hef g' hg'mem]

/-- **The blueprint STATEMENT's last clause — NOT contract text.** In the situation of B.58 the
polynomial `g` is irreducible over `O`. This is the short route's (step 3's) payoff, recovered
here from the singleton type rather than proved separately: `typeOf g = ⟨{(ℓ, m)}⟩` says
`monicFactors g` has exactly one element, and that element's product is `g`.

Signed nowhere in `leanspec/Leanspec/ChapB.lean` — added so that consumers of the `d = 1` leaf
(B.63, B.79, and the `HT` count layer) need not re-derive it. -/
theorem irreducible_of_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (h1 : sideDeg φ g u ℓ hne = 1)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ ℓ) :
    Irreducible g := by
  classical
  have hT := typeOf_leaf_resDeg_one hπ hφ hu hℓ hcop hg hpure hne h1 hres
  have hdata : (monicFactors g).map efPair = ({(ℓ, φ.natDegree)} : Multiset (ℕ × ℕ)) := by
    have h := congrArg FactorizationType.data hT
    rwa [typeOf_data] at h
  have hcard : Multiset.card (monicFactors g) = 1 := by
    have h := congrArg Multiset.card hdata
    simpa using h
  obtain ⟨g', hg'⟩ := Multiset.card_eq_one.1 hcard
  have hspec := monicFactors_spec hg
  have hgg' : g = g' := by rw [← hspec.2, hg', Multiset.prod_singleton]
  rw [hgg']
  exact (hspec.1 g' (by rw [hg']; exact Multiset.mem_singleton_self g')).2

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_leaf_resDeg_one
#print axioms Uniformity.Density.Leaf.irreducible_of_resDeg_one
end AxCheck
