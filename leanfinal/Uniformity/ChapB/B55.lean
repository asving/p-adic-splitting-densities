/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B52
import Uniformity.ChapB.B54
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapB.B55 — the residue-degree bracket, and its collapse at `d = 1`

**Chapter B, NODE B.55** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer),
ENV-C. Two signed declarations (`B.55a`, `B.55b`).

*The residue-degree bracket, and its collapse at `d = 1`.* Under the joint hypotheses of B.52
and B.54 — `φ` an order-1 key with `m = φ.natDegree`, `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, `g`
monic of positive degree, `(u,ℓ)`-pure with `d = sideDeg φ g u ℓ > 0` and `ḡ = φ̄ ^ (ℓ*d)` —

```
m ∣ inertiaDegOf g   and   inertiaDegOf g ∣ m * d          (B.55a, `inertiaDegOf_bracket`)
```

and in particular at `d = 1`

```
inertiaDegOf g = m   and   ramIndexOf g = ℓ.               (B.55b, `inertiaDegOf_eq_of_resDeg_one`)
```

The bracket is nothing but the two halves of GMN Cor 1.20 conjoined: B.52 is the lower half
(`m ∣ f(g)`, from the residue-field dimension count at the key), B.54 the upper half
(`f(g) ∣ m*d`, from the norm bracket and `gcd u ℓ = 1`). At `d = 1` the two ends of the bracket
coincide and `Nat.dvd_antisymm` closes it; `e(g) = ℓ` then falls out of `e·f = deg g` (landed
`ramIndexOf_mul_inertiaDegOf`) once the degree is pinned to `ℓ*m`.

**This node is where the chapter's unconditional `d = 1` row (B.58) gets its `(e,f)`.** At
`d ≥ 2` the bracket is genuinely a bracket and not an equality — pinning `f(g)` to `m*d` there is
exactly the chapter's carried hypothesis `B-BOX-1` (B.61's `hBOX`), which this node does **not**
touch and must not be read as supplying.

DEPENDS: B.52 (`key_natDegree_dvd_inertiaDegOf`) · B.54 (`inertiaDegOf_dvd_key_mul_resDeg`) ·
landed `Uniformity.Density.ramIndexOf_mul_inertiaDegOf` (`Density/TypeOf.lean:275`) · mathlib
`Nat.dvd_antisymm`, `Nat.mul_pos`, `Nat.eq_of_mul_eq_mul_right`, `Polynomial.natDegree_pow`,
`Polynomial.Monic.natDegree_map`.

**PROOF.**
1. **B.55a.** The conjunction of B.52 at `k := ℓ * d` (positive by `hℓ`, `hdd`, and matching
   `hres` verbatim) and B.54 at the same data. No new content; the node's whole job is to hold
   the two halves in one statement so that B.58 and B.61 can consume them together.
2. **B.55b, the collapse.** `h1 : d = 1` turns B.55a's upper half into `inertiaDegOf g ∣ m`
   (`mul_one`), so with the lower half `Nat.dvd_antisymm` gives `inertiaDegOf g = m`.
3. **B.55b, the ramification index.** `hres` pins the degree: `g` is monic, so
   `(g.map (residue O)).natDegree = g.natDegree`, while the right-hand side has degree
   `(ℓ * d) * m = ℓ * m` at `d = 1`. Landed `ramIndexOf_mul_inertiaDegOf hg hd` reads
   `ramIndexOf g * inertiaDegOf g = g.natDegree`; substituting step 2 and the pin gives
   `ramIndexOf g * m = ℓ * m`, and `m > 0` (`hφ.pos`) cancels.

## What each hypothesis pays for

`hu`, `hcop`, `hpure` and `hdd` are consumed only through B.54 (`hcop` is the gcd step's payoff —
the hypothesis whose necessity `EFF.HE6.52`'s tooth `HE6-T-BADKEY` established by
counterexample). `hres` is consumed three times: as B.52's reduction hypothesis, as B.54's, and
directly in step 3 as the degree pin (see B.54's minimum-hypothesis note, which resolves the
blueprint's §14 item 8 CLOSED-AGAINST: `hres` is load-bearing, not over-strong, because purity
alone leaves `m ∤ g.natDegree` possible through the truncated division in `IsPure`'s right
clause). `hℓ` enters both through B.54 and through B.52's `0 < k`.

## Environment note (0e type diff)

The elaborated signatures carry ENV-C's `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]`, which the stubs' `axiom` forms drop because the *statements* name
neither. They reappear here through B.52 and B.54, both of which bind them. Exactly the artifact
recorded at B.52 and B.54; the mismatch is the blueprint's own declared ENV-C hypotheses
reappearing, not a weakening introduced here.

## Signature provenance

* **B.55a** is the frozen stub, verbatim.
* **B.55b** is stub defect **B-D8**: the blueprint signed it as `(… same hypotheses …)`, and the
  expansion is B.55a's binder list plus `(h1 : sideDeg φ g u ℓ hne = 1)`, per the node's
  STATEMENT ("Under the joint hypotheses of B.52 and B.54 … In particular if `d = 1`"). The
  expansion is the one recorded in the RE-SIGN LOG of `leanspec/Leanspec/ChapB.lean` and is
  reproduced here byte-for-byte.
* B.54's own `hres` binder (stub defect **B-D7**, a missing closing parenthesis) is closed by
  this node's byte-identical `hres`, as the blueprint's repair note says.

## Faithfulness

`docs/GMN_citations.md` Cor 1.20 (the full bracket `m·deg ψ_i ∣ f(L/K) ∣ …`); `EFF.HE3.26`
(`COROLLARY HE3-0′`, the corpus's bracket); `EFF.HE3.33` (the corpus's own `d = 1` perimeter,
which is exactly B.55b's hypothesis `h1`).

SOURCE: `docs/GMN_citations.md` Cor 1.20; `EFF.HE3.26`; `EFF.HE3.33`.

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad) → **Lean theorem** at `d = 1` (B.55b);
**executable regression** retained at `d ≥ 2`, where the bracket is not an equality and the
pinning is `B-BOX-1`.

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Both instances enter the
-- signatures through B.52 and B.54 (see the environment note above).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.55a — the residue-degree bracket.** For an order-1 key `φ` with `m = φ.natDegree`, a
slope `−u/ℓ` in lowest terms with `0 < u`, and a monic `g` of positive degree that is
`(u,ℓ)`-pure with residual degree `d > 0` and reduction `φ̄ ^ (ℓ*d)`,

```
m ∣ inertiaDegOf g ∧ inertiaDegOf g ∣ m * d.
```

B.52 (the residue-field dimension count at the key) and B.54 (the norm bracket) conjoined. -/
theorem inertiaDegOf_bracket (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)) :
    φ.natDegree ∣ inertiaDegOf g ∧ inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne :=
  ⟨key_natDegree_dvd_inertiaDegOf hπ hφ hg hd (Nat.mul_pos hℓ hdd) hres,
    inertiaDegOf_dvd_key_mul_resDeg hπ hφ hu hℓ hcop hg hd hpure hne hdd hres⟩

/-- **B.55b — the collapse of the bracket at residual degree `1`.** In the situation of B.55a
with `sideDeg φ g u ℓ hne = 1`, the bracket `m ∣ inertiaDegOf g ∣ m` is an equality, and the
ramification index is the slope's denominator:

```
inertiaDegOf g = φ.natDegree ∧ ramIndexOf g = ℓ.
```

This is the `(e,f)` that B.58 reads off the unconditional `d = 1` leaf. -/
theorem inertiaDegOf_eq_of_resDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hd : 0 < g.natDegree) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) (hdd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    (h1 : sideDeg φ g u ℓ hne = 1) :
    inertiaDegOf g = φ.natDegree ∧ ramIndexOf g = ℓ := by
  -- Step 1: the bracket.
  obtain ⟨hlo, hhi⟩ := inertiaDegOf_bracket hπ hφ hu hℓ hcop hg hd hpure hne hdd hres
  -- Step 2: at `d = 1` the two ends coincide.
  rw [h1, mul_one] at hhi
  have hf : inertiaDegOf g = φ.natDegree := Nat.dvd_antisymm hhi hlo
  refine ⟨hf, ?_⟩
  -- Step 3: `hres` pins the degree to `ℓ * m`, and `e * f = deg g` gives `e = ℓ`.
  have hdeg : g.natDegree = ℓ * φ.natDegree := by
    have hm1 : (g.map (IsLocalRing.residue O)).natDegree = g.natDegree := hg.natDegree_map _
    have hm2 : ((φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne)).natDegree
        = (ℓ * sideDeg φ g u ℓ hne) * φ.natDegree := by
      rw [Polynomial.natDegree_pow, hφ.monic.natDegree_map]
    rw [← hm1, hres, hm2, h1, mul_one]
  have hef : ramIndexOf g * φ.natDegree = ℓ * φ.natDegree := by
    have h := ramIndexOf_mul_inertiaDegOf hg hd
    rw [hf, hdeg] at h
    exact h
  exact Nat.eq_of_mul_eq_mul_right hφ.pos hef

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.inertiaDegOf_bracket
#print axioms Uniformity.Density.Leaf.inertiaDegOf_eq_of_resDeg_one
end AxCheck
