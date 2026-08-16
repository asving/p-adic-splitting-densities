/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B54
import Uniformity.ChapB.B57
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapB.B61 — THE LEAF THEOREM in general, conditional on `B-BOX-1`

**Chapter B, NODE B.61** [theorem] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer),
ENV-C. One signed declaration.

*THE LEAF THEOREM in general, conditional on `B-BOX-1`.* For `φ` an order-1 key with
`m = φ.natDegree`, `0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, and `g` monic `(u,ℓ)`-pure with
`d = sideDeg φ g u ℓ > 0` and reduction `ḡ = φ̄ ^ (ℓ*d)`, **assuming**

```
(B-BOX-1)   ∀ g' ∈ monicFactors g,  m * d ∣ inertiaDegOf g',
```

one has `typeOf g = ⟨{(ℓ, m*d)}⟩` — a single factor, ramification index `ℓ`, residue degree
`m*d`.

## ⚠ `B-BOX-1` IS CARRIED, NOT DISCHARGED

`hBOX` is an **explicit hypothesis of this statement**. It is not an axiom, not a `sorry`, and
nothing in this file proves it or any special case of it. It is the chapter's declared
conditionality: the `d ≥ 2` row of DECISION D-3's `(e,f)` table (`ℓ ≥ 2` or `m ≥ 2`) holds only
under `B-BOX-1`, whose repair route is the OPTIONAL node B.62 (the spectral-norm root label,
deliberately not fired with the chapter). The two unconditional rows — B.58 (`d = 1`, any `m`,
any `ℓ`) and B.60 (integral slope at the linear key) — do not touch `hBOX`, and **no node outside
this one's consumers (B.71, B.79) may assume it**: an agent that finds itself wanting it has left
the perimeter and must return `BLOCKED: B-BOX-1`.

**The carried hypothesis is satisfiable, so the theorem is not vacuous.** At `d = 1` every
`g' ∈ monicFactors g` has `ḡ' = φ̄ ^ k` with `0 < k` (B.57's last clause, step 2 below), so B.52
gives `m ∣ inertiaDegOf g'`, which is `hBOX` at `d = 1`. What is open is `d ≥ 2` — and only
there. (This is an unverified reading of the two landed statements, not a machine-checked claim:
nothing in this file instantiates `hBOX`.)

Do not conflate `B-BOX-1` with `HE6-BOX-1`. The tooth `HE6-T-CASEB` (`EFF.HE6.37`, `.52`: "3
distinct PARI σ on identical outer data — box is real") certifies **HE6-BOX-1**, the *repeated*
residual factor (`a ≥ 2`), a **non-node**; `B-BOX-1` is about a *multiplicity-1* residual factor
of *degree* `d ≥ 2`. Neither is proved here (see B.66).

## What the hypothesis buys, mechanically

`hBOX` is the residue-degree **lower** bound; B.54 supplies the matching **upper** bound
`inertiaDegOf g' ∣ m * sideDeg φ g' u ℓ` at every monic irreducible factor `g'`, and B.57 says
every such factor is again `(u,ℓ)`-pure with `sideDeg φ g' u ℓ ≤ d`. Squeezing,
`m*d ∣ inertiaDegOf g' ∣ m * sideDeg g'` forces `d ∣ sideDeg g'`, hence `sideDeg g' = d`, hence
`deg g' = deg g` — so `g` is irreducible and its own monic factorization. The `(e,f)` pair is then
`inertiaDegOf g = m*d` (`hBOX` and B.54 at `g` itself, `Nat.dvd_antisymm`) and `ramIndexOf g = ℓ`
(landed `ramIndexOf_mul_inertiaDegOf` and the degree pin).

DEPENDS: B.13 (through B.54/B.57) · B.54 (`inertiaDegOf_dvd_key_mul_resDeg`) · B.57
(`isPure_of_monic_factor`, the A-F.6 repaired form, whose `hgd : φ.natDegree ∣ g.natDegree` is
supplied here by the degree pin) · landed `Uniformity.Density.typeOf_data`,
`monicFactors_spec`, `monicFactors_eq`, `IsMonicFactorization`, `isUnit_of_natDegree_zero`,
`ramIndexOf_mul_inertiaDegOf`, `efPair` (`Density/TypeOf.lean`) · mathlib
`Multiset.exists_mem_of_ne_zero`, `Multiset.cons_erase`, `Multiset.prod_cons`,
`Polynomial.monic_multiset_prod_of_monic`, `Polynomial.Monic.natDegree_eq_zero`,
`Nat.mul_dvd_mul_iff_left`, `Nat.dvd_antisymm`, `Nat.eq_of_mul_eq_mul_right`.

B.56 (`factorizationType_eq_of_dvd`) is in the node's DEPENDS as the *alternative* closing route
("step 4: conclude, or alternatively apply B.56 with `a := ℓ`, `b := m*d`"). The direct route is
taken here — once `monicFactors g = {g}` is in hand the type is read off the singleton and the
pigeonhole is not needed — so B.56 is not imported.

**PROOF.**
0. **The degree pin.** `hres` plus monicity gives `g.natDegree = (ℓ*d) * m`, hence
   `0 < g.natDegree` (all three factors positive) and `hgd : m ∣ g.natDegree`, which is B.57's
   A-F.6 hypothesis.
1. **A factor exists.** `monicFactors g ≠ 0`, else its product `1` would equal `g`, of positive
   degree. Pick `g'` in it and split `g = g' * h` with `h` the product of the rest, monic.
2. **B.57 at that split.** `g'` and `h` are `(u,ℓ)`-pure, `sideDeg g' + sideDeg h = d`, and
   `ḡ' = φ̄ ^ (ℓ * sideDeg g')`. The last clause pins `deg g' = (ℓ * sideDeg g') * m`; since `g'`
   is monic irreducible it has positive degree (`isUnit_of_natDegree_zero`), so
   `0 < sideDeg g'`.
3. **The squeeze.** B.54 at `g'` gives `inertiaDegOf g' ∣ m * sideDeg g'`; `hBOX` at `g'` gives
   `m*d ∣ inertiaDegOf g'`. Chaining and cancelling `m > 0` gives `d ∣ sideDeg g'`, so
   `d ≤ sideDeg g'`; step 2's additivity gives `sideDeg g' ≤ d`. Hence `sideDeg g' = d` and
   `deg g' = deg g`, so `deg h = 0`, `h = 1`, `g = g'`: **`g` is irreducible** and
   `monicFactors g = {g}`.
4. **The `(e,f)` pair.** `hBOX` at `g` (now a member of its own factor multiset) and B.54 at `g`
   bracket `inertiaDegOf g` between `m*d` and `m*d`, so `inertiaDegOf g = m*d`; then
   `ramIndexOf g * (m*d) = deg g = (ℓ*d)*m` gives `ramIndexOf g = ℓ`.
5. `typeOf g = ⟨(monicFactors g).map efPair⟩ = ⟨{(ℓ, m*d)}⟩`.

## Environment note (0e type diff)

The elaborated signature carries ENV-C's `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]`, which the stub's `axiom` form drops because the *statement* names
neither. They reappear through B.54 and B.57, both of which bind them. Exactly the artifact
recorded at B.52/B.54; the mismatch is the blueprint's own declared ENV-C hypotheses reappearing,
not a weakening introduced here.

## Faithfulness

`docs/GMN_citations.md` Cor 1.20 — the **full** statement, of which this is the *conditional* Lean
form: the corpus derives `hBOX` (the order-1 root label: the leaf's residue field realises a root
of the residual polynomial `ψ` over `resField φ`) through the resultant account that H-2 puts out
of scope, so here it is hypothesised. `EFF.HE6.29` (`[PIN HE6-ROOT-LABEL]`, Cor HE6-2″) is that
derivation; `EFF.HE3.26` (`COROLLARY HE3-0′`, "`f₁f_s ∣ f(L_ρ)`") is the divisibility shape.

Note what the signature does **not** say: the blueprint's prose statement also asks that the
residual polynomial be a unit times an irreducible `ψ` of degree `d`. The frozen signature does
not carry that clause, and the proof does not need it — `hBOX` is exactly the strength the
argument consumes at that point. The irreducibility of `ψ` is how a *caller* is expected to know
`hBOX` (via B.62), not a hypothesis of this theorem.

SOURCE: `docs/GMN_citations.md` Cor 1.20; `EFF.HE6.29`; `EFF.HE3.26`.

**TEETH.** `HE6-T-CASEB` (`EFF.HE6.37`, `.52`) → **executable regression** retained, and it
certifies HE6-BOX-1, *not* `B-BOX-1` (see the warning above).

**No new axioms; no `sorry`.** `B-BOX-1` is a hypothesis of the statement.

## Status

Sorry-free, axiom-free (Lean core only), and CONDITIONAL on the carried `hBOX`.
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **The degree pin.** A monic `p` whose reduction is `φ̄ ^ k`, for `φ` monic, has
`p.natDegree = k * φ.natDegree`. (Private helper; the same three lines appear inline in B.54's
step 0 and B.55's step 3.) -/
private theorem natDegree_of_map_residue_eq_pow {φ p : Polynomial O} (hφ : φ.Monic)
    (hp : p.Monic) {k : ℕ}
    (hres : p.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    p.natDegree = k * φ.natDegree := by
  have h1 : (p.map (IsLocalRing.residue O)).natDegree = p.natDegree := hp.natDegree_map _
  have h2 : ((φ.map (IsLocalRing.residue O)) ^ k).natDegree = k * φ.natDegree := by
    rw [Polynomial.natDegree_pow, hφ.natDegree_map]
  rw [← h1, hres, h2]

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field. Both instances enter the
-- signature through B.54 and B.57 (see the environment note above).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.61 — THE LEAF THEOREM in general, conditional on `B-BOX-1`.** For an order-1 key `φ` with
`m = φ.natDegree`, a slope `−u/ℓ` in lowest terms with `0 < u`, and a monic `(u,ℓ)`-pure `g` with
residual degree `d > 0` and reduction `φ̄ ^ (ℓ*d)`, **assuming** the residue-degree lower bound

```
hBOX :  ∀ g' ∈ monicFactors g,  m * d ∣ inertiaDegOf g'
```

(the chapter's carried hypothesis `B-BOX-1`, NOT proved anywhere in this development), the
splitting type of `g` is `⟨{(ℓ, m*d)}⟩`: `g` is irreducible with ramification index `ℓ` and
residue degree `m*d`.

`hBOX` and B.54's upper bound squeeze the residue degree of every factor; B.57 makes every factor
pure of residual degree `≤ d`; together they force a single factor of full degree. -/
theorem typeOf_leaf_of_resDeg_lower_bound (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (hd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    (hBOX : ∀ g' ∈ monicFactors g,
      φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g') :
    typeOf g = ⟨{(ℓ, φ.natDegree * sideDeg φ g u ℓ hne)}⟩ := by
  classical
  have hm : 0 < φ.natDegree := hφ.pos
  -- Step 0: the degree pin, and B.57's A-F.6 hypothesis.
  have hdeg : g.natDegree = (ℓ * sideDeg φ g u ℓ hne) * φ.natDegree :=
    natDegree_of_map_residue_eq_pow hφ.monic hg hres
  have hn : 0 < g.natDegree := by
    rw [hdeg]; exact Nat.mul_pos (Nat.mul_pos hℓ hd) hm
  have hgd : φ.natDegree ∣ g.natDegree := ⟨ℓ * sideDeg φ g u ℓ hne, by rw [hdeg]; ring⟩
  -- Step 1: `g` has at least one monic irreducible factor; split it off.
  have hspec := monicFactors_spec hg
  have hFne : monicFactors g ≠ 0 := by
    intro h0
    have hp := hspec.2
    rw [h0, Multiset.prod_zero] at hp
    rw [← hp, natDegree_one] at hn
    exact absurd hn (lt_irrefl 0)
  obtain ⟨g', hg'mem⟩ := Multiset.exists_mem_of_ne_zero hFne
  have hg'monic : g'.Monic := (hspec.1 g' hg'mem).1
  have hg'irr : Irreducible g' := (hspec.1 g' hg'mem).2
  obtain ⟨h, hhmonic, heq⟩ : ∃ h : Polynomial O, h.Monic ∧ g = g' * h := by
    refine ⟨((monicFactors g).erase g').prod, ?_, ?_⟩
    · have hid := monic_multiset_prod_of_monic ((monicFactors g).erase g') id
        (fun a ha => (hspec.1 a (Multiset.mem_of_mem_erase ha)).1)
      simpa using hid
    · rw [← Multiset.prod_cons, Multiset.cons_erase hg'mem]
      exact hspec.2.symm
  -- Step 2: B.57 — both factors are pure, their residual degrees add up, and `ḡ'` is a power
  -- of `φ̄`, which pins `deg g'`.
  obtain ⟨hne₁, hne₂, hp₁, -, hadd, hres₁⟩ :=
    isPure_of_monic_factor hπ hφ hu hℓ hcop hg hg'monic hhmonic hgd heq hpure hne
  have hg'deg : g'.natDegree = (ℓ * sideDeg φ g' u ℓ hne₁) * φ.natDegree :=
    natDegree_of_map_residue_eq_pow hφ.monic hg'monic hres₁
  have hg'pos : 0 < g'.natDegree := by
    rcases Nat.eq_zero_or_pos g'.natDegree with h0 | hp
    · refine absurd (isUnit_of_natDegree_zero h0 ?_) hg'irr.not_isUnit
      rw [hg'monic.leadingCoeff]; exact isUnit_one
    · exact hp
  have hd'pos : 0 < sideDeg φ g' u ℓ hne₁ := by
    rcases Nat.eq_zero_or_pos (sideDeg φ g' u ℓ hne₁) with h0 | hp
    · rw [h0] at hg'deg; simp at hg'deg; omega
    · exact hp
  -- Step 3: the squeeze — `hBOX` below, B.54 above.
  have hup : inertiaDegOf g' ∣ φ.natDegree * sideDeg φ g' u ℓ hne₁ :=
    inertiaDegOf_dvd_key_mul_resDeg hπ hφ hu hℓ hcop hg'monic hg'pos hp₁ hne₁ hd'pos hres₁
  have hlow : φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g' := hBOX g' hg'mem
  have hchain : φ.natDegree * sideDeg φ g u ℓ hne
      ∣ φ.natDegree * sideDeg φ g' u ℓ hne₁ := hlow.trans hup
  have hd'eq : sideDeg φ g' u ℓ hne₁ = sideDeg φ g u ℓ hne := by
    have hdvd : sideDeg φ g u ℓ hne ∣ sideDeg φ g' u ℓ hne₁ :=
      (Nat.mul_dvd_mul_iff_left hm).mp hchain
    have hge : sideDeg φ g u ℓ hne ≤ sideDeg φ g' u ℓ hne₁ := Nat.le_of_dvd hd'pos hdvd
    omega
  -- the factor has the full degree, so the cofactor is `1` and `g` is irreducible
  have hg'eqdeg : g'.natDegree = g.natDegree := by rw [hg'deg, hd'eq, hdeg]
  have hh0 : h.natDegree = 0 := by
    have hmul : g.natDegree = g'.natDegree + h.natDegree := by
      rw [heq, Polynomial.natDegree_mul hg'monic.ne_zero hhmonic.ne_zero]
    rw [hg'eqdeg] at hmul
    omega
  have hgg' : g = g' := by
    rw [heq, hhmonic.natDegree_eq_zero.mp hh0, mul_one]
  have hgirr : Irreducible g := by rw [hgg']; exact hg'irr
  have hFsingle : monicFactors g = {g} :=
    monicFactors_eq ⟨by
      intro a ha
      rw [Multiset.mem_singleton.1 ha]
      exact ⟨hg, hgirr⟩, by simp⟩
  -- Step 4: the `(e,f)` pair of the single factor.
  have hupg : inertiaDegOf g ∣ φ.natDegree * sideDeg φ g u ℓ hne :=
    inertiaDegOf_dvd_key_mul_resDeg hπ hφ hu hℓ hcop hg hn hpure hne hd hres
  have hlowg : φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g :=
    hBOX g (by rw [hFsingle]; exact Multiset.mem_singleton_self g)
  have hfg : inertiaDegOf g = φ.natDegree * sideDeg φ g u ℓ hne := Nat.dvd_antisymm hupg hlowg
  have heg : ramIndexOf g = ℓ := by
    have hef := ramIndexOf_mul_inertiaDegOf hg hn
    rw [hfg, hdeg] at hef
    have h2 : ramIndexOf g * (φ.natDegree * sideDeg φ g u ℓ hne)
        = ℓ * (φ.natDegree * sideDeg φ g u ℓ hne) := by rw [hef]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hm hd) h2
  -- Step 5: read the type off the singleton.
  ext
  rw [typeOf_data, hFsingle]
  simp [efPair, heg, hfg]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.typeOf_leaf_of_resDeg_lower_bound
end AxCheck
