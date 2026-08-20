/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B41a

/-!
# Uniformity.ChapB.B43 — uniqueness of the graded factorization

**Chapter B, NODE B.43** `graded_factorization_unique` (`blueprint/CHAP-B_leaf_layer.md` §6),
ENV-C, **[repaired: A-F.6]**.

*Under B.41's hypotheses, a monic `(u,ℓ)`-pure factorization with prescribed coprime residual
polynomials is unique.*  If `f = g*h = g'*h'` with all four factors monic of `φ.natDegree`-
divisible degree, `g'`, `h'` `(u,ℓ)`-pure, `(g,h)` graded-coprime, and `g`, `g'` (resp. `h`, `h'`)
carrying the same residual polynomial, then `g = g'` and `h = h'`.

The statement transcribed here is BYTE-FROZEN from `leanspec/Leanspec/ChapB.lean:877-889`
(`axiom graded_factorization_unique`), re-namespaced only.

## The route actually taken, and why it is not the blueprint's

The blueprint PROOF field says "mirror the landed `Hensel.monic_factorization_unique`" and its
A-F.6 route note flags a gap: step 2 consumes B.35's product law, which requires **both** factors
`(u,ℓ)`-pure, while the differences `g' − g` and `h − h'` are not pure — so the step needs a
*pure × arbitrary* half-law that B.35 does not provide, and the note authorises a `BLOCKED`
return.

**The gap is closed by an asset the note does not cite: `Uniformity/ChapB/B39a.lean` lands the
product law with no purity at all** (`suppVal_mul_gen`, `npHgt_mul_gen`, `sideMin_mul_gen`,
`sideDeg_mul_gen`, `resPoly_mul_gen` — hypotheses: only finiteness of the two support values and
nonemptiness of the two sides).  That is strictly stronger than the half-law B.43 needs, so no
new product law is written here.  The landed template's own route (`IsCoprime g h'` in `O[X]` via
`isCoprime_of_map_eq`) is **not** available in the graded setting and is not used: `g` and `h'`
both reduce to powers of `φ̄` mod `𝔪`, so they are never coprime in `O[X]`.  What is mirrored is
only the shape — difference, degree drop, divisibility, contradiction — with `O[X]`-divisibility
replaced by divisibility in `(resField φ)[Y]`.

Route, in five steps:

1. **The height pin is forced** (`height_le_of_resPoly_eq`).  `hgg'` is quantified over *all*
   `H₀`, and B.30 says the residual polynomial's `0`-th coefficient is nonzero at the side's true
   left height while `resMk` vanishes below the Gauss valuation (`resMk_eq_zero_of_lt`).  Reading
   `hgg'` at `H₀ := H_g` and again at `H₀ := H_{g'}` therefore gives `H_{g'} ≤ H_g` and
   `H_g ≤ H_{g'}`: the two heights agree.  Same for `h`, `h'`.
2. **Hence the degrees agree.**  With the heights pinned, `natDegree_resPoly` (B.30) turns
   `hgg'` into `sideDeg g = sideDeg g'`, and purity + `φ.natDegree ∣ ·` turn that back into
   `g.natDegree = g'.natDegree` (`sideDeg_of_pure`: `ℓ · sideDeg = natDegree / φ.natDegree`).
   This is exactly the derivation the A-F.6 note promised from the four divisibilities.
3. **The difference identity.**  `g * (h − h') = (g' − g) * h'`, and `δ := g' − g` has
   `natDegree < g.natDegree` (`degree_sub_lt_of_monic_of_natDegree_eq`).
4. **Read residuals through B39a.**  Both sides of step 3 are the *same* polynomial, so its side's
   left endpoint and height are computed twice, once per factorisation; `npHgt_mul_gen` forces
   `H_g + H_ε = H_δ + H_{h'}`, and `resPoly_mul_gen` then gives `G · E = D · H` in
   `(resField φ)[Y]`.
5. **Coprimality kills it.**  `IsCoprime G H` gives `G ∣ D`; but `D ≠ 0` (B.30, since `δ ≠ 0`) and
   `natDegree D = sideDeg δ < sideDeg g = natDegree G` (the degree drop of step 3, through
   `sideMax * φ.natDegree ≤ natDegree`).  Contradiction.  So `δ = 0`, and `h = h'` by cancelling
   the monic `g` in the domain `O[X]`.

**GC-1 (`sideMin` pin) is respected throughout**: every height here is read at
`npHgt φ f (sideMin φ f u ℓ hne)`, never at abscissa `0`, and the two agree for the *pure*
inputs by `sideMin_of_pure` — which is how the signature's `npHgt φ g 0 = Hg` (inside
B.37's `GradedCoprime`) is brought into the `sideMin` convention.  The differences `δ`, `ε` are
NOT pure, and for them only the `sideMin` reading is used.

**ENVIRONMENT.** The node is signed ENV-C, but the landed proof uses **neither**
`[IsAdicComplete (maximalIdeal O) O]` **nor** `[Finite (ResidueField O)]`: uniqueness is not a
limit statement (existence, B.41, is) and no counting happens.  The declaration therefore carries
the ENV-A instances only — which is *exactly* the `leanspec` axiom's type, since an `axiom` drops
section instances its statement does not mention (the B41b/B40 precedent, read in the other
direction).

DEPENDS: B.30 (`resCoeff_eq_zero_iff`, `natDegree_resPoly`) · B.33 · B.35b/c (the purity
dictionary: `suppVal_of_pure`, `sideMin_of_pure`, `sideDeg_of_pure`) · B.37 (`GradedCoprime`) ·
B39a (**the general product law**) · B39b (`sideSet_nonempty_gen`) · B41a
(`eq_zero_of_suppVal_eq_top`) · landed `Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq`
(`HenselFactorization.lean:381`).

## The frozen statement (verbatim, `leanspec/Leanspec/ChapB.lean:877-889`)

```lean
axiom graded_factorization_unique (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h g' h' : Polynomial O}
    (hg : g.Monic) (hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (hhd : φ.natDegree ∣ h.natDegree)
    (hgd' : φ.natDegree ∣ g'.natDegree) (hhd' : φ.natDegree ∣ h'.natDegree)
    (hgp' : IsPure φ g' u ℓ) (hhp' : IsPure φ h' u ℓ)
    (hcopGH : GradedCoprime π φ u ℓ g h)
    (hgg' : ∀ hne hne' H₀, resPoly π φ g u ℓ hne H₀ = resPoly π φ g' u ℓ hne' H₀)
    (hhh' : ∀ hne hne' H₀, resPoly π φ h u ℓ hne H₀ = resPoly π φ h' u ℓ hne' H₀)
    (heq : g * h = g' * h') : g = g' ∧ h = h'
```

## Binder-vacuity audit (MANDATORY, per `blueprint/CHAP-C_tower_grammar.md` §A-C.8.4)

**VERDICT: no vacuous binder.**  The hypothesis set is satisfiable *with the coprimality guard
live and the residual polynomials distinct* (so it is not satisfied only degenerately), two guards
are SHARP at explicit counterexamples constructed below, and two are recorded as *not consumed by
the landed route* (fidelity restorations from A-F.6, kept byte-frozen).

**The non-vacuity witness (all hypotheses TRUE, conclusion true and nontrivially so).**
`O = ℤ_p` (`p ≥ 3`), `π = p`, `φ = X` (so `m = φ.natDegree = 1`, `resField X ≅ 𝔽_p`),
`u = ℓ = 1`; `g = X + p`, `h = X + 2p`, `g' = g`, `h' = h`.  Each of `g, h` is `(1,1)`-pure
(polygon points `(0,1), (1,0)`, `suppVal = 1`, both on side); `resPoly g = Y + 1`,
`resPoly h = Y + 2`, which are coprime in `𝔽_p[Y]` for `p ≥ 3` — so `GradedCoprime` is genuinely
satisfied, not vacuously.

| binder | verdict | witness / counterexample |
| --- | --- | --- |
| `hπ : Irreducible π` | non-vacuous, load-bearing | `π = p` in `ℤ_p`. Consumed by every digit lemma (`digAt`, `resMk`); without it `resMk` is not a valuation-theoretic object at all. |
| `hφ : IsKey φ` | non-vacuous, load-bearing | `φ = X` over `ℤ_p`. `resField φ = 𝔽_p[y]/(φ̄)` is a FIELD only under `hφ.irred`, and step 5 divides in `(resField φ)[Y]`. |
| `hu : 0 < u` | load-bearing for the route; **sharpness NOT established** for the conclusion | Consumed by every B39a product-law lemma. Its upstream sharpness IS on record one level down: `resMk_dev_mul`'s docstring (`B35b.lean`) states the master identity is **false at `u = 0`** (amendment A-F.6). I did not construct a `u = 0` counterexample to B.43's own conclusion and do not claim one: at `u = 0` the graded read degenerates towards the mod-`𝔪` factorization, whose uniqueness is the landed Hensel theorem (true). Honest classification: required, not known-sharp. |
| `hℓ : 0 < ℓ` | load-bearing for the route; **sharpness NOT established** | Required by every consumed lemma (`sideMax_eq`, `natDegree_resPoly`, the product law). At `ℓ = 0` the lattice index `ℓ·k` collapses so all residual coefficients read the *same* development coefficient at descending heights, and the residual polynomial stops being a factorization invariant; no counterexample constructed. |
| `hcop : Nat.Coprime u ℓ` | load-bearing | Consumed by `sideMax_eq`, `onSide_eq_add_mul` and all of B39a (`onSide_mul_decomp` needs it to force lattice positions). |
| `hg hh hg' hh'` monic | non-vacuous, load-bearing | Used for the degree drop (`degree_sub_lt_of_monic_of_natDegree_eq` needs both monic and equal `natDegree`) and for the final cancellation. |
| `hgd : φ.natDegree ∣ g.natDegree` | load-bearing | Turns `sideDeg` back into `natDegree` (`sideDeg_of_pure` is stated for `f.natDegree = n * φ.natDegree`); this is the divisibility the A-F.6 re-sign added precisely so that step 2 can run. |
| `hgd' : φ.natDegree ∣ g'.natDegree` | load-bearing | Same, for `g'`; this is what makes `g.natDegree = g'.natDegree` derivable rather than assumed. |
| `hhd`, `hhd'` | satisfiable, **NOT consumed** by the landed route | Fidelity restorations (A-F.6). The route needs the degree bookkeeping only on the `g`-side: the `h`-side is reached by cancellation. Kept byte-frozen; `linter.unusedVariables` is silenced, exactly as the landed template `monic_factorization_unique` does for its own symmetric pair `hh`, `hhr`. |
| `hgp' : IsPure φ g' u ℓ` | load-bearing | Step 2 needs `sideDeg_of_pure` at `g'` to convert `sideDeg g' = sideDeg g` into `g'.natDegree = g.natDegree`. |
| `hhp' : IsPure φ h' u ℓ` | satisfiable, **NOT consumed** | The `h'` side enters only through the general (purity-free) product law and the height pin. Fidelity restoration (A-F.6), kept byte-frozen. |
| `hcopGH : GradedCoprime π φ u ℓ g h` | **SHARP — load-bearing** | Counterexample on dropping it: `O = ℤ_p`, `π = p`, `φ = X`, `u = ℓ = 1`, `g = X + p`, `h = X + p + p²`, `g' = h`, `h' = g` (the swap). Both are `(1,1)`-pure with `resPoly = Y + 1`, so `IsCoprime (Y+1) (Y+1)` FAILS — and every other hypothesis holds, including `hgg'`/`hhh'` at **every** `H₀`: the two constant terms `p` and `p + p²` have `digAt π 0 = 0`, `digAt π 1 = 1` (residues of `1` and `1 + p`), and `digAt π k = 0` for `k ≥ 2` (`p^k ∤ p` and `p^k ∤ p + p²`), while the linear coefficients are both `1`. Yet `g ≠ g'`. So the conclusion FAILS without `hcopGH`. |
| `hgg'` (residual pin on `g`) | **redundant given `hhh'`**; the PAIR is SHARP | `hgg'` and `hhh'` are mutually derivable given the rest: the product law turns `heq` into `G·H = G'·H'` in the domain `(resField φ)[Y]`, so `H = H'` cancels to `G = G'` and conversely. Hence each alone restricts nothing beyond the other — but dropping **both** is refuted: `O = ℤ_p` (`p ≥ 3`), `g = X + p`, `h = X + 2p`, `g' = h`, `h' = g`. Here `GradedCoprime` HOLDS (`Y+1`, `Y+2` coprime), every other hypothesis holds, and `g ≠ g'`. Both are consumed by the landed route (it does not perform the cancellation). |
| `hhh'` (residual pin on `h`) | as above | as above. |
| `heq : g * h = g' * h'` | load-bearing, trivially sharp | Without a relation between the two pairs nothing links them: `g = X + p`, `h = X + 2p`, `g' = X + 2p`, `h' = X + p` violates only `heq`… in fact it satisfies `heq`; take instead `g' = X + 3p`, `h' = X + 4p` (`p ≥ 5`), which satisfies every other hypothesis pattern with its own residual pins and fails only `heq` and the pins. |

Refutation attempts run against my own guards: `hcopGH` — attacked, attack SUCCEEDED (the swap
above), so it is sharp; `hgg'`/`hhh'` as a pair — attacked, attack SUCCEEDED, so the pair is
sharp, but the attempt also revealed the pair is internally redundant; `hhd`, `hhd'`, `hhp'` —
attacked in the weaker sense of asking whether the *proof* needs them, and it does not, so they
are recorded as restricting the instance set without carrying the conclusion; `hu`, `hℓ` — attacked
and NOT refuted, recorded honestly as required-but-not-known-sharp rather than promoted to sharp.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1) plus `hπ : Irreducible π` per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. Two general finiteness/height conveniences

`sideSet_nonempty` (B.18) and `suppVal_ne_top` (B.18) are both stated for MONIC `f` of
`φ.natDegree`-divisible degree.  The differences `g' − g` and `h − h'` are neither, so the two
facts are re-derived here in the form the route needs.  (`sideSet_nonempty_gen`, the unconditional
nonemptiness, is already landed in `B39b`.) -/

section Finiteness

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- **A nonzero polynomial has finite support value.**  Contrapositive of B41a's
`eq_zero_of_suppVal_eq_top`; no monicity, no degree condition. -/
theorem suppVal_ne_top_of_ne_zero (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f : Polynomial O}
    (hf : f ≠ 0) : suppVal φ f u ℓ ≠ ⊤ :=
  fun h => hf (eq_zero_of_suppVal_eq_top hφ hd h)

/-- **The height at a side's left endpoint is a natural number.** -/
theorem exists_sideMin_height (hℓ : 0 < ℓ) {f : Polynomial O} (htf : suppVal φ f u ℓ ≠ ⊤)
    (hnf : (sideSet φ f u ℓ).Nonempty) :
    ∃ H : ℕ, npHgt φ f (sideMin φ f u ℓ hnf) = (H : ℕ∞) := by
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1
    (npHgt_ne_top_of_onSide hℓ htf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf)))
  exact ⟨H, hH.symm⟩

/-- **The side lies inside the `φ`-adic abscissa range.**  Every on-side abscissa carries a
nonzero development coefficient, and `dev φ f j = 0` as soon as `f.natDegree < j * φ.natDegree`
(B.04) — so in particular the right endpoint satisfies `sideMax * φ.natDegree ≤ f.natDegree`.
This is the general form of the bound `sideMax_of_pure` proves under purity. -/
theorem mul_sideMax_le_natDegree (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {f : Polynomial O} (htf : suppVal φ f u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty) :
    sideMax φ f u ℓ hnf * φ.natDegree ≤ f.natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  have hT : npHgt φ f (sideMax φ f u ℓ hnf) ≠ ⊤ :=
    npHgt_ne_top_of_onSide hℓ htf (onSide_of_mem_sideSet (Finset.max'_mem _ hnf))
  exact hT (npHgt_eq_top_iff.2 (dev_eq_zero_of_lt hφ hd f _ hcon))

end Finiteness

/-! ## 2. The general product law, transported to a named product

B39a states the product law about the literal term `f * z`.  The route applies it twice to the
SAME polynomial under two different factorisations, so each clause is restated with the product
named by a variable `P` and an equation `hP : P = f * z`; `subst` then discharges it.  This avoids
rewriting under the dependent nonemptiness proof (`hnP`'s type mentions `P`). -/

section Transport

variable {φ : Polynomial O} {u ℓ : ℕ} {f z P : Polynomial O}

/-- `npHgt_mul_gen`, with the product named. -/
theorem npHgt_mul_gen' (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hP : P = f * z) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞)) :
    npHgt φ P (sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz) = ((Hf + Hz : ℕ) : ℕ∞) := by
  subst hP
  exact npHgt_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz

/-- `sideMin_mul_gen`, with the product named. -/
theorem sideMin_mul_gen' (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hP : P = f * z) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnP : (sideSet φ P u ℓ).Nonempty) :
    sideMin φ P u ℓ hnP = sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz := by
  subst hP
  exact sideMin_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnP

/-- `sideDeg_mul_gen`, with the product named. -/
theorem sideDeg_mul_gen' (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hP : P = f * z) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnP : (sideSet φ P u ℓ).Nonempty) :
    sideDeg φ P u ℓ hnP = sideDeg φ f u ℓ hnf + sideDeg φ z u ℓ hnz := by
  subst hP
  exact sideDeg_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnP

/-- `resPoly_mul_gen`, with the product named. -/
theorem resPoly_mul_gen' (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hP : P = f * z) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnP : (sideSet φ P u ℓ).Nonempty) :
    resPoly π φ P u ℓ hnP (Hf + Hz)
      = resPoly π φ f u ℓ hnf Hf * resPoly π φ z u ℓ hnz Hz := by
  subst hP
  exact resPoly_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnP

end Transport

/-! ## 3. The height pin

`hgg'` is quantified over **all** `H₀`, and that is exactly the strength needed to pin `g`'s and
`g'`'s side heights to each other.  Read at `H₀ := H` (the true left height of `f`), B.30's
"the `0`-th residual coefficient does not vanish" collides with "`resMk` vanishes strictly below
the Gauss valuation" (`resMk_eq_zero_of_lt`) unless `H' ≤ H`.  Applying the lemma twice, once in
each direction, gives `H = H'`.

Only the coefficient at `k = 0` is used, which is what makes this work: at `k = sideDeg` the
junk-digit above the line need not vanish, so a coefficientwise argument would fail there. -/

section HeightPin

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- **The height pin, one direction.**  If `f`'s residual polynomial read at `f`'s own left height
`H` equals `f'`'s residual polynomial read at the *same* `H`, then `f'`'s left height is at most
`H`. -/
theorem height_le_of_resPoly_eq (hπ : Irreducible π) (hφ : IsKey φ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {f f' : Polynomial O} (htf : suppVal φ f u ℓ ≠ ⊤)
    (hnf : (sideSet φ f u ℓ).Nonempty) (hnf' : (sideSet φ f' u ℓ).Nonempty) {H H' : ℕ}
    (hH : npHgt φ f (sideMin φ f u ℓ hnf) = (H : ℕ∞))
    (hH' : npHgt φ f' (sideMin φ f' u ℓ hnf') = (H' : ℕ∞))
    (heq : resPoly π φ f u ℓ hnf H = resPoly π φ f' u ℓ hnf' H) :
    H' ≤ H := by
  by_contra hcon
  rw [not_le] at hcon
  have h0 : resCoeff π φ f' u ℓ hnf' H 0 ≠ 0 := by
    have hne := (natDegree_resPoly hπ hφ hℓ hcop htf hnf hH).2
    rw [heq, resPoly_coeff] at hne
    simpa using hne
  refine h0 ?_
  simp only [resCoeff, Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  refine resMk_eq_zero_of_lt hπ ?_
  show ((H + 1 : ℕ) : ℕ∞) ≤ npHgt φ f' (sideMin φ f' u ℓ hnf')
  rw [hH']
  exact_mod_cast Nat.succ_le_of_lt hcon

/-- **The height pin.**  Both directions of `height_le_of_resPoly_eq`. -/
theorem height_eq_of_resPoly_eq (hπ : Irreducible π) (hφ : IsKey φ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {f f' : Polynomial O} (htf : suppVal φ f u ℓ ≠ ⊤)
    (htf' : suppVal φ f' u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnf' : (sideSet φ f' u ℓ).Nonempty) {H H' : ℕ}
    (hH : npHgt φ f (sideMin φ f u ℓ hnf) = (H : ℕ∞))
    (hH' : npHgt φ f' (sideMin φ f' u ℓ hnf') = (H' : ℕ∞))
    (hall : ∀ H₀ : ℕ, resPoly π φ f u ℓ hnf H₀ = resPoly π φ f' u ℓ hnf' H₀) :
    H = H' :=
  le_antisymm
    (height_le_of_resPoly_eq hπ hφ hℓ hcop htf' hnf' hnf hH' hH (hall H').symm)
    (height_le_of_resPoly_eq hπ hφ hℓ hcop htf hnf hnf' hH hH' (hall H))

/-- **A lower-degree polynomial has a strictly shorter side.**  For `g` monic `(u,ℓ)`-pure of
degree `a·φ.natDegree` the side has length `ℓ·sideDeg g = a`; a nonzero `δ` of smaller degree has
`ℓ·sideDeg δ · φ.natDegree ≤ sideMax δ · φ.natDegree ≤ δ.natDegree < a·φ.natDegree`. -/
theorem sideDeg_lt_of_natDegree_lt (hφ : IsKey φ) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {δ g : Polynomial O} (hδ : δ ≠ 0) (hg : g.Monic) {a : ℕ}
    (hga : g.natDegree = a * φ.natDegree) (hgp : IsPure φ g u ℓ)
    (hgne : (sideSet φ g u ℓ).Nonempty) (hδne : (sideSet φ δ u ℓ).Nonempty)
    (hlt : δ.natDegree < g.natDegree) :
    sideDeg φ δ u ℓ hδne < sideDeg φ g u ℓ hgne := by
  have htδ : suppVal φ δ u ℓ ≠ ⊤ := suppVal_ne_top_of_ne_zero hφ.monic hφ.pos hδ
  have hmax : sideMax φ δ u ℓ hδne = sideMin φ δ u ℓ hδne + ℓ * sideDeg φ δ u ℓ hδne :=
    sideMax_eq hℓ hcop htδ hδne
  have hb : sideMax φ δ u ℓ hδne * φ.natDegree ≤ δ.natDegree :=
    mul_sideMax_le_natDegree hφ.monic hφ.pos hℓ htδ hδne
  have ha : ℓ * sideDeg φ g u ℓ hgne = a :=
    sideDeg_of_pure hφ.monic hφ.pos hg hga hℓ hcop hgp hgne
  have hle : ℓ * sideDeg φ δ u ℓ hδne ≤ sideMax φ δ u ℓ hδne := by omega
  have h1 : ℓ * sideDeg φ δ u ℓ hδne * φ.natDegree ≤ δ.natDegree :=
    le_trans (Nat.mul_le_mul hle (le_refl _)) hb
  have h2 : ℓ * sideDeg φ δ u ℓ hδne * φ.natDegree < ℓ * sideDeg φ g u ℓ hgne * φ.natDegree := by
    rw [ha]
    exact lt_of_le_of_lt h1 (by rw [← hga]; exact hlt)
  exact lt_of_mul_lt_mul_left (lt_of_mul_lt_mul_right h2 (Nat.zero_le _)) (Nat.zero_le _)

end HeightPin

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_ne_top_of_ne_zero
#print axioms Uniformity.Density.Leaf.exists_sideMin_height
#print axioms Uniformity.Density.Leaf.mul_sideMax_le_natDegree
#print axioms Uniformity.Density.Leaf.npHgt_mul_gen'
#print axioms Uniformity.Density.Leaf.sideMin_mul_gen'
#print axioms Uniformity.Density.Leaf.sideDeg_mul_gen'
#print axioms Uniformity.Density.Leaf.resPoly_mul_gen'
#print axioms Uniformity.Density.Leaf.height_le_of_resPoly_eq
#print axioms Uniformity.Density.Leaf.height_eq_of_resPoly_eq
#print axioms Uniformity.Density.Leaf.sideDeg_lt_of_natDegree_lt
end AxCheck
