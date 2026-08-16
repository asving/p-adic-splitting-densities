/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E18

/-!
# Uniformity.ChapE.E37 — the standing-convention peel: `Ψ ∤ f_S` is no restriction

**Chapter E, NODE E.37** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §5), ENV-E2 +
`[IsDomain O]`. One signed theorem, `peel_once`, PROVED — no `sorry`, Lean-core axioms only.

## What the node says

The σ-ladder's standing convention is that the key does not divide the polynomial being read
(`Ψ ∤ f_S`). `EFF.HE7.09` records that this is a CONVENTION rather than a restriction, because
every input is decided either directly or after **one** peel: if `Ψ ∣ F` then `F = Ψ · F′` with
`F′` monic of degree `deg F − D`, and — this is the content — `Ψ ∤ F′`. Squarefreeness of `F`
over the fraction field is exactly what forbids the second peel: a second one would give
`Ψ² ∣ F`.

That is the whole node, and it is deliberately narrow. Three things in the blueprint STATEMENT
are **not** signed conjuncts here, per the A-E.3 disposition quoted below:

* clause (ii), `F′` and `Ψ` coprime — that is E.18's `midPeel` / E.36's `coprime_of_not_dvd`;
* clause (iii), the `Ψ ∤ F` branch — that is E.36's chain applied directly, nothing to prove;
* the LETTER claims about `Ψ` (irreducibility, and `(e,f) = (e₁ℓ, f₁d_r)` on the peel stratum).
  Those are LEMMA HE6R1-3's, a CONCLUSION there and never an assumption here; their supplier is
  the chapter-C placeholder `EFF.HE6R1 [supplied-by: chapter C]`. Nothing in this file asserts
  them, and nothing in this file could: `Ψ` is an arbitrary monic of degree `D`.

## ⚠ A-E.3 DISPOSITION — the SIGNATURE IS UNCHANGED, and no normality is threaded

Amendment A-E.3 (2026-08-16) re-signed E.36's `coprime_of_not_dvd` with `[IsIntegrallyClosed O]`
after machine-refuting the bare-domain form (the refutation lives in
`leanfinal/Uniformity/ChapE/E36.lean`, namespace `E36Refutation`). **This node needs no re-sign
and no instance threading**, and the file bears that out: the proof below uses only

1. monic factoring plus the degree drop (pure degree arithmetic over a domain), and
2. `Squarefree (F.map …)` against `(Ψ.map …)^2 ∣ F.map …`,

with **no descent from `Frac(O)[X]` back to `O[X]` anywhere** — the descent step is precisely
what forces integral closedness at E.36. Both `[IsDomain O]` and the monicity hypotheses stay
exactly as committed. A consumer who wants clause (ii) as a *term* calls `coprime_of_not_dvd`
itself and inherits its `[IsIntegrallyClosed O]`, free in the DVR arena (ENV-E2's
`[IsDiscreteValuationRing O]`) where every such consumer lives.

## Why `hD : 0 < D` is load-bearing here (unlike at E.18)

`hD` is what makes `Ψ.map (algebraMap O (FractionRing O))` a **nonunit**: `Ψ` monic gives
`(Ψ.map …).natDegree = Ψ.natDegree = D`, and a unit of `Frac(O)[X]` has `natDegree = 0`. At
`D = 0` the key is `1`, `Ψ ∣ F′` always, and the "at most once" clause is simply false — so the
hypothesis is consumed, not decorative. (Contrast E.18, where the signed `hD` is carried but
unconsumed; that file says so in its own comment.)

DEPENDS: **E.18** (`leanfinal/Uniformity/ChapE/E18.lean` — the peel identity layer; imported for
its `Polynomial`/`Squarefree`/`FractionRing` environment, and its `midPeel` proof steps 1–3 are
the model for the factoring half here) · **E.36** conceptually (the chain this convention feeds,
and the A-E.3 disposition above; **nothing is imported from it**, because no term of E.36 is
consumed) · mathlib `Squarefree`, `Polynomial.Monic.of_mul_monic_left`,
`Polynomial.Monic.natDegree_mul`, `Polynomial.Monic.natDegree_map`,
`Polynomial.natDegree_eq_zero_of_isUnit`, `Polynomial.map_mul`.

SOURCE: `EFF.HE7.09` (the CONVENTION, verbatim, including *"the peel happens at most once"* and
the necessity derivation — without it *"P₂ loses its j = 0 pin and THEOREM HE7.A(1)'s
`Σ L_{λ₂} = μ₂` is false"*); `EFF.HE7.60` (the n = 8 peel row: `μ₂′ = 1` after one peel, 8/8
machine members, `A₁^{(2)} ≠ 0`, *"one peel only"*); `EFF.HE7.62` (HE7.A′: *"on the peel stratum
irreducibility of `Ψ` is a CONCLUSION, not an assumption"*); blueprint amendment **A-E.3**
(the disposition recorded above).

TEETH: the sealed `DEGENERATE-key-divides` stratum (8 of 1,587 members, found BY the machine) and
`he7r1_supp.py` A1–A5 (8/8 peels exact, 2/2 PARI on both σ halves) → the identity layer is a
**Lean theorem**, landed here. The letter claim (`σ(Ψ) = {(4,1)}`) is NOT landed here: it rides
E.51's dictionary row with the HE6R1-3 placeholder.

ENVIRONMENT: ENV-E2 (+ `[IsDomain O]`).

## Status

Sorry-free, axiom-free: `peel_once` reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Transcribed declaration-for-declaration against the
signed SIGNATURE (`leanspec/Leanspec/ChapE.lean` §5, `peel_once`): binder list, implicit/explicit
status, hypothesis names and the four-conjunct conclusion unchanged.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- **E.37 — the standing-convention peel** (`EFF.HE7.09`). If the monic degree-`D` key `Ψ`
(`D > 0`) divides the monic `F`, and `F` is squarefree over the fraction field, then `F = Ψ · F′`
with `F′` monic of degree `deg F − D` and **`Ψ ∤ F′`**: the peel fires at most once. Hence the
convention `Ψ ∤ f_S` restricts nothing — every input is decided either directly or after ONE
peel. -/
theorem peel_once {O : Type*} [CommRing O] [IsDomain O]
    {F Ψ : Polynomial O} (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D)
    (hΨd : Ψ.natDegree = D)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O))))
    (hdvd : Ψ ∣ F) :
    ∃ F' : Polynomial O, F = Ψ * F' ∧ F'.Monic ∧
      F'.natDegree = F.natDegree - D ∧ ¬ Ψ ∣ F' := by
  -- step 1 (E.18's steps 1–3): factor, and the quotient of monics is monic
  obtain ⟨F', rfl⟩ := hdvd
  have hF'monic : F'.Monic := hΨ.of_mul_monic_left hF
  refine ⟨F', rfl, hF'monic, ?_, ?_⟩
  · -- the degree drop: `deg (Ψ * F′) = D + deg F′`, so the ℕ-subtraction is exact
    rw [hΨ.natDegree_mul hF'monic, hΨd]
    omega
  · -- step 2, "at most once": a second peel would put `Ψ²` inside a squarefree image
    rintro ⟨F'', rfl⟩
    have hsq' := hsq (Ψ.map (algebraMap O (FractionRing O))) ?_
    · -- `Ψ.map` is monic of degree `D > 0`, hence not a unit of `Frac(O)[X]`
      have hdegmap : (Ψ.map (algebraMap O (FractionRing O))).natDegree = D := by
        rw [hΨ.natDegree_map, hΨd]
      have := Polynomial.natDegree_eq_zero_of_isUnit hsq'
      omega
    · rw [Polynomial.map_mul, Polynomial.map_mul]
      exact ⟨F''.map (algebraMap O (FractionRing O)), by ring⟩

/-! ## Gates (executed `example`s, not blueprint declarations)

Three things a reader has to take on trust from the statement alone, machine-checked instead.

**(a) The `ℕ`-subtraction in the degree clause is EXACT.** `F'.natDegree = F.natDegree - D` is
truncated subtraction, which is silently true (`0 = 0`) whenever `D` exceeds `deg F`. The gate
recovers the additive form `deg F′ + D = deg F` from the signed conclusion, so a consumer reading
the mass drop off this node gets the real one. This is the `EFF.HE7.09` mass bookkeeping
`μ₂ − 1`.

**(b) and (c) The squarefreeness hypothesis is LOAD-BEARING, exhibited on a witness.** Gate (b)
is an explicit failure of the "at most once" clause over `ℤ`: for `Ψ = X`, `F = X²` the only
factorization is `F′ = X`, and `Ψ ∣ F′`. Gate (c) then shows that this witness violates exactly
`hsq` and nothing else — `X²` is not squarefree over `Frac(ℤ)` — so the pair is a genuine
necessity demonstration for the hypothesis rather than a defect in the statement. Had `hsq` been
dropped (or weakened to squarefreeness of `Ψ`, say), gate (b) would refute the theorem. -/

section Gate

-- (a) the degree clause's `ℕ`-subtraction is exact: the additive mass drop is recoverable.
example {O : Type*} [CommRing O] [IsDomain O] {F Ψ : Polynomial O}
    (hF : F.Monic) (hΨ : Ψ.Monic) {D : ℕ} (hD : 0 < D) (hΨd : Ψ.natDegree = D)
    (hsq : Squarefree (F.map (algebraMap O (FractionRing O)))) (hdvd : Ψ ∣ F) :
    ∃ F' : Polynomial O, F = Ψ * F' ∧ F'.natDegree + D = F.natDegree := by
  obtain ⟨F', hFF', hmon, -, -⟩ := peel_once hF hΨ hD hΨd hsq hdvd
  refine ⟨F', hFF', ?_⟩
  rw [hFF', hΨ.natDegree_mul hmon, hΨd]
  omega

-- (b) without squarefreeness the "at most once" clause is FALSE: `Ψ = X`, `F = X²` over `ℤ`.
example : ¬ ∃ F' : Polynomial ℤ,
    (Polynomial.X ^ 2 : Polynomial ℤ) = Polynomial.X * F' ∧
      ¬ (Polynomial.X : Polynomial ℤ) ∣ F' := by
  rintro ⟨F', hF', hndvd⟩
  refine hndvd ⟨1, ?_⟩
  have hmul : (Polynomial.X : Polynomial ℤ) * Polynomial.X = Polynomial.X * F' := by
    rw [← hF']; ring
  have := mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℤ)) hmul
  rw [← this]; ring

-- (c) …and that witness fails exactly `hsq`: `X²` is not squarefree over `Frac(ℤ)`.
example :
    ¬ Squarefree ((Polynomial.X ^ 2 : Polynomial ℤ).map (algebraMap ℤ (FractionRing ℤ))) := by
  intro h
  have hu := h (Polynomial.X.map (algebraMap ℤ (FractionRing ℤ)))
    ⟨1, by rw [Polynomial.map_pow]; ring⟩
  have hd := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective ℤ (FractionRing ℤ))] at hd
  simp at hd

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.peel_once

end AxCheck
