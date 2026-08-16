/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02
import Uniformity.ChapC.C43

/-!
# Uniformity.ChapC.C71 — the two reads (`shadowDev`) and the faithfulness threshold (`Θ`)

**Chapter C, NODE C.71** [def] [fresh] [signed: A-C.1 — `shadowDev`'s REAL body determined]
(`blueprint/CHAP-C_tower_grammar.md` §8, the shadow-read layer; twin
`leanspec/Leanspec/ChapC.lean`, both halves: the `margin`/`theta` pair of the first signing pass
and the `devQ`/`biRead`/`shadowDev` block of the A-C.1 completion layer). **ENV-C1**.  Five
signed declarations, all definitional, plus two arithmetic companions.

Fix a frame `F` (C.01) pinned at `H₀` (C.14a's `F.Pin H₀`) and a tower datum `T` (C.42), and
write `Φ′ = F.key`, `D′ = e₁f₁`, `Φ₂ = composedKey T` (C.43).  For `f ∈ 𝒯` (C.51's
`towerLocus`) §8 runs two different `Φ₂`-adic reads of `f` side by side:

* the **composed (honest) read** — `dev (composedKey T) f j`, B.02's development at the key
  `Φ₂`, the object every earlier section of this chapter is written at;
* the **stage-shadow read** — `shadowDev T f j`, the same division tower carried out with every
  coefficient reduced mod `Φ′`.

They are *not* equal (that is the point of §8: the shadow is the refuted `T(b)` object, kept
because it is cheap).  What §8 proves is that they agree BELOW an explicit height, and C.71 is
the node that names the two reads and that height:

* `TowerDatum.margin T = u₂ − e₂·D′·h` — the **margin** `δ`, the slack in C.42's node floor
  `hfloor`; `1 ≤ δ` is the companion `TowerDatum.one_le_margin` below;
* `TowerDatum.theta T μ₂ j = (μ₂ − j)·E₂ + δ` — the **threshold** `Θ_j`, with `E₂ = e₂f₂u₂`
  (C.42).  C.72 is the statement that the two reads' `dv₂`-digits agree strictly below `Θ_j`
  and that the first disagreement sits at height `≥ Θ_j`; C.74's `TouchCert` is the statement
  that the bound is attained.  Neither is claimed here.

## `shadowDev`'s body: what "mod-`Φ′`-reduced division tower" was made to mean (A-C.1)

The corpus phrase is *"iterated `Polynomial.modByMonic` at `Φ′` inside the `Φ₂`-division"*.  A
literal alternating `%ₘ Φ′` inside B.02's recursion is not a well-defined object — the reduction
does not commute with the division step, so "reduce after every step" and "reduce at the end"
name different functions and the phrase does not say which.  The A-C.1 determination fixes it
the only way that is canonical, by doing the whole division in the reduced ring:

1. `biRead F g` transports `g ∈ O[x]` to `(O[x]/Φ′)[Z]` — the two-variable image, whose
   `Z^b`-coefficient is the class mod `Φ′` of `g`'s `b`-th `Φ′`-adic digit (B.02's `dev` at the
   key `Φ′`, C.01's `F.key`).  `AdjoinRoot F.key` IS `O[x]/Φ′` here; no field structure is used
   or available (`O[x]/Φ′` is not a domain in general, and none of this needs it to be).
2. `devQ Ψ` is B.02's `dev` recursion over an arbitrary `CommRing` — the same two lines, so that
   the division tower can be run at the transported key `biRead F Φ₂` inside `(O[x]/Φ′)[Z]`.
   (B.02's `dev` is stated over a DVR `O` and cannot be instantiated at `AdjoinRoot F.key`,
   which is why the generic copy exists; `devQ` and `dev` agree wherever both apply, and the
   `example` below pins the two defining equations.)
3. the result is mapped back to `O[x]` through `AdjoinRoot.modByMonicHom F.hmonic` — the
   CANONICAL representative of a class mod the monic `Φ′` (the remainder of degree `< D′`), so
   no `Classical.choice` and no section is involved — and reassembled against the powers of
   `Φ′`.

This is the honest reading of the phrase: the shadow read is the `Φ₂`-development computed
*after* forgetting everything above `Φ′`, then lifted back by the degree-`< D′` representative.

**⚠ Mandatory, trust-boundary definition.**  `shadowDev` is a new definition whose body was
DETERMINED (not transcribed) at A-C.1; the recast above is the substantive content and it is
what makes C.72/C.73/C.74 mean what §8 says they mean.  **Flagged for human review** (parent
CLAUDE.md trust boundary).  In particular:

* the reassembly ranges over `Finset.range (S.natDegree + 1)`, so it reads exactly the `Z`-degrees
  the transported development actually populates; `natDegree`'s junk value at `S = 0` is harmless
  (the single term is then `0`);
* `biRead`'s range is likewise `Finset.range (g.natDegree + 1)`, which covers every nonzero
  `Φ′`-digit of `g` since `dev F.key g b = 0` for `b > g.natDegree` (`Φ′` monic of degree
  `D′ ≥ 1`), and over-counts harmlessly otherwise;
* `shadowDev` takes NO irreducibility or `1 ≤ h` hypothesis: like `composedKey` it is a total
  `O[x]`-construction, and the corpus preconditions ride on C.72's statements, not on the term.

## Totality and junk

`devQ`, `biRead`, `shadowDev`, `margin` and `theta` are total.  `margin` is a `ℕ`-subtraction and
is therefore `0` at a datum violating the floor — but no `TowerDatum` does (`hfloor` is a field),
which is exactly what `one_le_margin` records.  `theta`'s `(μ₂ − j)` is `ℕ`-subtraction as well:
above the top index the threshold degenerates to the bare margin `δ`, checked below.

**DEPENDS.** B.02 (`dev`) · C.01 (`KeyFrame`) · C.14a (`KeyFrame.Pin`) · C.42 (`TowerDatum`,
`E₂`) · C.43 (`composedKey`) — imported.  By committed node ID: C.50 (`slotOffset`/`gridWeight`,
the `dv₂`-grid the threshold is measured on — C.72's carrier, not consumed here) · C.51
(`towerLocus`, the locus C.72 quantifies over).

**PROOF.** Definitional; `one_le_margin` is `T.hfloor` re-associated.

**SIZE.** 18 lines (blueprint estimate).

**SOURCE.** `EFF.GENTOW3.16` (the two reads, verbatim — the shadow is "the refuted `T(b)`
object", the docstring says so); `EFF.GENTOW3.18` (`δ := u₂ − e₂D′h`, `Θ_j`).

**TEETH.** Signed non-applicable at this node (C.72 carries the P-1 FLOOR / P-6 LABEL rows).
The `example`s below are local unfolding checks only.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  Definitional throughout.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.71 (i)** — the generic monic-division development: B.02's `dev` verbatim, but over
an arbitrary `CommRing R` rather than over the DVR `O`.  Needed because the shadow read runs its
`Φ₂`-division inside `(O[x]/Φ′)[Z] = (AdjoinRoot F.key)[Z]`, which is not a DVR (nor even a
domain).  `devQ Ψ g j` is the `j`-th coefficient of the `Ψ`-adic development of `g`. -/
noncomputable def devQ {R : Type*} [CommRing R] (Ψ : Polynomial R) :
    Polynomial R → ℕ → Polynomial R
  | g, 0 => g %ₘ Ψ
  | g, j + 1 => devQ Ψ (g /ₘ Ψ) j

/-- **NODE C.71 (ii)** — the mod-`Φ′`-reduced two-variable image `O[x] → (O[x]/Φ′)[Z]`: the
`Z^b`-coefficient of `biRead F g` is the class mod `Φ′ = F.key` of the `b`-th `Φ′`-adic digit of
`g` (B.02's `dev` at the key `F.key`).  The range `b ≤ g.natDegree` covers every nonzero digit
(`F.key` is monic of degree `e₁f₁ ≥ 1`). -/
noncomputable def biRead (F : KeyFrame O π) (g : Polynomial O) :
    Polynomial (AdjoinRoot F.key) :=
  (Finset.range (g.natDegree + 1)).sum fun b =>
    Polynomial.C (AdjoinRoot.mk F.key (dev F.key g b)) * Polynomial.X ^ b

/-- **NODE C.71 (iii) — the STAGE-SHADOW READ.**  `shadowDev T f j` is the `j`-th coefficient of
the `Φ₂`-adic development of `f` computed with every coefficient reduced mod `Φ′`: transport both
`f` and `Φ₂ = composedKey T` into `(O[x]/Φ′)[Z]` (`biRead`), run the division tower there
(`devQ`), and map back through the canonical degree-`< D′` representative
(`AdjoinRoot.modByMonicHom F.hmonic`, no choice) against the powers of `Φ′`.

This is NOT `dev (composedKey T) f j` — the composed (honest) read — and the two are not claimed
equal here.  C.72 bounds their disagreement below `T.theta`; C.73 gives the x-free genres at which
they do coincide identically.  See the module docstring for the A-C.1 determination of this body
and its trust-boundary flag. -/
noncomputable def shadowDev {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (f : Polynomial O) (j : ℕ) : Polynomial O :=
  let S := devQ (biRead F (composedKey T)) (biRead F f) j
  (Finset.range (S.natDegree + 1)).sum fun b =>
    (AdjoinRoot.modByMonicHom F.hmonic (S.coeff b)) * F.key ^ b

/-- **NODE C.71 (iv) — the MARGIN `δ`** (`EFF.GENTOW3.18`): `δ T = u₂ − e₂·D′·h` with
`D′ = e₁f₁`, the slack in C.42's node floor `hfloor`.  `ℕ`-subtraction; `1 ≤ δ` at every
`TowerDatum` is `one_le_margin` below. -/
def TowerDatum.margin {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  T.u₂ - T.e₂ * ((F.e₁ * F.f₁) * F.h)

/-- **NODE C.71 (v) — the FAITHFULNESS THRESHOLD `Θ_j`** (`EFF.GENTOW3.18`):
`Θ T μ₂ j = (μ₂ − j)·E₂ + δ`, with `E₂ = e₂f₂u₂` (C.42) and `δ` the margin.  Below `Θ_j` the two
reads of C.71 agree (C.72(ii)); the first disagreement sits at height `≥ Θ_j` (C.72(i)).
`ℕ`-subtraction in `(μ₂ − j)`: for `j ≥ μ₂` the threshold is the bare margin. -/
def TowerDatum.theta {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin)
    (μ₂ j : ℕ) : ℕ := (μ₂ - j) * T.E₂ + T.margin

/-! ### The two arithmetic companions

`margin ≥ 1` is the blueprint's own companion ("definitional, via `T.hfloor`") and is what every
`Θ_j` bound in §8 leans on: it is the reason the faithful band is nonempty even at the top index
`j = μ₂`, where `Θ` degenerates to `δ`. -/

/-- **C.71 companion** — the margin is at least `1`, by C.42's node floor
`hfloor : e₂·D′·h < u₂`.  (`TowerDatum.margin` is a `ℕ`-subtraction, so this is exactly the
statement that it does not silently truncate to `0`.) -/
theorem TowerDatum.one_le_margin {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : 1 ≤ T.margin := by
  have h := T.hfloor
  rw [mul_assoc] at h
  simp only [TowerDatum.margin]
  omega

/-- **C.71 companion** — the threshold is positive at every index, immediately from
`one_le_margin`; the faithful band `{m | m < Θ_j}` of C.72(ii) is therefore never empty. -/
theorem TowerDatum.one_le_theta {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ j : ℕ) : 1 ≤ T.theta μ₂ j := by
  have h := T.one_le_margin
  simp only [TowerDatum.theta]
  omega

end Uniformity.Density.Tower

/-! ## Unfolding checks

`example`s, not declarations: the local pins on the shape of the five bodies.  They fix the two
defining equations of `devQ` against B.02's `dev` (so that a later edit to either recursion breaks
a compile rather than silently desynchronizing the generic copy from the original), the two
degenerations of `Θ_j`, and its antitonicity in `j` — the direction of travel that makes `Θ_0` the
widest band and `Θ_{μ₂}` the narrowest. -/

section UnfoldingChecks

open Uniformity.Density.Tower Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `devQ`'s base case IS B.02's: the `0`-th development coefficient is the remainder. -/
example {R : Type*} [CommRing R] (Ψ g : Polynomial R) : devQ Ψ g 0 = g %ₘ Ψ := rfl

/-- `devQ`'s step IS B.02's: the `(j+1)`-st coefficient of `g` is the `j`-th of the quotient. -/
example {R : Type*} [CommRing R] (Ψ g : Polynomial R) (j : ℕ) :
    devQ Ψ g (j + 1) = devQ Ψ (g /ₘ Ψ) j := rfl

/-- the generic copy agrees with B.02's `dev` where both apply (`R = O`), at every index: the two
recursions are literally the same function, so the induction closes by `rfl` at each step. -/
example (φ : Polynomial O) (j : ℕ) : ∀ g : Polynomial O, devQ φ g j = dev φ g j := by
  induction j with
  | zero => intro g; rfl
  | succ k ih => intro g; exact ih (g /ₘ φ)

/-- at the top index the threshold degenerates to the bare margin `δ` (which `one_le_margin`
keeps `≥ 1`): `Θ_{μ₂} = δ`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) :
    T.theta μ₂ μ₂ = T.margin := by
  simp [TowerDatum.theta]

/-- at the bottom index the threshold is the full `μ₂` side-constant stack plus the margin:
`Θ_0 = μ₂·E₂ + δ`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) :
    T.theta μ₂ 0 = μ₂ * T.E₂ + T.margin := by
  simp [TowerDatum.theta]

/-- `Θ_j` is ANTITONE in `j` — the faithful band shrinks by exactly `E₂` per coordinate step, so
`Θ_0` is the widest and `Θ_{μ₂}` the narrowest.  (A `j ↔ μ₂ − j` transposition of the signed body
would reverse this and cannot survive the check.) -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    {μ₂ j j' : ℕ} (h : j ≤ j') : T.theta μ₂ j' ≤ T.theta μ₂ j := by
  simp only [TowerDatum.theta]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_left h _)) _

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.devQ
#print axioms Uniformity.Density.Tower.biRead
#print axioms Uniformity.Density.Tower.shadowDev
#print axioms Uniformity.Density.Tower.TowerDatum.margin
#print axioms Uniformity.Density.Tower.TowerDatum.theta
#print axioms Uniformity.Density.Tower.TowerDatum.one_le_margin
#print axioms Uniformity.Density.Tower.TowerDatum.one_le_theta

end AxCheck
