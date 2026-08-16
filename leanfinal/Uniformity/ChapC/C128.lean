/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C74
import Uniformity.ChapC.C127

/-!
# Uniformity.ChapC.C128 — LAW B-S2: the P-BINOM cascade pair-or-triple attainment law (PARTIAL)

**Chapter C, NODE C.128** [theorem] [fresh] [signed: A-C.4; RE-SIGNED A-C.5 — the geography pin
`he₁ : F.e₁ = 2`, `hf₂ : T.f₂ = 2` is in the binder list] (`blueprint/CHAP-C_tower_grammar.md`,
NODE C.128; twin `leanspec/Leanspec/ChapC.lean`, section `AC4Laws`).  **ENV-C1**.  Proof source:
the corpus-grade note `lean/notes/openmath/LAWBS2_PROOF_2026-08-16.md` (PROVED at the pinned
geography; 4 adversarial passes CLEAN; battery `verification/openmath/bs2_lawbs2_cert.py` GREEN
666/0, 6/6 teeth).

**THIS FILE IS A PARTIAL LANDING.**  The capstone `lawBS2_pair_or_triple` is NOT landed here.
What is landed are three of the node's four named ingredient pieces, each stated and proved in
full; the census that welds them is BLOCKED, with the piece boundary named in the section
"What is BLOCKED" below and in `leanfinal/notes/C128_PARTIAL_2026-08-16.md`.

## The law, and the three landed pieces

At the `D′ = 2` cascade geography (`F.e₁ = 2`, `F.f₁ = 1`, `T.f₂ = 2`, hence `T.e₂ = 1` and
`t* = 1`, the `t*`-entry carrying `x`-power exactly `1`), the pure power `Φ₂^{μ₂}` attains its
top-coordinate floor — `TouchCert T hπ μ₂ (μ₂ − 1)` in C.74's vocabulary — iff the residue
characteristic `p` misses `binom(μ₂,2)` or misses `binom(μ₂,3)`.

* **Part 1 — the unit bridge** (`isUnit_natCast_iff`).  The proof note's standing convention
  "an integer is a unit of `O` iff `p ∤ n`", in both directions, in mixed AND equal
  characteristic.  It is what converts the census's *height* statements (`v(b₂) = 0`) into the
  *divisibility* statements the signed conclusion is phrased in
  (`¬ ringChar (ResidueField O) ∣ Nat.choose μ₂ 2`).
* **Part 2 — the trinomial chain (the note's LEMMA 4)** (`devQ_triKey_X_pow_even`,
  `devQ_triKey_X_pow_odd`, `devQ_triKey_eq_zero_of_natDegree_lt`).  Over ANY commutative ring:
  at the degree-2 trinomial key `K = Y² + P·Y + c₀`, the `(n)`-th chain coordinate of a pure
  `Y`-power is `0` below `Y^{2n}`, is `1` at `Y^{2n}`, and is `Y − n·P` at `Y^{2n+1}`.  This is
  the top-band filter of the note's §4: it is what kills every seed whose `Y`-power falls short
  of `2μ₂ − 2`, and it is what produces the PAIR branch's quotient cross-term `−(μ₂−1)P` — the
  reason the `(1,0)` slot carries the MIXED integer `M = b₃ − (μ₂−1)b₂` and not `b₃`.
  Part 2 also lands **the degree-2 wrap dictionary** (`X_sq_eq_triKey_sub`,
  `X_cube_eq_triKey`, `X_four_eq_triKey`): the note's §4 displays for `x²`, `x³`, `x⁴` in the
  `Φ′`-adic basis, which is how an over-grid `x`-power becomes `Φ′`-powers.  `key_eq_triKey`
  (Part 3) is what makes them apply to the frame key.
* **Part 3 — the trinomial shape of the composed key** (`stageLiftO_of_f1`,
  `KeyFrame.slotIdx_mul_left`, `composedKey_trinomial`, `isUnit_entryCoef`, `key_eq_triKey`).
  C.127's three clauses were HANDED the shape
  `Φ₂ = Φ′^{f₂} + C(c₂π^{v₂})x^{i₂}Φ′^{f₂−1} + C(c₀π^{v₀})` as a hypothesis (`hcomp`),
  which is what made that node D19-safe.  C.128's signed binder list has no such hypothesis, so
  the shape must be DERIVED from C.43's body — through C.14a's `stageLiftO` — and that
  derivation is Part 3.  At `f₁ = 1` every `stageLiftO` entry is a single monomial
  `C(λ·π^a)·x^i` with `i = slotIdx M`, `a = (M − i·h)/e₁` (`stageLiftO_of_f1`); at `e₁ = 2`,
  `f₂ = 2`, `e₂ = 1` and the signed `hslot` the two entries come out at slots `1` and `0`
  (`KeyFrame.slotIdx_mul_left` computes the second), giving the C.127 shape together with the
  two on-side relations `u₂ = e₁v₂ + i₂` and `e₁v₀ = f₂u₂` that the note's (G3) asserts and
  that the Lean carrier makes automatic.

## What is BLOCKED, and where the boundary runs

The remaining two pieces are the note's §2–§4 and they are a node's worth of work each:

1. **the wrap-seed sum (§2) and the weight calculus (§3)** — the multinomial expansion
   `K^{μ₂} = Σ_{k+l+r=μ₂} C(μ₂;k,l,r)P^lc₀^rY^{2k+l}` and LEMMA 3(3a)–(3d)'s statement that
   wrap depth `j` sits exactly `jδ` above the pure power's own weight `μ₂E₂`.  (The dictionary
   the expansion is developed against — `x²`, `x³`, `x⁴` in the `Φ′`-adic basis — IS landed,
   in Part 2; what is missing is the expansion itself and the grading.)  Nothing landed
   carries a weight grading of this kind:
   C.127's `shadowDev_of_ingrid` explicitly does NOT apply (the pure power is OVER-grid, which
   is the whole content of the law), and C.129's `binomKey_mod_monomial` is stated at the
   BINOMIAL key `X^D − C w` and cannot be reused at the one-sided non-binomial `Φ′` this node
   is proved for.
2. **the top-coordinate census (§4)** — the three-branch survival argument (`l ∈ {2,3,4}`,
   `r = 0`), the exact slot dictionary, and the heights of §5.  Part 2 of this file is its
   chain-value input; the census itself needs piece 1's grading to know that only depth-1 seeds
   can reach the floor layer.

The boundary between what is landed and what is not is therefore exactly: **the seed sum**.
Everything upstream of the sentence "`Δ_j = red(R_j(T̂))` for every `j < μ₂`" (the note's §2
closing display) is landed here or in C.127; everything downstream is open.

**DEPENDS.** C.74 (`TouchCert`) · C.127 (`devQ` API, `reass`, the slot-height layer) · C.129
(through C.127) · C.43 (`composedKey`, `wrapExp`) · C.14a (`stageLiftO`, `stageLiftIA`,
`stageCoord`, `resLift`) · C.15/C.16 (`slotIdx`, `slotIdx_spec`, `slotIdx_unique`) · C.42
(`TowerDatum`) — all imported (C.14a/C.15/C.16/C.42/C.43 transitively through C.74/C.127).

**SIZE.** the blueprint estimates ~90 lines for the capstone; this partial landing is the
three ingredient pieces.

**SOURCE.** `lean/notes/openmath/LAWBS2_PROOF_2026-08-16.md` §0 (the frame class), §1 LEMMA 4
(Part 2), §5 (the unit bridge of Part 1); C.43/C.14a's own bodies (Part 3).

**TEETH.** The node's numeric leg exists and is GREEN
(`verification/openmath/bs2_lawbs2_cert.py`, 666/0, 6/6 teeth); it certifies the census, which
is the BLOCKED half.  The `example`s below pin the two chain values at `n = 1, 2` — the rows
that a `Y − nP` ↦ `Y + nP` sign flip or an off-by-one in the coordinate index cannot survive.

**SCOPE FENCE (do not widen).**  `he₁ : F.e₁ = 2` and `hf₂ : T.f₂ = 2` are load-bearing: the
un-pinned statement is REFUTED on two constructed PARI-valid axes (`e₁ = 4`, empty top band;
`e₁ = 3`, unit-dependent merged digit — note §7.1/§7.2, battery BS2-STUBGAP).  Part 3 is stated
at exactly the pinned geography for that reason.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  PARTIAL: the capstone `lawBS2_pair_or_triple` is not
landed — see "What is BLOCKED" above.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

/-! ## Part 1 — the unit bridge: an integer is a unit of `O` iff `p` misses it

The note's §5 uses this in both directions and in both mixed and equal characteristic: the
verdict `p ∤ b₂` is what makes the `(0,1)` slot sit AT the floor rather than above it (mixed
characteristic) or exist at all (equal characteristic).  Nothing here is specific to `B-S2`. -/

section UnitBridge

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Part 1 — the unit bridge.**  A natural number is a unit of the DVR `O` exactly when the
residue characteristic does not divide it.  (`ringChar (ResidueField O)` is `p` in mixed
characteristic and the characteristic itself in equal characteristic; the statement is uniform
in the two cases because it is read entirely through the residue field.) -/
theorem isUnit_natCast_iff (n : ℕ) :
    IsUnit ((n : O)) ↔ ¬ (ringChar (ResidueField O) ∣ n) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
  rw [map_natCast (IsLocalRing.residue O) n]
  exact not_congr (ringChar.spec (ResidueField O) n)

end UnitBridge

/-! ## Part 2 — the trinomial chain (the note's LEMMA 4)

The chain of a polynomial at the degree-2 trinomial key `K = Y² + P·Y + c₀` is B.02's
development read through C.71's generic `devQ`: the `n`-th chain coordinate `R_n` IS
`devQ K · n`.  LEMMA 4 computes it on pure `Y`-powers, which is all the top band ever sees:

* below `Y^{2n}` the coordinate vanishes for degree reasons (4a);
* at `Y^{2n}` it is `1` (4b) — the TRIPLE and QUAD branches' input;
* at `Y^{2n+1}` it is `Y − n·P` (4c) — the PAIR branch's input, and the source of the
  `−(μ₂−1)P` quotient cross-term that merges the `(1,0)` slot digit into
  `M = b₃ − (μ₂−1)b₂`.

Stated over an arbitrary commutative ring because the shadow read runs its division tower in
`(O[x]/Φ′)[Z]` (C.71's `biRead`), not in `O[x][Z]`. -/

section TrinomialChain

variable {R : Type*} [CommRing R]

/-- The **degree-2 trinomial key** `K = Y² + P·Y + c₀` over an arbitrary commutative ring — the
note's (G2) shape, transported to the coefficient ring the chain is run in.

⚠ New definition (trust boundary): it is a plain polynomial expression, introduced only so that
the three chain lemmas below can be stated without repeating it; nothing is claimed about its
relation to `composedKey` here (that is Part 3's `composedKey_trinomial`). -/
noncomputable def triKey (P c0 : R) : Polynomial R :=
  Polynomial.X ^ 2 + Polynomial.C P * Polynomial.X + Polynomial.C c0

/-- the tail `P·Y + c₀` sits strictly below `Y²` — the one degree fact the trinomial's monicity
and degree both come from. -/
private theorem triKey_tail_degree_lt [Nontrivial R] (P c0 : R) :
    (Polynomial.C P * Polynomial.X + Polynomial.C c0).degree
      < ((Polynomial.X : Polynomial R) ^ 2).degree := by
  rw [degree_X_pow]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (degree_C_mul_X_le P) (by exact_mod_cast by norm_num)
  · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast by norm_num)

private theorem triKey_tail_natDegree_le [Nontrivial R] (P c0 : R) :
    (Polynomial.C P * Polynomial.X + Polynomial.C c0).natDegree ≤ 1 := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · simpa using natDegree_C_mul_le P (Polynomial.X : Polynomial R)
  · simp

private theorem triKey_assoc (P c0 : R) :
    triKey P c0 = Polynomial.X ^ 2 + (Polynomial.C P * Polynomial.X + Polynomial.C c0) := by
  rw [triKey, add_assoc]

theorem triKey_monic [Nontrivial R] (P c0 : R) : (triKey P c0).Monic := by
  rw [triKey_assoc]
  exact (monic_X_pow 2).add_of_left (triKey_tail_degree_lt P c0)

theorem triKey_natDegree [Nontrivial R] (P c0 : R) : (triKey P c0).natDegree = 2 := by
  refine natDegree_eq_of_degree_eq_some ?_
  rw [triKey_assoc, degree_add_eq_left_of_degree_lt (triKey_tail_degree_lt P c0), degree_X_pow]

theorem triKey_degree [Nontrivial R] (P c0 : R) : (triKey P c0).degree = 2 := by
  rw [degree_eq_natDegree (triKey_monic P c0).ne_zero, triKey_natDegree]
  rfl

/-- The wrap identity in the chain's own variable: `Y² = K − (P·Y + c₀)`. -/
theorem X_sq_eq_triKey_sub (P c0 : R) :
    (Polynomial.X : Polynomial R) ^ 2
      = triKey P c0 - (Polynomial.C P * Polynomial.X + Polynomial.C c0) := by
  rw [triKey]; ring

/-! ### The degree-2 wrap dictionary (the note's §4 displays)

The same shape `Y² + P·Y + c₀` is BOTH the level-2 key `K` (the chain above) and, at the pinned
geography `e₁ = 2`, `f₁ = 1`, the level-1 key `Φ′ = x² + κ₁x − π^hω` (`triKey κ₁ (−π^hω)`).  The
three identities below are the note's §4 wrap dictionary at the second reading: they express
`x²`, `x³`, `x⁴` in the `Φ′`-adic basis, which is how an over-grid `x`-power turns into `Φ′`
(i.e. `Y`) powers.  `X_sq_eq_triKey_sub` above is the `x²` row; these are the `x³` and `x⁴`
rows, in the exact form the census consumes (the `Φ′`-coefficient of `x³` is `x − κ₁`, which is
the ONLY `κ₁`-decorated top-band content, and the `Φ′²`-coefficient of `x⁴` is exactly `1`).

Both are ring identities — no monicity, no degree hypothesis, any commutative ring. -/

/-- **the `x³` row** of the wrap dictionary: `x³ = (x − κ₁)·Φ′ + ((κ₁² − κ₀)x + κ₁κ₀)` at
`Φ′ = x² + κ₁x + κ₀`.  (The note writes it at `κ₀ = −π^hω`:
`x³ = (x − κ₁)Φ′ + ((π^hω + κ₁²)x − κ₁π^hω)`.)  The depth-1 `Φ′`-coefficient `x − κ₁` is the
TRIPLE branch's input, and its `−κ₁` is the note's only `κ₁`-decorated top-band deposit. -/
theorem X_cube_eq_triKey (a b : R) :
    (Polynomial.X : Polynomial R) ^ 3
      = (Polynomial.X - Polynomial.C a) * triKey a b
        + (Polynomial.C (a ^ 2 - b) * Polynomial.X + Polynomial.C (a * b)) := by
  simp only [triKey, Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_mul]
  ring

/-- **the `x⁴` row** of the wrap dictionary:
`x⁴ = Φ′² + ((κ₁² − 2κ₀) − 2κ₁x)·Φ′ + ((2κ₁κ₀ − κ₁³)x + (κ₀² − κ₁²κ₀))`.  The leading
coefficient is exactly `1` — the QUAD branch's depth-2 input, and the reason the quad deposit
is `ω`-free and `κ₁`-free at the top band. -/
theorem X_four_eq_triKey (a b : R) :
    (Polynomial.X : Polynomial R) ^ 4
      = triKey a b ^ 2
        + (Polynomial.C (a ^ 2 - 2 * b) - Polynomial.C (2 * a) * Polynomial.X) * triKey a b
        + (Polynomial.C (2 * a * b - a ^ 3) * Polynomial.X
            + Polynomial.C (b ^ 2 - a ^ 2 * b)) := by
  simp only [triKey, Polynomial.C_sub, Polynomial.C_pow, Polynomial.C_mul, Polynomial.C_ofNat]
  ring

/-- Scalars pass through the development: `devQ Ψ (C c · g) j = C c · devQ Ψ g j` at a monic
`Ψ`.  (Needed for the PAIR branch, whose surviving deposit is `P` times a pure power.) -/
theorem devQ_C_mul [Nontrivial R] {Ψ : Polynomial R} (hΨ : Ψ.Monic) (c : R) :
    ∀ (g : Polynomial R) (j : ℕ),
      devQ Ψ (Polynomial.C c * g) j = Polynomial.C c * devQ Ψ g j := by
  have hstep : ∀ g : Polynomial R,
      (Polynomial.C c * g) /ₘ Ψ = Polynomial.C c * (g /ₘ Ψ)
        ∧ (Polynomial.C c * g) %ₘ Ψ = Polynomial.C c * (g %ₘ Ψ) := by
    intro g
    refine div_modByMonic_unique (Polynomial.C c * (g /ₘ Ψ)) (Polynomial.C c * (g %ₘ Ψ)) hΨ
      ⟨?_, ?_⟩
    · have h := modByMonic_add_div g Ψ
      linear_combination Polynomial.C c * h
    · refine lt_of_le_of_lt ?_ (degree_modByMonic_lt g hΨ)
      rw [← Polynomial.smul_eq_C_mul]
      exact degree_smul_le c _
  intro g j
  induction j generalizing g with
  | zero => exact (hstep g).2
  | succ j ih =>
      change devQ Ψ ((Polynomial.C c * g) /ₘ Ψ) j = _
      rw [(hstep g).1]
      exact ih _

variable [Nontrivial R]

/-- **LEMMA 4(a)** — a dividend of `Y`-degree below `2n` has vanishing `n`-th chain
coordinate at the degree-2 key: no seed short of `Y^{2n}` reaches coordinate `n`. -/
theorem devQ_triKey_eq_zero_of_natDegree_lt (P c0 : R) {g : Polynomial R} {n : ℕ}
    (hg : g.natDegree < 2 * n) : devQ (triKey P c0) g n = 0 := by
  refine devQ_eq_zero_of_lt (triKey_monic P c0) g n ?_
  rw [triKey_natDegree]
  omega

/-- **LEMMA 4(b)** — `R_n(Y^{2n}) = 1`.  (The note proves it by a binomial expansion of
`Y² = K − (PY + c₀)`; the induction below is the same computation done one wrap at a time,
which is what the `devQ` recursion natively supports.) -/
theorem devQ_triKey_X_pow_even (P c0 : R) :
    ∀ n : ℕ, devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ (2 * n)) n = 1 := by
  intro n
  induction n with
  | zero =>
      change ((Polynomial.X : Polynomial R) ^ 0) %ₘ triKey P c0 = 1
      rw [pow_zero]
      refine (modByMonic_eq_self_iff (triKey_monic P c0)).2 ?_
      rw [degree_one, triKey_degree]
      exact_mod_cast by norm_num
  | succ n ih =>
      have hsplit : (Polynomial.X : Polynomial R) ^ (2 * (n + 1))
          = Polynomial.X ^ (2 * n) * triKey P c0
            - (Polynomial.C P * Polynomial.X + Polynomial.C c0) * Polynomial.X ^ (2 * n) := by
        have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [h2, pow_add, X_sq_eq_triKey_sub P c0]
        ring
      rw [hsplit, sub_eq_add_neg, devQ_add (triKey_monic P c0)]
      have h1 : devQ (triKey P c0) (Polynomial.X ^ (2 * n) * triKey P c0) (n + 1) = 1 := by
        have := devQ_mul_pow (Ψ := triKey P c0) (triKey_monic P c0) 1
          ((Polynomial.X : Polynomial R) ^ (2 * n)) n
        rw [pow_one] at this
        rw [show n + 1 = 1 + n from by omega, this]
        exact ih
      have h2 : devQ (triKey P c0)
          (-((Polynomial.C P * Polynomial.X + Polynomial.C c0) * Polynomial.X ^ (2 * n)))
          (n + 1) = 0 := by
        refine devQ_triKey_eq_zero_of_natDegree_lt P c0 ?_
        rw [natDegree_neg]
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        have hle : (Polynomial.C P * Polynomial.X + Polynomial.C c0).natDegree ≤ 1 :=
          triKey_tail_natDegree_le P c0
        have hx : ((Polynomial.X : Polynomial R) ^ (2 * n)).natDegree = 2 * n := by
          simp
        omega
      rw [h1, h2, add_zero]

/-- **LEMMA 4(c)** — `R_n(Y^{2n+1}) = Y − n·P`.  The `−n·P` is the accumulated quotient
cross-term: each wrap of `Y²` deposits one more `−P` into the coordinate.  At the PAIR branch
(`n = μ₂ − 1`) this is exactly the `−(μ₂−1)b₂ĉ₂³π^{3v₂}` deposit that merges with the TRIPLE
digit `b₃ĉ₂³π^{3v₂}` into `M = b₃ − (μ₂−1)b₂`. -/
theorem devQ_triKey_X_pow_odd (P c0 : R) :
    ∀ n : ℕ, devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ (2 * n + 1)) n
      = Polynomial.X - Polynomial.C ((n : R) * P) := by
  intro n
  induction n with
  | zero =>
      change ((Polynomial.X : Polynomial R) ^ 1) %ₘ triKey P c0 = _
      rw [pow_one]
      have hlt : (Polynomial.X : Polynomial R).degree < (triKey P c0).degree := by
        rw [degree_X, triKey_degree]
        exact_mod_cast by norm_num
      rw [(modByMonic_eq_self_iff (triKey_monic P c0)).2 hlt]
      simp
  | succ n ih =>
      have hsplit : (Polynomial.X : Polynomial R) ^ (2 * (n + 1) + 1)
          = Polynomial.X ^ (2 * n + 1) * triKey P c0
            - Polynomial.C P * Polynomial.X ^ (2 * (n + 1))
            - Polynomial.C c0 * Polynomial.X ^ (2 * n + 1) := by
        have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        have h3 : 2 * (n + 1) = 2 * n + 2 := by omega
        rw [h2, h3, pow_add, X_sq_eq_triKey_sub P c0, pow_add]
        ring
      rw [hsplit, sub_sub, sub_eq_add_neg, devQ_add (triKey_monic P c0)]
      have h1 : devQ (triKey P c0) (Polynomial.X ^ (2 * n + 1) * triKey P c0) (n + 1)
          = Polynomial.X - Polynomial.C ((n : R) * P) := by
        have := devQ_mul_pow (Ψ := triKey P c0) (triKey_monic P c0) 1
          ((Polynomial.X : Polynomial R) ^ (2 * n + 1)) n
        rw [pow_one] at this
        rw [show n + 1 = 1 + n from by omega, this]
        exact ih
      have h2 : devQ (triKey P c0)
          (-(Polynomial.C P * Polynomial.X ^ (2 * (n + 1))
              + Polynomial.C c0 * Polynomial.X ^ (2 * n + 1))) (n + 1)
          = - Polynomial.C P := by
        rw [neg_add, devQ_add (triKey_monic P c0)]
        have ha : devQ (triKey P c0) (-(Polynomial.C P * Polynomial.X ^ (2 * (n + 1)))) (n + 1)
            = - Polynomial.C P := by
          rw [neg_mul_eq_neg_mul, ← Polynomial.C_neg,
            devQ_C_mul (triKey_monic P c0) (-P) _ (n + 1),
            devQ_triKey_X_pow_even P c0 (n + 1), Polynomial.C_neg]
          ring
        have hb : devQ (triKey P c0) (-(Polynomial.C c0 * Polynomial.X ^ (2 * n + 1))) (n + 1)
            = 0 := by
          refine devQ_triKey_eq_zero_of_natDegree_lt P c0 ?_
          rw [natDegree_neg]
          refine lt_of_le_of_lt natDegree_mul_le ?_
          have h1' : (Polynomial.C c0).natDegree = 0 := natDegree_C c0
          have h2' : ((Polynomial.X : Polynomial R) ^ (2 * n + 1)).natDegree = 2 * n + 1 := by
            simp
          omega
        rw [ha, hb, add_zero]
      rw [h1, h2]
      push_cast
      rw [add_mul, one_mul, Polynomial.C_add]
      ring

end TrinomialChain

/-! ## Part 3 — the trinomial shape of the composed key (the node's missing `hcomp`)

C.127's three clauses are handed the shape
`Φ₂ = Φ′^{f₂} + C(c₂π^{v₂})x^{i₂}Φ′^{f₂−1} + C(c₀π^{v₀})` as a HYPOTHESIS, which is what makes
that node D19-safe (it never touches `stageLiftO`).  C.128's signed binder list has no such
hypothesis: the shape has to come out of C.43's body,

```
Φ₂ = Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)}) · Φ′^{e₂t},   c_t = −(ψ₂.coeff t),
```

through C.14a's `stageLiftO`.  Three steps:

* `stageLiftO_of_f1` — at `f₁ = 1` the lift `L_M(c)` collapses to the single monomial
  `C(resLift(coord₀ c)·π^{(M − i(M)h)/e₁})·x^{i(M)}` (C.14a's `stageLiftIA` has exactly `f₁`
  summands);
* `KeyFrame.slotIdx_mul_left` — `i(e₁·k) = 0`: a height that is a multiple of `e₁` sits at the
  `x`-free slot.  At `f₂ = 2` the CONSTANT entry has height `2u₂ = e₁u₂`, so this is what makes
  it `x`-free — the note's (G3) remark "at `D′ = 2` the `x`-freeness of `c₀` is automatic";
* `composedKey_trinomial` — the two together, at the pinned geography
  (`e₁ = 2`, `f₁ = 1`, `f₂ = 2`, `e₂ = 1`, `hslot : i(u₂) = 1`), give the C.127 shape with
  `i₂ = 1`, `v₂ = (u₂ − h)/2`, `v₀ = u₂`; `onSide_of_slot_one` is the note's (G3) height
  arithmetic `u₂ = e₁v₂ + i₂` and `e₁v₀ = f₂u₂`, which the Lean carrier makes automatic rather
  than hypothetical.

`entryCoef T t` names the entry coefficient so that no information is lost to an existential:
`isUnit_entryCoef` is its unit status, which the census consumes. -/

section Trinomial

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **Part 3(a)** — at `f₁ = 1` every `stageLiftO` entry is a single monomial: C.14a's
`stageLiftIA` sums `f₁` terms, so one survives, at slot `i(M) = F.slotIdx M` and `π`-exponent
`(M − i(M)h)/e₁`. -/
theorem stageLiftO_of_f1 (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (hf₁ : F.f₁ = 1)
    (M : ℕ) (c : F.stageField H₀ hpin) :
    F.stageLiftO H₀ hpin M c
      = Polynomial.C (resLift (F.stageCoord H₀ hpin c 0)
            * π ^ ((M - F.slotIdx M * F.h) / F.e₁))
        * Polynomial.X ^ F.slotIdx M := by
  rw [KeyFrame.stageLiftO, KeyFrame.stageLiftIA, hf₁, Finset.sum_range_one]
  simp

/-- **Part 3(b)** — a height divisible by `e₁` sits at the `x`-free slot: `i(e₁·k) = 0`.
(`slotIdx` solves `i·h ≡ M [MOD e₁]` with `i < e₁`; at `M = e₁k` the solution `i = 0` is
available, and C.16's uniqueness identifies it with the search value.) -/
theorem KeyFrame.slotIdx_mul_left (F : KeyFrame O π) (k : ℕ) : F.slotIdx (F.e₁ * k) = 0 :=
  (F.slotIdx_unique (i := 0) F.he₁ (by simp [Nat.ModEq, Nat.mul_mod_right])).symm

/-- **Part 3 — the entry coefficient.**  The `t`-th coefficient of C.43's composed-key display
at `f₁ = 1`, i.e. the `O`-lift of the single letter-basis digit of `c_t·η^{W(t)}`, with the
display's leading minus already absorbed.  (`resLift` is C.14a's zero-guarded section of the
residue map; the outer `-` is the display's own sign, so that `composedKey_trinomial` reads
`Φ′² + C(ĉ₂π^{v₂})x + C(ĉ₀π^{v₀})` with PLUS signs, as C.127's `hcomp` does.) -/
noncomputable def entryCoef {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (t : ℕ) : O :=
  - resLift (F.stageCoord H₀ hpin
      (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) 0)

/-- **Part 3(c) — the note's (G3), and it is not a hypothesis.**  At the pinned geography the
two on-side relations `u₂ = e₁·v₂ + i₂` (with `i₂ = 1`, `v₂ = (u₂ − h)/2`) and
`e₁·v₀ = f₂·u₂` (with `v₀ = u₂`) hold outright: the first because `hslot` forces `h ≡ u₂` mod
`2` and C.42's node floor `hfloor` forces `2h < u₂`, so the `ℕ`-division is exact; the second
by arithmetic. -/
theorem onSide_of_slot_one {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hf₁ : F.f₁ = 1) (he₁ : F.e₁ = 2) (hf₂ : T.f₂ = 2)
    (he₂ : T.e₂ = 1) (hslot : F.slotIdx T.u₂ = 1) :
    T.u₂ = F.e₁ * ((T.u₂ - F.h) / 2) + 1 * F.h ∧ F.e₁ * T.u₂ = T.f₂ * T.u₂ := by
  have hcong : F.slotIdx T.u₂ * F.h ≡ T.u₂ [MOD F.e₁] := (F.slotIdx_spec T.u₂).2
  rw [hslot, one_mul, he₁] at hcong
  have hfl : 2 * F.h < T.u₂ := by
    have h := T.hfloor
    rw [he₂, he₁, hf₁, one_mul, mul_one] at h
    exact h
  have hmod : F.h % 2 = T.u₂ % 2 := hcong
  refine ⟨?_, by rw [he₁, hf₂]⟩
  rw [he₁]
  omega

/-- **Part 3(c) — THE TRINOMIAL SHAPE.**  At the pinned geography (`e₁ = 2`, `f₁ = 1`,
`f₂ = 2`, `e₂ = 1`, and the signed `hslot : i(u₂) = 1`) C.43's composed key IS C.127's `hcomp`
shape with `i₂ = 1`:

```
Φ₂ = Φ′² + C(ĉ₂·π^{(u₂−h)/2})·x·Φ′ + C(ĉ₀·π^{u₂}).
```

Nothing is assumed about the entries: they are C.43's own `stageLiftO` monomials, read by
`stageLiftO_of_f1`, at the slots `KeyFrame.slotIdx_mul_left` and `hslot` compute. -/
theorem composedKey_trinomial {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hf₁ : F.f₁ = 1) (he₁ : F.e₁ = 2) (hf₂ : T.f₂ = 2)
    (he₂ : T.e₂ = 1) (hslot : F.slotIdx T.u₂ = 1) :
    composedKey T
      = F.key ^ 2
        + Polynomial.C (entryCoef T 1 * π ^ ((T.u₂ - F.h) / 2)) * Polynomial.X ^ 1 * F.key
        + Polynomial.C (entryCoef T 0 * π ^ T.u₂) := by
  have hslot0 : F.slotIdx (2 * T.u₂) = 0 := by
    have := F.slotIdx_mul_left T.u₂
    rw [he₁] at this
    exact this
  have hexp0 : (2 * T.u₂ - F.slotIdx (2 * T.u₂) * F.h) / F.e₁ = T.u₂ := by
    rw [hslot0, he₁]
    simp
  have hexp1 : (T.u₂ - F.slotIdx T.u₂ * F.h) / F.e₁ = (T.u₂ - F.h) / 2 := by
    rw [hslot, he₁, one_mul]
  rw [composedKey, hf₂, he₂, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, show (2 : ℕ) - 1 = 1 from rfl, one_mul, mul_one, pow_zero, pow_one]
  rw [stageLiftO_of_f1 F H₀ hpin hf₁, stageLiftO_of_f1 F H₀ hpin hf₁, hexp0, hexp1, hslot0,
    hslot, pow_zero, mul_one]
  simp only [entryCoef, neg_mul, Polynomial.C_neg]
  ring

/-- **Part 3(e) — the wrap dictionary applies to the frame key.**  At the pinned geography the
level-1 key is a degree-2 monic, hence literally a `triKey`: `Φ′ = x² + κ₁x + κ₀` with
`κ₁ = Φ′.coeff 1`, `κ₀ = Φ′.coeff 0` (the note's (G1) at `κ₀ = −π^hω`; the BINOMIAL subclass is
`κ₁ = 0`, and the law is proved for the whole one-sided class, so no binomial hypothesis is
taken).  This is what lets `X_sq_eq_triKey_sub` / `X_cube_eq_triKey` / `X_four_eq_triKey` be
read as the `Φ′`-adic wrap dictionary. -/
theorem key_eq_triKey (F : KeyFrame O π) (he₁ : F.e₁ = 2) (hf₁ : F.f₁ = 1) :
    F.key = triKey (F.key.coeff 1) (F.key.coeff 0) := by
  have hdeg : F.key.natDegree = 2 := by rw [F.hdeg, he₁, hf₁]
  have h2 : F.key.coeff 2 = 1 := by
    have hm := F.hmonic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hm
    exact hm
  have h := Polynomial.as_sum_range_C_mul_X_pow F.key
  rw [hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h2] at h
  conv_lhs => rw [h]
  rw [triKey, Polynomial.C_1]
  ring

/-! ### The entry coefficients are units

The census reads the entries as `ĉ₂π^{v₂}` and `ĉ₀π^{v₀}` with `ĉ₂, ĉ₀ ∈ O^×` — the note's
(G2).  At the Lean carrier that is a THEOREM, not a hypothesis: the entry digit is a nonzero
element of the residue field (the stage field is a field, `η ≠ 0` by C.19, and `ψ₂`'s
coefficient is nonzero by hypothesis / by C.42's `hψ0`), and `resLift` of a nonzero residue is
outside the maximal ideal. -/

/-- **D9 (cured).**  The order-0 key `X` is an order-1 key; the private-copy pattern
(C.04/C.12/C.19/C.21/C.22/C.44/C.46 each carry one), because `private` does not export. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    rw [Polynomial.map_X]
    exact Polynomial.irreducible_X

/-- The `Field` structure on the stage field `K` — C.04's private copy (a `@[reducible]`
`def`, not an `instance`, for B.25(b)'s reason). -/
@[reducible] private noncomputable def fieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- C.14's private helper, re-derived: a nonzero residue lifts to a unit. -/
private theorem isUnit_of_residue_ne_zero {x : O} (hx : IsLocalRing.residue O x ≠ 0) :
    IsUnit x := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff] at hx
  exact IsLocalRing.notMem_maximalIdeal.mp hx

/-- At `f₁ = 1` the single letter-basis digit detects nonvanishing: `stageCoord c 0 = 0` would
make C.14a's reconstruction identity `sum_stageCoord` read `c = 0`. -/
theorem stageCoord_ne_zero_of_f1 (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (hf₁ : F.f₁ = 1)
    {c : F.stageField H₀ hpin} (hc : c ≠ 0) : F.stageCoord H₀ hpin c 0 ≠ 0 := by
  intro h0
  refine hc ?_
  have hsum := F.sum_stageCoord H₀ hpin c
  rw [hf₁, Finset.sum_range_one, h0] at hsum
  simpa using hsum.symm

/-- **Part 3(d)** — the entry coefficients are UNITS, whenever the corresponding `ψ₂`-digit is
nonzero (which C.42's `hψ0` gives at `t = 0` and the signed `hψt` gives at `t = t*`).  This is
the note's (G2) `ĉ₂, ĉ₀ ∈ O^×`, discharged rather than assumed. -/
theorem isUnit_entryCoef {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hf₁ : F.f₁ = 1) {t : ℕ}
    (ht : T.ψ₂.coeff t ≠ 0) : IsUnit (entryCoef T t) := by
  letI : Field (F.stageField H₀ hpin) := fieldStageField F H₀ hpin
  have hne : (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ wrapExp T t) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr ht)
      (pow_ne_zero _ (F.stageLetter_ne_zero hπ H₀ hpin))
  have hcoord := stageCoord_ne_zero_of_f1 F H₀ hpin hf₁ hne
  rw [entryCoef]
  refine IsUnit.neg (isUnit_of_residue_ne_zero ?_)
  rw [resLift_spec]
  exact hcoord

end Trinomial

end Uniformity.Density.Tower

/-! ## Unfolding checks

`example`s, not declarations: the local pins on the two chain values at the first two
coordinates.  A `Y − nP ↦ Y + nP` sign flip, an off-by-one in the coordinate index, or a
`2n ↔ 2n+1` transposition of the two cases cannot survive them. -/

section UnfoldingChecks

open Uniformity.Density.Tower Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- `R₁(Y²) = 1`. -/
example (P c0 : R) : devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ 2) 1 = 1 := by
  simpa using devQ_triKey_X_pow_even P c0 1

/-- `R₁(Y³) = Y − P` — one wrap, one `−P`. -/
example (P c0 : R) :
    devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ 3) 1
      = Polynomial.X - Polynomial.C P := by
  simpa using devQ_triKey_X_pow_odd P c0 1

/-- `R₂(Y⁴) = 1`. -/
example (P c0 : R) : devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ 4) 2 = 1 := by
  simpa using devQ_triKey_X_pow_even P c0 2

/-- `R₂(Y⁵) = Y − 2P` — the cross-term accumulates one `−P` per wrap. -/
example (P c0 : R) :
    devQ (triKey P c0) ((Polynomial.X : Polynomial R) ^ 5) 2
      = Polynomial.X - Polynomial.C (2 * P) := by
  simpa using devQ_triKey_X_pow_odd P c0 2

/-- `R₁(Y) = Y`: below the band the coordinate is the dividend itself, not `0` — the boundary
row of LEMMA 4(a), whose hypothesis is `natDegree < 2n` and not `≤`. -/
example (P c0 : R) : devQ (triKey P c0) (Polynomial.X : Polynomial R) 0 = Polynomial.X := by
  simpa using devQ_triKey_X_pow_odd P c0 0

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.isUnit_natCast_iff
#print axioms Uniformity.Density.Tower.triKey
#print axioms Uniformity.Density.Tower.triKey_monic
#print axioms Uniformity.Density.Tower.triKey_natDegree
#print axioms Uniformity.Density.Tower.triKey_degree
#print axioms Uniformity.Density.Tower.devQ_C_mul
#print axioms Uniformity.Density.Tower.devQ_triKey_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.devQ_triKey_X_pow_even
#print axioms Uniformity.Density.Tower.devQ_triKey_X_pow_odd
#print axioms Uniformity.Density.Tower.stageLiftO_of_f1
#print axioms Uniformity.Density.Tower.KeyFrame.slotIdx_mul_left
#print axioms Uniformity.Density.Tower.entryCoef
#print axioms Uniformity.Density.Tower.onSide_of_slot_one
#print axioms Uniformity.Density.Tower.composedKey_trinomial
#print axioms Uniformity.Density.Tower.stageCoord_ne_zero_of_f1
#print axioms Uniformity.Density.Tower.isUnit_entryCoef
#print axioms Uniformity.Density.Tower.X_sq_eq_triKey_sub
#print axioms Uniformity.Density.Tower.X_cube_eq_triKey
#print axioms Uniformity.Density.Tower.X_four_eq_triKey
#print axioms Uniformity.Density.Tower.key_eq_triKey

end AxCheck
