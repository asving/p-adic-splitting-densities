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

**THIS FILE IS A PARTIAL LANDING (in progress: Parts 1–2 are in the file, Part 3 is being
written).**  The capstone `lawBS2_pair_or_triple` is NOT landed here.
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
* **Part 3 — the trinomial shape of the composed key** (`stageLiftO_of_f1`,
  `KeyFrame.slotIdx_mul_left`, `composedKey_trinomial`).  C.127's three clauses were HANDED the
  shape `Φ₂ = Φ′^{f₂} + C(c₂π^{v₂})x^{i₂}Φ′^{f₂−1} + C(c₀π^{v₀})` as a hypothesis (`hcomp`),
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
   `K^{μ₂} = Σ_{k+l+r=μ₂} C(μ₂;k,l,r)P^lc₀^rY^{2k+l}`, the degree-2 wrap dictionary
   (`x² = Φ′ + (π^hω − κ₁x)`, `x³ = (x−κ₁)Φ′ + …`, `x⁴ = Φ′² + (2π^hω + κ₁² − 2κ₁x)Φ′ + …`),
   and LEMMA 3(3a)–(3d)'s statement that wrap depth `j` sits exactly `jδ` above the pure
   power's own weight `μ₂E₂`.  Nothing landed carries a weight grading of this kind:
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
      show devQ Ψ ((Polynomial.C c * g) /ₘ Ψ) j = _
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
      show ((Polynomial.X : Polynomial R) ^ 0) %ₘ triKey P c0 = 1
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
      show ((Polynomial.X : Polynomial R) ^ 1) %ₘ triKey P c0 = _
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

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.isUnit_natCast_iff
#print axioms Uniformity.Density.Tower.triKey
#print axioms Uniformity.Density.Tower.triKey_monic
#print axioms Uniformity.Density.Tower.triKey_natDegree
#print axioms Uniformity.Density.Tower.devQ_C_mul
#print axioms Uniformity.Density.Tower.devQ_triKey_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.devQ_triKey_X_pow_even
#print axioms Uniformity.Density.Tower.devQ_triKey_X_pow_odd

end AxCheck
