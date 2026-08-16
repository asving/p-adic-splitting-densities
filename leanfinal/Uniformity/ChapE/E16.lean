/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E14
import Uniformity.ChapE.E15

/-!
# Uniformity.ChapE.E16 — `he7a_clause12`: THEOREM HE7.A clauses (1)–(2), schema form

**Chapter E, NODE E.16** [theorem] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §4 — the master
HE7.A suite). ENV-E2. Landed at the signed SIGNATURE byte-for-byte from
`leanspec/Leanspec/ChapE.lean`.

Two clauses of `EFF.T2.31`, at the strength the *schema* owns:

* **clause (1)** — every side of the rung satisfies the node condition `λ > T` (spelled
  `p.2 * B.T < p.1`, i.e. `ℓ_λ · T < u_λ`) and the side lengths sum to the block's mass
  `μ` (`(HULL-LENGTH)`). This is a repackaging of E.12's `hside_node`/`hlen_sum` fields —
  and the packaging is the point: it is the interface chapter I reads, and the gate below
  shows the second half is not decoration (it forbids an empty side set).
* **clause (2)** — at a SEPARABLE side, every residual factor's class count is *exactly*
  its forced value: `D·e′` at a linear residual factor, `D·e′·deg r′` at a higher one.
  This is the sandwich `EFF.T2.30` describes ("Summing over disjoint exhaustive classes …
  forces equality term by term"), run once per factor multiset.

## The proof in one paragraph

At a separable side, E.14's `forced_sum_eq` says the two FORCED sums total the side's root
count `D·L_λ`, and E.12's `hexhaust` says the two ACTUAL sums total the same. E.12's `hforce`
gives the forced value as a termwise LOWER bound on each actual count, hence (monotonicity of
multiset sums) a lower bound on each of the two partial sums. Two nonnegative quantities that
each dominate a partner and whose totals agree are each equal to their partner — that is the
one `omega` step — so both partial sums are saturated, and E.15's `multiset_sandwich` converts
each saturated total into termwise equality.

## ⚠ WHAT THE SIGNED TYPE DOES *NOT* SAY — three disclosures

1. **No orbit reading, no irreducible factor (the GC-3 / HYP.01 fence).** The blueprint's
   STATEMENT prose for clause (2) continues "the class is ONE GALOIS ORBIT = the root set of
   one monic irreducible factor with local invariants `(e,f)`". That step consumes `(FUND)`
   (`|Ω| = [K₀(ρ):K₀] = e·f`) and the field-theoretic orbit reading — carrier content, and
   identifying the polynomial-level `efPair` with the ideal-theoretic pair is `HYP.01` +
   `HYP.12`. It is NOT done here, silently or otherwise: the conclusion below is counts, and
   only counts.
2. **The `(e,f)` half of clause (2) is E.15(ii), not this theorem.** The signed type carries
   the class-count equalities alone; the "any `(e,f)` pair divisible by `(e_𝒞e′, f_𝒞deg r′)`
   whose product is the class count equals it componentwise" half is `ef_forcing` (E.15(ii)),
   applied BY a consumer to this theorem's output. Gate (b) below performs exactly that
   composition once, so the claim that the two nodes compose is a term, not a comment.
3. **Separability is a hypothesis of clause (2) and of nothing else.** Clause (1) holds at every
   side of every interface; clause (2) is stated under `I.SepSide p`. Per `EFF.T2.18` neither
   clause consumes `(LB1)`/`(MP1)` — "their proofs run on the unsplit hull of `F` itself" — and
   accordingly nothing below mentions a block construction, `BlockSuite`, or E.39/E.40. That
   independence is definitional in Lean (this node's signature does not mention them) and is
   what E.41 reads off.

**DEPENDS.** E.12 (`RungInterface`: `hside_node`, `hlen_sum`, `hforce`, `hexhaust`), E.14
(`SepSide`, `forced_sum_eq`), E.15 (`multiset_sandwich`; `ef_forcing` at gate (b)) · mathlib
`Multiset.sum_map_le_sum_map`.

**SOURCE.** `EFF.T2.31` clauses 1–2 (verbatim: "every side λ … satisfies λ > T, `Σ L_λ = μ`;
… `|S_{λ,r′}| = De′deg r′`"); `EFF.T2.30` (the sandwich argument this reproduces);
`EFF.HE7.13` (the level-2 instance whose proof shape the schema generalises); `EFF.T2.18`
(clauses 1–2 carry NO `(LB1)` conditionality).

**TEETH.** Q1 / HE7-READ2 (1,335 PARI jobs, 0 mismatch — the level-2 instance of this clause
pair); the schema is this Lean theorem, the instance evidence is recorded at E.23.

**ENVIRONMENT.** ENV-E2.

## Status

Sorry-free, axiom-free beyond the Lean-core triple. Signature byte-identical to the committed
stub (binder names, implicit/explicit split, and both clauses' statements unchanged).
-/

namespace Uniformity.Density.Ladder

/-- **E.16** THEOREM HE7.A, clauses (1)–(2), schema form (`EFF.T2.31`).

Clause (1): every side satisfies the node condition `ℓ_λ·T < u_λ` and `Σ_λ L_λ = μ`.
Clause (2): at a separable side the class counts are pinned to their forced values,
`D·e′` per linear residual factor and `D·e′·deg r′` per higher one.

⚠ Counts only — the orbit/irreducible-factor reading of a class is `(FUND)` + `HYP.01`
carrier content and belongs to the instance records (E.22/E.23), not to the schema; and the
`(e,f)` forcing half of `EFF.T2.31`'s clause 2 is E.15's `ef_forcing`, applied downstream. -/
theorem he7a_clause12 {O : Type*} [CommRing O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B) :
    ((∀ p ∈ I.sides, p.2 * B.T < p.1) ∧ ∑ p ∈ I.sides, I.len p = B.μ) ∧
    (∀ p ∈ I.sides, I.SepSide p →
      (∀ q ∈ I.linFac p, I.classCount p q = C.D * p.2) ∧
      (∀ q ∈ I.hiFac p, I.classCountHi p q = C.D * p.2 * q.1)) := by
  -- clause (1): the two interface fields, packaged
  refine ⟨⟨I.hside_node, I.hlen_sum⟩, ?_⟩
  -- clause (2): the sandwich, run on each of the two residual multisets
  intro p hp hsep
  obtain ⟨hlin, hhi⟩ := I.hforce p hp
  have hle_lin : ((I.linFac p).map fun _ => C.D * p.2).sum
      ≤ ((I.linFac p).map (I.classCount p)).sum :=
    Multiset.sum_map_le_sum_map _ _ hlin
  have hle_hi : ((I.hiFac p).map fun q => C.D * p.2 * q.1).sum
      ≤ ((I.hiFac p).map (I.classCountHi p)).sum :=
    Multiset.sum_map_le_sum_map _ _ hhi
  -- forced total = root count = actual total, with each part dominating its partner
  have hforced := I.forced_sum_eq hp hsep
  have hex := I.hexhaust p hp
  have heq_lin : ((I.linFac p).map (I.classCount p)).sum
      = ((I.linFac p).map fun _ => C.D * p.2).sum := by omega
  have heq_hi : ((I.hiFac p).map (I.classCountHi p)).sum
      = ((I.hiFac p).map fun q => C.D * p.2 * q.1).sum := by omega
  exact ⟨multiset_sandwich (I.linFac p) (I.classCount p) (fun _ => C.D * p.2) hlin heq_lin,
    multiset_sandwich (I.hiFac p) (I.classCountHi p) (fun q => C.D * p.2 * q.1) hhi heq_hi⟩

/-! ## Gate (executed `example`s, not blueprint declarations)

Three checks. (a) clause (1)'s length identity has content — it forbids a side-free interface,
which is the shape a vacuous rung would take. (b) the composition disclosure 2 promises is
performed: clause (2) feeds `ef_forcing` and out comes the `(e,f)` pair, so the two nodes really
do assemble into `EFF.T2.31`'s full clause 2 (minus the orbit reading, which stays fenced).
(c) `hforce` is load-bearing: `hexhaust` alone leaves the counts free. -/

section Gate

-- (a) NO INTERFACE HAS AN EMPTY SIDE SET. `∑_{p ∈ ∅} L_p = 0`, while `B.hμ` demands `μ ≥ 1`;
-- so clause (1)'s second half already excludes the degenerate rung. (This is the cheapest
-- non-vacuity signal available at the schema layer, where full instances are E.22/E.23's.)
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface C B) : I.sides.Nonempty := by
  rcases Finset.eq_empty_or_nonempty I.sides with h | h
  · exfalso
    have hsum := (he7a_clause12 I).1.2
    rw [h, Finset.sum_empty] at hsum
    have hμ := B.hμ
    omega
  · exact h

-- (b) THE COMPOSITION WITH E.15(ii), performed. At a separable side and a residual factor of
-- degree `d = q.1 ≥ 1`, clause (2) pins the class count to `D·e′·d = (e_𝒞e′)(f_𝒞d)` — using
-- `(DEG-EF)` `D = e_𝒞f_𝒞` — so any pair `(e,f)` divisible by `(e_𝒞e′, f_𝒞d)` with that product
-- is forced to BE it. This is `EFF.T2.31`'s "equality in `(FUND)` forces equality in both local
-- divisibilities", with the `(FUND)` input supplied by the caller as `hprod` (GC-3 fence: the
-- caller's `e·f` is the polynomial-level dictionary pair, never an ideal-theoretic one).
example {O : Type*} [CommRing O] {K : Type*} [Field K] {C : SlotCarrier O K}
    {B : BlockData C} (I : RungInterface C B) {p : ℕ × ℕ} (hp : p ∈ I.sides)
    (hsep : I.SepSide p) {q : ℕ × ℕ} (hq : q ∈ I.hiFac p) {e f : ℕ}
    (hae : C.eC * p.2 ∣ e) (hbf : C.fC * q.1 ∣ f)
    (hprod : e * f = I.classCountHi p q) :
    e = C.eC * p.2 ∧ f = C.fC * q.1 := by
  have hcount := ((he7a_clause12 I).2 p hp hsep).2 q hq
  have hd : 0 < q.1 := by
    rcases Nat.eq_zero_or_pos q.1 with h0 | h
    · exfalso
      have h1 : 1 ≤ I.classCountHi p q := (I.hnonempty p hp).2 q hq
      have h2 : C.D * p.2 * q.1 ≤ I.classCountHi p q := (I.hforce p hp).2 q hq
      rw [hcount, h0] at h1
      omega
    · exact h
  have heC : 0 < C.eC := C.heC
  have hfC : 0 < C.fC := C.hfC
  have hl : 0 < p.2 := (I.hside_cop p hp).2
  refine ef_forcing (Nat.mul_pos heC hl) (Nat.mul_pos hfC hd) hae hbf ?_
  rw [hprod, hcount, C.hef]
  ring

-- (c) `hforce` IS LOAD-BEARING. With two linear residual factors at `D = 2`, `e′ = 3`, the
-- side's root count is `2·(3·2) = 12` and `hexhaust` alone permits the split `(0, 12)`, which
-- violates clause (2)'s value `D·e′ = 6`. The forced lower bounds are what remove the slack.
example : ∃ c₁ c₂ : ℕ, c₁ + c₂ = 2 * (3 * 2) ∧ c₁ ≠ 2 * 3 := ⟨0, 12, by norm_num, by norm_num⟩

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.he7a_clause12

end AxCheck
