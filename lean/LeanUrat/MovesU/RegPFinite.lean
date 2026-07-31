/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger
import LeanUrat.MovesU.BridgeB4_legRosterFintype
import LeanUrat.Kernels.KA9

/-!
# MovesU/RegPFinite — M17: the (REG-p) failing-prime set is FINITE, exactly characterized

Formalization of the DUAL-PROVED open-math result M17-regp-density:
* Fable attempt `lean/notes/openmath/M17-regp-density_fable.md` (VERDICT: PROVED,
  2026-07-31) — Lemma 0 (the dictionary: RegP at a pinned record is a concrete
  arithmetic condition; the act-agreement conjunct is FREE given definedness),
  Lemma 1/2 (finiteness + prime-power escape), Theorem A (exact characterization
  of the failing set as {p : ∃ δ ∈ Δ, p^δ ∈ B}), Theorem B (DetHyp costs nothing
  — `rs3_det_symbolic`).
* Codex twin `/tmp/openmath/M17-regp-density_codex.jsonl` (independent, fresh
  context, same session): its Lemma 1 = `RegPin.act_agree` here, its Theorem 1
  (RegP D ⟺ p ∉ ℬ) = `regP_iff_pool_avoids`/`not_regP_iff_exists_depth` here,
  its Theorem 2 (finiteness, effective) = `regP_failing_finite` here.

WHAT IS PROVED (schema level, at the corpus vocabulary as of 2026-07-31):
* `UCarriers.detHyp` — Theorem B wired: every carrier pack satisfies the symbolic
  determinant hypothesis (the chain's `pools_e0`/`prime_base` feed
  `Kernels.detHyp_of_escape_infinite` = `MovesS.rs3_det_symbolic`).
* `RegPin.act_agree` — Lemma 0's act-agreement FREENESS: at a pinned record the
  (r2) agreement conjunct holds wherever definedness does (`act_pin` + defeq of
  `MovesS.evalAt` with `RatFunc.eval`); so (REG-p) can only fail through a
  zero/pole, never through the ACT seam.
* `RegData.zeroPoleSet` — Theorem A's B as a FINSET (finiteness by type):
  per block, the rational roots of the full determinant's reduced numerator and
  denominator plus the poles of every entry-list member.
* `regP_iff_pool_avoids` / `not_regP_iff_exists_depth` — the EXACT dictionary:
  (REG-p) fails iff some pool value p^δ (δ ∈ depthSet) lies in the locus.
  ⟹ is pin-free; ⟸ consumes the pin exactly twice (act freeness; Φ ≠ 0).
* `pow_hits_finite` — Lemma 2 (prime-power escape): a finite B is hit by powers
  p^δ (δ in a finite positive depth set) for only finitely many bases p.
* Stage 2 below: the p-UNIFORM real locus (`realZeroPoleSet`) via the Lemma-0
  roster identity (`RegPin.entryList_eq`), pin-independence of the (REG-p) truth
  value, and Theorem A's family form: for a `RegPin`-pinned family the failing
  set {p prime : ¬ RegP (Dfam p hp)} EQUALS {p : ∃ δ ∈ Δ, p^δ ∈ B_real} and is
  FINITE (`regP_failing_eq` / `regP_failing_finite`).

Statement fence respected: `RegP` (MovesU/Defs.lean:209) and every existing
declaration untouched; this file only CONSUMES the pinned vocabulary.
Sharpness (recorded, not restated here): finiteness cannot be improved to
emptiness at schema level — the compiled countermodel `BridgeB15a_r2Neg.lean`
exhibits an admissible pack whose failing set is exactly {2}.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-! ## Theorem B: the symbolic determinant hypothesis costs nothing -/

/-- M17 Theorem B, wired: EVERY carrier pack carrying the chain laws satisfies
    the symbolic determinant hypothesis — `rs3_det_symbolic` (through the KA9
    consumer face) fed by the chain's own base-prime pool set and per-pool
    escape packages. So Theorem A's branch (A-ii) (DetHyp fails ⟹ (REG-p) fails
    everywhere) never fires at a carrier pack. -/
theorem UCarriers.detHyp {n : ℕ} (C : UCarriers n) : MovesS.DetHyp C.T C.RB C.hK :=
  LeanUrat.Kernels.detHyp_of_escape_infinite C.RB C.hdc C.hK C.chain.PrimePools
    C.chain.prime_sub C.chain.prime_base C.chain.pools_e0

/-! ## Lemma 0's act-agreement freeness -/

/-- M17 Lemma 0, the FREENESS of the agreement conjunct (= the Codex twin's
    Lemma 1): at a pinned record, ANY rational function defined at a pool value
    automatically satisfies the (r2) agreement clause — `act_pin` reads ACT as
    `MovesS.evalAt` on the defined locus, and `evalAt` is definitionally
    `RatFunc.eval (RingHom.id ℚ)`. Hence (r2) can fail ONLY through a pole. -/
theorem RegPin.act_agree {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (g : RatFunc ℚ) (q₀ : ℕ) (h : DefinedAt g (q₀ : ℚ)) :
    g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀ := by
  rw [P.act_pin g q₀ (MovesS.mem_OKat_iff.mpr h)]
  rfl

/-! ## The full determinant as a named object -/

/-- The FULL block determinant det(1 − K_e) of the abstract record (junk blocks
    included — exactly (r1)'s object, factored out of `RegP`'s letI inline). -/
noncomputable def RegData.detFull {p : ℕ} (D : RegData p) (e : D.Block) : RatFunc ℚ :=
  letI := D.instBi e; letI := D.instBd e
  Matrix.det (1 - D.K e)

/-- (r1) of `RegP` at (q₀, e), read at the named `detFull` (definitional regroup). -/
theorem RegP.detFull_clause {p : ℕ} {D : RegData p} (h : RegP D) {q₀ : ℕ}
    (hq : q₀ ∈ D.Pool) (e : D.Block) :
    DefinedAt (D.detFull e) (q₀ : ℚ) ∧
      (D.detFull e).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0 :=
  (h q₀ hq e).1

/-- M17 Lemma 0(ii)'s contrapositive at schema level: under (REG-p) no full
    block determinant is the zero rational function (the zero function
    evaluates to 0 at the base pool value p ∈ Pool, killing (r1)). -/
theorem RegP.detFull_ne_zero {p : ℕ} {D : RegData p} (h : RegP D) (e : D.Block) :
    D.detFull e ≠ 0 := by
  intro h0
  have h1 := (h.detFull_clause D.pool_self_mem e).2
  rw [h0] at h1
  exact h1 (RatFunc.eval_zero _ _)

/-- The pin transports the full determinant to the REAL block determinant
    Φ_{blk b} = det(1 − K_{blk b}) — `RegPin.detHyp`'s submatrix calc
    (DefsLedger.lean:552ff), factored out as an equation. -/
theorem RegPin.detFull_eq {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (b : D.Block) :
    D.detFull b
      = (1 - MovesS.Kmat C.T C.RB (P.blk b).1 (C.hK (P.blk b).1 (P.blk b).2)).det := by
  letI := D.instBi b; letI := D.instBd b
  have hmat : (1 - D.K b)
      = (1 - MovesS.Kmat C.T C.RB (P.blk b).1
          (C.hK (P.blk b).1 (P.blk b).2)).submatrix (P.st b) (P.st b) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply,
      P.K_pin b i j, EmbeddingLike.apply_eq_iff_eq]
  show (1 - D.K b).det = _
  rw [hmat, Matrix.det_submatrix_equiv_self]

/-- Theorem B transported through the pin: at a pinned record every full block
    determinant is a NONZERO rational function (so its numerator root set is a
    genuine finite zero set — Theorem A's branch (A-i) is the live branch). -/
theorem RegPin.detFull_ne_zero {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (hdet : MovesS.DetHyp C.T C.RB C.hK) (b : D.Block) :
    D.detFull b ≠ 0 := by
  rw [P.detFull_eq b]
  exact hdet (P.blk b).1 (P.blk b).2

/-! ## The zero/pole locus (Theorem A's B, as a Finset — finiteness by type) -/

/-- The zero/pole contribution of ONE block: the rational roots of the full
    determinant's reduced numerator and denominator, plus the poles (reduced-
    denominator roots) of every entry-list member. Finite BY TYPE (`roots` is a
    multiset; `Finset` union/biUnion). -/
noncomputable def blockZeroPole (Φ : RatFunc ℚ) (E : Finset (RatFunc ℚ)) : Finset ℚ :=
  Φ.num.roots.toFinset ∪ Φ.denom.roots.toFinset
    ∪ E.biUnion fun g => g.denom.roots.toFinset

theorem mem_blockZeroPole {Φ : RatFunc ℚ} {E : Finset (RatFunc ℚ)} {x : ℚ} :
    x ∈ blockZeroPole Φ E
      ↔ x ∈ Φ.num.roots ∨ x ∈ Φ.denom.roots ∨ ∃ g ∈ E, x ∈ g.denom.roots := by
  unfold blockZeroPole
  simp only [Finset.mem_union, Multiset.mem_toFinset, Finset.mem_biUnion]
  tauto

/-- B(D) — M17 Theorem A's zero/pole locus of the abstract record: the union of
    the per-block contributions over ALL blocks. A `Finset ℚ`, so Lemma 1's
    finiteness is carried by the type. -/
noncomputable def RegData.zeroPoleSet {p : ℕ} (D : RegData p) : Finset ℚ :=
  letI := D.instB
  Finset.univ.biUnion fun e : D.Block => blockZeroPole (D.detFull e) (D.entryList e)

theorem RegData.mem_zeroPoleSet {p : ℕ} {D : RegData p} {x : ℚ} :
    x ∈ D.zeroPoleSet
      ↔ ∃ e : D.Block, x ∈ blockZeroPole (D.detFull e) (D.entryList e) := by
  letI := D.instB
  unfold RegData.zeroPoleSet
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- Evaluation of a rational function = reduced numerator over reduced
    denominator, at the identity ring hom (junk value 0 at poles). -/
private theorem eval_eq_num_div_denom (g : RatFunc ℚ) (x : ℚ) :
    g.eval (RingHom.id ℚ) x = g.num.eval x / g.denom.eval x := by
  rw [RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id]

/-! ## The exact characterization (M17 Lemma 0 / Theorem A's dictionary) -/

/-- THE DICTIONARY (M17 Lemma 0 assembled; = the Codex twin's Theorem 1 at one
    record): at a pinned record, (REG-p) holds IFF no pool value lies in the
    zero/pole locus. The ⟹ direction is pin-free (a locus point kills the
    matching clause literally); the ⟸ direction consumes the pin exactly twice
    — `act_agree` (the agreement conjunct is free given definedness) and
    `detFull_ne_zero` (Φ ≠ 0, so a non-root numerator value is nonzero). -/
theorem regP_iff_pool_avoids {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (hdet : MovesS.DetHyp C.T C.RB C.hK) :
    RegP D ↔ ∀ q₀ ∈ D.Pool, (q₀ : ℚ) ∉ D.zeroPoleSet := by
  constructor
  · intro hreg q₀ hq hmem
    obtain ⟨e, he⟩ := RegData.mem_zeroPoleSet.mp hmem
    rcases mem_blockZeroPole.mp he with hnum | hden | ⟨g, hg, hgden⟩
    · have h1 := (hreg.detFull_clause hq e).2
      have hroot : (D.detFull e).num.eval (q₀ : ℚ) = 0 :=
        (Polynomial.mem_roots'.mp hnum).2
      exact h1 (by rw [eval_eq_num_div_denom, hroot, zero_div])
    · exact (hreg.detFull_clause hq e).1 (Polynomial.mem_roots'.mp hden).2
    · exact ((hreg q₀ hq e).2 g hg).1 (Polynomial.mem_roots'.mp hgden).2
  · intro havoid q₀ hq e
    have hmem : (q₀ : ℚ) ∈ blockZeroPole (D.detFull e) (D.entryList e) → False :=
      fun hc => havoid q₀ hq (RegData.mem_zeroPoleSet.mpr ⟨e, hc⟩)
    have hdefden : (D.detFull e).denom.eval (q₀ : ℚ) ≠ 0 := by
      intro h0
      exact hmem (mem_blockZeroPole.mpr (Or.inr (Or.inl
        (Polynomial.mem_roots'.mpr ⟨RatFunc.denom_ne_zero _, h0⟩))))
    have hnum : (D.detFull e).num.eval (q₀ : ℚ) ≠ 0 := by
      intro h0
      exact hmem (mem_blockZeroPole.mpr (Or.inl
        (Polynomial.mem_roots'.mpr ⟨RatFunc.num_ne_zero (P.detFull_ne_zero hdet e), h0⟩)))
    refine ⟨⟨hdefden, ?_⟩, ?_⟩
    · rw [eval_eq_num_div_denom]
      exact div_ne_zero hnum hdefden
    · intro g hg
      have hgden : g.denom.eval (q₀ : ℚ) ≠ 0 := by
        intro h0
        exact hmem (mem_blockZeroPole.mpr (Or.inr (Or.inr
          ⟨g, hg, Polynomial.mem_roots'.mpr ⟨RatFunc.denom_ne_zero _, h0⟩⟩)))
      exact ⟨hgden, P.act_agree g q₀ hgden⟩

/-- M17 Theorem A's failing form (the ∃δ, p^δ ∈ B display): ¬(REG-p) IFF some
    consumed depth δ puts the pool value p^δ in the zero/pole locus. -/
theorem not_regP_iff_exists_depth {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (hdet : MovesS.DetHyp C.T C.RB C.hK) :
    ¬ RegP D ↔ ∃ δ ∈ D.depthSet, ((p ^ δ : ℕ) : ℚ) ∈ D.zeroPoleSet := by
  rw [regP_iff_pool_avoids P hdet]
  push Not
  constructor
  · rintro ⟨q₀, hq, hmem⟩
    rw [D.pool_eq] at hq
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨δ, hδ, hmem⟩
  · rintro ⟨δ, hδ, hmem⟩
    exact ⟨p ^ δ, by rw [D.pool_eq]; exact Finset.mem_image_of_mem _ hδ, hmem⟩

/-- At a pinned record every consumed depth is positive (the depth set is the
    ℕ-image of the ℕ+-valued consumed-deltas closure). -/
theorem RegPin.depth_ne_zero {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) : ∀ δ ∈ D.depthSet, δ ≠ 0 := by
  intro δ hδ
  rw [P.depth_pin] at hδ
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hδ
  exact d.ne_zero

/-! ## M17 Lemma 2: prime-power escape -/

/-- M17 Lemma 2 (prime-power escape): a FINITE target set B ⊂ ℚ is hit by pool
    values p^δ — δ ranging over a fixed finite set of POSITIVE depths — for only
    finitely many bases p; every hitting base is bounded by the ceiling-sup of B
    (p ≤ p^δ = ⌈p^δ⌉₊ ≤ sup). Stated for arbitrary ℕ bases (primality not
    needed for finiteness). -/
theorem pow_hits_finite (B : Finset ℚ) (Δ : Finset ℕ) (hΔ : ∀ δ ∈ Δ, δ ≠ 0) :
    {p : ℕ | ∃ δ ∈ Δ, ((p ^ δ : ℕ) : ℚ) ∈ B}.Finite := by
  refine Set.Finite.subset (Set.finite_le_nat (B.sup fun x => ⌈x⌉₊)) ?_
  rintro p ⟨δ, hδ, hmem⟩
  simp only [Set.mem_setOf_eq]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact Nat.zero_le _
  calc p ≤ p ^ δ := le_self_pow hp (hΔ δ hδ)
    _ = ⌈((p ^ δ : ℕ) : ℚ)⌉₊ := (Nat.ceil_natCast _).symm
    _ ≤ B.sup fun x => ⌈x⌉₊ := Finset.le_sup hmem

/-! ## The p-UNIFORM real roster (M17 Lemma 0's (r2) roster identity)

The pins force every `entryList` family onto the REAL §S block system, which is
p-independent; so the zero/pole locus of EVERY pinned record at EVERY prime is
ONE finite set computed from the instance data. -/

/-- E(e), the REAL entry list of block e — the seven displayed families read
    directly off the §S vocabulary (exactly the `RegPin` pin targets): K entries,
    designated `verdictImage`-assembled terminal rows, `Sigmas`-assembled split
    rows (under DetHyp), the per-cell J values, entrances ι, shape weights W_Ŝ,
    and the β-legs `powSubst d (Σ_{σ'} blockSolve …)` over the ℕ+ consumed-deltas
    closure and the real `LegRoster`. p-INDEPENDENT by inspection. -/
noncomputable def realEntryList {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) (e : ℕ) (he : e ∈ Finset.Icc 1 n) :
    Finset (RatFunc ℚ) :=
  letI := Classical.decEq (RatFunc ℚ)
  (Finset.univ.image fun ij : C.T.State e × C.T.State e =>
      MovesS.Kmat C.T C.RB e (C.hK e he) ij.1 ij.2)
    ∪ (Finset.univ.image fun τ : C.T.State e =>
        ∑ σ' ∈ MovesS.verdictImage C.T e τ, MovesS.bTerm C.T C.RB e σ' τ)
    ∪ (Finset.univ.image fun τ : C.T.State e =>
        ∑ σ' ∈ C.chain.Sigmas,
          MovesS.bSplit C.T C.RB C.hdc e he
            (MovesS.blockSolveLt C.RB C.hdc C.hK hdet e) σ' τ)
    ∪ ((Finset.univ : Finset (C.T.State e)).biUnion fun τ =>
        (MovesS.splitOuts C.T e τ).biUnion fun o =>
          (C.MS.cells e τ o).image fun c => (C.RB.jPCell e τ c).val)
    ∪ (Finset.univ.image fun τ : C.T.State e => C.RB.ι e τ)
    ∪ (C.Fam.Sh.image fun Ŝ => (C.chain.WshP Ŝ).val)
    ∪ (MovesS.consumedDeltas C.T C.Fam).biUnion fun d =>
        Finset.univ.image fun r : LegRoster C.T e =>
          MovesS.powSubst d
            (∑ σ' ∈ C.chain.Sigmas,
              MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
                (legTarget C e he r).1.1 (legTarget C e he r).1.2
                (legTarget C e he r).2 σ')

/-- M17 Lemma 0's (r2) ROSTER IDENTITY: at a pinned record the abstract entry
    list IS the real entry list of the pinned block — each of the seven families
    transported along its pin (`K_pin`/`bterm_pin`/`bsplit_pin`/`Jcell_pin`/
    `iota_pin`/`W_pin`/`betaLeg_pin`+`legSt_pin`+`legEquiv`+`depth_pin`). -/
theorem RegPin.entryList_eq {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (hdet : MovesS.DetHyp C.T C.RB C.hK) (b : D.Block) :
    D.entryList b = realEntryList C hdet (P.blk b).1 (P.blk b).2 := by
  letI := Classical.decEq (RatFunc ℚ)
  letI := D.instBi b; letI := D.instBd b; letI := D.instJ b
  letI := D.instW; letI := D.instL b
  have hK : (Finset.univ.image fun ij : D.bidx b × D.bidx b => D.K b ij.1 ij.2)
      = Finset.univ.image fun ij : C.T.State (P.blk b).1 × C.T.State (P.blk b).1 =>
          MovesS.Kmat C.T C.RB (P.blk b).1 (C.hK (P.blk b).1 (P.blk b).2) ij.1 ij.2 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨(P.st b ij.1, P.st b ij.2), (P.K_pin b ij.1 ij.2).symm⟩
    · rintro ⟨ij, rfl⟩
      refine ⟨((P.st b).symm ij.1, (P.st b).symm ij.2), ?_⟩
      rw [P.K_pin b]
      simp only [Equiv.apply_symm_apply]
  have hbterm : Finset.univ.image (D.bterm b)
      = Finset.univ.image fun τ : C.T.State (P.blk b).1 =>
          ∑ σ' ∈ MovesS.verdictImage C.T (P.blk b).1 τ,
            MovesS.bTerm C.T C.RB (P.blk b).1 σ' τ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨P.st b i, (P.bterm_pin b i).symm⟩
    · rintro ⟨τ, rfl⟩
      refine ⟨(P.st b).symm τ, ?_⟩
      rw [P.bterm_pin b]
      simp only [Equiv.apply_symm_apply]
  have hbsplit : Finset.univ.image (D.bsplit b)
      = Finset.univ.image fun τ : C.T.State (P.blk b).1 =>
          ∑ σ' ∈ C.chain.Sigmas,
            MovesS.bSplit C.T C.RB C.hdc (P.blk b).1 (P.blk b).2
              (MovesS.blockSolveLt C.RB C.hdc C.hK hdet (P.blk b).1) σ' τ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨P.st b i, (P.bsplit_pin hdet b i).symm⟩
    · rintro ⟨τ, rfl⟩
      refine ⟨(P.st b).symm τ, ?_⟩
      rw [P.bsplit_pin hdet b]
      simp only [Equiv.apply_symm_apply]
  have hiota : Finset.univ.image (D.iota b)
      = Finset.univ.image fun τ : C.T.State (P.blk b).1 => C.RB.ι (P.blk b).1 τ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨P.st b i, (P.iota_pin b i).symm⟩
    · rintro ⟨τ, rfl⟩
      refine ⟨(P.st b).symm τ, ?_⟩
      rw [P.iota_pin b]
      simp only [Equiv.apply_symm_apply]
  have hbeta : (D.depthSet.biUnion fun δ =>
        Finset.univ.image fun l => D.betaLeg b l δ)
      = (MovesS.consumedDeltas C.T C.Fam).biUnion fun d =>
          Finset.univ.image fun r : LegRoster C.T (P.blk b).1 =>
            MovesS.powSubst d
              (∑ σ' ∈ C.chain.Sigmas,
                MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
                  (legTarget C (P.blk b).1 (P.blk b).2 r).1.1
                  (legTarget C (P.blk b).1 (P.blk b).2 r).1.2
                  (legTarget C (P.blk b).1 (P.blk b).2 r).2 σ') := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨δ, hδ, l, rfl⟩
      have hδ' := hδ
      rw [P.depth_pin] at hδ'
      obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hδ'
      subst hdeq
      refine ⟨d, hd, P.legEquiv b l, ?_⟩
      rw [P.betaLeg_pin hdet b l (↑d) d.pos hδ, P.legSt_pin b l]
    · rintro ⟨d, hd, r, rfl⟩
      have hmem : (d : ℕ) ∈ D.depthSet := by
        rw [P.depth_pin]; exact Finset.mem_image_of_mem _ hd
      refine ⟨(d : ℕ), hmem, (P.legEquiv b).symm r, ?_⟩
      rw [P.betaLeg_pin hdet b ((P.legEquiv b).symm r) (↑d) d.pos hmem,
        P.legSt_pin b ((P.legEquiv b).symm r), Equiv.apply_symm_apply]
  show (Finset.univ.image fun ij : D.bidx b × D.bidx b => D.K b ij.1 ij.2)
      ∪ Finset.univ.image (D.bterm b) ∪ Finset.univ.image (D.bsplit b)
      ∪ Finset.univ.image (D.Jcell b) ∪ Finset.univ.image (D.iota b)
      ∪ Finset.univ.image D.Wcoef
      ∪ (D.depthSet.biUnion fun δ => Finset.univ.image fun l => D.betaLeg b l δ)
      = _
  rw [hK, hbterm, hbsplit, hiota, hbeta, P.Jcell_pin b, P.W_pin]

/-- B, the p-UNIFORM REAL zero/pole locus (M17 Theorem A's B at the instance
    data): the union over the real blocks e ∈ [1, n] of the per-block
    contributions at Φ_e = det(1 − K_e) and E(e). One `Finset ℚ` for ALL primes. -/
noncomputable def realZeroPoleSet {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK) : Finset ℚ :=
  (Finset.Icc 1 n).attach.biUnion fun e =>
    blockZeroPole (1 - MovesS.Kmat C.T C.RB e.1 (C.hK e.1 e.2)).det
      (realEntryList C hdet e.1 e.2)

/-- The pin transports the abstract locus onto the real locus: B(D) = B for
    EVERY pinned record at EVERY prime (Lemma 0(iii)'s substrate). -/
theorem RegPin.zeroPoleSet_eq {n : ℕ} {C : UCarriers n} {p : ℕ} {D : RegData p}
    (P : RegPin C D) (hdet : MovesS.DetHyp C.T C.RB C.hK) :
    D.zeroPoleSet = realZeroPoleSet C hdet := by
  letI := D.instB
  unfold RegData.zeroPoleSet realZeroPoleSet
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_attach,
    exists_true_left]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨P.blk b, ?_⟩
    rwa [P.detFull_eq b, P.entryList_eq hdet b] at hb
  · rintro ⟨e, he⟩
    refine ⟨P.blk.symm e, ?_⟩
    rw [P.detFull_eq (P.blk.symm e), P.entryList_eq hdet (P.blk.symm e)]
    simp only [Equiv.apply_symm_apply]
    exact he

/-- M17 Lemma 0(iii), instance-independence: the truth value of (REG-p) is a
    function of (C, p) alone — any two pinned records at the same prime agree. -/
theorem regP_iff_of_pins {n : ℕ} {C : UCarriers n} {p : ℕ} {D D' : RegData p}
    (P : RegPin C D) (P' : RegPin C D') (hdet : MovesS.DetHyp C.T C.RB C.hK) :
    RegP D ↔ RegP D' := by
  rw [regP_iff_pool_avoids P hdet, regP_iff_pool_avoids P' hdet,
    P.zeroPoleSet_eq hdet, P'.zeroPoleSet_eq hdet, D.pool_eq, D'.pool_eq,
    P.depth_pin, P'.depth_pin]

/-! ## M17 Theorem A, family form -/

/-- M17 THEOREM A (exact characterization, family form): for a `RegPin`-pinned
    family of records, the (REG-p) failing-prime set IS the set of primes with
    some pool value p^δ (δ in the ℕ-image of the consumed-deltas closure) in the
    p-UNIFORM real zero/pole locus. EXACT equality, both inclusions. -/
theorem regP_failing_eq {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (Dfam : ∀ p : ℕ, p.Prime → RegData p)
    (Pfam : ∀ (p : ℕ) (hp : p.Prime), RegPin C (Dfam p hp)) :
    {p : ℕ | ∃ hp : p.Prime, ¬ RegP (Dfam p hp)}
      = {p : ℕ | p.Prime ∧ ∃ δ ∈ (MovesS.consumedDeltas C.T C.Fam).image
            (fun d : ℕ+ => (d : ℕ)),
          ((p ^ δ : ℕ) : ℚ) ∈ realZeroPoleSet C hdet} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp, hfail⟩
    obtain ⟨δ, hδ, hmem⟩ := (not_regP_iff_exists_depth (Pfam p hp) hdet).mp hfail
    rw [(Pfam p hp).depth_pin] at hδ
    rw [(Pfam p hp).zeroPoleSet_eq hdet] at hmem
    exact ⟨hp, δ, hδ, hmem⟩
  · rintro ⟨hp, δ, hδ, hmem⟩
    refine ⟨hp, (not_regP_iff_exists_depth (Pfam p hp) hdet).mpr ⟨δ, ?_, ?_⟩⟩
    · rw [(Pfam p hp).depth_pin]; exact hδ
    · rw [(Pfam p hp).zeroPoleSet_eq hdet]; exact hmem

/-- M17 THEOREM A (finiteness; = the Codex twin's Theorem 2): the failing-prime
    set of a pinned family is FINITE — the characterization above + prime-power
    escape at the positive consumed depths, every failing prime bounded by the
    ceiling-sup of the real locus. -/
theorem regP_failing_finite {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (Dfam : ∀ p : ℕ, p.Prime → RegData p)
    (Pfam : ∀ (p : ℕ) (hp : p.Prime), RegPin C (Dfam p hp)) :
    {p : ℕ | ∃ hp : p.Prime, ¬ RegP (Dfam p hp)}.Finite := by
  rw [regP_failing_eq C hdet Dfam Pfam]
  refine Set.Finite.subset (pow_hits_finite (realZeroPoleSet C hdet)
    ((MovesS.consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))) ?_) ?_
  · intro δ hδ
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hδ
    exact d.ne_zero
  · rintro p ⟨-, hδ⟩
    exact hδ

/-- M17 COROLLARY (Theorem A + Theorem B assembled, HYPOTHESIS-FREE): at any
    pinned family there is a finite set of primes outside which (REG-p) HOLDS —
    theoremU's one per-prime hypothesis is available at every prime beyond a
    finite perimeter (the applicable primes are cofinite, hence density 1).
    The DetHyp witness is `C.detHyp` (Theorem B: the chain supplies it free). -/
theorem regP_cofinite {n : ℕ} (C : UCarriers n)
    (Dfam : ∀ p : ℕ, p.Prime → RegData p)
    (Pfam : ∀ (p : ℕ) (hp : p.Prime), RegPin C (Dfam p hp)) :
    ∃ S : Set ℕ, S.Finite ∧ ∀ (p : ℕ) (hp : p.Prime), p ∉ S → RegP (Dfam p hp) := by
  refine ⟨_, regP_failing_finite C C.detHyp Dfam Pfam, ?_⟩
  intro p hp hnot
  by_contra hfail
  exact hnot ⟨hp, hfail⟩

end LeanUrat.MovesU
