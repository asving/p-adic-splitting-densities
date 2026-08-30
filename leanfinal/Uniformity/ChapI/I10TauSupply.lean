/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10Suppliers

/-!
# Uniformity.ChapI.I10TauSupply — TWD: the tau-word/descent supply at general witnesses
(rows C3 + R5 of the deepTwist boundary) [TWD 2026-08-30]

**Unit TWD** — the vartheta half of the capstone `deepTwist` boundary after USUP: the two
missing fields of the C3 record, `CanonicalTauWordAt` (row C3, "triangular spanning") and
`CanonicalGeneratorDescent` (row R5, OPEN-LETTERS), scoped and discharged at general
residue cardinality where derivable.

## The scope verdict (charge 1)

* **Row C3 is a LATTICE statement in disguise.**  The demanded tau classes are the
  normalizer two-cocycle `τ(a,b) = n̂(a)·n̂(b)·n̂(a+b)⁻¹` (D02's `NormSection.tau` at the
  transported arena section); under the canonical-read plumbing
  (`canonicalResFamily → canonicalResAt → canonicalRes0 → canonicalRead ∘ kerLevelProj0`)
  its value is the read of a LEVEL-`j` kernel element.  Since the read of any
  distinguished-generator word is already the demanded word shape (C130cr's landed
  `canonicalRead_generatorWord`), row C3 follows from: *the level kernel is spanned by
  the distinguished generators* (`wrapClass`, `letterClass`) — a statement in the exponent
  lattice in which the residue field NEVER appears.  What the keystone's card-2 collapse
  bought was the READ side (the level-3 read is constantly `1`); the uniform replacement
  is the lattice-side spanning, uniform in `q`.
* **The spanning CLOSES for the concrete normalizer.**  For
  `DeepTower.laurentNormalizer` (the CC-4 greedy digit solve), the triangular-basis
  bridge that freeze v2 §4 left OPEN is a theorem (`laurentNormalizer_kernelSpan`
  below): induction on the level — the top digit of any kernel element is divisible by
  `e_{i+2}` (coprimality `gcd(u_{i+2}, e_{i+2}) = 1`), peeling the top letter `Λ_top`
  lands in the top-zero sublattice, which is the level-`(i+1)` lattice (heights scale
  exactly by `e_{i+2}`), and the level-1 kernel is exactly `⟨W₀⟩` by
  `gcd(e₁, u₁) = 1`.  Uniform in `q`, every tower, every stage-live level.
* **The spanning does NOT close for the abstract normalizer field.**
  `ChainRealization.normalizer` demands only `norm_zero` + `exact_height`, and the letter
  classes depend on it: twisting the canonical norm word at the single top letter height
  by the kernel element `Λ_top` (still exact-height) replaces `Λ_top` by `Λ_top²`, whose
  span `⟨W₀, Λ_top²⟩` has index 2 in the level kernel — so `KernelSpanAt` is genuinely
  falsifiable across the abstract field, and no proof from the realization interface
  alone can exist.  The honest per-realization remainder is the named lattice `Prop`
  `KernelSpanAt` — closed by an `rfl`-side condition whenever the realization is built
  with the canonical normalizer, as EVERY landed witness is
  (`s2LaurentNormalizerFour := (s2DepthFour h2 hq).laurentNormalizer`).
* **Row R5 splits.**  `CanonicalGeneratorDescent` = wrap clause + letter clauses.  The
  letter clauses follow from field-level preimages through the terminal embedding — in
  particular from the `DeepLevelExport.letter_receiver` receiver equalities (the site-tied
  shape the campaign already owns), via the landed `letter_descent_of_receiver_eq`.  The
  wrap clause (`WrapDescentAt` below) is the irreducible OPEN-LETTERS remainder: no landed
  law ties `wrapValue = canonicalRead (x^{e₁}π^{−u₁})` to any site letter or receiver
  value, and this unit claims NO reduction for it.

## What lands (charges 2/3)

* **§1 the spanning engine** (namespace `Uniformity.Density.Tower`): `levelSnocHom` (the
  top-zero inclusion of exponent lattices), its `wrapGen`/`keyLetter`/`laurentNormAt`
  transport laws, and ★ `DeepTower.laurentNormalizer_kernelSpan` — every level-kernel
  element is a distinguished-generator word for the concrete Laurent normalizer.  THE
  general-depth triangular spanning, uniform in `q`.
* **§2 the C3 reduction** (namespace `Uniformity.Density.DeepExport`): `KernelSpanAt`
  (NEW Prop — the lattice remainder, universe-free), ★
  `canonicalTauWordAt_of_kernelSpan` (row C3 from the lattice Prop alone, every arising
  realization), `kernelSpanAt_of_laurent` (the remainder CLOSES at canonical-normalizer
  realizations).
* **§3 the R5 dissection**: `WrapDescentAt` (NEW Prop — R5's wrap clause, named),
  `canonicalGeneratorDescent_of_wrap_letterPreimages` (field-level entry point) and
  `canonicalGeneratorDescent_of_wrap_letterReceiver` (the site-tied consolidation:
  letter clauses from `letter_receiver`-shape equalities; R5's Lean remainder = wrap +
  the receiver equalities the site record already targets).
* **§4 the supply compilations**: ★ `tauWordDescentSupply_of_laurent_descent` — USUP's
  per-witness vartheta supply from (normalizer = canonical) + descent alone: row C3 is
  ELIMINATED from the boundary at every canonical-normalizer realization.  Universal
  forms `UniversalKernelSpan`/`UniversalGeneratorDescent` and their compilation into
  USUP's `UniversalTauWordDescentSupply`.
* **§5 keystone coherence**: the keystone's normalizer is the canonical one by `rfl`;
  `s2Four_canonicalTauWordAt_uniform` re-derives the keystone's `tau_word` through the
  GENERAL spanning route — the card-2 collapse is machine-checkedly REPLACED, not merely
  matched — and `s2Four_tauWordDescentSupply'` re-derives USUP's keystone supply.

## Honesty scope

The vartheta half does NOT fully close.  Open after this unit, per arising realization
and deep-live level: (1) `KernelSpanAt` at realizations whose normalizer is NOT the
concrete Laurent solve (no such realization is landed; the Prop is refutable for
adversarial abstract normalizers, so this is the exact honest boundary, not a deferral);
(2) `WrapDescentAt` (R5's wrap clause) and the letter receiver equalities (R5's letter
clauses at the site dictionary) — OPEN-LETTERS content, precisely as USUP graded it.
No statement is weakened; the landed record shapes are consumed verbatim.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`KernelSpanAt`, `WrapDescentAt`, `UniversalKernelSpan`, `UniversalGeneratorDescent`
(supplier-side interface `Prop`s below the signed surface; no leanspec name touched).

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_TWD.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

/-! ## §1 The spanning engine: the concrete Laurent normalizer spans the level kernels -/

namespace Uniformity.Density.Tower

open scoped BigOperators
open Uniformity.Density.Leaf

universe uG uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- `Fin.snoc · 0` sends the zero tuple to the zero tuple. -/
theorem snoc_zero_int (i : ℕ) :
    (Fin.snoc (0 : Fin i → ℤ) (0 : ℤ) : Fin (i + 1) → ℤ) = 0 := by
  funext x
  refine Fin.lastCases ?_ (fun a => ?_) x
  · rw [Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc]
    rfl

/-- `Fin.snoc · 0` is additive in the tuple. -/
theorem snoc_add_int (i : ℕ) (f g : Fin i → ℤ) :
    (Fin.snoc (f + g) (0 : ℤ) : Fin (i + 1) → ℤ) =
      Fin.snoc f (0 : ℤ) + Fin.snoc g (0 : ℤ) := by
  funext x
  refine Fin.lastCases ?_ (fun a => ?_) x
  · simp only [Pi.add_apply, Fin.snoc_last]
    rw [add_zero]
  · simp only [Pi.add_apply, Fin.snoc_castSucc]

/-- **[TWD §1] The top-zero inclusion of exponent lattices**: the level-`(i+1)` Laurent
lattice into the level-`(i+2)` lattice, appending exponent `0` at the new top letter
`Φ_{i+1}`.  The multiplicative form of `Fin.snoc · 0`. -/
def levelSnocHom (i : ℕ) :
    LevelExponentLattice (i + 1) →* LevelExponentLattice (i + 2) where
  toFun g :=
    Multiplicative.ofAdd
      ((Multiplicative.toAdd g).1, (Multiplicative.toAdd g).2.1,
        Fin.snoc (Multiplicative.toAdd g).2.2 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show (Fin.snoc (0 : Fin i → ℤ) (0 : ℤ) : Fin (i + 1) → ℤ) = 0
    exact snoc_zero_int i
  map_mul' g g' := by
    apply Multiplicative.toAdd.injective
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show (Fin.snoc ((Multiplicative.toAdd g).2.2 + (Multiplicative.toAdd g').2.2) (0 : ℤ) :
        Fin (i + 1) → ℤ) =
      Fin.snoc (Multiplicative.toAdd g).2.2 (0 : ℤ) +
        Fin.snoc (Multiplicative.toAdd g').2.2 (0 : ℤ)
    exact snoc_add_int i _ _

/-- Anti-drift pin: the inclusion is `Fin.snoc · 0` on exponents, nothing else. -/
theorem levelSnocHom_ofAdd (i : ℕ) (v : ℤ × ℤ × (Fin i → ℤ)) :
    levelSnocHom i (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (v.1, v.2.1, Fin.snoc v.2.2 0) := rfl

/-- The greedy solve at a multiple of the top rung: the top digit is `0` and the residual
descends exactly — `laurentSolve (i+1) (e_{i+2}·x)` is the level-down solve of `x` with a
`0` appended. -/
theorem DeepTower.laurentSolve_e_mul (T : DeepTower F H₀ hpin r) (i : ℕ)
    (he : 0 < T.e (i + 2)) (x : ℤ) :
    T.laurentSolve (i + 1) ((T.e (i + 2) : ℤ) * x) =
      ((T.laurentSolve i x).1, (T.laurentSolve i x).2.1,
        Fin.snoc (T.laurentSolve i x).2.2 0) := by
  have hne : (T.e (i + 2) : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  simp only [laurentSolve, Int.mul_emod_right, Int.toNat_zero, towerSolve_zero,
    Nat.cast_zero, zero_mul, sub_zero, Int.mul_ediv_cancel_left x hne]

/-- The lattice form: the level-`(i+2)` Laurent norm word at a top-rung multiple is the
included level-`(i+1)` word. -/
theorem DeepTower.laurentNormAt_e_mul (T : DeepTower F H₀ hpin r) (i : ℕ)
    (he : 0 < T.e (i + 2)) (x : ℤ) :
    T.laurentNormAt (i + 2) ((T.e (i + 2) : ℤ) * x) =
      levelSnocHom i (T.laurentNormAt (i + 1) x) := by
  show Multiplicative.ofAdd (T.laurentSolve (i + 1) ((T.e (i + 2) : ℤ) * x)) = _
  rw [T.laurentSolve_e_mul i he x]
  rfl

/-- The wrap generator is stable under the top-zero inclusion. -/
theorem levelSnocHom_wrapGen (T : DeepTower F H₀ hpin r) (i : ℕ) :
    levelSnocHom i (T.wrapGen (i + 1)) = T.wrapGen (i + 2) := by
  show Multiplicative.ofAdd
      (-(T.u 1 : ℤ), (T.e 1 : ℤ), (Fin.snoc (0 : Fin i → ℤ) (0 : ℤ) : Fin (i + 1) → ℤ)) = _
  rw [snoc_zero_int]
  rfl

/-- `Fin.snoc · 0` sends a `Pi.single` to the `Pi.single` at the cast index. -/
theorem snoc_single_int (i : ℕ) (a : Fin i) :
    (Fin.snoc (Pi.single a (1 : ℤ)) (0 : ℤ) : Fin (i + 1) → ℤ) =
      Pi.single a.castSucc (1 : ℤ) := by
  funext x
  refine Fin.lastCases ?_ (fun b => ?_) x
  · rw [Fin.snoc_last, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne']
  · rw [Fin.snoc_castSucc]
    rcases eq_or_ne b a with rfl | hne
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hne,
        Pi.single_eq_of_ne (fun h => hne (Fin.castSucc_injective _ h))]

/-- The key letters transport along the top-zero inclusion via `Fin.castSucc`. -/
theorem levelSnocHom_keyLetter (i : ℕ) (a : Fin i) :
    levelSnocHom i (keyLetter (i + 1) a) = keyLetter (i + 2) a.castSucc := by
  show Multiplicative.ofAdd ((0 : ℤ), (0 : ℤ),
      (Fin.snoc (Pi.single a (1 : ℤ)) (0 : ℤ) : Fin (i + 1) → ℤ)) = _
  rw [snoc_single_int]
  rfl

/-- The exact-height scaling of the non-top letter heights: one level up, the letter
height `e_{a+2}·(ê/ê_{a+2})·u_{a+2}` scales by exactly `e_{i+2}`. -/
theorem DeepTower.letterHeight_e_mul (T : DeepTower F H₀ hpin r) {i : ℕ} (a : Fin i) :
    (T.e (a.1 + 2) : ℤ) *
        ((T.ehat (i + 2) : ℤ) / (T.ehat (a.1 + 2) : ℤ) * (T.u (a.1 + 2) : ℤ)) =
      (T.e (i + 2) : ℤ) *
        ((T.e (a.1 + 2) : ℤ) *
          ((T.ehat (i + 1) : ℤ) / (T.ehat (a.1 + 2) : ℤ) * (T.u (a.1 + 2) : ℤ))) := by
  have hdvd : T.ehat (a.1 + 2) ∣ T.ehat (i + 1) := T.ehat_dvd (by omega)
  rw [T.natCast_ehat_div_succ hdvd]
  ring

/-- Anti-drift pin: the concrete normalizer's word IS the Laurent solve. -/
theorem DeepTower.laurentNormalizer_norm (T : DeepTower F H₀ hpin r) :
    T.laurentNormalizer.norm = T.laurentNormAt := rfl

/-- The letter classes of the CONCRETE Laurent normalizer transport along the top-zero
inclusion: `ι(Λ_a^{(i+1)}) = Λ_{castSucc a}^{(i+2)}`. -/
theorem DeepTower.levelSnocHom_letterClass (T : DeepTower F H₀ hpin r) {i : ℕ}
    (hi1 : StageLive r (i + 1)) (hi2 : StageLive r (i + 2)) (a : Fin i) :
    levelSnocHom i
        ((T.laurentNormalizer.letterClass hi1 a : LevelExponentLattice (i + 1))) =
      ((T.laurentNormalizer.letterClass hi2 a.castSucc :
        LevelExponentLattice (i + 2))) := by
  rw [LaurentNormalizer.letterClass_coe, LaurentNormalizer.letterClass_coe]
  rw [map_mul, map_inv, map_pow, levelSnocHom_keyLetter]
  simp only [Fin.val_castSucc]
  rw [DeepTower.laurentNormalizer_norm, T.letterHeight_e_mul a,
    T.laurentNormAt_e_mul i (T.he (i + 2) (by omega) hi2.2)]

/-- The TOP letter class of the concrete Laurent normalizer, resolved: the key power
`Φ_{i+1}^{e_{i+2}}` against the included level-down norm word at height `u_{i+2}`. -/
theorem DeepTower.letterClass_top_coe (T : DeepTower F H₀ hpin r) {i : ℕ}
    (hi : StageLive r (i + 2)) :
    ((T.laurentNormalizer.letterClass hi (Fin.last i) :
        LevelExponentLattice (i + 2))) =
      keyLetter (i + 2) (Fin.last i) ^ T.e (i + 2) *
        (levelSnocHom i (T.laurentNormAt (i + 1) (T.u (i + 2))))⁻¹ := by
  have hpos : (0 : ℤ) < (T.ehat (i + 2) : ℤ) := by exact_mod_cast T.ehat_pos hi.2
  rw [LaurentNormalizer.letterClass_coe, DeepTower.laurentNormalizer_norm]
  simp only [Fin.val_last]
  rw [Int.ediv_self hpos.ne', one_mul,
    T.laurentNormAt_e_mul i (T.he (i + 2) (by omega) hi.2)]

/-- `heightAux` is additive in the exponent tuple. -/
theorem DeepTower.heightAux_add (T : DeepTower F H₀ hpin r) (i : ℕ)
    (v w : ℤ × ℤ × (Fin i → ℤ)) :
    T.heightAux i (v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2) =
      T.heightAux i v + T.heightAux i w := by
  unfold DeepTower.heightAux
  simp only [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- `heightAux` commutes with integer scaling of the exponent tuple. -/
theorem DeepTower.heightAux_zsmul (T : DeepTower F H₀ hpin r) (i : ℕ) (c : ℤ)
    (v : ℤ × ℤ × (Fin i → ℤ)) :
    T.heightAux i (c * v.1, c * v.2.1, c • v.2.2) = c * T.heightAux i v := by
  unfold DeepTower.heightAux
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun a _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

/-- The wrap generator's integer powers, additively. -/
theorem DeepTower.wrapGen_zpow (T : DeepTower F H₀ hpin r) (i : ℕ) (m : ℤ) :
    T.wrapGen i ^ m =
      Multiplicative.ofAdd
        (-(m * (T.u 1 : ℤ)), m * (T.e 1 : ℤ), (0 : Fin (i - 1) → ℤ)) := by
  rw [DeepTower.wrapGen, ← ofAdd_zsmul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show m • (-(T.u 1 : ℤ)) = -(m * (T.u 1 : ℤ))
    rw [zsmul_eq_mul, Int.cast_id]
    ring
  · show m • ((T.e 1 : ℤ)) = m * (T.e 1 : ℤ)
    rw [zsmul_eq_mul, Int.cast_id]
  · show m • (0 : Fin (i - 1) → ℤ) = 0
    rw [smul_zero]

/-- Generator words with a snoc-split exponent, along the top-zero inclusion:
`word(m, snoc t c) = ι(word(m, t)) · Λ_top^c` — the multiplicative recursion the spanning
induction assembles with. -/
theorem DeepTower.generatorWord_snoc (T : DeepTower F H₀ hpin r) {k : ℕ}
    (h1 : StageLive r (k + 1)) (h2 : StageLive r (k + 2)) (m : ℤ) (t : Fin k → ℤ)
    (c : ℤ) :
    ((T.laurentNormalizer.generatorWord h2 m (Fin.snoc t c) :
        LevelExponentLattice (k + 2))) =
      levelSnocHom k
          ((T.laurentNormalizer.generatorWord h1 m t : LevelExponentLattice (k + 1))) *
        ((T.laurentNormalizer.letterClass h2 (Fin.last k) :
          LevelExponentLattice (k + 2))) ^ c := by
  rw [LaurentNormalizer.generatorWord, LaurentNormalizer.generatorWord]
  simp only [MulMemClass.coe_mul, SubgroupClass.coe_zpow, SubmonoidClass.coe_finsetProd,
    map_mul, map_zpow, map_prod, DeepTower.wrapClass_coe, levelSnocHom_wrapGen,
    T.levelSnocHom_letterClass h1 h2]
  have hsplit : ∀ F : Fin (k + 2 - 1) → LevelExponentLattice (k + 2),
      (∏ a, F a) = (∏ a : Fin k, F a.castSucc) * F (Fin.last k) := fun F =>
    Fin.prod_univ_castSucc F
  rw [hsplit]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [mul_assoc]
  rfl

/-- The additive assembly step of the spanning induction: peeling the top-letter power
`Λ_top^c` off a tuple whose top exponent is `e_{k+2}·c` leaves exactly the included
descended tuple. -/
theorem DeepTower.span_assemble (T : DeepTower F H₀ hpin r) {k : ℕ}
    (v : ℤ × ℤ × (Fin (k + 1) → ℤ)) (c : ℤ)
    (hc : v.2.2 (Fin.last k) = (T.e (k + 2) : ℤ) * c) :
    Multiplicative.ofAdd v =
      levelSnocHom k (Multiplicative.ofAdd
        (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
         v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
         Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2)) *
        (keyLetter (k + 2) (Fin.last k) ^ T.e (k + 2) *
          (levelSnocHom k (T.laurentNormAt (k + 1) (T.u (k + 2) : ℤ)))⁻¹) ^ c := by
  apply Multiplicative.toAdd.injective
  show v =
    (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
     v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
     Fin.snoc (Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2) (0 : ℤ)) +
    c • ((T.e (k + 2)) • ((0 : ℤ), (0 : ℤ), Pi.single (Fin.last k) (1 : ℤ)) +
      -((T.laurentSolve k (T.u (k + 2) : ℤ)).1, (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
        Fin.snoc (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2 (0 : ℤ)))
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show v.1 = v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1 +
      c • ((T.e (k + 2)) • (0 : ℤ) + -((T.laurentSolve k (T.u (k + 2) : ℤ)).1))
    rw [smul_zero, zero_add, zsmul_eq_mul, Int.cast_id]
    ring
  · show v.2.1 = v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1 +
      c • ((T.e (k + 2)) • (0 : ℤ) + -((T.laurentSolve k (T.u (k + 2) : ℤ)).2.1))
    rw [smul_zero, zero_add, zsmul_eq_mul, Int.cast_id]
    ring
  · funext x
    show v.2.2 x =
      (Fin.snoc (Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2) (0 : ℤ) :
        Fin (k + 1) → ℤ) x +
        c • ((T.e (k + 2)) • ((Pi.single (Fin.last k) (1 : ℤ) : Fin (k + 1) → ℤ) x) +
          -((Fin.snoc (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2 (0 : ℤ) :
            Fin (k + 1) → ℤ) x))
    refine Fin.lastCases ?_ (fun a => ?_) x
    · rw [Fin.snoc_last, Fin.snoc_last, Pi.single_eq_same, hc, zsmul_eq_mul, Int.cast_id,
        nsmul_eq_mul]
      ring
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc,
        Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]
      simp only [Fin.init, Pi.add_apply, Pi.smul_apply, smul_zero, zero_add]
      simp only [zsmul_eq_mul, Int.cast_id]
      ring

/-- ★ **[TWD §1] THE TRIANGULAR SPANNING, auxiliary form** — every element of the
level-`(i+1)` kernel is a distinguished-generator word of the CONCRETE Laurent
normalizer.  Freeze v2 §4's OPEN triangular-basis bridge, closed for the canonical
normalizer: induction on the level; the top exponent of a kernel element is divisible by
`e_{i+2}` (coprimality of the rung), peeling `Λ_top` lands in the top-zero copy of the
level-`(i+1)` lattice, whose heights scale exactly by `e_{i+2}`; the level-1 kernel is
`⟨W₀⟩` by the frame coprimality.  Uniform in the residue cardinality — no residue
arithmetic occurs. -/
theorem DeepTower.laurentGeneratorSpan_aux (T : DeepTower F H₀ hpin r) :
    ∀ i : ℕ, (hi : i + 1 ≤ r) → ∀ g : LevelExponentLattice (i + 1),
      levelExponentHeight T (i + 1) g = 1 →
      ∃ (m : ℤ) (t : Fin i → ℤ),
        g = (T.laurentNormalizer.generatorWord ⟨Nat.le_add_left 1 i, hi⟩ m t :
          LevelExponentLattice (i + 1)) := by
  intro i
  induction i with
  | zero =>
      intro hi g hg
      have hrepr : ∃ v : ℤ × ℤ × (Fin 0 → ℤ), g = Multiplicative.ofAdd v :=
        ⟨Multiplicative.toAdd g, rfl⟩
      obtain ⟨v, hgv⟩ := hrepr
      rw [hgv] at hg
      rw [hgv]
      clear hgv
      have hadd : T.heightAux 0 v = 0 := by
        have h1 : levelExponentHeight T (0 + 1) (Multiplicative.ofAdd v)
            = Multiplicative.ofAdd (T.heightAux 0 v) := rfl
        rw [h1] at hg
        exact ofAdd_eq_one.mp hg
      have he1 : (0 : ℕ) < T.e 1 := by rw [T.he1]; exact F.he₁
      have he1Z : ((T.e 1 : ℤ)) ≠ 0 := by exact_mod_cast he1.ne'
      have hlin : v.1 * (T.e 1 : ℤ) + v.2.1 * (T.u 1 : ℤ) = 0 := by
        have h2 := hadd
        unfold DeepTower.heightAux at h2
        rw [Fin.sum_univ_zero, add_zero,
          show ((T.ehat (0 + 1) : ℕ) : ℤ) = (T.e 1 : ℤ) by exact_mod_cast T.ehat_one,
          Int.ediv_self he1Z, one_mul] at h2
        exact h2
      have hcopZ : IsCoprime ((T.e 1 : ℤ)) ((T.u 1 : ℤ)) := by
        rw [T.he1, T.hu1]
        exact (Nat.isCoprime_iff_coprime.mpr F.hcop).symm
      have hdvd : ((T.e 1 : ℤ)) ∣ v.2.1 :=
        hcopZ.dvd_of_dvd_mul_right ⟨-v.1, by linear_combination hlin⟩
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨m, fun a => a.elim0, ?_⟩
      have hword : T.laurentNormalizer.generatorWord ⟨Nat.le_add_left 1 0, hi⟩ m
          (fun a => a.elim0) = T.wrapClass ⟨Nat.le_add_left 1 0, hi⟩ ^ m := by
        rw [LaurentNormalizer.generatorWord]
        have h0 : ∀ f : Fin (0 + 1 - 1) → MonoidHom.ker (levelExponentHeight T (0 + 1)),
            (∏ a, f a) = 1 := fun f => Fin.prod_univ_zero f
        rw [h0, mul_one]
      rw [hword, SubgroupClass.coe_zpow, T.wrapClass_coe, T.wrapGen_zpow]
      refine congrArg Multiplicative.ofAdd ?_
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show v.1 = -(m * (T.u 1 : ℤ))
        have h3 : v.1 * (T.e 1 : ℤ) = -(m * (T.u 1 : ℤ)) * (T.e 1 : ℤ) := by
          rw [hm] at hlin
          linear_combination hlin
        exact mul_right_cancel₀ he1Z h3
      · show v.2.1 = m * (T.e 1 : ℤ)
        rw [hm]
        ring
      · show v.2.2 = 0
        funext a
        exact a.elim0
  | succ k ih =>
      intro hi g hg
      have hk1 : k + 1 ≤ r := by omega
      have hk2 : k + 2 ≤ r := hi
      have hrepr : ∃ v : ℤ × ℤ × (Fin (k + 1) → ℤ), g = Multiplicative.ofAdd v :=
        ⟨Multiplicative.toAdd g, rfl⟩
      obtain ⟨v, hgv⟩ := hrepr
      rw [hgv] at hg
      rw [hgv]
      clear hgv
      have hadd : T.heightAux (k + 1) v = 0 := by
        have h2 : Multiplicative.ofAdd (T.heightAux (k + 1) v) = 1 := hg
        exact ofAdd_eq_one.mp h2
      have hveq : ((v.1, v.2.1, Fin.snoc (Fin.init v.2.2) (v.2.2 (Fin.last k))) :
          ℤ × ℤ × (Fin (k + 1) → ℤ)) = v := by
        refine Prod.ext rfl (Prod.ext rfl ?_)
        show Fin.snoc (Fin.init v.2.2) (v.2.2 (Fin.last k)) = v.2.2
        exact Fin.snoc_init_self v.2.2
      have hsplit : T.heightAux (k + 1) v =
          (T.e (k + 2) : ℤ) * T.heightAux k (v.1, v.2.1, Fin.init v.2.2) +
            v.2.2 (Fin.last k) * (T.u (k + 2) : ℤ) := by
        conv_lhs => rw [← hveq]
        exact T.heightAux_snoc hk2 (v.1, v.2.1, Fin.init v.2.2) (v.2.2 (Fin.last k))
      have he2 : 0 < T.e (k + 2) := T.he (k + 2) (by omega) hk2
      have he2Z : ((T.e (k + 2) : ℤ)) ≠ 0 := by exact_mod_cast he2.ne'
      have hcopZ : IsCoprime ((T.e (k + 2) : ℤ)) ((T.u (k + 2) : ℤ)) :=
        (Nat.isCoprime_iff_coprime.mpr (T.hcop (k + 2) (by omega) hk2)).symm
      have hdvd : ((T.e (k + 2) : ℤ)) ∣ v.2.2 (Fin.last k) := by
        refine hcopZ.dvd_of_dvd_mul_right
          ⟨-(T.heightAux k (v.1, v.2.1, Fin.init v.2.2)), ?_⟩
        rw [hsplit] at hadd
        linear_combination hadd
      obtain ⟨c, hc⟩ := hdvd
      have hs : T.heightAux k (T.laurentSolve k (T.u (k + 2) : ℤ)) = (T.u (k + 2) : ℤ) :=
        T.laurentSolve_exact k hk1 _
      have hlow : T.heightAux k
          (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
           v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
           Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2) = 0 := by
        have hz := T.heightAux_zsmul k c (T.laurentSolve k (T.u (k + 2) : ℤ))
        have hsum : T.heightAux k
            (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
             v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
             Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2) =
            T.heightAux k (v.1, v.2.1, Fin.init v.2.2) +
              c * T.heightAux k (T.laurentSolve k (T.u (k + 2) : ℤ)) := by
          rw [← hz]
          exact T.heightAux_add k (v.1, v.2.1, Fin.init v.2.2)
            (c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
             c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
             c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2)
        rw [hsum, hs]
        rw [hsplit, hc] at hadd
        exact mul_left_cancel₀ he2Z (by linear_combination hadd)
      obtain ⟨m, t, hword⟩ := ih hk1 (Multiplicative.ofAdd
        (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
         v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
         Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2))
        (by
          show Multiplicative.ofAdd (T.heightAux k
            (v.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).1,
             v.2.1 + c * (T.laurentSolve k (T.u (k + 2) : ℤ)).2.1,
             Fin.init v.2.2 + c • (T.laurentSolve k (T.u (k + 2) : ℤ)).2.2)) = 1
          rw [hlow]
          rfl)
      refine ⟨m, Fin.snoc t c, ?_⟩
      show Multiplicative.ofAdd v =
        ((T.laurentNormalizer.generatorWord
          (⟨Nat.le_add_left 1 (k + 1), hk2⟩ : StageLive r (k + 2)) m (Fin.snoc t c) :
            LevelExponentLattice (k + 2)))
      rw [T.generatorWord_snoc ⟨Nat.le_add_left 1 k, hk1⟩
        ⟨Nat.le_add_left 1 (k + 1), hk2⟩ m t c, ← hword,
        T.letterClass_top_coe ⟨Nat.le_add_left 1 (k + 1), hk2⟩]
      exact T.span_assemble v c hc

/-- ★★ **[TWD §1] THE TRIANGULAR SPANNING** (bundled form): at every stage-live level,
every level-kernel element IS a distinguished-generator word of the concrete Laurent
normalizer `T.laurentNormalizer`. -/
theorem DeepTower.laurentNormalizer_kernelSpan (T : DeepTower F H₀ hpin r) {i : ℕ}
    (hi : StageLive r i) (z : MonoidHom.ker (levelExponentHeight T i)) :
    ∃ (m : ℤ) (t : Fin (i - 1) → ℤ), z = T.laurentNormalizer.generatorWord hi m t := by
  have h1 : 1 ≤ i := hi.1
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, t, hz⟩ := T.laurentGeneratorSpan_aux j hi.2 (z : LevelExponentLattice (j + 1))
    (MonoidHom.mem_ker.mp z.2)
  exact ⟨m, t, Subtype.ext (by rw [hz])⟩

end Uniformity.Density.Tower

/-! ## §2–§4 The per-realization reduction and the supply compilations -/

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

section Suppliers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}

/-- **[TWD §2] The lattice remainder of row C3, named** — the level-`j` kernel of the
realization's own tower is spanned by the realization's distinguished-generator words.
A statement in the exponent lattice ONLY: no residue field, no read, no universe
parameters beyond the realization's.  Implied by `Aℛ.normalizer = core.T.laurentNormalizer`
(`kernelSpanAt_of_laurent`); refutable for adversarial abstract normalizers, so this is
the exact honest per-realization boundary of row C3.  NEW STATEMENT (review). -/
def KernelSpanAt
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop :=
  ∀ z : MonoidHom.ker (levelExponentHeight core.T j),
    ∃ (m : ℤ) (t : Fin (j - 1) → ℤ), z = Aℛ.normalizer.generatorWord hj.stageLive m t

/-- **[TWD §2] The lattice remainder CLOSES at canonical-normalizer realizations** —
whenever the realization's normalizer is the concrete Laurent solve (as at every landed
witness), `KernelSpanAt` holds at every gauge-live level, by the §1 spanning theorem. -/
theorem kernelSpanAt_of_laurent
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (hN : Aℛ.normalizer = core.T.laurentNormalizer)
    (j : ℕ) (hj : GaugeLive core.r j) : KernelSpanAt Aℛ j hj := by
  intro z
  rw [hN]
  exact core.T.laurentNormalizer_kernelSpan hj.stageLive z

variable {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
  (hpin := core.hpin) core.T Kt E L}

/-- The generic form of the landed keystone step: at a gauge-live level the exported read
FAMILY value is the `canonicalResAt` value, through the view's `KernelRead` equality
(both memberships carried as hypotheses, as in `s2Four_canonicalResFamily_eq_one`). -/
theorem canonicalResFamily_eq_canonicalResAt (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j) {x : GaugeLattice.{uG} core.r}
    (hx : x ∈ MonoidHom.ker (gaugeHeightFamily X j))
    (hx' : x ∈ MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
      GaugeLattice.{uG} core.r →* Multiplicative ℤ)) :
    canonicalResFamily X j ⟨x, hx⟩ = canonicalResAt X hj ⟨x, hx'⟩ :=
  kernelRead_snd_congr ((X.gaugeFamilyViewEq.2 j hj).1) hx hx'

/-- ★ **[TWD §2] ROW C3 FROM THE LATTICE ALONE** — `CanonicalTauWordAt` at every arising
realization from `KernelSpanAt`: the demanded tau class is the transported two-cocycle,
whose canonical-read value is the read of a level-`j` kernel element (the view's
`KernelRead` equality + the `canonicalRes` plumbing); spanning rewrites that element as a
generator word, and the landed `canonicalRead_generatorWord` produces exactly the
demanded word in `wrapValue`/`letterValue`.  Uniform in the residue cardinality: the
card-2 collapse is replaced, not reused. -/
theorem canonicalTauWordAt_of_kernelSpan (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j) (hspan : KernelSpanAt Aℛ j hj) :
    CanonicalTauWordAt.{uG, uKt, uL} X j hj := by
  intro s
  have hmem' :
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau
          ((s : ℤ) * useHeightFamily X j) (useHeightFamily X j) ∈
        MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
          GaugeLattice.{uG} core.r →* Multiplicative ℤ) :=
    canonical_tau_mem X hj _ _
  obtain ⟨m, t, hword⟩ := hspan
    (kerLevelProj0 core.T ⟨j, hj⟩ (kerGaugeEquiv core.T ⟨j, hj⟩ ⟨_, hmem'⟩))
  refine ⟨m, t, (canonicalResFamily_eq_canonicalResAt X hj
    (canonical_tau_mem_family X hj _ _) hmem').trans ?_⟩
  show Aℛ.node.canonicalRead j
      (kerLevelProj0 core.T ⟨j, hj⟩ (kerGaugeEquiv core.T ⟨j, hj⟩ ⟨_, hmem'⟩)) = _
  rw [hword]
  exact Aℛ.node.canonicalRead_generatorWord Aℛ.normalizer hj.stageLive m t

/-- **[TWD §3] Row R5's wrap clause, named** — the canonical wrap value descends to
`Ktˣ`.  This is `CanonicalGeneratorDescent.wrap` extracted: the irreducible OPEN-LETTERS
remainder of row R5 (no landed law ties `wrapValue` to any site letter or receiver
value; this unit claims NO reduction for it).  NEW STATEMENT (review). -/
def WrapDescentAt
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop :=
  ∃ u : Ktˣ, Aℛ.node.wrapValue hj.stageLive = unitAlgebraMap u

/-- **[TWD §3] R5 from wrap + field-level letter preimages** — the full
`CanonicalGeneratorDescent` from `WrapDescentAt` and a `Kt`-preimage of each letter value
through the terminal embedding (the landed `letter_descent_of_receiver_eq` upgrades each
field-level preimage to a unit-level descent). -/
theorem canonicalGeneratorDescent_of_wrap_letterPreimages {j : ℕ}
    (hj : GaugeLive core.r j) (hwrap : WrapDescentAt Aℛ j hj)
    (hletter : ∀ a : Fin (j - 1), ∃ x : Kt,
      algebraMap Kt L x =
        ((Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a : Lˣ) : L)) :
    CanonicalGeneratorDescent Aℛ j hj where
  wrap := hwrap
  letter := fun a => by
    obtain ⟨x, hx⟩ := hletter a
    exact letter_descent_of_receiver_eq hx

/-- **[TWD §3] R5's letter clauses consolidate into the site's receiver equalities** —
given any wired-site export `S` at a deep-live level, the `DeepLevelExport.letter_receiver`
equalities (the shape the campaign's site record already targets) discharge R5's letter
clauses; the remainder of row R5 is then `WrapDescentAt` + those equalities, ONE shape
instead of two. -/
theorem canonicalGeneratorDescent_of_wrap_letterReceiver {X : RealizedInput core Aℛ}
    {j : ℕ} (hj : DeepLive core.r j)
    (S : WleClearedLevelExport.{0, uG, uKt, uL} X j hj.2.le)
    (hwrap : WrapDescentAt Aℛ j hj.gaugeLive)
    (hlr : ∀ a : Fin (j - 1),
      algebraMap Kt L (Aℛ.receiver.levelHom j (S.calculus.letterZ (a.1 + 2))) =
        ((Aℛ.node.letterValue Aℛ.normalizer hj.gaugeLive.stageLive a : Lˣ) : L)) :
    CanonicalGeneratorDescent Aℛ j hj.gaugeLive :=
  canonicalGeneratorDescent_of_wrap_letterPreimages hj.gaugeLive hwrap fun a =>
    ⟨Aℛ.receiver.levelHom j (S.calculus.letterZ (a.1 + 2)), hlr a⟩

/-- **[TWD §4] The per-witness vartheta supply from spanning + descent** — USUP's
`TauWordDescentSupply` from the two named remainders at every deep-live level. -/
theorem tauWordDescentSupply_of_span_descent (X : RealizedInput core Aℛ)
    (hspan : ∀ j, (hj : DeepLive core.r j) → KernelSpanAt Aℛ j hj.gaugeLive)
    (hdesc : ∀ j, (hj : DeepLive core.r j) → CanonicalGeneratorDescent Aℛ j hj.gaugeLive) :
    TauWordDescentSupply.{uG, uKt, uL} X := fun j hj =>
  ⟨canonicalTauWordAt_of_kernelSpan X hj.gaugeLive (hspan j hj), hdesc j hj⟩

/-- ★ **[TWD §4] ROW C3 ELIMINATED AT CANONICAL-NORMALIZER REALIZATIONS** — the
per-witness vartheta supply from `Aℛ.normalizer = core.T.laurentNormalizer` (a
construction-time `rfl` at every landed witness) + descent alone.  After this theorem the
vartheta half's open boundary at such realizations is row R5 ONLY. -/
theorem tauWordDescentSupply_of_laurent_descent (X : RealizedInput core Aℛ)
    (hN : Aℛ.normalizer = core.T.laurentNormalizer)
    (hdesc : ∀ j, (hj : DeepLive core.r j) → CanonicalGeneratorDescent Aℛ j hj.gaugeLive) :
    TauWordDescentSupply.{uG, uKt, uL} X :=
  tauWordDescentSupply_of_span_descent X
    (fun j hj => kernelSpanAt_of_laurent Aℛ hN j hj.gaugeLive) hdesc

end Suppliers

/-! ## §4b The universal forms -/

/-- **[TWD §4] The universal spanning supply**: `KernelSpanAt` at every arising
realization of degree `n`, every deep-live level.  NEW STATEMENT (review). -/
def UniversalKernelSpan (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    ∀ j, (hj : DeepLive core.r j) → KernelSpanAt Aℛ j hj.gaugeLive

/-- **[TWD §4] The universal descent supply**: row R5 at every arising realization of
degree `n`, every deep-live level.  NEW STATEMENT (review). -/
def UniversalGeneratorDescent (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    ∀ j, (hj : DeepLive core.r j) → CanonicalGeneratorDescent Aℛ j hj.gaugeLive

/-- ★ **[TWD §4] The universal compilation** — USUP's `UniversalTauWordDescentSupply`
from the two universal remainders; through USUP's ★ `deepTwistField_of_supplies`, the
capstone `deepTwist` field's vartheta half now rests on `UniversalKernelSpan` (closed
pointwise at canonical-normalizer realizations) + `UniversalGeneratorDescent` (row R5). -/
theorem universalTauWordDescentSupply_of_span_descent {n : ℕ}
    (hs : UniversalKernelSpan.{uKt, uL} n)
    (hd : UniversalGeneratorDescent.{uKt, uL} n) :
    UniversalTauWordDescentSupply.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X
  exact tauWordDescentSupply_of_span_descent X (hs O Kt E L core Aℛ X)
    (hd O Kt E L core Aℛ X)

/-! ## §5 Keystone coherence: the wired genre through the GENERAL route -/

section Wired

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- **[TWD §5] The keystone's normalizer IS the canonical one**, definitionally — the
side condition of `tauWordDescentSupply_of_laurent_descent` at the wired genre is `rfl`. -/
theorem s2Four_normalizer_eq_laurent :
    (s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer
      = (s2DepthFour h2 hq).laurentNormalizer := rfl

/-- ★ **[TWD §5] The keystone's `tau_word` clause through the GENERAL spanning route** —
`CanonicalTauWordAt` at every depth-4 keystone witness, derived from
`laurentNormalizer_kernelSpan` with NO use of the card-2 collapse
(`s2CanonicalReadFour3_eq_one` does not occur): the uniform mechanism machine-checkedly
REPLACES what `q = 2` bought. -/
theorem s2Four_canonicalTauWordAt_uniform (hj : GaugeLive 4 3) :
    CanonicalTauWordAt.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) 3 hj :=
  canonicalTauWordAt_of_kernelSpan _ hj
    (kernelSpanAt_of_laurent _ (s2Four_normalizer_eq_laurent h2 hq L w₁ w₂ w₃ w₄) 3 hj)

/-- **[TWD §5] USUP's keystone tau supply, re-derived through the general route**
(coherence pin: the supply route and the landed card-2 route agree on the wired genre). -/
theorem s2Four_tauWordDescentSupply' :
    TauWordDescentSupply.{uG, 0, uL}
      (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop) :=
  tauWordDescentSupply_of_laurent_descent _
    (s2Four_normalizer_eq_laurent h2 hq L w₁ w₂ w₃ w₄)
    (fun j hj => by
      have hj' : 3 ≤ j ∧ j < 4 := hj
      have hj3 : j = 3 := by omega
      subst hj3
      exact s2Four_canonicalGeneratorDescent h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg
        hblock hcop hj.gaugeLive)

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.Tower.levelSnocHom
#print axioms Uniformity.Density.Tower.DeepTower.laurentSolve_e_mul
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormAt_e_mul
#print axioms Uniformity.Density.Tower.levelSnocHom_wrapGen
#print axioms Uniformity.Density.Tower.levelSnocHom_keyLetter
#print axioms Uniformity.Density.Tower.DeepTower.letterHeight_e_mul
#print axioms Uniformity.Density.Tower.DeepTower.levelSnocHom_letterClass
#print axioms Uniformity.Density.Tower.DeepTower.letterClass_top_coe
#print axioms Uniformity.Density.Tower.DeepTower.laurentGeneratorSpan_aux
#print axioms Uniformity.Density.Tower.DeepTower.laurentNormalizer_kernelSpan
#print axioms Uniformity.Density.DeepExport.KernelSpanAt
#print axioms Uniformity.Density.DeepExport.kernelSpanAt_of_laurent
#print axioms Uniformity.Density.DeepExport.canonicalTauWordAt_of_kernelSpan
#print axioms Uniformity.Density.DeepExport.WrapDescentAt
#print axioms Uniformity.Density.DeepExport.canonicalGeneratorDescent_of_wrap_letterPreimages
#print axioms Uniformity.Density.DeepExport.canonicalGeneratorDescent_of_wrap_letterReceiver
#print axioms Uniformity.Density.DeepExport.tauWordDescentSupply_of_span_descent
#print axioms Uniformity.Density.DeepExport.tauWordDescentSupply_of_laurent_descent
#print axioms Uniformity.Density.DeepExport.UniversalKernelSpan
#print axioms Uniformity.Density.DeepExport.UniversalGeneratorDescent
#print axioms Uniformity.Density.DeepExport.universalTauWordDescentSupply_of_span_descent
#print axioms Uniformity.Density.DeepExport.s2Four_normalizer_eq_laurent
#print axioms Uniformity.Density.DeepExport.s2Four_canonicalTauWordAt_uniform
#print axioms Uniformity.Density.DeepExport.s2Four_tauWordDescentSupply'

end AxCheck
