/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B18
import Uniformity.ChapB.B30
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C83

/-!
# Uniformity.ChapC.C97 — TERMINAL SUPPLY: the S2 tower witness, built

**Chapter C, NODE C.97** [def+lemma] [fresh] [signed: A-C.1, fragile no. 3]
(`blueprint/CHAP-C_tower_grammar.md` §10, the GENTOW2 supply layer; twin
`leanspec/Leanspec/ChapC.lean`, the A-C.1 completion layer). **ENV-C3 (concrete).**  Four signed
declarations — `s2Frame`, `s2Frame_data`, `s2Witness`, `s2Witness_values` — plus the frame's
polygon lemmas they are built from and two pin companions.

The node the TERMINAL SUPPLY table advertises to chapter D (T1 battery check 10) and to §13's
`q = 2` regression rows: the genre `(2,1,4) → (2,1,2)` third-stage tower over `ℤ₂`-class data,
as an actual object.

* `s2Frame h2 hq : KeyFrame O 2` — the frame `Φ′ = x² − 2`, `(e₁, f₁, h) = (2, 1, 1)`, over any
  base in which `2` is irreducible (i.e. is a uniformizer);
* `s2Frame_data` — its four numerals, by `rfl`;
* `s2Witness h2 hq H₀ hpin : DeepTower (s2Frame h2 hq) H₀ hpin 3` — the depth-3 tower datum
  `(e, f, u) = (2,1,1), (2,1,5), (2,1,21)` over that frame (C.83's carrier);
* `s2Witness_values` — its stage numerals and the normalizer read `n̂₂(21) = 16Φ′`, the latter in
  C.83's exponent form `towerNorm 1 21 = (4, 0, ![1])` (`π = 2`: `2⁴·x⁰·Φ′¹`).

**The signature is the stub layer's, with `axiom` replaced by the construction.**  The A-C.1
layer parked all four as axiom CONSTANTS on the grounds that `KeyFrame`'s `hirr`/`hpure`/`hresirr`
fields at `Φ′ = x² − 2` are theorem-grade; this node discharges them, so the `#print axioms`
footprint below is Lean core throughout and nothing about C.97 is assumed.

## What is a THEOREM here, and what is DATA (read this before citing the node)

Everything in the FRAME half is theorem-grade and proved:

* `s2Key_irr` — `x² − 2` is irreducible over `O`, by **Eisenstein at the maximal ideal**
  (`2 ∈ 𝔪`, `−2 ∉ 𝔪²` because `π² ∣ π` would make `π` a unit; monic ⟹ primitive).  This is the
  one genuinely non-formal step of the node and it is not a numeral check.
* `s2Key_pure` — the `X`-adic polygon of `x² − 2` is the single side of slope `1/2`: the heights
  are `(1, ⊤, 0)` at abscissae `(0, 1, 2)` (`npHgt_X`: at the key `X` the polygon heights ARE the
  coefficient valuations, and `addVal O (−2) = 1` exactly because `2` is a uniformizer), the
  cleared support value is `2`, and both endpoints attain it.
* `s2Key_sideMin`/`s2Key_sideMax`/`s2Key_sideDeg` — the side is `{0, 2}`, so `d = 1`;
* `s2Key_resirr` — the residual is irreducible of degree `1` (B.30's `natDegree_resPoly` gives
  `natDegree = sideDeg = 1` and `coeff 0 ≠ 0`; degree one over a field is irreducible).
* `s2Frame_pin` / `s2Frame_pin_unique` — **the frame's pin is satisfiable and pins `H₀ = 1`.**
  Without these the `hpin` binder of `s2Witness` could be empty and the witness vacuous; they are
  what makes the witness a witness (the repo's honesty invariant, applied at this node).

The TOWER half is DATA satisfying C.83's constraints.  `DeepTower` carries no field tying `ψ i`
to any actual polynomial factorisation — it is `(e, f, u, ψ)` plus properness, coprimality, the
floor chain and the residue-field iterate witnesses (see C.83's own docstring, where `hfloor` is
explicitly a datum field and not a theorem).  So what `s2Witness` certifies is: **the audited
numerals `u = 1, 5, 21` with `e = 2`, `f = 1` at every stage satisfy every constraint C.83
imposes**, in particular the floor chain `5 > 2·(2·1·1) = 4` and `21 > 2·(2·1·5) = 20` — which is
tooth P-B1/B2's content and T1 battery check 10's binding inequality.  It does **not** re-derive
`Φ₂ = Φ′² − 4x`, `Φ₃ = Φ₂² − 16Φ′` or `u₃ = 21` from the polynomials: those are the numeric
gate's (blueprint finding D25/F1, four independent occurrences of `u₃ = 21`, zero disagreements),
cited here, not re-proved.

**⚠ Two faithfulness recasts, flagged for human review** (parent CLAUDE.md trust boundary):

1. *the residue tower is CONSTANT.*  `fld i` is the frame's stage field `K₁` at every `i`, and
   `base`/`step` are the identity resp. the canonical `K ≃+* AdjoinRoot (T − 1)`.  This is not a
   shortcut: `f₂ = f₃ = 1` says both upper stages are totally ramified, so `K₁ = K₂ = K₃` is what
   the corpus tower actually does at this witness.  C.83's GC-7 carrier asks exactly for the
   `RingEquiv`s, and they are the honest ones.
2. *`ψ i = T − 1` at both live rungs.*  `ψ₃^{repo} = T − 1` is the corpus's, verbatim.  `ψ₂` is
   not displayed by the STATEMENT; `f₂ = 1` plus C.83's `hψ` (monic, degree `f₃ = 1`, nonzero
   constant term) forces `ψ₂ = T − c` with `c ≠ 0`, and at residue cardinality `2` that is
   `T − 1`.  The choice is therefore forced, not free — but it IS a choice made here rather than
   read from the source, and it is recorded as such.

## The two carried hypotheses that the construction does not consume

`[Finite (ResidueField O)]` and `hq : residueCard O = 2` are the signed signature's and are kept
byte-for-byte; **neither is used**.  What the frame needs is `h2 : Irreducible (2 : O)` alone —
`2` a uniformizer.  So `s2Frame` exists over the unramified quadratic extension of `ℤ₂` as well,
where `residueCard = 4`; `hq` is the ℤ₂-class pin that C.97's CONSUMERS (the dictionary rows, the
`q = 2` regression) read, not a hypothesis of the object.  Flagged rather than dropped: the
signature is A-C.1-signed and frozen.

**DEPENDS.** C.83 (`DeepTower`, `towerNorm`, `towerSolve`) · C.42/C.43 by node ID (the depth-2
sub-instance is `DeepTower.trunc`, not re-packaged here) · C.01 (`KeyFrame`) · C.14a
(`KeyFrame.Pin`) · C.03 (`stageField`, `frameRes`) · B.15 (`npHgt_X`) · B.18
(`sideSet_nonempty`) · B.25 (`resField`, `instFieldResField`) · B.30 (`natDegree_resPoly`) —
imported.

**PROOF.** Eisenstein for `hirr`; `npHgt_X` + a three-point `inf` for `hpure`; B.30 + degree-one
irreducibility for `hresirr`; `norm_num`/`decide`-grade for every tower numeral.  (The
blueprint's PROOF line reads *"`decide`/`norm_num`-grade computation"* — that is right for the
TOWER half and understates the FRAME half, whose `hirr`/`hpure`/`hresirr` are the theorem-grade
work the A-C.1 layer flagged when it parked the node as axioms.)

**SOURCE.** `EFF.GENTOW2.05` (the dictionary's witness column with the compile-time audit table);
`EFF.GENTOW5.21` (the deeper chain `u = 5, 21, 85, 341`, the extended witness for C.83).

**TEETH.** P-W1/P-N1/P-N2 + T1 battery check 10 → the `example`s below hold the executable part
that lives at this node (the floor chain as the datum's own field, the ladder numerals, the rung
solves); §13's `q = 2` rows consume `s2Witness_values`.

**ENVIRONMENT.** ENV-C3 (concrete).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## The frame `Φ′ = x² − 2`

Everything in this section is about the single polynomial `s2Key O = X² − C 2` over a base in
which `2` is a uniformizer.  The five facts `s2Key_irr`, `s2Key_pure`, `s2Key_ne`,
`s2Key_resirr` (and the numerals feeding them) are exactly `KeyFrame`'s theorem-grade fields. -/

/-- The S2 witness's stage key `Φ′ = x² − 2` (`EFF.GENTOW2.05`). -/
noncomputable def s2Key (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Polynomial O := Polynomial.X ^ 2 - Polynomial.C 2

theorem s2Key_monic : (s2Key O).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem s2Key_natDegree : (s2Key O).natDegree = 2 := natDegree_X_pow_sub_C

theorem s2Key_coeff0 : (s2Key O).coeff 0 = -2 := by simp [s2Key]

theorem s2Key_coeff1 : (s2Key O).coeff 1 = 0 := by simp [s2Key, coeff_X_pow]

theorem s2Key_coeff2 : (s2Key O).coeff 2 = 1 := by simp [s2Key, coeff_X_pow]

/-- **`Φ′` is irreducible — EISENSTEIN at the maximal ideal.**  `𝔪 = (2)` because `2` is a
uniformizer (`Irreducible.maximalIdeal_eq`); the two lower coefficients `−2` and `0` lie in `𝔪`,
the leading coefficient `1` does not, and `−2 ∉ 𝔪² = (4)` — otherwise `2 = 4c`, whence
`2·(1 + 2c) = 0`, whence (`O` a domain, `2 ≠ 0`) `2·(−c) = 1` and `2` is a unit, contradicting
its irreducibility.  Monic ⟹ primitive supplies the last hypothesis of
`IsEisensteinAt.irreducible`. -/
theorem s2Key_irr (h2 : Irreducible (2 : O)) : Irreducible (s2Key O) := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {(2 : O)} := h2.maximalIdeal_eq
  have hE : (s2Key O).IsEisensteinAt (IsLocalRing.maximalIdeal O) := by
    constructor
    · rw [(s2Key_monic (O := O)).leadingCoeff]
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    · intro n hn
      rw [s2Key_natDegree] at hn
      interval_cases n
      · rw [s2Key_coeff0, hmax, Ideal.mem_span_singleton]; exact ⟨-1, by ring⟩
      · rw [s2Key_coeff1]; exact Submodule.zero_mem _
    · rw [s2Key_coeff0, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h0 : (2 : O) * (1 + 2 * c) = 0 := by linear_combination -hc
      rcases mul_eq_zero.mp h0 with h | h
      · exact h2.ne_zero h
      · exact h2.not_isUnit ⟨⟨2, -c, by linear_combination -h, by linear_combination -h⟩, rfl⟩
  exact hE.irreducible inferInstance (s2Key_monic).isPrimitive (by rw [s2Key_natDegree]; norm_num)

/-! ### The polygon of `Φ′` at the order-0 key `X`

`npHgt_X` (B.15) says the `X`-adic polygon heights are the coefficient valuations, so the three
heights are `addVal(−2) = 1`, `addVal 0 = ⊤`, `addVal 1 = 0`. -/

/-- height `1` at abscissa `0` — this is where `Irreducible (2 : O)` enters as
`addVal O 2 = 1`. -/
theorem s2Key_h0 (h2 : Irreducible (2 : O)) : npHgt X (s2Key O) 0 = (1 : ℕ∞) := by
  rw [npHgt_X, s2Key_coeff0, show (-2 : O) = -(2 : O) from by ring, AddValuation.map_neg,
    addVal_uniformizer h2]

/-- height `⊤` at abscissa `1`: `Φ′` has no `x`-term, so abscissa `1` is off the polygon. -/
theorem s2Key_h1 : npHgt X (s2Key O) 1 = (⊤ : ℕ∞) := by
  rw [npHgt_X, s2Key_coeff1, AddValuation.map_zero]

/-- height `0` at abscissa `2`: `Φ′` is monic. -/
theorem s2Key_h2 : npHgt X (s2Key O) 2 = (0 : ℕ∞) := by
  rw [npHgt_X, s2Key_coeff2, AddValuation.map_one]

/-- the cleared support value at the slope `h/e₁ = 1/2` is `2`: the three cleared terms are
`2·1 + 0 = 2`, `2·⊤ + 1 = ⊤`, `2·0 + 2 = 2`. -/
theorem s2Key_supp (h2 : Irreducible (2 : O)) : suppVal X (s2Key O) 1 2 = (2 : ℕ∞) := by
  rw [suppVal, s2Key_natDegree, show Finset.range 3 = {0, 1, 2} from rfl]
  simp [s2Key_h0 h2, s2Key_h1, s2Key_h2]

/-- **`Φ′` is `(1,2)`-pure**: both endpoints of the abscissa range `0 … 2` attain the support
value, i.e. the polygon is the single side of slope `−1/2`. -/
theorem s2Key_pure (h2 : Irreducible (2 : O)) : IsPure X (s2Key O) 1 2 := by
  have hdd : (s2Key O).natDegree / (X : Polynomial O).natDegree = 2 := by
    simp [s2Key_natDegree]
  refine ⟨?_, ?_⟩
  · rw [OnSide, s2Key_h0 h2, s2Key_supp h2]; simp
  · rw [hdd, OnSide, s2Key_h2, s2Key_supp h2]; simp

theorem s2Key_ne : (sideSet X (s2Key O) 1 2).Nonempty :=
  sideSet_nonempty (μ := 2) monic_X (by simp) s2Key_monic (by simp [s2Key_natDegree]) 1 2

theorem s2Key_zero_mem (h2 : Irreducible (2 : O)) : 0 ∈ sideSet X (s2Key O) 1 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp [s2Key_natDegree]), ?_⟩
  exact (s2Key_pure h2).1

theorem s2Key_two_mem (h2 : Irreducible (2 : O)) : 2 ∈ sideSet X (s2Key O) 1 2 := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp [s2Key_natDegree]), ?_⟩
  have := (s2Key_pure h2).2
  rwa [show (s2Key O).natDegree / (X : Polynomial O).natDegree = 2 from by
    simp [s2Key_natDegree]] at this

theorem s2Key_sideMin (h2 : Irreducible (2 : O)) :
    sideMin X (s2Key O) 1 2 s2Key_ne = 0 :=
  Nat.le_zero.mp (Finset.min'_le _ 0 (s2Key_zero_mem h2))

theorem s2Key_sideMax (h2 : Irreducible (2 : O)) :
    sideMax X (s2Key O) 1 2 s2Key_ne = 2 := by
  classical
  refine le_antisymm ?_ (Finset.le_max' _ 2 (s2Key_two_mem h2))
  have hmem : sideMax X (s2Key O) 1 2 s2Key_ne ∈ sideSet X (s2Key O) 1 2 :=
    Finset.max'_mem _ _
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  rw [s2Key_natDegree] at h
  omega

/-- the side has residual degree `d = (2 − 0)/2 = 1`, which is the frame's `f₁`. -/
theorem s2Key_sideDeg (h2 : Irreducible (2 : O)) :
    sideDeg X (s2Key O) 1 2 s2Key_ne = 1 := by
  rw [sideDeg, s2Key_sideMax h2, s2Key_sideMin h2]

/-- **the pin numeral**: the polygon height at the side's left endpoint is `1`, so the GC-1 pin
of this frame is `H₀ = 1` and nothing else (`s2Frame_pin_unique`). -/
theorem s2Key_pinHgt (h2 : Irreducible (2 : O)) :
    npHgt X (s2Key O) (sideMin X (s2Key O) 1 2 s2Key_ne) = (1 : ℕ∞) := by
  rw [s2Key_sideMin h2, s2Key_h0 h2]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- **the frame's residual read is irreducible of degree `1`.**  B.30's `natDegree_resPoly`
supplies `natDegree = sideDeg = 1` together with `coeff 0 ≠ 0`; a degree-one polynomial over the
field `resField X` is irreducible. -/
theorem s2Key_resirr (h2 : Irreducible (2 : O)) (H₀ : ℕ)
    (hH : npHgt X (s2Key O) (sideMin X (s2Key O) 1 2 s2Key_ne) = (H₀ : ℕ∞)) :
    Irreducible (resPoly (2 : O) X (s2Key O) 1 2 s2Key_ne H₀) ∧
      (resPoly (2 : O) X (s2Key O) 1 2 s2Key_ne H₀).natDegree = 1 := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have htop : suppVal X (s2Key O) 1 2 ≠ ⊤ := by rw [s2Key_supp h2]; exact ENat.coe_ne_top 2
  obtain ⟨hdeg, hc0⟩ :=
    natDegree_resPoly h2 isKey_X (by norm_num) (Nat.coprime_one_left 2) htop s2Key_ne hH
  rw [s2Key_sideDeg h2] at hdeg
  have hne0 : resPoly (2 : O) X (s2Key O) 1 2 s2Key_ne H₀ ≠ 0 := fun hz => hc0 (by rw [hz]; simp)
  exact ⟨irreducible_of_degree_eq_one ((degree_eq_iff_natDegree_eq hne0).mpr hdeg), hdeg⟩

/-! ## NODE C.97 (i)–(ii) — the frame -/

-- `hq` and `[Finite (ResidueField O)]` are the signed signature's and are unused by the
-- construction; see the module docstring's "two carried hypotheses" section.
set_option linter.unusedVariables false in
/-- **NODE C.97 (i) — the S2 stage key frame.**  `Φ′ = x² − 2` with `(e₁, f₁, h) = (2, 1, 1)`
over any base in which `2` is a uniformizer.  Every theorem-grade field is discharged above:
`hirr` is Eisenstein (`s2Key_irr`), `hpure` is the slope-`1/2` single side (`s2Key_pure`),
`hresirr` is B.30 plus degree-one irreducibility (`s2Key_resirr`). -/
noncomputable def s2Frame [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) : KeyFrame O (2 : O) where
  e₁ := 2
  f₁ := 1
  h := 1
  key := s2Key O
  he₁ := by norm_num
  hf₁ := by norm_num
  hcop := by simp [Nat.Coprime]
  hmonic := s2Key_monic
  hdeg := by rw [s2Key_natDegree]
  hirr := s2Key_irr h2
  hpure := s2Key_pure h2
  hne := s2Key_ne
  hresirr := fun H₀ hH => s2Key_resirr h2 H₀ hH

/-- **NODE C.97 (ii) — the frame's four numerals**, all by `rfl`. -/
theorem s2Frame_data [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) :
    (s2Frame h2 hq).e₁ = 2 ∧ (s2Frame h2 hq).f₁ = 1 ∧ (s2Frame h2 hq).h = 1 ∧
      (s2Frame h2 hq).key = Polynomial.X ^ 2 - Polynomial.C 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The pin is satisfiable, and pins `H₀ = 1`

These two are what keep `s2Witness` from being vacuous: its `hpin` binder is inhabited, at
exactly one numeral. -/

/-- **the pin exists**: `s2Frame` is pinned at `H₀ = 1`. -/
theorem s2Frame_pin [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) : (s2Frame h2 hq).Pin 1 :=
  s2Key_pinHgt h2

/-- **the pin is unique**: any `H₀` pinning `s2Frame` is `1`. -/
theorem s2Frame_pin_unique [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) {H₀ : ℕ} (hpin : (s2Frame h2 hq).Pin H₀) : H₀ = 1 := by
  have h := (s2Key_pinHgt h2).symm.trans hpin
  exact_mod_cast h.symm

/-! ## NODE C.97 (iii)–(iv) — the depth-3 tower -/

/-- the `Field` structure on the frame's stage field `K₁`, from `hresirr` (C.03's `stageField` is
`AdjoinRoot (frameRes …)`, a field exactly because the frame residual is irreducible).  Reducible
so that the `CommRing` it induces is the ambient `AdjoinRoot` one. -/
@[reducible] noncomputable def s2StageFieldInst [Finite (ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) (H₀ : ℕ)
    (hpin : (s2Frame h2 hq).Pin H₀) : Field ((s2Frame h2 hq).stageField H₀ hpin) :=
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible ((s2Frame h2 hq).frameRes H₀ hpin)) :=
    ⟨((s2Frame h2 hq).hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- **NODE C.97 (iii) — THE S2 TOWER WITNESS**, the concrete depth-3 `DeepTower` over `s2Frame`:
stages `(e, f, u) = (2,1,1), (2,1,5), (2,1,21)`, residue tower constant at `K₁` (both upper
stages are totally ramified — `f₂ = f₃ = 1`), residuals `ψ = T − 1`.

The floor chain is the datum's `hfloor` at these numerals: `2·(2·1·1) = 4 < 5` and
`2·(2·1·5) = 20 < 21`.  See the module docstring for the two recorded faithfulness recasts (the
constant residue tower; `ψ₂ = T − 1` forced by `f₂ = 1` and `hψ`). -/
noncomputable def s2Witness [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    DeepTower (s2Frame h2 hq) H₀ hpin 3 :=
  letI : Field ((s2Frame h2 hq).stageField H₀ hpin) := s2StageFieldInst h2 hq H₀ hpin
  { e := fun _ => 2
    f := fun _ => 1
    u := fun i => if i = 1 then 1 else if i = 2 then 5 else 21
    fld := fun _ => (s2Frame h2 hq).stageField H₀ hpin
    fldField := fun _ => s2StageFieldInst h2 hq H₀ hpin
    ψ := fun _ => Polynomial.X - Polynomial.C 1
    he1 := rfl
    hf1 := rfl
    hu1 := rfl
    he := fun i _ _ => by norm_num
    hf := fun i _ _ => by norm_num
    hproper := fun i _ _ => by norm_num
    hcop := fun i hi hi' => by interval_cases i <;> decide
    hfloor := fun i hi hi' => by interval_cases i <;> norm_num
    hψ := fun i _ _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, natDegree_X_sub_C 1, by
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, ne_eq, neg_eq_zero]
      exact one_ne_zero⟩
    base := RingEquiv.refl _
    step := fun i _ _ => (Polynomial.quotientSpanXSubCAlgEquiv (1 : _)).toRingEquiv.symm }

/-- **NODE C.97 (iv) — the witness's signed value clauses.**  The two upper stages' `(e, f, u)`,
and the normalizer read `n̂₂(21) = 16Φ′` in C.83's exponent form: `towerNorm 1 21 = (4, 0, ![1])`
is `π⁴·x⁰·Φ′¹` at `π = 2`, i.e. `2⁴Φ′ = 16Φ′`.

The `towerNorm` leg is a genuine computation, not a `rfl`: the rung solve is
`towerSolve 5 2 21 = 1` (so `b = 1`), the carried remainder is `(21 − 1·5)/2 = 8`, the frame slot
is `slotIdx 8 = 0` (`e₁ = 2`, `h = 1`), and the `π`-exponent is `(8 − 0)/2 = 4`. -/
theorem s2Witness_values [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).e 2 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 2 = 1 ∧
      (s2Witness h2 hq H₀ hpin).u 2 = 5 ∧
      (s2Witness h2 hq H₀ hpin).e 3 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 3 = 1 ∧
      (s2Witness h2 hq H₀ hpin).u 3 = 21 ∧
      (s2Witness h2 hq H₀ hpin).towerNorm 1 21 = (4, 0, fun _ => 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hu2 : (s2Witness h2 hq H₀ hpin).u (0 + 2) = 5 := rfl
  have he2 : (s2Witness h2 hq H₀ hpin).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  have hb : towerSolve 5 2 21 = 1 := rfl
  have hsl : (s2Frame h2 hq).slotIdx 8 = 0 := by
    change ((List.range 2).find? (fun i => (i * 1) % 2 == 8 % 2)).getD 0 = 0
    rfl
  simp only [DeepTower.towerNorm, hu2, he2, hh, he1, hb]
  norm_num [hsl, Prod.ext_iff]
  funext j
  fin_cases j
  rfl

end Uniformity.Density.Tower

/-! ## Teeth — the executable part that lives at this node

P-W1/P-N1/P-N2 and T1 battery check 10 read the floor chain and the ladder numerals off the
witness.  The three ladder values `4, 10, 21` appear here as `ê₂ = e₁e₂`, `E₂ = e₂f₂u₂` and
`u₃`; their identification with the `dv₂`-weights of `(x, Φ′, Φ₂)` is the numeric gate's reading
(blueprint finding D25/F1) and is NOT asserted by these checks. -/

section Teeth

open IsLocalRing Uniformity.Density Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- the floor chain, read off the datum's own `hfloor` field at the two live rungs:
`e₂·E₁ = 2·(2·1·1) = 4 < 5 = u₂` and `e₃·E₂ = 2·(2·1·5) = 20 < 21 = u₃`. -/
example [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (4 : ℕ) < 5 ∧ (20 : ℕ) < 21 :=
  ⟨(s2Witness h2 hq H₀ hpin).hfloor 1 (by norm_num) (by norm_num),
    (s2Witness h2 hq H₀ hpin).hfloor 2 (by norm_num) (by norm_num)⟩

/-- the ladder numerals `[4, 10, 21]` as the witness's own bookkeeping: `ê₂ = 4`, `E₂ = 10`,
`u₃ = 21`. -/
example [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).ehat 2 = 4 ∧ (s2Witness h2 hq H₀ hpin).Econst 2 = 10 ∧
      (s2Witness h2 hq H₀ hpin).u 3 = 21 := by
  refine ⟨?_, rfl, rfl⟩
  change ∏ _j ∈ Finset.Icc 1 2, (2 : ℕ) = 4
  decide

/-- the rung solves of this witness's chain (`towerSolve` at `(u_{i+1}, e_{i+1})`): the height
jumps by an odd multiple at each stage, so `b = 1` at every rung. -/
example : towerSolve 5 2 21 = 1 := by decide

end Teeth

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.s2Key
#print axioms Uniformity.Density.Tower.s2Key_irr
#print axioms Uniformity.Density.Tower.s2Key_pure
#print axioms Uniformity.Density.Tower.s2Key_resirr
#print axioms Uniformity.Density.Tower.s2Frame
#print axioms Uniformity.Density.Tower.s2Frame_data
#print axioms Uniformity.Density.Tower.s2Frame_pin
#print axioms Uniformity.Density.Tower.s2Frame_pin_unique
#print axioms Uniformity.Density.Tower.s2Witness
#print axioms Uniformity.Density.Tower.s2Witness_values

end AxCheck
