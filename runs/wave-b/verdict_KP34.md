# Verdict — unit KP34 (nodes KP-3 + KP-4, CORES 3–4/4 — `key_criterion` CLOSED)

**COMPLETE.** One new file `leanfinal/Uniformity/ChapC/C130kp3.lean`, built green
(`lake build Uniformity.ChapC.C130kp3`, 8751 jobs), zero `sorry`, all 10 `#print axioms`
footprints Lean-core `{propext, Classical.choice, Quot.sound}`. Imports C130kp1 only
(everything else transitively).

## NODE KP-3 — μ-minimality at the recipe degree (honest hypothesis set WORKED OUT)

* ★ `s2MuMinimal_of_not_isUnit_normRes` — the engine, at the set the proof forces:
  `0 < deg g ≤ 4` + `¬ IsUnit (R₃ g)` → `S2MuMinimal g`. **NO monicity, NO grade data, NO
  odd-carry case analysis needed**: any nonzero `f` of degree `< deg g ≤ 4` has a UNIT
  residual (KP-1's degree law `s2NormRes_isUnit_of_natDegree_lt_four`), and KP-1's
  UNIVERSAL forward translation would make the non-unit `R₃(g)` divide a unit. (The
  brief's named tools — the odd-carry engine and the degree law — are consumed here
  PRE-PACKAGED inside those two KP-1 lemmas.)
* ★ `s2MuMinimal_of_irreducible_normRes` — the row form: `deg g = 4` + `Irreducible (R₃ g)`
  → μ₂-minimal.
* **The degree-4 trichotomy, machine-witnessed** (the fences):
  ★ `tooth_kp3_needs_nonunit` — naked "monic + degree 4 → minimal" is FALSE: `Φ′² + Φ′`
  is monic, degree 4, UNIT residual (`∼µ₂ Φ′`, so `R₃ = 1`), yet μ₂-divides the
  degree-two `Φ′` with cofactor `1`. `not_S2MuDvd_of_gradedRes_coeff_zero` — the SECOND
  mechanism (trailing scalar death: zero top-grade scalar on `φ` kills every `R(φ·q)`
  scalar vs RP-7's nonzero low-degree scalar); by it `s2MuMinimal_key_sq` — `Φ′²`
  (unit residual!) IS minimal, so `¬ IsUnit` is sufficient-not-necessary. Bonus:
  `tooth_key_sq_not_muIrreducible` — `Φ′²` divides `Φ′·Φ′` but neither factor: minimal
  ≠ key, the criterion's Irreducible hypothesis is not decorative.

## NODE KP-4 — the literal frontier field, CLOSED

* ★★ `s2_key_criterion` — the C130fg `key_criterion` / A-C.11 `KP_criterion` hypothesis
  list at the landed `r = 1` anchoring (`(e',f') = (2,1)`, recipe degree
  `2·1·deg Φ′ = 4`): monic → degree → `Irreducible (R₃ g)` → `deg R₃(g) = 1` →
  `(R₃ g)(0) ≠ 0` → `S2KeyPoly g`. Assembly exactly as briefed: monic given, KP-3's
  minimality, KP-2's `s2_key_criterion_muIrreducible`.
* ★★ **crown**: `s2KeyPoly_lift : S2KeyPoly (Φ′² + 4x)` — RP-12's lift IS a key
  polynomial (published Thm 5.7's construction machine-closed end to end); spelled at
  `(x²−2)² + 4x` as `s2KeyPoly_lift_spelled`.
* ★ **FD-0 pin** `s2_key_criterion_fills`: for any
  `S : FGMNSourceData (s2DepthTwo) K 2 1 5` with `normalizedResidual := s2NormRes`,
  `keyPolynomial := S2KeyPoly`, the field shape holds with the degree binder at
  `K.keyAt 1` (tied to `Φ′` by the chain's own `keyAt_one`) — zero residual assembly
  work. **Anchoring note (RP-11's standing course correction applied)**: the pin reads
  `keyAt 1`, NOT the tower-literal `keyAt 2` (whose numeral `2·1·4 = 8` is KP-6's row and
  is out of KP-3's method — above degree 4 low-degree cofactors lose unit residuals).

## Honesty scope / flags

No `keyAt 2` field instance (KP-6), no `FGMNSourceData/Laws/ChainRealization` instance
(FD-0), no `initial_iff_residual` (KP-7..9), no `key_irreducible` (KP-5), no minimality
above degree 4. Flagged for human review (new statements): KP-3's honest hypothesis set,
the trichotomy teeth, `s2_key_criterion`, the crown, and the pin's `keyAt 1` anchoring.
