# Verdict — RP1112 (S2-source plan nodes RP-11/RP-12)

**Deliverable:** `leanfinal/Uniformity/ChapC/C130rp11.lean` (new file). `lake build
Uniformity.ChapC.C130rp11` green; every declaration Lean-core only
(`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom, no `unsafe`, no
existing file/statement touched.

**Course correction (recorded, not silently absorbed):** the row's own "degree-eight"
framing reads the recipe at `r = 2` (`keyAt 2 = composedKey`); `C130rp0`'s own docstring
is explicit that the landed `s2Hgt₂`/`s2GradedRes`/`s2NormRes` realize `nextValue := μ₂`,
i.e. `r = 1` with `K.keyAt r = Φ′` (degree `2`) — matching RP-8's own precedent of
realizing `carried_key_residual`'s genre at `Φ′`, not the literal `keyAt 2`. At `r = 1`,
`e'f'·deg(Φ′) = 4`, not `8`.

**Second correction:** the field's printed `khat` grade `(f'-t)u' = 5` is machine-checked
VACUOUS against the degree fence (`s2_recipe_naive_numeral_vacuous`: a short digit's
cleared grade is always even, `5` is odd). The non-vacuous S2 realization needs grade `10`
(`= e'·u'`, a true tie with the leading term `Φ′·Φ′`) — exactly the calibration RP-2's
already-landed `tooth_C4X_grade`/`tooth_sum_exact`/`tooth_gradedRes_add_exact` teeth use.

**RP-11 landed:** `s2_normalized_recipe` — for any `khat` with `S2ExactGrade 10 khat` and
`natDegree < 2`, `s2NormRes(Φ′·Φ′ − khat) = X − C((s2GradedRes 10 khat).coeff 0)`, proved
symbolically from RP-2's strong ADD law, RP-1's zero-of-above law, RP-8's scalar
nonvanishing and `s2NormRes_of_exact`, and a new char-2 negation identity.

**RP-12 landed:** `s2_unique_admissible_linear` (`X+1` is the unique monic linear `K₂`
poly with nonzero constant term) + `s2_normalized_exists` — the explicit degree-4 monic
lift `g := Φ′·Φ′ + 4x` has `s2NormRes g = X+1`, assembled from RP-2's landed C4X teeth as
the `khat := 4x` instance of RP-11; packaged in the `normalized_exists` field shape
(`Monic`, `Irreducible`, `natDegree = f' = 1`, `coeff 0 ≠ 0` all discharged, including a
standalone `Irreducible (X+1)` witness).

**Honesty scope:** no literal instance of `C130fg`'s printed numerals (see corrections
above); no `FGMNSourceData`/`Laws` instance (FD-0); OPEN-DICT-2's clearing dictionary is
still open (it would confirm or replace the factor-of-`e'` correction). Flagged for human
review: the two course corrections, and the four ★ headline theorems.
