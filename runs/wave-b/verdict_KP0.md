# Verdict — unit KP0R (relaunch of node KP-0, initial-form predicates)

**COMPLETE.** One new file `leanfinal/Uniformity/ChapC/C130kp0.lean` (S2-source plan node
KP-0), built green (`lake build Uniformity.ChapC.C130kp0`, 8747 jobs), zero `sorry`, all 32
`#print axioms` footprints Lean-core `{propext, Classical.choice, Quot.sound}`. Imports
C130rp8 only.

## Increment 1 — the four honest predicates (published FGMN Def 1.2 / Def 1.4, at μ₂)

Anchored per the RP chain's decided realization (`nextValue := μ₂ = s2Hgt₂` at `r = 1`,
key `Φ′ = x² − 2`; C130rp0's docstring + C130rp11's course correction):

* `S2InitialEquiv g h` — Def 1.2's value criterion: `µ₂(g−h) > µ₂(g) = µ₂(h) ∨ (g = 0 ∧ h = 0)`
  (U12 `MuEquiv` prototype shape; C130fg `initialEquiv` field byte-shape, shape-pinned).
* `S2MuDvd φ g` — Def 1.2's factor criterion `∃ q, g ∼µ₂ φ·q` (U12 `MuDivides` shape).
* `S2MuMinimal φ` — Def 1.2 verbatim, INCLUDING the printed `deg φ > 0` clause.
* `S2MuIrreducible φ` — "nonzero prime ideal" rendered through `S2MuDvd`: `φ ≠ 0` ∧
  `¬ φ ∣µ₂ 1` ∧ homogeneous primality; fidelity argument recorded in the module docstring.
* `S2KeyPoly φ` — Def 1.4: monic ∧ minimal ∧ irreducible (C130fg `keyPolynomial` byte-shape).

## Increment 2 — the basic bank

Full equivalence bank (`refl`/`symm`/`trans`/`Equivalence` package), value preservation
(`S2InitialEquiv_hgt_eq`), zero laws both sides, exact-grade + `s2GradeOf` transport,
`s2Hgt₂_neg`, `s2GradedRes_neg_of_le`. ★ **The graded-piece characterization is a genuine
IFF** (`S2InitialEquiv_iff_gradedRes`): at a common exact grade β, `g ∼µ₂ h ↔ R_β(g) =
R_β(h)` (forward: RP-2 strong add + RP-1 vanishing-above; backward: exact-grade
nonvanishing + negation trick). Tie to `s2NormRes`: `s2NormRes_eq_of_initialEquiv`
(`g ∼µ₂ h → R₃(g) = R₃(h)` — the KP-7 genre's forward direction, no KP hypothesis needed;
converse for key polys stays at KP-8/KP-9). `S2MuDvd` basics: plain-dvd ⇒ µ-dvd, self,
zero, `∼µ₂`-congruence in the dividend.

## Increment 3 — teeth

* `S2ExactGrade_even_of_natDegree_lt_two` — short digits sit at EVEN grade (general-β form
  of C130rp11's vacuity parity computation).
* ★ `not_S2MuDvd_key_of_even_grade` — the odd-carry engine: at even grade with nonzero
  residual scalar, `Φ′ ∤µ₂ g` (any `Φ′·q` forces odd `µ₂(q)`, so RP-4's carry `y` kills the
  scalar).
* ★ `s2MuMinimal_key` — **`Φ′` is µ₂-minimal, machine-proved** (the minimality clause of
  Prop 1.7(4)'s carried-key status); spelled at `x² − 2` too; `¬ Φ′ ∣µ₂ 1` corollary;
  `s2KeyPoly_key_of_muIrreducible` names the exact remaining gap (primality = KP-2's row,
  NOT claimed).
* Lift teeth at RP-12's landed degree-four witness `Φ′² + 4x` (composed-key GENRE; literal
  `keyAt 2` is KP-6): `Φ′ ∣µ₂ Φ′²`; ★ `¬ (Φ′² ∼µ₂ Φ′² + 4x)` (proper-augmentation/MacLane
  genre, residuals `X ≠ X + 1`); ★ `Φ′ ∤µ₂ Φ′² + 4x` (engine at grade 10); positive tooth
  `Φ′² ∼µ₂ Φ′² + 4x·Φ′` (higher-grade perturbation is invisible).

## Honesty scope / flags

No `S2MuIrreducible Φ′`/`S2KeyPoly Φ′` outright; no KP-1..KP-9/FD-0 field instances; no
`FGMNSourceData` instance. Flagged for human review (new statements): the five predicate
definitions (esp. the prime-ideal-through-divisibility rendering), the graded-piece
characterization, the odd-carry engine.
