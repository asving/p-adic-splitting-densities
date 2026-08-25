# Verdict — unit KP12 (nodes KP-1 + KP-2, CORES 1–2/4 of `key_criterion`)

**COMPLETE, with the named gap discharged.** One new file
`leanfinal/Uniformity/ChapC/C130kp1.lean`, built green
(`lake build Uniformity.ChapC.C130kp1`, 8750 jobs), zero `sorry`, all 19 `#print axioms`
footprints Lean-core `{propext, Classical.choice, Quot.sound}`. Imports C130kp0 + C130rp9
+ C130rp11 only.

## NODE KP-1 — the translation, at the scopes the proofs force

* ★ `normRes_dvd_of_S2MuDvd` — forward, **UNIVERSAL** (no hypothesis at all):
  `φ ∣µ₂ g → R₃(φ) ∣ R₃(g)` (KP-0's normalized tie + RP-10's universal `s2NormRes_mul`).
* ★ `S2MuDvd_of_normRes_dvd` / `S2MuDvd_iff_normRes_dvd` — backward at the honest fences:
  monic `g`, `deg g ≤ 4 = e'f'·deg Φ′`, `¬ IsUnit (R₃ g)`. **The mechanism is the
  `modByMonic` remainder — NO residual-realization lemma**: the μ₂-cofactor is the literal
  `a /ₘ g`; the remainder either sits strictly above in value (giving `a ∼µ₂ g·(a /ₘ g)` by
  the value criterion) or its graded residual — a nonzero CONSTANT, since `deg < 4` means
  slots `{0,1}` and parity kills one — would be divisible by the non-unit `R₃(g)`
  (published Lemma 5.2's mechanism, the Prop 1.7(2)/1.9 genre). Support lemmas:
  `s2GradedRes_eq_C_of_natDegree_lt_four`, `s2NormRes_isUnit_of_natDegree_lt_four`.
* ★ `S2MuDvd_key_iff` — the CARRIED-KEY scope (the row's "needed scopes", second scope):
  for `Φ′` the residual test is void (`R₃(Φ′) = 1`), and the honest translation is the
  slot-0 gate: `Φ′ ∣µ₂ f ↔ f`'s slot-0 digit is off the grade line (forward = KP-0's
  odd-carry engine; backward = the same remainder mechanism at `f %ₘ Φ′ = dev(f,0)`).
  `S2MuDvd_key_of_odd_grade`: odd grades are `Φ′`-divisible outright.
* Both fences PROVED essential: `tooth_backward_needs_nonunit` (`(Φ′,1)`: residual dvd
  without μ₂-dvd) and the Part-8 degree-six refuter (residual dvd into `(Φ′²+4x)²` without
  μ₂-dvd).

## NODE KP-2 — irreducible residual gives prime initial form

* ★ `s2MuIrreducible_of_irreducible_normRes`: monic + `deg ≤ 4` + `Irreducible (R₃ g)` →
  `S2MuIrreducible g` (Lemma 5.2(2)'s primality substance: push forward, split by `K₂[y]`
  primality, pull back through KP-1). The row's "nonzero constant term" hypothesis is
  AUTOMATIC (RP-8's `s2NormRes_coeff_zero_ne_zero`); it is restored in the field-shaped
  wrapper ★ `s2_key_criterion_muIrreducible` (the C130fg `key_criterion` hypothesis list
  concluding the irreducibility conjunct — KP-4's consumable).
* ★ `s2MuIrreducible_lift`: KP-2 fires at RP-12's landed recipe key —
  `S2MuIrreducible (Φ′² + 4x)`.
* ★ **honesty fence, machine-refuted** (`tooth_kp2_degree_fence_sharp`): naked KP-2 (no
  degree fence) is FALSE — the degree-6 monic `Φ′·(Φ′²+4x)` has irreducible residual
  `X+1` yet its initial form divides `(Φ′·Φ′)·((Φ′²+4x)²)` and neither factor (forward
  residual test kills one side; RP-9's odd×odd trailing carry `+1` kills the other). The
  printed degree hypothesis of Lemma 5.2/Thm 5.7 is essential.

## ★★ KP-0's named gap DISCHARGED: `s2KeyPoly_key : S2KeyPoly Φ′`

Not via KP-2 (the key's residual is a unit) but via the carried-key scope: primality
`S2MuDvd_key_or` from slot-0 gate multiplicativity (RP-4 trivial twist at even×even; odd
grades divisible outright), then `s2MuIrreducible_key`, then KP-0's own reduction
`s2KeyPoly_key_of_muIrreducible`. Published Prop 1.7(4) at the carried key; spelled at
`x² − 2` as `s2KeyPoly_X_sq_sub_two`.

## Honesty scope / flags

No KP-3 (μ-minimality at recipe degree), no KP-4 assembly (`S2KeyPoly (Φ′²+4x)` NOT
claimed — its minimality is open), no KP-6 literal `keyAt 2` field, no KP-7..9, no FD-0
instance. Flagged for human review (new statements): the backward translation + fences,
the carried-key characterization, KP-2's statement, the naked-KP-2 refutation, and the
named-gap discharge.
