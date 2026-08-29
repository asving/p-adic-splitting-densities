# UNIT GCK — VERDICT: HONEST PARTIAL; MULTI-SIDE KERNEL REMAINS OPEN

Date: 2026-08-29. File: `leanfinal/Uniformity/ChapI/IFCG11.lean` (sorry-free; requested
single-file command exits 0, no warnings). No landed or leanspec file was edited.

## Kernel status

**HONEST PARTIAL. `RecentredClusterDegreeExhaustionStatement` is not proved.**

What lands:

* `below_eq_one_of_isDvPure`: the predicted C133mh12 no-far-primes mechanism works exactly.
  If the whole dissection product is `IsDvPure` at one above-floor direction, `D.hbelow`
  makes the monic `D.below` point-sided there; no-far-primes forces its degree to zero, hence
  `D.below = 1`.
* `degreeExhausted_of_isDvPure`: the corresponding complete one-side exhaustion sub-kernel,
  closed through IFCG9's `degreeExhausted_iff_below_eq_one` dictionary.
* `below_eq_one_of_monicFactorsHaveAboveFloorSide`: the general dissection argument after
  the missing coefficient/factor polygon inheritance is supplied. A positive-degree
  `D.below` would itself have a genuine above-floor side, contradicting `D.hbelow`.
* `recentredClusterDegreeExhaustion_of_factorSide`: packages that argument into IFCG9's
  kernel type.

The exact residual mathematical bridge is named `StrictRecentredFactorSideStatement`:

```lean
f.Monic → ¬ F.key ∣ f → StrictlyRecentredAboveFloor F f →
  MonicFactorsHaveAboveFloorSide F f
```

Here `MonicFactorsHaveAboveFloorSide F f` says every positive-degree monic factor `g` in a
monic product `f = g * w` has some coprime direction strictly above the frame floor with
positive `dvSideDeg`. It mentions neither `DvDissection` nor `D.below`, so it is not the target
renamed. This is precisely the multi-side entire/principal Newton-polygon inheritance absent
from the landed corpus: C133mh12 closes a pure-product case, while a general recentred cluster
may have several successive above-floor sides and is not `IsDvPure` at one direction spanning
its whole degree.

## Fired cover

**FIRED CONDITIONALLY, NOT UNCONDITIONALLY.**

`finiteGenreCoverAt_strong_of_factorSide` composes
`recentredClusterDegreeExhaustion_of_factorSide` with IFCG10's
`finiteGenreCoverAt_strong_of_kernel`, yielding

```lean
StrongCoverExhaustive ∧ StrongCoverDisjoint ∧
  ∀ m : ℕ, DecreasingGenreBankAt m
```

from the single residual `StrictRecentredFactorSideStatement`. Declaring the campaign's
unconditional stop-line theorem would hide that unproved multi-side bridge, so no such theorem
is declared.

## Verification and AxCheck

Command run after each increment and finally:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG11.lean
```

Final result: exit 0, no errors, no warnings, no `sorry`, no new `axiom`.

The AxCheck footer prints Lean core only (`propext`, `Classical.choice`, `Quot.sound`) for the
two no-far/exhaustion sub-kernel declarations, the factor-side contradiction, and the
factor-side-to-kernel reduction. The fired conditional cover additionally carries exactly
`Uniformity.Density.Tower.exists_dvDissection`, the allowlisted C.33 cite inherited through
IFCG10. No other literature axiom appears.
