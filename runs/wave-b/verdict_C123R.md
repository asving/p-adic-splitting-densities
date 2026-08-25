# verdict — unit C123R (re-fire C.123's deferred rows)

**Task.** `C123.lean` (commits `c24787cf` skeleton, `46197bb3` "COMPLETE (honest partial)",
`241a997d` "wire C123") fired 16+ rows on 2026-08-24 and DEFERRED five row-groups, each with
a named missing object. This unit re-checks each named object against the corpus as it
stands today (post dv-graded-engine v2 / S2-source landings) and fires whatever is now
available, in a NEW file (`leanfinal/Uniformity/ChapC/C123r.lean`). `C123.lean` itself is
untouched (`git diff --stat` on it is empty).

## The five-row table

| # | row-group (as deferred in `C123.lean`) | named missing object | verdict | evidence |
|---|---|---|---|---|
| 1 | node floors `[21,11]/[29,15]/[13,7]` | C.54's NODE-EQ anchor frames (no `C54.lean`) | **STILL DEFERRED** | `find leanfinal -iname "*c54*"` → nothing. `docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §5 plans `C.131ah′`/`C.131ai′`/`C.131aj′` for "C.54 node floor" / "C.54 sharp CRT realization" / "C.54 field floor" — but no `C131ah.lean`/`C131ai.lean`/`C131aj.lean` exist, and the doc's own §5.1 and §7 say so explicitly: *"C.54 is currently a blueprint node, not a landed `C54.lean` file"*, *"...the corresponding C.54 consumers remain **OPEN**."* |
| 2 | refine row A5-R1 (`p₀ = 2λ = 26`, `q=2` vanishing of the `j=1` pin) | C.56/C.57 refine-row carrier (no `C56.lean`/`C57.lean`) | **STILL DEFERRED** | `find leanfinal -iname "*c56*" -o -iname "*c57*"` → only `C56a.lean` (a different node, the K₂-digit lift; `C123.lean` already flagged this). `rg -l "C\.56\|C\.57"` hits `C99r/C84/C56a/C47/C43/C14/C14a.lean`, all references to `C.56a`, none to a refine-row carrier. |
| 3 | FAM-B BAND-2/3 window rows | C.72's `shadow_faithful_band` (statement carrier only in `C72.lean`) | **FIRED** | `C131w.lean` lands `shadow_floor` (Lean-core), `C131y.lean` lands `shadow_faithful_band` (Lean-core) — both real theorems, not carriers. Fired in `C123r.lean`: general tie-in `shadow_faithful_band_statement` (new, mirrors `C131w.shadow_floor_statement`, which C131y left undone) + concrete instantiation of both `shadow_floor` and `shadow_faithful_band` at `s2Tower` and `linTower`, `μ₂ = 3`, via the witness `composedKey T ^ 3 ∈ towerLocus T 3` (C.131ac's `composedKey_pow_mem_towerLocus`, the membership fact `C72.lean`'s own audit flagged as unlanded). See disclosure below. |
| 4 | `(1,2)`-genre bite (`EFF.HE6.20`(3), σ `{(2,2),(2,2)}`) | σ-genre member carrier C.119/C.120/C.122 (no such files) | **STILL DEFERRED** | `find leanfinal -iname "*c119*" -o -iname "*c120*" -o -iname "*c122*"` → nothing. `rg "HE6\.20"` hits only `C31.lean`/`C34.lean`, both item 1 (`R = r^m` self-label), never item 3. `rg "1,2..genre\|sigma-genre"` → no hits anywhere. |
| 5 | FR5X (C.96 negative control: attainment FAILS at `m=4,p=2`) | C.96 (no `C96.lean`) | **STILL DEFERRED** | `find leanfinal -iname "*c96*"` → nothing; `rg "C\.96\b"` hits only `C123.lean`'s own deferral note. |

## Row 3 detail: what was fired, and the one honest gap left in it

`leanfinal/Uniformity/ChapC/C123r.lean`, all `lake env lean`-checked, zero `sorry`, zero
warnings, footprint Lean-core except where noted:

* `shadow_faithful_band_statement` — general theorem, ties C.131y's `shadow_faithful_band`
  to C.72's frozen carrier `ShadowFaithfulBandStatement` (Lean-core; the one genuinely new
  declaration, filling the gap C.131w left filled for the floor but C.131y did not for the
  band).
* `s2_composedKeyPow_mem` / `lin_composedKeyPow_mem` — `composedKey T ^ 3 ∈ towerLocus T 3`
  at `s2Tower`/`linTower`, via C.131ac's `composedKey_pow_mem_towerLocus` (**carries the
  declared cite `fgmn_dv_exact_mul`, C66b**, by inheritance — reported per the rules, not a
  new axiom).
* `s2_shadow_floor_row` / `lin_shadow_floor_row` — `shadow_floor` instantiated at the two
  towers and this witness, for every `j < 3`; genuinely non-vacuous (the floor bound is
  content, not a drain artifact). Carries the cite (via the witness).
* `s2_theta_row` / `lin_theta_row` — the concrete `Θ_j` numerals the floor row clears:
  `s2Tower` (`E₂=10, δ=1`): `Θ_0=31, Θ_1=21, Θ_2=11`; `linTower` (`E₂=6, δ=1`):
  `Θ_0=19, Θ_1=13, Θ_2=7`. Lean-core (`rfl`-checked).
* `s2_shadow_faithful_band_row` / `lin_shadow_faithful_band_row` — the BAND theorem's
  statement-carrier form, instantiated at the two towers and this witness, for every
  `j < 3` and every `m < Θ_j`. Carries the cite (via the witness).
* `s2_composedKeyPow_drain(_top)` / `lin_composedKeyPow_drain(_top)` — **the honest
  disclosure, machine-checked rather than left as prose**: at the witness
  `composedKey T ^ 3`, every `Φ₂`-digit below coordinate `3` is exactly `0`
  (`dev_pow_self`'s Kronecker delta), hence has level-two height `⊤`. So the band row's
  hypothesis `hval : dv2Hgt (…) = (m : ℕ∞)` is never satisfiable at this witness for
  `j < 3` — the fired BAND row is a true, non-`sorry` statement, but at THIS particular
  witness it certifies no live `(j, m)` pair. This is exactly C.72's own module docstring's
  pattern-4 disclosure (the drain stratum), now checked by the kernel instead of asserted
  in prose.

**What remains for a fully non-vacuous numeric BAND window row:** a locus member
`f ∈ towerLocus T μ₂` with non-drain digits below `μ₂` (i.e. not a bare power of
`composedKey T`). The only landed path to such a witness is C.131ae's
`mem_towerLocus_of_budget`, which needs a genuine `hbud` — budget floors supplied at
concrete box digits of a candidate `f`. No such `f` and no such `hbud` are landed anywhere
in the corpus today; building one is a further, undertaken-sized task, not attempted here.

## Rules compliance

No `sorry`, no new `axiom` declared (only the pre-existing DECLARED cite `fgmn_dv_exact_mul`,
inherited through `composedKey_pow_mem_towerLocus`, reported above and in the AxCheck
footer). `C123.lean` untouched. No roll-up, `leanspec/`, `C130fd0.lean`, or sibling
DT2/scout files touched. No commit made.

## `#print axioms` (from the AxCheck footer, `lake env lean` run 2026-08-25)

```
shadow_faithful_band_statement        : propext, Classical.choice, Quot.sound
s2_composedKeyPow_mem                 : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
lin_composedKeyPow_mem                : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
s2_shadow_floor_row                   : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
lin_shadow_floor_row                  : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
s2_theta_row                          : propext, Classical.choice, Quot.sound
lin_theta_row                         : propext, Classical.choice, Quot.sound
s2_shadow_faithful_band_row           : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
lin_shadow_faithful_band_row          : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
s2_composedKeyPow_drain               : propext, Classical.choice, Quot.sound
s2_composedKeyPow_drain_top           : propext, Classical.choice, Quot.sound
lin_composedKeyPow_drain              : propext, Classical.choice, Quot.sound
lin_composedKeyPow_drain_top          : propext, Classical.choice, Quot.sound
```

(`fgmn_dv_exact_mul` = the declared literature cite C66b, FGMN J. Algebra 427 (2015)
Thm 2.8 + Cor 4.12(3); allowlist member 7. All other footprints are Lean-core only:
`propext, Classical.choice, Quot.sound`.)
