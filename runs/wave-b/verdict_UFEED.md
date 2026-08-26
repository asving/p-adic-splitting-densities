# Verdict — unit U-FEED (af′ plan's final node) + the C.53 wiring

**File delivered:** `leanfinal/Uniformity/ChapC/C131uf.lean` (new; only file written by this
unit besides this verdict). Builds clean: `cd leanfinal && lake env lean
Uniformity/ChapC/C131uf.lean` and `lake build Uniformity.ChapC.C131uf` both exit 0 — zero
errors, zero warnings, zero `sorry`, zero new `axiom`.

## Part 1 — U-FEED (`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3/§4)

Constructed the plan's non-drain witness at `s2Tower`, `μ₂ = 3`:

* `s2Extra h2 hq := C(2⁶)·X·Φ′` (`Φ′ = (s2Frame h2 hq).key`) and
  `s2Witness h2 hq := Φ₂³ + s2Extra h2 hq` (`Φ₂ = composedKey (s2Tower h2 hq)`) — exactly the
  plan's `f₀ = Φ₂³ + π⁶xΦ′`.
* Digit bookkeeping: `s2Extra`'s inner (`Φ′`) digits are `(g, 0, 0, …)` at slots
  `b = 0, 1, ≥2` (`s2Extra_dev_zero/_one/_dev_ge_two`, via `dev_mul_pow`/`dev_mul_pow_of_lt`
  reading `s2Extra` as `x·Φ′¹` — no residual/purity machinery needed); `s2Witness`'s outer
  (`Φ₂`) digits are `s2Extra, 0, 0` at `j = 0, 1, 2` (`s2Witness_dev_zero/_one/_two`, via
  `dev_add_of_monic` + `dev_pow_self`'s Kronecker law, copying `C131ae`/`C123r`'s `hgdig`
  pattern). `s2Witness_monic` + `s2Witness_natDegree` (`= 12 = 3·D₂`) via
  `Polynomial.Monic.add_of_left` / `degree_add_eq_left_of_degree_lt` (`s2Extra.degree <
  (Φ₂³).degree`, the same "monic⁻top + lower correction" recipe as `mem_towerLocus_of_budget`
  itself uses in reverse).
* `s2Witness_hbud` — the explicit finite `hbud`: at `(j,a,b) = (0,1,1)` the digit's
  coefficient is `2⁶` and the floor is TIGHT (`budgetFloor _ 3 0 1 1 = wtCoeff = 31`, via the
  landed `budgetFloor_le_addVal_of_wtCoeff`, AF-5b, `C131ag.lean`); at all other 11 of the 12
  `(j,a,b)` slots (`j<3,a<2,b<2`) the coefficient is literally `0`, so `addVal = ⊤` and the
  floor clears by `le_top` — no arithmetic needed there.
* `s2Witness_mem : s2Witness h2 hq ∈ towerLocus (s2Tower h2 hq) 3` — via
  `mem_towerLocus_of_budget` (C.131ae) fed the `hbud` above. **This disposes
  `verdict_C123R.md`'s named gap** ("no such `f` and no such `hbud` are landed anywhere in
  the corpus" for a fully non-vacuous BAND window row): the witness and its `hbud` are now
  landed.
* `s2Witness_digit_height` — the `j = 0` digit is **non-drain**, exact level-two height `31`
  (`dv2Hgt (dev Φ₂ f₀ 0) = 31`), proved by antisymmetry through the `WT`/`wtCoeff` bridge
  (`dv2Hgt_eq_WT_phiNF`, `WT_le_wtCoeff`, `le_WT_of_forall_wtCoeff`, `wtCoeff_zero`): the
  two-key normal form of `s2Extra` has its ONLY nonzero entry at `(a,b) = (1,1)`, value `2⁶`,
  weight exactly `31 = (3−0)·10 + 1`. This is the first landed locus member with a *finite*
  sub-top composed-key digit — `composedKey T ^ μ₂` itself (C123r's witness) is drain
  (height `⊤`) at every digit below `μ₂`.

**The honest scope limit, stated per the task's own instruction.** The plan's §4 finding —
the FAM-B BAND *window* is provably EMPTY at both landed margin-1 towers, because AF-4's
strict floor `(μ₂−j)E₂ + 1` already equals `Θ_j` when `margin = 1` — is NOT re-proved as a
separate theorem here; this unit lands only the budget/locus facts (membership + the exact
digit height), not a live-window claim, per the assignment. The general fact is available
on demand directly from the already-landed `Uniformity.Density.Tower.towerLocus_dev_strict_floor`
(AF-4, `C131af.lean`) with no further work: for any margin-1 `T`, `hval : dv2Hgt (dev Φ₂ f j)
= (m:ℕ∞)` and `m < Θ_j` are jointly contradictory since AF-4 forces `m ≥ Θ_j`.

**Cite footprint.** `s2Witness_mem` carries `fgmn_dv_exact_mul` (C66b), inherited through
`mem_towerLocus_of_budget` → `composedKey_pow_mem_towerLocus`. All digit/degree bookkeeping
and `s2Witness_digit_height` are Lean-core only (`propext, Classical.choice, Quot.sound`).

## Part 2 — the C.53 wiring (`runs/wave-b/verdict_RB1.md`'s blocked row, now unblocked)

`towerLocus_fibration_of_leg1` (`C53b.lean`) needed `h1 : TowerBudgetIff T μ₂`. Both halves
of that iff are now landed: `mem_towerLocus_of_budget` (C.131ae, `⟸`, pre-existing) and
`budget_of_mem_towerLocus` (C.131af′, `⟹`, landed by unit U-ASSEMBLE in `C131ag.lean`) —
together assembled by `C131ag.lean`'s own `towerLocus_iff_budget`, which byte-mirrors
leanspec `ChapC.lean:2030`'s signed `axiom towerLocus_iff_budget`.

* `Uniformity.Density.Tower.towerBudgetIff_of_iff` — `TowerBudgetIff T μ₂ := fun f hf hdeg
  => towerLocus_iff_budget T hπ hh hμ₂ hf hdeg`, i.e. `TowerBudgetIff` unfolded is exactly
  `towerLocus_iff_budget`'s statement, applied pointwise.
* `Uniformity.Density.Tower.towerLocus_fibration` — the **unconditional** signed-shape
  theorem, hypothesis list byte-identical to leanspec `ChapC.lean:2048-2055` (`(T, hπ, hh,
  [IsAdicComplete …], [Finite (ResidueField O)], μ₂ N, hμ₂)`, `axiom → theorem`): proved as
  `towerLocus_fibration_of_leg1 hπ T hμ₂ N (towerBudgetIff_of_iff T hπ hh hμ₂)`. `hh` IS
  consumed (through `towerLocus_iff_budget`); `[IsAdicComplete …]` is genuinely unused —
  confirmed by checking `towerLocus_fibration_of_leg1`'s own signature, which never asks for
  it (the same finding `towerLocus_fibration_of_frontier`'s docstring already records for
  `hh`/`hμ₂` in the OTHER unconditional route). No statement was narrowed: the signed
  conclusion, `T`, and all binders are unchanged from leanspec's axiom.

**Cite footprint.** Both `towerBudgetIff_of_iff` and `towerLocus_fibration` carry
`fgmn_dv_exact_mul` (C66b), inherited through `towerLocus_iff_budget`'s `←` branch
(`mem_towerLocus_of_budget`). Not a new axiom — the same single declared cite already
landed by U-HEART/U-ASSEMBLE, consumed here by reference only.

## Rules compliance

No `sorry`, no new `axiom` (only the pre-existing declared cite `fgmn_dv_exact_mul`,
reported above and in the AxCheck footer). `leanspec/` was read-only (`rg`/`sed`, never
edited); no roll-up touched; no PK12 mid-retype file (`C130fg`/`pk`/`s17`/`s18`/`vw`)
touched. (Note: `git status` shows `leanfinal/Uniformity/ChapC/C130in.lean` modified —
that is a concurrent unit's in-flight PK-1/U15 retype, not touched by this unit; verified
by inspecting its diff, which references `[PK-1/U15, 2026-08-25]`/`PACKAGING_ROUTE_2026-08-25.md`.)
No `git commit` taken.

## `#print axioms` (AxCheck footer, `lake env lean` run 2026-08-26)

```
s2_key_natDegree            : propext, Classical.choice, Quot.sound
s2_composedKey_natDegree     : propext, Classical.choice, Quot.sound
s2Extra_natDegree_lt         : propext, Classical.choice, Quot.sound
s2Extra_dev_zero             : propext, Classical.choice, Quot.sound
s2Extra_dev_one              : propext, Classical.choice, Quot.sound
s2Extra_dev_ge_two           : propext, Classical.choice, Quot.sound
s2Witness_dev_zero           : propext, Classical.choice, Quot.sound
s2Witness_dev_one            : propext, Classical.choice, Quot.sound
s2Witness_dev_two            : propext, Classical.choice, Quot.sound
s2Witness_monic              : propext, Classical.choice, Quot.sound
s2Witness_natDegree          : propext, Classical.choice, Quot.sound
s2Witness_hbud               : propext, Classical.choice, Quot.sound
s2Witness_mem                : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
s2Witness_digit_height       : propext, Classical.choice, Quot.sound
towerBudgetIff_of_iff        : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
towerLocus_fibration         : propext, Classical.choice, Quot.sound, fgmn_dv_exact_mul
```

(`fgmn_dv_exact_mul` = the declared literature cite C66b, FGMN J. Algebra 427 (2015)
Thm 2.8 + Cor 4.12(3); allowlist member 7. All other footprints are Lean-core only.)
