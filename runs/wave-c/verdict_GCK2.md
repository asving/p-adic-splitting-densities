# UNIT GCK2 — VERDICT: THE BRIDGE IS PROVED; THE KERNEL AND THE COVER ARE FIRED

Date: 2026-08-29.  File: `leanfinal/Uniformity/ChapI/IFCG12.lean` (NEW; sorry-free, zero
new axioms; the requested single-file command exits 0 with no errors and no warnings,
~9 s).  No landed or leanspec file was edited; repo footprint is exactly this file and
this verdict.

## Headline

**`IFCG11.StrictRecentredFactorSideStatement` — the exhaustion kernel's residual bridge,
the one open input to the strong finite genre cover — is now a THEOREM**
(`IFCG12.strictRecentredFactorSide`), with axiom footprint **Lean core only**
(`propext, Classical.choice, Quot.sound` — it does not even consume the C.33 cite).

Fired through the landed IFCG11 reductions:

* `recentredClusterDegreeExhaustion : RecentredClusterDegreeExhaustionStatement` — IFCG9's
  kernel, **Lean core only** (the kernel quantifies over GIVEN dissections, so the
  existence cite never enters);
* ★★★ `finiteGenreCoverAt_strong_all : StrongCoverExhaustive ∧ StrongCoverDisjoint ∧
  ∀ m, DecreasingGenreBankAt m` — **THE COVER, unconditional**, Lean core + exactly the
  allowlisted `Uniformity.Density.Tower.exists_dvDissection` (entering only through
  IFCG10's realization assembly).  The uniform-a0 campaign's stop line falls.

## Count recoveries (m ≤ 4)

* `rpCount_cubic : IFCG0.rpCount 3 = 5` — the official cubic residue-pattern count,
  **kernel-checked** (`decide`, Lean core; needs `maxRecDepth 4000`).
* `strongCover_cubic` / `strongCover_quartic` — the mass-3 / mass-4 exhaustive gates:
  every recentred monic above-floor context of that mass strong-realizes a member of the
  precomputed bank (Lean core + the C.33 cite).
* HONEST LIMIT: `rpCount 4 = 11` is NOT declared as a theorem — kernel `decide` on the
  `Sym`-grid count is intractable at `n = 4` (tested: > 8 min at 4M heartbeats; exactly
  as IFCG0's comment predicts; `native_decide` would break the axiom fence).  The
  quartic count remains IFCG0's recorded `#eval` regression.

## Proof route (DEVIATES from the unit brief — no dissection of the factor needed)

The brief's candidate route (dissect the factor g, split on its slope set) was not used:
the below-type case reduces to the same missing polygon fact, so the proof goes direct.
For monic `f = g·w`, `¬ F.key ∣ f`, `StrictlyRecentredAboveFloor F f`, `deg g > 0`
(write `E := e₁f₁`, `H := E·h` the floor coefficient, `m := deg f / E`):

1. **Key escape** (`key_dvd_of_dvHgt_zero_eq_top`): if `dvHgt F g 0 = ⊤` the zeroth
   development digit `g %ₘ F.key` vanishes (`KeyFrame.stageHeight_ne_top`,
   `modByMonic_eq_zero_iff_dvd`), so `F.key ∣ g ∣ f` — contradiction.  Hence
   `dvHgt F g 0 = A₀` finite.
2. **Last-side lemma** (`exists_lastSide_direction`, NEW, Lean core): strict recentring +
   the monic top digit (`dev_top_eq_one` ⟹ `dvHgt F f m = 0` via `stageHeight_one`)
   produce a coprime above-floor direction `(u₀, ℓ₀)` — the reduced fraction of
   `hgt(x*)/(m − x*)` at the x* MINIMIZING that ratio over the finite support left of `m`
   (ℚ-valued `Finset.exists_min_image`, cross-multiplied back to ℕ) — at which
   `m ∈ dvSideSet F f u₀ ℓ₀` and `dvSideMax = m`.  Above-floor is EXACTLY the strict
   recentring inequality at `x*`; indices `j > m` are dominated by the linear term alone.
3. **Unfenced `dvSideMax` additivity** (`dvSideMax_mul_all`): `C133mh3.dvSideMax_mul`
   (Theorem M) at `0 < F.h`; at the degenerate `F.h = 0` frame — which the bridge's
   quantifier includes and Theorem M does not — the C133h0leg dictionary
   (`dvSideSet_eq_sideSet` under B43's `suppVal_ne_top_of_ne_zero` guard, `isKey_key`)
   transports B43's order-1 `sideMin_mul_gen'`/`sideDeg_mul_gen'`, and the dv-level
   spacing law (`dvSideLen_eq`) rebuilds the max sum.  A pin exists for every frame
   (`exists_pin`, off `suppVal_key_ne_top'` + `npHgt_ne_top_of_onSide`).
4. **The cofactor cap**: `dvSideMax w ≤ deg w/E ≤ m − 1` (`le_natDegree_div_of_mem_dvSideSet`
   + `deg g ≥ 1`), so additivity at the last side pins `b := dvSideMax g ≥ 1`; the
   on-side equation at `b` against the index-0 term of `dvSupp` (`C131y.dvSupp_le_term`)
   gives the STRICT drop `hgt_g(b) + H·b < A₀` (strictness = the floor inequality times
   `b ≥ 1`).
5. **Secant lemma** (`hasGenuineAboveFloorSide_of_secant`, NEW, Lean core — the
   multi-side polygon content GCK isolated): a strictly-above-floor secant `0 → b` forces
   a genuine above-floor side.  Maximize `(A₀ − hgt(y))/y` over the finite support
   (ℚ-valued `Finset.exists_max_image`); the reduced maximizing fraction `(u, ℓ)` is
   above floor (its ratio beats the secant's, which beats `H`), and BOTH `0` and the
   maximizer `y*` sit in `dvSideSet F g u ℓ` (the maximality is exactly the support-wide
   term bound; `u·y* = ℓ·Δ` makes the two terms equal).  Two distinct side points +
   C08's exact spacing law (`dvSideLen_eq`) force `0 < dvSideDeg` — this IS
   `HasGenuineAboveFloorSide F g`.

Every ℚ excursion is cross-multiplied back to ℕ (`div_le_div_iff₀`/`lt_div_iff₀`,
`le_of_mul_le_mul_right`, `Nat.cast_sub`); `ℕ∞` terms are collapsed to single casts by a
local `term_coe` kit lemma.

## Verification and AxCheck

Command run after each increment and finally:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG12.lean
```

Final: exit 0, no errors, no warnings, no `sorry`, no new `axiom`.  AxCheck footer:

* Lean core ONLY: `hasGenuineAboveFloorSide_of_secant`, `exists_lastSide_direction`,
  `dvSideMax_mul_all`, `strictRecentredFactorSide`, `recentredClusterDegreeExhaustion`,
  `rpCount_cubic`;
* Lean core + exactly `Uniformity.Density.Tower.exists_dvDissection`:
  `finiteGenreCoverAt_strong_all`, `strongCover_cubic`, `strongCover_quartic`.

No other axiom appears anywhere — within the unit's "Lean core + at most the C.33 cite"
fence, with the bridge and kernel strictly inside Lean core.

## Notes for the orchestrator

* The `h = 0` leg (§4's degenerate branch) was MANDATORY: the landed bridge/kernel Props
  quantify over all `KeyFrame`s and Theorem M is `0 < F.h`-fenced.  C133h0leg's
  dictionary covered it; no new mathematics.
* IFCG11's conditional theorems (`recentredClusterDegreeExhaustion_of_factorSide`,
  `finiteGenreCoverAt_strong_of_factorSide`) are consumed as-is; IFCG9/10/11 unchanged.
* Candidate follow-ups: (i) PROJECT_STATE/frontier update — the GC stop-line is down;
  (ii) the quartic count as a computation-free combinatorial theorem (partition count),
  if anyone wants `rpCount 4 = 11` in the kernel.
