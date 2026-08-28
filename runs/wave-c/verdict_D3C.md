# Verdict D3C — the μ₄ operator stack's upper-middle tranche: D3-11..D3-14

Date: 2026-08-28
Target: `leanfinal/Uniformity/ChapC/C136d2.lean` (new file; nothing else touched)

## ACCEPTANCE — STATUS FIRST

| row | status | exact result |
|---|---|---|
| **D3-11 graded product/scalar** | **GREEN — UNCONDITIONAL** | Gate witness `exists_mu4SlotOnGrade_of_exact` (inf attainment off `dv3Supp`'s own `Finset.inf`, mirror of `C132rp7` Part 1); the eval-1 collapse of the INNER μ₃-level operator `s2Mu3GradedRes` under the degree-`8` fence (`eval_one_s2Mu3GradedRes_eq_coeff_zero` — genuinely new content, one level up from `C132rp7`'s own Part 2, using `g8`'s degree `8` in place of `Φ₂`'s `4`); the twisted/plain product laws `s2Mu4GradedRes_mul_of_exact`/`_of_prevGrade` off D3-10's `s2Mu4Coeff_mul`; `S2Mu4PrevGrade := 2 ∣ β` + packaged `s2Mu4_graded_mul`; the coefficient-zero nonvanishing `s2Mu4GradedRes_coeff_zero_ne_zero_of_exact`/`s2Mu4_graded_scalar_nonzero` below degree `8`, citing the LANDED μ₃-level nonvanishing `C132rp7.s2Mu3GradedRes_coeff_zero_ne_zero_of_exact` DIRECTLY (the "genuine transport" step the campaign brief predicts) via the Part-2 eval-1 bridge; the non-vacuity tooth `tooth_mu4_scalar_fires`. |
| **D3-12 normalized operator** | **GREEN — UNCONDITIONAL** | `s2Mu4GradeOf`/`s2Mu4NormRes` (strip the initial `X`-power at the input's own exact grade, mirror of `C132rp8`); polynomial-level nonvanishing `s2Mu4GradedRes_ne_zero_of_exact` via the development DIGIT's automatic degree bound (`C132rp8`'s own route, distinct from D3-11's g-itself-bounded route, citing `C132rp8.s2Mu3GradedRes_ne_zero_of_exact` for the inner leg); the universal multiplication `s2Mu4NormRes_mul` (both zero cases + the exact-grade case via `natTrailingDegree` bookkeeping); the "one" bank (`S2Mu4ExactGrade_one`, `s2Mu4GradedRes_one`, `s2Mu4NormRes_one`); the key-power bank at `g8` itself (`S2Mu4ExactGrade_key_pow`, `s2Mu4GradedRes_key` `=1`, `s2Mu4GradedRes_key_pow` `= X^(k/2)`, `s2Mu4NormRes_key`/`_key_pow` `=1`) — the "key reads" deliverable. |
| **D3-13 recipe/B-1** | **GREEN — UNCONDITIONAL** | The ONE genuinely new computation T4 deferred: the exact μ₄ grade `170 = 2·85` of the tooth `2⁸·Φ₂` (`s2Mu4_chainNormBelow_tooth_exactGrade`), via a fresh mu₂→mu₃ constant-doubling bridge `s2Hgt₃_C_two : μ₃(2) = 8 = 2·μ₂(2)` (the SAME "single `Φ₂`/`g8`-slot" mechanism `C132rp10b.s2Hgt₃_corr` uses, specialized to the bare constant — a genuinely new tooth, not previously landed since the μ₃ campaign never needed `μ₃(2)` alone) squared up to `μ₃(2⁸)=64` and combined with `tooth_Φ₂`'s `21` via the UNCONDITIONAL `S2Mu3ExactGrade_mul`, then doubled again by a general private "single-`g8`-slot" bridge (`dv3Supp_eq_two_smul_of_natDegree_lt`, reused verbatim by D3-14's own grade computation); wrapped as the generic B-1 supply bundle over `I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85` with `hkey`, mirroring `C132fd1`'s style (`s2Mu4_B1_degree_supply`/`_nonzero_supply`/`_exact_grade_supply`, plus the bare-tooth `s2Mu4_chainNormBelow_exactGrade`) — **no concrete μ₄ calculus exists yet** (that is D3-18/19's job), so this row deliberately does NOT mirror `C132sg3`'s concrete-instance discharge; it supplies exactly the three B-1 facts the campaign row names. |
| **D3-14 normalized existence** | **GREEN — UNCONDITIONAL, no gaps** | `g16 := g8² − 2⁸·Φ₂`, monic of degree `16` (`g16_monic`/`g16_natDegree`, `C132rp10`'s route one level up); its exact μ₄ grade `170` — BOTH summands individually at grade `170` (`g8²` via `S2Mu4ExactGrade_mul` on `tooth_g8` twice; `−tooth` via D3-13's tooth-grade fact negated), established via `s2Hgt₄_add_ge` (≥) plus a direct `dv3Supp` slot-0 computation (≤), mirroring `C132rp10b.s2Hgt₃_g8`'s STAGE B route (`g16_exactGrade`); the graded/normalized residual `X + 1` — the hardest sub-step, needing a full mu₂/mu₃-level value chain mirroring `C132rp10b`'s STAGE C (`exactGrade_C_two_pow_eight_mu2`, `s2GradedRes_C_two_pow_eight_mu2`/`_neg_...`, the exact quotient/remainder facts for `2⁸·Φ₂`'s own `Φ₂`-development, `s2Mu3GradedRes_neg_tooth_eq_one`, then `s2Mu4GradedRes_g8_sq = X` + `s2Mu4GradedRes_neg_tooth = 1` combined via the LANDED `s2Mu4GradedRes_add` into `s2Mu4GradedRes_g16 = X+1`, giving `s2Mu4NormRes_g16 = X+1` trivially since the polynomial is already trailing-degree `0`); packaged as `s2Mu4_hex` (the `C132rp10b.s2Mu3_hex` mirror: every admissible monic degree-one residual over the two-element field is `X+1` via `C132rp10.s2Mu3_unique_admissible_linear`, and `g16` is its monic degree-`16` witness). **No sorry, no gap, no partial result** — despite being flagged as the campaign's hardest row, it landed complete. |

## What lands (all Lean-core, all sorry-free)

~90 new declarations (public + private) across the four rows, listed in the file's own
AxCheck footer (public ones) plus private helpers visible in-file. Every declaration is
the one-level-up mirror of a landed μ₃-campaign declaration (`C132rp6`/`C132rp7` for
D3-11, `C132rp8` for D3-12, `C132rp9`/`C132fd1` for D3-13, `C132rp10`/`C132rp10b` for
D3-14), substituting: inner key `Φ₂ ↦ g8`; outer side `(u₃,ℓ₃)=(21,2) ↦ (u₄,ℓ₄)=(85,2)`;
inner graded/normalized read `s2GradedRes`/`s2NormRes` (μ₂-level) ↦ the landed μ₃-level
`s2Mu3GradedRes`/`s2Mu3NormRes`.

Genuine departures from a byte-for-byte port (all flagged in the file docstring/this
verdict):
* D3-11's Part-2 eval-1 collapse fence is `8` (not `4`) because it is about the *inner*
  μ₃-level operator read at the *outer* ambient tower `s2DepthThree` (`r=3`) — the fence
  numeral tracks the ambient tower's own ambient key degree, not the operator's own
  internal key, exactly as `C132rp7`'s docstring documents for the μ₂/μ₃ pair at `r=2`.
* D3-13 cannot mirror `C132sg3`'s concrete-instance discharge (no `s2Mu4Calculus` exists);
  it supplies the generic-`I` B-1 bundle only, matching the row's literal wording.
* D3-14's Stage C needed a fresh mu₂-level computation for `μ₂(2⁸)=32` and its negation
  (`C132rp10b` never needed the mu₂-height of a BARE constant, only of `2⁴·Φ′`) — built via
  `C130rp0.S2ExactGrade_mul` squared twice off the LANDED `C132rp10b.exactGrade_C_two_pow`
  (`μ₂(2⁴)=16`), and the exact-division facts for `2⁸·Φ₂`'s own `Φ₂`-quotient/remainder via
  `Polynomial.modByMonic_add_div` + `Polynomial.modByMonic_eq_zero_iff_dvd` (mathlib,
  monic-hypothesis-free identity) rather than a `dev`-recursion unfolding trick.

## What this unit does NOT claim (honesty scope)

No key predicates/divisibility (D3-15), no key criterion/irreducibility (D3-16), no
`FGMNSourceData`/`FGMNSourceLaws` record or `FGMNCalculus` instance (D3-18/19) — D3-13's
"B-1 supply" and D3-14's "normalized existence" theorems are stated generically (over an
abstract `I`/pointwise polynomial facts), never against a concrete μ₄ calculus, since none
exists yet. `S2Mu4KeyPoly` and its criterion are D3-15/16's job, not consumed here.

## Verification and footprint

Required command, run after the skeleton and after each fill increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136d2.lean
```

Final exit status: `0`; zero errors, zero warnings, zero `sorry`. The AxCheck footer
prints every public declaration at exactly `[propext, Classical.choice, Quot.sound]`
(Lean core) or with NO axioms at all (`S2Mu4PrevGrade`). No landed or leanspec file was
edited (`git status`: the new file is the unit's only footprint). No git operation was
run. File-wide `set_option maxHeartbeats 1000000` added (mirroring `C132sg3`'s own
practice) — one Stage-C field-nonvanishing step (`(-1 : F) ≠ 0` via generic `one_ne_zero`/
`neg_ne_zero`) hit the default `synthInstance` heartbeat cap on this file's heavier import
graph; routed around it with a direct `neg_eq_zero`-based proof instead of raising the cap
further (the outer `maxHeartbeats` bump alone did not touch the *typeclass-search* cap).

Repair log: iterative, ~6 rounds of `lake env lean` → fix → recheck across the file
(concentrated in D3-13's grade computation and D3-14's Stage C); no proof-content
rewrite was needed on D3-11/D3-12 beyond porting. Notable repairs: (1) two `s2Mu3Coeff`-
level "mul_zero_of_odd"/multiplicativity helpers had to be re-derived locally (the model's
own analogues in `C132rp5`/`C136l2e4` are `private`, hence inaccessible across files —
copied per the corpus's private-copy convention, not re-invented); (2) `dev_eq_zero_of_lt`
vs `s2Mu4Coeff_eq_zero_of_natDegree_lt` confusion twice (the latter bounds the OUTER index
against the input's own degree; the needed fact bounds a *specific development slot*
against the key's degree — these are different lemmas with different hypotheses, and only
the first is the right tool for "digit vanishes because the slot index is large enough");
(3) `Polynomial.modByMonic_add_div`'s exact argument order/no-monic-hypothesis signature;
(4) one `rw` ordering slip (`neg_zero` before its target subterm was reduced to `0`).

## Trust boundary

New statement shapes flagged for human review (every `def` introducing a new predicate/
operator, and the fresh numeral pins): `S2Mu4PrevGrade`, `g16` (the depth-four recipe
candidate `g8² − 2⁸·Φ₂`), and the two fresh constant-height teeth `s2Hgt₃_C_two`
(`μ₃(2)=8`) / `S2Mu3ExactGrade_C_two_pow_eight` (`μ₃(2⁸)=64`) — the first mu₂→mu₃ height
computations for a bare constant in this campaign, feeding D3-13's tooth grade and D3-14's
Stage C alike.
