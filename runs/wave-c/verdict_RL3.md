# UNIT RL3 verdict — `RungLift` at rungs ≥ 3: the GENERIC CORE LANDS (root relation by construction, derived D3AD laws, the f′ = 1 closed form) (2026-08-31)

**Status: COMPLETE (generic layer landed Lean-core; S2 witness remainder named exactly).**
`leanfinal/Uniformity/ChapI/I10RungLift3.lean` (NEW, ~560 lines, namespace
`Uniformity.Density.Tower.I10rl3`) — 0 errors, 0 warnings, **0 `sorry`**; all **9**
printed footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified per-file
(`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift3.lean`, exit 0) and
per-target + aggregator (below).  Cite ledger: **empty** — Lean core only; no numeral,
no `residueCard`, no S2 datum in any DECLARATION (S2 material appears only in the §6
remainder documentation, as prose).

## STATUS FIRST

| charge | status | exact result |
|---|---|---|
| 1. scope RungLift's rung-3 fields against the tower's own data | **DONE — adjudication sharpened in the tower's favor** | the root relation `read_key = 0` is NOT per-realization data once the next ring is CHOSEN correctly: it holds BY CONSTRUCTION at `K' = AdjoinRoot ρ` for `ρ` a prime factor of the key's own read (which is nonzero generically — `nextRead_ne_zero_of_exact`, no fence).  The genuinely per-rung content concentrates in: the next key's exact iterated grade, the factor datum (`SmallCoprime` — FGMN `graded_scalar_nonzero`), and the slopes.  The C136 depth-3/4 witness machinery (charge's grep) confirms: at S2 the depth-3 key is `g16 = g8²−2⁸Φ₂` (deg 16 = 2·8), exact grade 170, μ₄ residual `X+1` — the SAME eval-at-1 root relation as depth 2→3, i.e. the f′ = 1 mechanism at every stage |
| 2. prove the generic parts | **GREEN — ★★ LANDED, Lean-core, uniform in `q` and the frame** | ★ `nextSupp_quot_le` + `nextSupp_mod_eq` — the two D3AD-interface `CarrierKey` laws (`supp_mod`/`supp_quot`) at the ITERATED carrier are DERIVED from the pack's own laws + the factor datum (they stop being per-rung obligations); ★ `RungLift.ofPrime` — the generic rung-≥3 constructor (root relation proved, not assumed); ★★ `RungLift.ofRootF1` — the **f′ = 1 closed form**: at `deg key₃ ≤ ℓ·deg key`, `gcd u ℓ = 1`, ANY nonzero root of the key's read supplies the WHOLE lift with next ring `K` itself (`nextRead_eq_monomial`, the diagonal singleton); §4 f′ ≥ 2 supports (`exists_prime_factor_nextRead` over a field, `smallCoprime_of_natDegree_le` — generic exactly in the e′ = 1 regime); §5 `liftAtOfRootF1`/`liftAtOfPrime` — `towerPacks` fires through both constructors (the prime route re-domains via `Ideal.Quotient.isDomain`, no field needed on the source) |
| 2′. keystone nonvacuity | **HONEST PARTIAL — remainder named exactly (§6 of the file), NO weakened substitute** | the S2 rung-3 instance does NOT close in this unit: `ofRootF1` needs three S2 dictionary lemmas, none landed — (W-a) the S2 rung-2 `RungPack` (WCC's `s2Carrier/s2Key` lack only `exact_ne`, the eval-1 nonvanishing below the g8 fence — true by the same singleton mechanism one level down, needs C132rp1's `s2Mu3Coeff` gates); (W-b) `nextSupp = 170` at `g16` (the `nextSupp ↔ dv3Supp/s2Hgt₄` identification + landed `g16_exactGrade`); (W-c) `eval 1 (nextRead 170 g16) = 0` (from landed `s2Mu4GradedRes_g16 = X+1`, eval-1 is reindex-invariant).  All three are S2 plumbing against landed content, no new structure — the exact successor charge |
| 3. `PrevGrade` f′ ≥ 2 + `CarrierReadLaw` tie | **DONE — honest fences, machine-visible collapse recorded (§7 of the file)** | `PrevGrade` is a CALCULUS-spine field (`LevelSiteBank.prev`), vacuous at f′ = 1; on the carrier spine there is NO analogous obligation at any rung (the lattice gate is definitional in `wcoeff`; `ofRootF1`'s signature carries no `PrevGrade`-genre input).  `CarrierReadLaw`: its multiplicativity half is exactly what `pushCarrier (nextCarrier R) φ` exports at every rung (the `hmul` input of LRS's `carrierReadLaw_of_mult_agree`); the kernel-agreement and peel-tie halves are realization-side — the carrier→calculus spine-bridge leg, same as D3AD-spine's remaining calculus leg |

## The mathematical findings (what changed about the obligation map)

1. **The root relation was mis-classified as irreducibly per-rung.**  RUNG's fence
   (`carrierKey_nextCarrier_isEmpty`) forces a proper quotient; RL3 shows the quotient
   CHOICE discharges the root relation: `AdjoinRoot.mk ρ (nextRead kg key₃) = 0` iff
   `ρ ∣ nextRead kg key₃` — and a prime factor EXISTS generically over a field whenever
   the read has positive degree (`exists_prime_factor_nextRead`; the read is nonzero
   from `supp_key` alone).  What is genuinely per-rung: WHICH factor (= the residual
   polynomial), and `SmallCoprime` — the FGMN Cor 4.9(1) content.
2. **★ The D3AD-interface laws propagate up the tower for free.**  `supp_mod` and
   `supp_quot` at rung k+1 are THEOREMS given the rung-k pack + the factor datum
   (`nextSupp_quot_le` even holds for EVERY dividend, no degree fence).  Proofs are
   neg-free on the support side: all ultrametric case analyses read at the dominated
   grade and use `nextRead_ne_zero_of_exact`/`nextRead_mul`/`nextRead_above` only;
   `Prime ρ` is consumed exactly once (the `supp_mod` equal-grade case, factoring the
   product read).
3. **★★ The f′ = 1 regime is CLOSED generically** — the deepTwist program's rung-≥3
   obligation in the totally-ramified-residual regime reduces to three data: the next
   key's exact grade, a nonzero root of its read, the next slopes with `ℓ'·kg < u'`.
   Mechanism (`nextRead_eq_monomial`): guard slots on a grade diagonal are spaced `ℓ`
   apart (`Nat.ModEq.cancel_left_of_coprime` at `gcd u ℓ = 1`) while dev slots run only
   to `⌊deg g/deg key⌋ < ℓ` (`dev_eq_zero_of_lt` + `deg key₃ ≤ ℓ·deg key`) — so exact
   reads are monomials `C w·X^{j₀}`, `w ≠ 0`, and eval at `c ≠ 0` cannot vanish.  The
   next ring is `K` itself: an f′ = 1 stream iterates WITHOUT ring growth
   (`liftAtOfRootF1`), matching the S2 witness where every stage reads in `fld 2`.
4. The S2 witness answer to the charge's C136 grep: the s2Mu4/s2Mu5 refinement calculi
   used the SAME root mechanism at depth ≥ 3 — residual `X+1`, letter `1`, char 2
   (`s2Mu4NormRes_g16 = X+1`, C136d2 D3-14) — witness-specific is only the root VALUE
   and the numerals `(g16, 170, (u₄,2))`; everything else is now the generic §§1–5.

## Honesty

* Uniform in `q` and the frame: zero numerals, zero `residueCard`, zero S2 data in all
  declarations (grep: S2 names appear only in §6/§7 comments and the module docstring).
* Nothing weakened: `RungLift`/`CarrierKey`/`RungPack`/`PackAt`/`LiftAt` consumed
  verbatim; no landed file edited (aggregator import line only); the constructors SUPPLY
  the signed shapes, never alter them.  The keystone instance is NOT claimed — §6 names
  the three missing dictionary lemmas instead of substituting a toy witness.
* Honest hypotheses: `SmallCoprime` (per-rung, the true FGMN residual content at
  e′ > 1), `hsupp` (the exact iterated grade — the tower-norm computation), the slopes
  (`hfloor` genre, D3AD-spine's B-1 row), `Prime ρ`/root datum; `[Field K]` only where
  factor EXISTENCE is claimed (§4); `[IsDomain K]` for the f′ = 1 route (prime
  linear factors), `[NoZeroDivisors K]` elsewhere — each the minimal ambient.
* Local twins (flagged for the standing dedup): the `wcoeff` guard unfoldings
  (`if_pos`/`if_neg` forms, 5th corpus repetition) and `natDegree_mod_lt`.

## New statements flagged for the standing review

`SmallCoprime`, `nextSupp_quot_le`, `nextSupp_mod_eq`, `RungLift.ofPrime`,
`nextRead_eq_monomial`, `RungLift.ofRootF1`, `exists_prime_factor_nextRead`,
`smallCoprime_of_natDegree_le`, `liftAtOfRootF1`, `liftAtOfPrime` (supplier-side
interface shapes below the signed surface; no leanspec name touched).

## The remainder map after this unit

| leg | before (RUNG §2.3 / D3AD-spine) | after RL3 |
|---|---|---|
| `RungLift` per rung ≥ 3 | open, shape pinned, "genuinely new research" | **generic core DISCHARGED**: root relation by construction; supp_mod/supp_quot derived; f′ = 1 fully closed given (grade, root, slopes); f′ ≥ 2 given (prime factor — exists generically over a field, `SmallCoprime`, grade, slopes) |
| the S2 rung-3 instance | — | three named dictionary lemmas (W-a/b/c above); then `liftAtOfRootF1` + `towerPacks` fire with the tower's own μ₅ slopes |
| `PrevGrade` at f′ ≥ 2 | open | fence recorded: calculus-spine field, no carrier-side analogue arises; belongs to the spine bridge |
| `CarrierReadLaw` tie | — | multiplicativity half supplied by the packs at every rung; kernel/tie halves = realization-side spine bridge |

## Verification, repair log, footprint

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift3.lean`
  throughout; FINAL per-file exit 0, 0 errors, 0 warnings, 0 `sorry`; AxCheck **9/9**
  Lean-core (`nextSupp_quot_le`, `nextSupp_mod_eq`, `RungLift.ofPrime`,
  `nextRead_eq_monomial`, `RungLift.ofRootF1`, `exists_prime_factor_nextRead`,
  `smallCoprime_of_natDegree_le`, `liftAtOfRootF1`, `liftAtOfPrime`); per-target
  `lake build Uniformity.ChapI.I10RungLift3` — Build completed successfully (8854
  jobs); aggregator `Uniformity/ChapI.lean` re-verified exit 0 after the one standing
  import-line edit.  Honesty grep confirmed: every S2/`residueCard` string in the file
  sits in comments/docstrings only; `grep -c sorry` = 0.
* Repair log (4 rounds, all mechanical, zero mathematical rework): (1) this mathlib's
  `modByMonic_add_div` takes the divisor polynomial, not the monic proof (matching
  WCC's note); (2) `rw [← hid]` (division identity) rewrites every `f` occurrence —
  restructured to apply `nextRead_add` on the sum and `rw [hid]` at the hypothesis;
  (3) one `rw` orientation slip; (4) `Nat.ModEq.cancel_left_of_coprime` wants
  `gcd ℓ u`, and `natDegree_le_of_dvd` needs `[NoZeroDivisors K]`; (5) the
  `[Field Q.K]`-on-`PackAt` instance diamond (RUNG's flagged risk DID bite at the
  wrapper) — resolved by DROPPING the field: `liftAtOfPrime` re-domains the quotient
  via `Ideal.span_singleton_prime` + `Ideal.Quotient.isDomain`, strictly more general.
* Footprint: `leanfinal/Uniformity/ChapI/I10RungLift3.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed theorem
  file edited; no git operation; IFCG60 untouched.
