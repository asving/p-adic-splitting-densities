# ENGINE REFIT: `engine_ext.py` — the standing extension over the two committed capability walls (2026-08-08 campaign)

**Unit:** ENGINE REFIT (dispatched after the (SD-YJ′) adjudication, ledger
e01ed12; the construct-unit wall disclosure, ledger 1047b48).
**Machine leg:** `verification/openmath/engine_ext.py` (+ its run artifacts
`engine_ext_output.txt`, `engine_ext_results.json`).
**Seal discipline:** two-commit — this note's prediction sheet + the runner are
committed BEFORE the sealed battery; the verdict section is appended from the
artifacts in commit 2.

## The two walls (why this unit exists)

The committed engine chain is consumed byte-pinned by many sealed artifacts and
is NEVER edited. Two capability walls were machine-lit this week:

- **(W1)** `grb_order2_check.fp_irreducible` raises `ValueError` above degree 2,
  and `pick_irreducible` enumerates only `[b, a, 1]` at g ≥ 2 — at g = 3 the
  committed chain SILENTLY returns a degree-2 ψ₀ and then hangs in `PE.prep`
  (the SURVDISJ-CONSTRUCT `CON-WALL` disclosure; the earlier "g₀ ≥ 3 cost wall"
  wording was wrong). The construct unit's fix is UNIT-LOCAL
  (`survdisj_construct.py`, deg ≤ 3 only).
- **(W2)** `grb_order2_check.Tower.__init__` hardcodes a QUADRATIC φ̄ for every
  d₀ ≥ 2 (`[1,1,1]` at p = 2 else `[1,0,1]`) — at d₀ = 3 it silently builds a
  deg-2 root key (the (SD-YJ′) `SDYJ-WALL` disclosure). d₀ ≥ 3 was engine-dark.

## What `engine_ext.py` provides

A standalone extension module: committed engines imported READ-ONLY, extended
in memory only (disclosed call-time patches; files on disk untouched).

1. **General-degree irreducible generation/verification over F_q**
   (`fp_irreducible_gen`, `irr_certificate`, `pick_irreducible_gen`): deg ≤ 2
   delegates to the COMMITTED functions verbatim; deg ≥ 3 (capped deg 8)
   computes TWO independent legs on every call — trial division by all monic
   divisors of degree ≤ deg/2, and the Rabin/Frobenius criterion
   (x^(q^d) ≡ x mod A, gcd(x^(q^(d/r)) − x, A) = 1 for primes r | d) — and
   raises on any disagreement (the non-textual-decorrelation discipline).
   Certificates carry a re-verified witness factor when reducible. The g ≥ 3
   pick continues the committed enumeration convention one degree up and is
   candidate-order-identical to the construct unit's g = 3 pick.
2. **The corrected general-d₀ tower** (`TowerExt`, a subclass; the committed
   `Tower` untouched): the committed constructor with exactly two blocks
   generalized — the φ̄/Φ₀ block (`phibar_of`: committed hardcodes VERBATIM on
   the committed grid d₀ ≤ 2, p ∈ {2,3}; first certified irreducible of degree
   d₀ over F_p elsewhere; the committed Fpt t-noise convention — x¹-coefficient
   gets +t — continued to all degrees) and the ψ-picks (routed through the
   general pick, byte-identical at g ≤ 2 by delegation). ALL methods inherited
   unchanged, so equal attributes ⇒ equal behavior.
3. **`install()`** routes the whole multi-level chain through the extension:
   `G.fp_irreducible`/`G.pick_irreducible` rebound + `strata3_probe.Tower =
   TowerExt` (Tower3/4/5 and `PE.Eng` all construct the level-0/1 tower through
   strata3_probe's binding, so one rebind carries every engine level).
4. **`agreement_gate()`** — the re-runnable LAW-KEYED agreement battery.

## THE STANDING RULE (for every future unit)

**Instruments needing shapes beyond the committed walls (g ≥ 3 residues,
d₀ ≥ 3 root keys, deg ≥ 3 irreducibility) import `engine_ext` and call
`install()` — no new unit-local pick/tower forks — and RE-RUN
`engine_ext.agreement_gate()` in-unit, reporting its counts in the unit's
verdict families.** The committed engines stay byte-pinned; the extension is
the single disclosed seam.

## Sealed prediction sheet (commit 1; verdict appended in commit 2)

All families predict **0 violations** unless marked measured:

| family | content | prediction |
|---|---|---|
| EXT-PIN | md5 pins, 13 consumed artifacts | 0 |
| EXT-WALL | (W1)+(W2) reproduce from COMMITTED objects; TowerExt clears d₀=3 (wall counters exactly 3 + cleared + routing) | 0 |
| EXT-WALL3 | census: committed-style hardcode X²+1 REDUCIBLE at p ≡ 1 (mod 4) — witness roots at p = 5, 13 (latent THIRD wall; committed rosters never ran there) | measured (2 witnesses) |
| AGR-IRR | gen == committed on EVERY monic deg ≤ 2 over F2/F3/F5/F4/F9 | 0 |
| AGR-CERT | division leg == Frobenius leg on EVERY monic deg 3 (F2/F3/F4/F9) and deg 4 (F2/F3/F4); census == Gauss/Möbius count; witnesses re-verified | 0 |
| AGR-PICK | gen pick == committed pick, g ∈ {1,2}, idx ∈ {0,1,2}, five fields | 0 |
| AGR-IRR3 | gen == construct unit's `fp_irr_gen` on every monic cubic (4 fields) | 0 |
| AGR-PICK3 | gen pick == construct unit's `pick_irr_gen` at g = 3: FULL idx scan F2/F3/F4, idx ≤ 2 on F9 | 0 |
| AGR-TOWER | TowerExt attribute-exact vs committed Tower (19 attributes) on the full grb ROSTER × 4 rings, mode C + mode P on C/D/E/H/J = 60 pairs | 0 |
| AGR-ENG | multi-level Φ-data byte-exact, reference routing vs extension routing, 4 Eng specs (incl. one g₀ = 3) | 0 |
| EXT-GRB | the COMMITTED order-2 law families T1–T8 + T10 (harness code unchanged, RNG reseeded 20260808) on the FIRST deg ≥ 3 root keys: d₀ ∈ {3,4} × 4 rings × 3 read-shapes = 8 towers | 0 (incl. the T8 TOTAL-form gate) |
| EXT-PARI | external oracle: factorpadic irreducibility + unique prime (e,f) = (e₀e₁, d₀g₀g₁) on 4 Zp towers at d₀ ∈ {3,4} | 0 |
| REB | the 3 committed g₀ = 3 towers (C3W2F / C3K2AF / C3OM3F) re-run through `survdisj_construct.run_tower` under the extension routing: 42 committed row records dict-EXACT vs the pinned results json; 0 new construct violations/findings/skips | 0 |
| D3-SDYJ | the FIRST d₀ = 3 towers (g₀ = 1: D3YJ2F, D3YJ3FLT, D3YJ3FLTB, D3YJ3Z, D3YJ3F3, D3YJ4FLT + one d₀ = 4 FIRST, D4YJ3FLT) under the `sdyj_checks_v2` portable families SDYJ-GAM/DIG/CASC/SUPER/COMP/NEP + HARNESS (the (SD-YJ′) proof is d₀-blind — these are its first d₀ ≥ 3 instances) | 0 violations, 0 skips; companions measured |

**Disclosures (pre-seal):** (i) a build-phase prototype smoke of the same logic
ran outside the repo (throwaway /tmp scripts; it caught one prototype-only bug:
a shared-generator misuse in the division leg's `itertools.product` — fixed
before this runner was written); (ii) `python3 engine_ext.py --shakedown`
(crash-freedom probe: reduced grids, 1 rebuild tower, 1 d₀ = 3 tower, no json)
ran clean before commit 1; (iii) `EXT-GRB` reseeds the committed harness RNG to
its own committed seed 20260808 for reproducibility; (iv) `cypari2` presence
was probed pre-seal (available; an unavailable oracle would be a RED, not a
skip).

## VERDICT (commit 2 — appended from the sealed artifacts)

**ALL GREEN — 0 violations in all 13 families; every sealed prediction hit
exactly** (`engine_ext_output.txt`, `engine_ext_results.json`; elapsed 10.7 s).

- **EXT-PIN** 13/13 pins green. **EXT-WALL** both walls reproduced from the
  committed objects (counters `wall_pick_deg2`, `wall_irr_valueerror`,
  `wall_quadratic_phi0` each = 1) and cleared by `TowerExt`
  (`wall_cleared_d0_3` + `routing_verified` — a `PE.Eng` at d₀ = 3 carries a
  `TowerExt` with a cubic root key through the full chain).
- **Agreement battery, LAW-KEYED, 0 violations everywhere:** AGR-IRR 158
  deg ≤ 2 cases; AGR-CERT 1181 double-leg certificates with 7/7 Gauss/Möbius
  census confirmations (the non-textual count leg); AGR-PICK 30 cases;
  AGR-IRR3 828 cubic cases and AGR-PICK3 33 picks vs the construct unit's
  local extension; **AGR-TOWER 60/60 tower pairs attribute-exact** (full grb
  ROSTER × 4 rings, modes C+P); AGR-ENG 4/4 multi-level pairs byte-exact.
- **EXT-GRB:** the committed order-2 law families T1–T8 + T10 run UNCHANGED on
  the first deg ≥ 3 root keys — 8 towers (d₀ ∈ {3,4} × 4 rings × 3
  read-shapes), 0 violations including the T8 TOTAL-form gate.
- **EXT-PARI (external oracle):** all 4 Zp towers confirmed — d₀ = 3: deg-12
  Φ₂ irreducible over Q₂ and Q₃ with (e,f) = (4,3); d₀ = 4: deg-8 Φ₂
  irreducible with (e,f) = (2,4). The corrected constructor's first deg ≥ 3
  root keys are externally certified OM data.
- **REB (the rebuild leg):** `reb_rows_exact` = **42/42** — the three committed
  g₀ = 3 towers (C3W2F 16 rows, C3K2AF 22, C3OM3F 4) re-traced through the
  extension routing reproduce the pinned `survdisj_construct_results.json`
  row records dict-EXACTLY, 0 new construct-family violations, 0 new findings,
  0 skips.
- **D3-SDYJ (the first d₀ ≥ 3 instances):** 7 towers (6 × d₀ = 3 incl. Zp and
  p = 3, m up to 4, + the d₀ = 4 first D4YJ3FLT), 15 live rows, **every
  cascade slot SURV**, 0 violations in SDYJ-GAM/DIG/CASC/SUPER/COMP/NEP +
  HARNESS — the (SD-YJ′) proof's d₀-blindness is now instance-backed at
  d₀ ∈ {3,4}. **14 companions measured** (census): every gain ≥ 1 as the
  SDY-L1/L2 floors force, with the flat-shape towers showing the same sharp
  gain-1 companions as their d₀ = 2 twins (D3YJ3FLT/D3YJ3Z/D4YJ3FLT: w₀ = 18
  at ŵ = 17 — the w₀/gain ledger is exactly d₀-invariant on these shapes,
  while lines shift with E_m·(w₀−ŵ) as SDY-L3 predicts), and richer gains
  {2,4} on D3YJ3FLTB / {1,2} on D3YJ4FLT.
- **EXT-WALL3 (measured, as predicted):** the latent THIRD wall machine-lit —
  the committed d₀ = 2 hardcode X²+1 is reducible at p ≡ 1 (mod 4) (witness
  roots 2 mod 5, 5 mod 13); `phibar_of` picks certified irreducibles there
  ([1,1,1] mod 5, [1,3,1] mod 13). The committed rosters never ran that
  perimeter, so no sealed artifact is affected.

**Standing rule now in force** (see above): future instruments import
`engine_ext` + `install()` for beyond-wall shapes and re-run
`agreement_gate()` in-unit. The K2-ENG "T1-RES" boxed door (the g₀ = 3
double-kill at budget n = 5) and the PE-Y1 queue can now be attempted without
unit-local engine forks.
