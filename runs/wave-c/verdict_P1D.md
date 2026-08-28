# UNIT P1D verdict — P1 CLOSED OUTRIGHT: the cite dies before being born (2026-08-28)

## Outcome (headline)

**`IsTestKey L Ψ → IsMuKey L Ψ` is now a THEOREM** —
`Uniformity.Density.Tower.C134p1d.isMuKey_of_isTestKey` in the new file
`leanfinal/Uniformity/ChapC/C134p1d.lean` (833 lines), footprint exactly
`[propext, Classical.choice, Quot.sound]` on every one of its 11 declarations, zero
`sorry`, zero new axiom, no `exists_dvDissection`.  This is P1U's route (a) — priced
there as "substantially the unformalized proof of GN Lemma 3.1(3)" — completed.  The
planned cite **AX-GN-REPKEY (P1U's `isMuKey_of_isTestKey` axiom draft) is RETIRED
UNDECLARED**: no axiom, no faithfulness entry, no CITE_REVIEW_LIST row is needed.  The
theorem's statement is byte-shaped as P1U's draft (same binders `L hπ hh {Ψ} hΨ`, same
conclusion `C134dv2g.IsMuKey L Ψ`), so every consumer P1U anticipated fires unchanged.

## The per-clause dictionary table (charge item 2)

`C134dv2g.IsMuKey L Ψ = Ψ.Monic ∧ MuMinimal L Ψ ∧ MuPrime L Ψ`, against C.13's clauses:

| `IsMuKey` conjunct | Verdict | Mechanism | Declaration |
|---|---|---|---|
| `Ψ.Monic` | **DEFINITIONAL** | = `IsTestKey` clause 1 | (projection `hΨ.1`) |
| `0 < deg Ψ` (in `MuMinimal`) | **PROVED** | clause 2 (`deg Ψ = keyDeg₂`) + frame positivity | `natDegree_pos_of_isTestKey` |
| `MuMinimal L Ψ` | **PROVED** | degree count: `Ψ ∣µ g` ⟹ `L.r ∣ R(g)` (landed P2 bridge, contrapositive) but `deg g < deg Ψ = D′ℓd` ⟹ side abscissae `< ℓd` (B.04) ⟹ `deg R(g) = dvSideDeg(g) < d = deg L.r` (C.26 teeth: `R(g) ≠ 0`, exact degree) — divisibility impossible | `muMinimal_of_isTestKey` via `not_residual_dvd_of_natDegree_lt` |
| `MuPrime L Ψ` — head | **PROVED** | `Ψ ∣µ g·z` ⟹ `L.r ∣ R(g)·R(z)` (Theorem M clause 3 `C133mh3.dvResPoly_mul_gen`) + `L.r` prime in `K[y]` (`L.hrirr`, EuclideanDomain→PID→UFD) | `residual_dvd_or_of_muDvd_mul` |
| `MuPrime L Ψ` — residual lift `L.r ∣ R(g) → Ψ ∣µ g` | **PROVED** (was P1U's "real literature wall") | the S2 `C130kp1.S2MuDvd_of_normRes_dvd` remainder mechanism, made frame-generic — see below | `muDvd_of_residual_dvd` |
| assembly | **PROVED** | conjunction | `isMuKey_of_isTestKey` (+ factored forms `…_of_muPrime`, `…_of_residualLift`, `muPrime_of_residualLift` kept as the record of the exact leg a cite would have supplied) |

## Why the lift was provable after all (the mechanism P1U's pricing missed)

P1U assumed the lift needs a residual-REALIZATION lemma (construct a polynomial with
prescribed residual — a C.14-scale build).  The S2 file C130kp1 shows the published
Lemma 5.2 mechanism avoids it: **the μ-cofactor is the literal polynomial quotient
`g /ₘ Ψ`**.  Frame-generically, with `r := g %ₘ Ψ`, `q := g /ₘ Ψ`, `V· := dvSupp · L.u L.ℓ`:

1. `deg g < deg Ψ` — impossible outright (`L.r ∣ R(g)` dies on the degree count).
2. `r = 0` — `q` is the witness (`g = Ψ·q` exactly).
3. `V(Ψq) < V(r)` — the quotient term carries the initial form: `q` is the witness
   (landed ultrametric `dvSupp_add_eq_of_lt`).
4. `V(r) < V(Ψq)` — then `g ∼µ r`, so `L.r ∣ R(r)` (landed `dvResPoly_eq_of_muEquiv`)
   with `deg r < deg Ψ` — killed by the degree count.
5. `V(r) = V(Ψq) < V(g)` (tie with cancellation) — then `r ∼µ Ψ·(−q)`, i.e. `Ψ ∣µ r`,
   so `L.r ∣ R(r)` (landed forward bridge) — killed by the degree count.
6. `V(r) = V(Ψq) = V(g)` (full tie) — **the one genuinely new tool**: the `V`-line read
   `lineRes` (private, Part 8) — the residual read along the whole value line, based at
   `j₀ = jmin % ℓ`.  It is ADDITIVE (C130rp2's `twistRead_add_of_le` digitwise through
   B32a's linear `dev_add_of_monic`) and equals `dvResPoly · X^δ` (`lineRes_eq_shift`,
   by C26-style slot bookkeeping: on-window slots read the residual coefficients
   verbatim; off-side line slots vanish by `twistRead_eq_zero_of_lt`; the truncation cap
   `t ≤ N₀/u` covers every on-side slot of every tied summand).  Then
   `L.r ∣ lineRes(g)` and `L.r ∣ lineRes(Ψq) = (L.r·R(q))·X^γ` force
   `L.r ∣ lineRes(r) = R(r)·X^β`; `L.r` is prime with nonzero constant term (`L.hr0`),
   so `L.r ∤ X^β` and `L.r ∣ R(r)` — killed by the degree count.

Every non-new ingredient is a landed public theorem: C.26 (`natDegree_dvResPoly`,
degree + nonzero constant term), C133mh3 (Theorem M clause 3), C131y (`dvSupp_le_term`,
`dvHgt_eq_top_of_natDegree_lt`), C130rp2 (read additivity/vanishing/zero), C130s6
(ultrametric `dvSupp` bank), C.34 (`dvSideSet_nonempty`), C.08 (`dvSideLen_eq`), B.04
(`dev_eq_zero_of_lt`), B32a (`dev_add_of_monic`), C131aa (`dvResPoly_testKey`), C134p1
(P2's bridge).  The private plumbing re-declared per the standing local-twin convention:
`isKey_X`, `localFieldStageField`, `exists_pin`, `dvResPoly_congr`.

## Disposition of P1U's deliverables

* **AX-GN-REPKEY faithfulness entry (P1U draft): DEAD — never declared.**  Record for
  the axiom ledger: the intended content is now the machine-checked theorem
  `C134p1d.isMuKey_of_isTestKey`; GN Lemma 3.1(3) is no longer trusted content anywhere
  in the corpus.
* **The narrow-cite design this unit would have delivered had the lift failed** (for the
  record only): the dictionary had already shrunk the trusted content from all of
  `IsMuKey` to the single conjunct `MuPrime L Ψ` (Monic definitional, `MuMinimal`
  proved), and further to the lift `∀ g ≠ 0, L.r ∣ R(g) → Ψ ∣µ g`
  (`muPrime_of_residualLift` is the machine-checked reduction).  Both reduction theorems
  are kept in the file, so the decomposition is auditable even though moot.
* **GN pdf location (charge: "verify which file")**: the GN *Genetics* paper is **NOT**
  in `docs/references/`.  Present there: the FGMN *Residual ideals* paper twice
  (`FGMN_residual_ideals_2015_authorpdf.pdf`, `fgmn_residual_ideals_1305.0775v3.pdf` +
  `_layout.txt`) and `s10208-024-09646-x.pdf` = Alberich-Carramiñana–Guàrdia–Nart–
  Poteaux–Roé–Weimann, *Polynomial Factorization Over Henselian Fields*, FoCM 25 (2025)
  — a survey covering the same key-polynomial theory.  Moot for citation purposes now.

## Statements flagged for human review (trust boundary — new statements)

1. `not_residual_dvd_of_natDegree_lt` — "below the recipe degree, `L.r ∤ R(g)`".
2. `muDvd_of_residual_dvd` — the backward translation (statement shape: for a test key
   `Ψ` and any `g ≠ 0` with side witness/pin, `L.r ∣ R(g) → MuDvd L Ψ g`).
3. `isMuKey_of_isTestKey` — the P1 statement itself (byte-shaped as P1U's axiom draft,
   with `hπ : Irreducible π`, `hh : 0 < F.h` exactly as drafted), now load-bearing for
   DV2G's F1.3–F1.6 chain.

## Downstream (what this unblocks — not attempted here)

`C134dv2g` Part 7's BLOCKED-BECAUSE record listed three premises for signed F1.3:
**(P1)** `IsTestKey → IsMuKey` — **now discharged by this unit**; **(P2)** the
complement's `¬ MuDvd` — landed at `C134p1.block_complement_not_muDvd`; **(P3)** the
engine floor — A-C.22 ENACTED (unit A22E).  The F1.3 signed assembly (feeding
`dv2Supp_translation_of_muKey` with `C131aa`'s test-key grade `KΨ = L.ℓ·L.seam`) is now
a pure plumbing unit; F1.4–F1.6 still need the `dv2Res` cocycle telescope / side-min
equality mechanisms recorded by DV2G.

## Verification record

```text
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134p1d.lean
```

Exit 0; zero errors, zero warnings; the only textual "sorry" is the docstring word
"sorry-free"; AxCheck footer prints `[propext, Classical.choice, Quot.sound]` for all
11 public declarations (`natDegree_pos_of_isTestKey`,
`not_residual_dvd_of_natDegree_lt`, `residual_dvd_of_muDvd`, `muMinimal_of_isTestKey`,
`residual_dvd_or_of_muDvd_mul`, `muPrime_of_residualLift`,
`isMuKey_of_isTestKey_of_muPrime`, `isMuKey_of_isTestKey_of_residualLift`,
`muDvd_of_residual_dvd`, `muPrime_of_isTestKey`, `isMuKey_of_isTestKey`).  No landed
`.lean`/leanspec file was edited; no git operation was performed.
