# UNIT RB3R — `refine_invariants` (C.56) re-based against the completed Hensel engine

**Date:** 2026-08-28 · **Charge:** re-adjudicate the C93Census item `refine_invariants`
(recorded BLOCKED by C93T, citing `C150rb3.lean`'s pre-engine gap analysis "genuinely new
~200–900 line Hensel-refinement mathematics") against the landed dv-graded one-slope
Hensel engine (C133mh0–mh15, C134*, C134dv2g).

**OUTCOME: (b) PARTIALLY — sharpened.** Conjuncts 1–2 of the signed conclusion plus
IsTestKey conjuncts 3 and (conditionally) 4 are **LANDED** in
`leanfinal/Uniformity/ChapC/C150rb4.lean` (compiles clean, all footprints Lean-core
only). The remainder is **NOT a missing-mathematics gap and NOT an engine gap**: the
signed `IsTestKey` conjunct is a ⚠ **STATEMENT-LEVEL DEFECT** (an elaboration overclaim
relative to the source clause `EFF.GENTOW1.28`) — unprovable as signed, and false under
any faithful (pinned) reading of `k2Coord`. Codex-verified (5/5 claims CONFIRMED, no
CRITICAL; log `runs/wave-c/RB3R_codex_log.txt`, brief `runs/wave-c/RB3R_codex_brief.txt`). The C93T
pricing ("~200–900 new lines of Hensel mathematics") is **SUPERSEDED**.

---

## 0. The signed statement (leanspec `Leanspec/ChapC.lean:2163`; blueprint NODE C.56,
`blueprint/CHAP-C_tower_grammar.md:3583`)

Under hypotheses about `f ∈ towerLocus T μ₂` (level-2 side of `composedKey T` at slope
`(lam, 1)`, `lam > E₂`, residual `(X − C s)^μ₂`, `s ≠ 0`), conclude for
`Φ₂⁺ := composedKey T − k2DigitLift T s lam`:

1. `Φ₂⁺.Monic`
2. `Φ₂⁺.natDegree = T.D₂`
3. `IsTestKey (T.levelDatum hπ) Φ₂⁺`

`IsTestKey L Ψ` (C13.lean:143) is the rigid HE6-1 test-family membership: monic ∧ degree
`keyDeg₂` ∧ top `F.key`-digit `= 1` ∧ **off-lattice digits `= 0` exactly** (clause 4) ∧
per-slot: **zero-label slots have digit `= 0` exactly** (clause 5a) / nonzero-label slots
have exact pinned height `(f₂−t)u₂` and twist-read `= r.coeff t` (clause 5b).

**Key structural fact:** the conclusion mentions `f` NOWHERE. The hypotheses enter only
through `s` and `lam`.

## 1. Sub-demand mapping table (C150rb3's gap analysis → the engine / the landed / the defect)

C150rb3's BLOCKED note named two sub-demands; the conclusion decomposes over five
IsTestKey clauses. Rows below map each onto the post-engine corpus.

| # | Gap sub-demand / conclusion clause | Post-engine status | Where |
|---|---|---|---|
| G1 | "transport `f`'s dv2-residual pattern to `composedKey T`'s own residual at that slope" | **MOOT for the signed statement** — the conclusion never mentions `f`; the hypotheses can be discarded wholesale. (The demand arose from reading the intended refinement mathematics, which the signed statement routes through `s` alone.) | — |
| G2 | "subtract the digit lift, the corrected key is still monic/right-degree" | **LANDED NOW**, engine-independent: the lift's degree bound is pure exponent numerology (`slotIdx_spec` `i<e₁`, `towerSolve_lt` `b<e₂` ⟹ `deg < D₂`), then `Monic.add_of_left` + `natDegree_sub_eq_left_of_natDegree_lt`. This proves the blueprint's `.27` rider "deg lift < D₂ always". | `C150rb4.lean`: `natDegree_k2DigitLift_lt`, `corrected_monic`, `corrected_natDegree` |
| C3 | IsTestKey conjunct 3 (top digit = 1) | **LANDED NOW**: `dev_sub` (C131v) + `composedKey_top_digit` (C47) + `dev_eq_zero_of_lt` (B04) on the degree bound. | `C150rb4.lean`: `corrected_top_digit` |
| C4 | IsTestKey conjunct 4 (off-lattice digits = 0 exactly) | **SPLIT.** At `e₂ ∣ lam`: LANDED (`towerSolve` vanishes on the lattice ⟹ the lift's digits sit at abscissae `e₂·t` only). At `e₂ ∤ lam`: **FALSE for `Φ₂⁺`** — every lift term sits at `F.key`-exponent `b₀ + e₂t` with `b₀ = towerSolve u₂ e₂ lam ≠ 0` (constant over terms: `Δ(r,t) ≡ 0 (mod e₂)`, no ℕ-truncation since `Δ < E₂ < lam`), i.e. the corrected key CARRIES the lift's own digits at exactly the positions clause 4 forbids. The engine cannot help: its perturbation law (M4) preserves height floors and side data, not exact zeros. | landed half: `C150rb4.lean` `dev_k2DigitLift_off_lattice`, `corrected_offLattice_digit`; defect half: §2 below |
| C5a | IsTestKey conjunct 5, zero-label branch (digit = 0 exactly at slots with `(towerLabel T).coeff t = 0`) | **FALSE for `Φ₂⁺` in general** (even at `e₂ ∣ lam`): at such a slot the composed key's digit is 0 (C47 `composedKey_zero_slot`), so `Φ₂⁺`'s digit is −(the lift's slot digit), nonzero whenever the `t`-coordinate of `s` is nonzero. Nothing constrains `supp(s) ⊆ supp(towerLabel T)`. Reachable: legal labels with interior zero coefficients exist (C47's own record: `ψ₂ = X²+1` over `F₃`). | §2 below |
| C5b | IsTestKey conjunct 5, nonzero-label branch (exact slot heights `(f₂−t)u₂` + twist reads preserved) | **DERIVABLE from landed atoms, not yet landed** (the honest remainder): the lift's slot digit has height `≥ (lam − u₂e₂t)/e₂ > (f₂−t)u₂` (choice-robust: `π^{a₀}`-divisibility from `n2Exp`'s grade equation `e₁e₂a₀ + ie₂h + bu₂ = lam − Δ`), then `dvHgt_add_eq_left_of_lt` (C131y) / `twistRead_add_eq_left_of_lt` (C131ae) — the exact atom set MH.6 consumes. Priced ~150–300 lines. At `e₂ ∤ lam` it is FREE (the lift has no digits on the lattice at all). | engine atoms C131ae/C131y + `C150rb4` numerology |
| E1 | Engine row: `C133mh0` MH.6 (M4 perturbation family: `deg y < deg x`, `W(y) ≥ W(x)+1` ⟹ monic/degree/purity/`M₀`/`dvResPoly` preserved) | This IS the faithful content of source clause (i) — see §3. Does NOT prove IsTestKey (exact zeros are not M4-stable). | `C133mh0.lean` |
| E2 | Engine row: `C133mh5` MH.5 (`dvSideLift`: monic Λ(P) with `R(Λ(P)) = P`, slot digits at exact heights, off digits zero) | Constructs a FRESH test-key-shaped lift from a prescribed residual — the clause list IS IsTestKey's, but for `dvSideLift P`, not for `composedKey − k2DigitLift`. Cannot substitute (signed statement pins the carrier `Φ₂⁺`). Reusable for a repaired refinement design. | `C133mh5.lean` |
| E3 | Engine row: `C133mh9.theoremA` (dv-graded Hensel factor-splitting: coprime residual factorization lifts to exact factorization with degrees/purity/heights/residuals) | Element-level (factors `f`), not key-level (does not correct `Φ₂`). Orthogonal to this node's conclusion. | `C133mh9.lean:1470`, statement `C133mh14.TheoremAStatement` |
| E4 | Engine row: `C133mh15.blockFrontier_of_context` | Consumer of E3 at the block frontier; orthogonal to C.56. | `C133mh15.lean:37` |
| E5 | Engine row: `C134dv2g` (level-2 support engine, `IsMuKey`, `dv2ResSurv`) | Supplies level-2 valuation-theoretic key-hood (`IsMuKey`) — the natural REPLACEMENT admissibility predicate for a repaired C.56 conclusion (μ-key-hood IS M4-stable). | `C134dv2g.lean` |

## 2. The statement-level finding (⚠ owner-review row, Tier 1)

**The signed `IsTestKey (T.levelDatum hπ) Φ₂⁺` conjunct is unprovable, and the axiom
should not be consumed as-is.** Mechanism (all Lean-verified support facts are in
`C150rb4.lean`; the semantic composite is Codex-CONFIRMED 5/5):

* Every `k2DigitLift T s lam` term sits at v₂-grade exactly `lam` with `F.key`-exponent
  `b₀ + e₂t`, `b₀ = 0 ⟺ e₂ ∣ lam` (`towerSolve` semantics + `hcop`).
* `dev` is unconditionally additive (`dev_sub`, C131v), so `Φ₂⁺`'s digit at any abscissa
  where `composedKey`'s digit vanishes is −(the lift's digit).
* Hence: at `e₂ ∤ lam` clause 4 demands `k2Coord T s t = 0` for ALL `t < f₂`; at
  `e₂ ∣ lam` clause 5a demands it at every zero-label slot. Neither is implied by the
  hypotheses.
* **No vacuity escape** (Codex, decisive): the signed statement permits `μ₂ = 0`, and
  `f = 1 ∈ towerLocus T 0` inhabits ALL hypotheses at EVERY `lam > E₂` and EVERY
  `s ≠ 0` (`(X − Cs)^0 = 1`; unit side facts landed: `C133mh9.isDvPure_one`/
  `dvResPoly_one`, `C132nv6` side-nonemptiness). No divisibility `e₂ ∣ lam` and no
  support constraint on `s` is forced.
* **The opacity twist** (the landed C56a `k2Coord` is the A-C.3 opaque
  `Classical.choice` read — the k2PB repair of 2e133686 was reverted at fc352404 to the
  byte-exact signed body): there EXISTS a pathological realization of the choice
  (representatives divisible by `X^{f₂}`, available since `β` is a unit) under which
  `k2DigitLift ≡ 0` and the axiom degenerates to C47's `composedKey_isTestKey`. Lean
  cannot derive that realization; under the canonical/power-basis reading the axiom is
  FALSE (e.g. the `s2Tower` instance: `e₂ = 2`, `E₂ = 10`, `lam = 11`, `s = 1`,
  `μ₂ = 0`, `f = 1`). So the signed statement is not a determinate claim about the
  intended objects: unprovable AND unrefutable in Lean, false under the faithful read.
* **Where the overclaim entered:** the source `EFF.GENTOW1.28` claims the
  perturbation-stable package — "monic of degree D2; level-1 development one-sided of
  slope kappa2 with residual psi2 and side digits byte-unchanged (what's slots sit at
  weight lam > E2, strictly above the key's side)" — NOT exact-zero test-family
  membership. The blueprint's "hence IsTestKey-hood … reruns verbatim" and the A-C.1
  leanspec elaboration turned a sufficient carrier (IsTestKey was the vehicle that
  proved the forcing package FOR `Φ₂`) into a claimed invariant of `Φ₂⁺` — reversing a
  sufficient implication without an equivalence.

**Consequence for consumers:** `refine_kills` / `refine_bijection` /
`refine_transported_event` (C.56(ii)/C.57) do not consume the IsTestKey conjunct
directly — their carrier needs `Φ₂⁺` monic of degree `D₂` (dv2-reads well-defined),
which IS landed here. Any future consumer wanting key-admissibility of `Φ₂⁺` should
consume the M4 package or `IsMuKey` (E5), not `IsTestKey`.

## 3. The re-priced remainder (the faithful repair, for the owner + a future unit)

The faithful GENTOW-2(i), in landed vocabulary, is:

> `Φ₂⁺` is monic of degree `D₂` [LANDED], `IsDvPure F Φ₂⁺ u₂ e₂` with `M₀` and
> `dvResPoly = the ψ₂-label` unchanged [= C133mh0 MH.6's exact conclusion at
> `x := composedKey T` (pure with residual label, landed via C47 + `isTestKey_isDvPure`),
> `y := −k2DigitLift T s lam`], plus the side-digit byte-equality [dev_sub + the lattice
> support lemmas landed here].

Missing input for MH.6: `W(k2DigitLift T s lam) ≥ E₂ + 1` — the grade floor of the lift,
choice-robust (`π^{a₀}`-divisibility numerology through `n2Exp`, same shape as
`C150rb4.xexp_lt/keyexp_lt`), priced **~100–250 lines**, plus clause 5b's slot-exactness
(~150–300 lines, atoms C131ae/C131y). Total honest remainder for a REPAIRED C.56(i):
**~250–550 lines against landed atoms** — engine-era pricing, versus the pre-engine
"200–900 lines of new mathematics". The statement repair itself (leanspec + blueprint)
is owner-gated; the natural repaired conclusion replaces conjunct 3 by the M4 package
(or `IsMuKey` per E5). The C56a opacity defect (A-C.5 lifecycle, k2PB retirement) is
independently on the books and blocks any VALUE-pinned clause until retired.

## 4. Landed artifact inventory (`leanfinal/Uniformity/ChapC/C150rb4.lean`, compiles
clean via `lake env lean`, footprints = {propext, Classical.choice, Quot.sound} — and
`towerSolve_lt` even {propext, Quot.sound})

| Theorem | Content |
|---|---|
| `towerSolve_lt` | `0 < e → towerSolve u e k < e` |
| `towerSolve_eq_zero_of_dvd` | `e ∣ k → towerSolve u e k = 0` |
| `n2Exp_snd_fst_eq` / `n2Exp_snd_snd_eq` | definitional bridges (slot index / solve) |
| `n2Exp_snd_fst_lt` / `n2Exp_snd_snd_lt` | `i < e₁`, `b < e₂` |
| `natDegree_k2DigitLift_lt` | `deg(k2DigitLift T s m) < T.D₂` (the `.27` rider) |
| `keyDeg₂_eq_D₂` | the C.48-pattern dictionary numeral, now public |
| `corrected_monic` | **signed conjunct 1**, hypotheses: `T, hπ, s, lam` only |
| `corrected_natDegree` | **signed conjunct 2**, same hypotheses |
| `corrected_top_digit` | IsTestKey conjunct 3 at `Φ₂⁺`, hypotheses `T, s, lam` only |
| `dev_k2DigitLift_off_lattice` | lift digit support on the lattice case (`e₂ ∣ m`) |
| `corrected_offLattice_digit` | IsTestKey conjunct 4 at `Φ₂⁺` under `e₂ ∣ lam` |

## 5. Supersessions

* `runs/wave-c/verdict_C93T.md` row (2) ("BLOCKED, unchanged … ~200–900 new lines"):
  **SUPERSEDED by this verdict** — the blocker is not missing Hensel mathematics; it is
  the signed conclusion's IsTestKey conjunct (statement defect, §2) + the booked C56a
  opacity (A-C.5). Conjuncts 1–2 are landed.
* `C150rb3.lean`'s BLOCKED note: its sub-demand G1 is moot for the signed statement;
  its "new mathematics on the scale of C.47/C.131w" pricing applies only to the
  now-defect-flagged conjunct; the true residue is §3's ~250–550 lines against landed
  atoms, PLUS the owner-gated statement repair.
* GenhnTow1At n ≥ 8 supply chain (C93Census consumer): the chain should NOT wait on
  `refine_invariants` as signed; it needs the repaired C.56(i) (M4 package) — whose
  price is now §3's, and whose two Lean-ready sub-lemmas (grade floor, clause 5b) can be
  dispatched as ordinary units once the statement repair is signed.

## 6. Verification record

* Lean: `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C150rb4.lean` — exit 0,
  zero errors/warnings, AxCheck footer all Lean-core.
* Codex adversarial pass (fresh context, quote-and-classify): Claims 1–5 ALL CONFIRMED
  (1, 2, 5 clean; 3, 4 with the opacity GAP-qualifier that is itself part of the
  finding); escape hatches (a) slope divisibility, (b) support constraint, (c) vacuity
  all CLOSED (μ₂ = 0 witness); hatch (d) identified the pathological-choice realization
  (recorded in §2). No CRITICAL. Log: `runs/wave-c/RB3R_codex_log.txt`.
