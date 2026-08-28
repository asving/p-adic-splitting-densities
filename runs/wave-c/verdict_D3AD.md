# Verdict D3AD — the depth-three μ-key adapter: D3-03 DISCHARGED, D3-04 LANDED

Date: 2026-08-28
Target: `leanfinal/Uniformity/ChapC/C136d3ad.lean` (new file; nothing else touched)

## ACCEPTANCE — STATUS FIRST

| row | status | exact result |
|---|---|---|
| **adapter adjudication** | **DECIDED: mirror, not instance** | (a) a depth-3 `LevelDatum` is IMPOSSIBLE; (b) the landed L2E engine is NOT LevelDatum-polymorphic at its root; (c) the survival core re-lands one level up in ~340 lines — details below. |
| **D3-03 `Dv3ResSurv` at `(g8, 85, 2)`** | **GREEN — UNCONDITIONAL** | `C136d3ad.s2_dv3ResSurv_at_85 : Dv3ResSurv ((s2Tower h2 hq).levelDatum h2) (s2DepthTwoKeyAt h2 hq 2) 21 2 (g8 h2 hq) 85 2` — the exact demanded carrier of `verdict_L2E3.md`'s "D3 exact adapter mismatch", no hypothesis beyond the standing S2 pair `(h2, hq)`. Lean-core footprint. |
| **D3-04 unconditional `s2Hgt₄_mul`** | **GREEN — UNCONDITIONAL** | `s2Hgt₄_mul_unconditional` (nonzero factors) + `s2Hgt₄_mul_all` (`AddValuation.of`'s `hmul` shape, zero cases folded) — the exact μ₄ twins of `C132nv6.s2Hgt₃_mul_unconditional`/`s2Hgt₃_mul_all`, fired through `C136d0.dv3Supp_mul_eq_add_of_endpoint_le` at the discharged survival. |
| **D3-10 `(85,2)` convolution** | **adapter prerequisite CLEARED; still blocked** | Its FIRST blocker (this adapter) is gone. Its SECOND blocker stands: L2E-09's fixed-grade coefficient read (`verdict_L2E3.md`'s `hconv` subgoal — `dv2Res` normalizes at its input's own height, so equal-grade diagonal cancellation breaks the sum-of-reads conversion). Untouched here, out of unit scope. |

## The adjudication, recorded honestly (charge item 2)

* **(a) IMPOSSIBLE.** `LevelDatum` (C.09) carries `(u, ℓ, r)` + hypotheses and NO valuation
  field. The engine's inner read is `dv2Hgt L := dvSupp F · L.u L.ℓ` (C.11) — a fixed
  single-development read through `F.stageHeight`. `Dv3ResSurv`'s inner read is the NESTED
  two-level `dv2Supp L Ψ₂ · u₂ ℓ₂`. No `L' : LevelDatum F' H₀' hpin'` makes these equal as
  Lean terms, so no type-correct instantiation of the landed L2E theorems exists.
* **(b) design-vs-landed gap, recorded.** DWR §11.7's claim "instantiate both at `(g8,85,2)`
  and for F1.4–F1.6" is TRUE of the statement shapes (C136l2e0–3 contain no S2 numeral) but
  FALSE of the root carrier: every landed engine theorem binds `L : LevelDatum` and reads
  `dv2Hgt L`/`dv2Res L`. The engine is frame-generic, not VALUATION-generic. A future
  valuation-generic refactor (an abstract `(ν : Polynomial O → ℕ∞)` + six laws) would make
  all three levels instances of one core; not attempted here (would edit landed files).
* **(c) taken: the mirror is cheap because the interface is six laws.** `C134dv2g`'s
  survival core (`MuEquiv → dv2ResSurv_of_muKey`) consumes exactly: zero→⊤, finiteness off
  zero, ultrametric min, equality off ties, negation invariance, multiplicativity on nonzero
  factors — of its inner valuation. All six have landed `dv2Supp` twins: C132nv0's
  `dv2Supp_zero_eq_top`/`dv2Supp_ne_top_of_ne_zero`/`min_dv2Supp_le_dv2Supp_add`/
  `dv2Supp_add_eq_of_lt`/`dv2Supp_neg`, and (multiplicativity, at the S2 instance)
  `C132nv4.s2_dv2Supp_mul_at_21` fed by the landed survival `C132nv4.s2_dv2ResSurv_at_21`
  through `C132nv6.s2_dv2SideSet_nonempty_at_21`. Since no GENERIC `dv2Supp`
  multiplicativity is landed, the generic core threads it as ONE honest explicit hypothesis
  `hmul` — exactly the role `C133mh3.dvSupp_mul` + `L.hκ` played one level down.

## What landed (all Lean-core, all sorry-free)

Part 1 — generic μ-predicates at the level-3 valuation `dv2Supp L Ψ₂ · u₂ ℓ₂`
(= `C136d0.dv3Hgt L Ψ₂ u₂ ℓ₂`, definitionally): `Mu3Equiv`, `Mu3Dvd`, `Mu3Minimal`,
`Mu3Prime`, `IsMu3Key`, `mu3Dvd_zero` — the one-level-up mirror of `C134dv2g` Part 1.

Part 2 — the survival core one level up, mirroring `C134dv2g` Part 2–3 proof-for-proof:
* `dv2Supp_mul_modByKey_le` / `dv2Supp_mul_modByKey_eq` — reduction modulo a μ₃-key
  preserves the product's level-3 value (FGMN tie-exclusion, verbatim mechanism).
* `dv2Supp_add_le_key_quot_add` — the sharp slot-1 relation `µ₃(a)+µ₃(b) ≤ µ₃(Ψ₃)+µ₃(quot)`.
* ★ `dv3ResSurv_of_mu3Key` — **the generic D3-03 discharge**: `Dv3ResSurv L Ψ₂ u₂ ℓ₂ Ψ₃ u₃ ℓ₃`
  from `hmul` + `IsMu3Key L Ψ₂ u₂ ℓ₂ Ψ₃` + the key grade `dv2Supp L Ψ₂ Ψ₃ u₂ ℓ₂ = KΨ₃` +
  the OUTER floor `ℓ₃ · KΨ₃ < u₃` — the exact mirror of `C134dv2g.dv2ResSurv_of_muKey`.
* `dv3SideSet_nonempty_of_ne_zero` — the dv3 twin of `C134dv2g.dv2SideSet_nonempty_of_ne_zero`
  (needed by D3-04's endpoint assembly; C136d0 had no nonemptiness-from-nonzero fact).

Part 3 — the S2 instance at `(g8, 85, 2)`:
* `toZ` bridge (private `toZ_lt_toZ_iff`, `mu3Equiv_iff_s2`, `mu3Dvd_iff_s2`): the generic
  ℕ∞-valued predicates at the S2 numerals are propositionally the landed `s2Hgt₃`-anchored
  `S2Mu3InitialEquiv`/`S2Mu3Dvd` (C132kp0), since `s2Hgt₃ = toZ ∘ dv2Supp(Φ₂,21,2)` and
  `toZ` is an order embedding.
* `s2_isMu3Key_g8` — **the T2 key proof consumed**: `C136t.s2Mu3KeyPoly_g8` (monic +
  `S2Mu3Minimal` + `S2Mu3Irreducible`) bridged to `IsMu3Key`. This is precisely the
  "IsMuKey-analogous data from T2's key proof" the charge predicted.
* `s2_dv2Supp_g8` — the key grade `dv2Supp L Φ₂ g₈ 21 2 = 42`, read backwards through `toZ`
  from `C132rp10b.s2Hgt₃_g8`.
* ★ `s2_dv3ResSurv_at_85` — D3-03 discharged; fence `2·42 = 84 < 85` (`norm_num`), the
  depth-3 occurrence of the tower's `+1`-strictness pattern (`21 = 2·10+1`, `85 = 2·42+1`).
* `s2_dv3SideSet_nonempty_at_85` — the μ₄ side-set nonemptiness (the fact whose μ₃
  absence C132nv5 once recorded as THE blocking hypothesis, now free at μ₄ from
  `C136d0.dv3Supp_ne_top_of_ne_zero`).

Part 4 — ★ D3-04: `s2Hgt₄_mul_unconditional` and `s2Hgt₄_mul_all`.

## Verification and footprint

Required command, run after the skeleton and after each fill increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136d3ad.lean
```

Final exit status: `0`; zero errors, zero warnings, zero `sorry`. The AxCheck footer prints
all 17 public declarations at exactly `[propext, Classical.choice, Quot.sound]` — Lean core
only, no `exists_dvDissection`, no new axiom, no D3-special assumption. No landed or
leanspec file was edited (`git status`: the new file is the unit's only footprint). No git
operation was run.

Repair log: 1 error total across the whole unit (an ambiguous `toZ_inj` between
`_root_.toZ_inj` and `C130s6.toZ_inj`; qualified). Everything else compiled first-pass —
the C134dv2g mechanism is genuinely valuation-generic once the six inner laws are supplied.

## Trust boundary

New statement shapes flagged for human review: `Mu3Equiv`, `Mu3Dvd`, `Mu3Minimal`,
`Mu3Prime`, `IsMu3Key` (FGMN Def 1.2/1.4 at the level-3 valuation — same recasts as
`C134dv2g`'s reviewed level-2 set, one level up), and the `hmul` hypothesis shape of
`dv3ResSurv_of_mu3Key` (multiplicativity on nonzero factors, the `AddValuation` product
law shape).
