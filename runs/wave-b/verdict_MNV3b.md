# Verdict — unit MNV3b, node M3-NV3b (μ₃ campaign, NV2/NV3 interface closure) — HALF-DISCHARGED

Date: 2026-08-27. File created (the ONLY repo file touched, besides this verdict):
`leanfinal/Uniformity/ChapC/C132nv3b.lean` (node tag `[M3-NV3b, 2026-08-27]`; 5 public
theorems + 2 private helpers, 306 lines). Not added to any roll-up/leanspec file.
`C132nv2.lean`, `C132nv3.lean` (siblings) NOT touched. No git commit.

## The charge

Discharge `Dv2ResSurv` (`C132nv2.lean:220-233`, the ONLY spec that matters) at the S2
instance `L = (s2Tower h2 hq).levelDatum h2`, `Ψ = Φ₂ = s2DepthTwoKeyAt h2 hq 2`,
`(u₂, ℓ₂) = (5, 2)`. `Dv2ResSurv` needs, for `A B` of degree `< Ψ.natDegree` with known
`dv2Hgt` heights `Ha, Hb`: **(1)** `dv2Hgt L (dev Ψ (A·B) 0) = Ha+Hb` (EQUALITY); **(2)**
`ℓ₂•(Ha+Hb)+1 ≤ ℓ₂•dv2Hgt L (dev Ψ (A·B) 1) + u₂` (the strict carry bound). `C132nv3`
(node M3-NV3) had proved only the `≤` half of (1) and left both (1)'s `≥` half and all of
(2) open, flagging the exact gap in its own honesty addendum.

## Verdict: HALF-DISCHARGED — clause 1 proved, clause 2 BLOCKED at `(5,2)` with a positive
cross-check at `(21,2)`

### Half 1 — DISCHARGED: the slot-0 equality

The missing `≥` direction of `C132nv3`'s survival core closes with the SAME mechanism
`C132nv3` used, run on the REMAINDER `r := (a·b) %ₘ Φ₂` instead of on the two factors:
the unconditional S2 product law `s2_dvSupp_mul` (`C130nv3`) gives `dvSupp(a·b) = Ha+Hb`
outright, so proving `Ha+Hb ≤ dvSupp(r)` finishes the job. Writing `a·b = r + Φ₂·q₀`: if
`dvSupp(r) < dvSupp(a·b)`, a short ultrametric case analysis forces `dvSupp(r) =
dvSupp(Φ₂·q₀)` exactly, which builds `S2InitialEquiv h2 hq r (-(Φ₂·q₀))`, i.e.
`Φ₂ ∣_µ r`. But `r` has degree `< 4` (`Polynomial.natDegree_modByMonic_lt`) and, if
`r ≠ 0`, `S2MuMinimal Φ₂` (already inside `s2Φ₂_keyPoly`, landed) directly excludes
`Φ₂ ∣_µ r` — contradiction (no irreducibility/primality needed this time, unlike
`C132nv3`'s proof: `r` is a single polynomial, not a factored product, so only
minimality is used). `r = 0` is the trivial `⊤`-RHS case.

**Lands as:**
* `s2_dvSupp_mul_modByComposedKey_eq` — the `dvSupp`-level equality, universal in `a, b`
  of degree `< 4`.
* `dv2Hgt_dev_composedKey_mod_eq` — the `dv2Hgt`-shaped corollary, matching
  `Dv2ResSurv`'s slot-0 clause **VERBATIM** (same hypotheses `A.natDegree < Ψ.natDegree`,
  `dv2Hgt L A = Ha`, etc., same conclusion), universal in `u₂, ℓ₂` (the clause doesn't
  mention them).

### Half 2 — BLOCKED-BECAUSE at `(u₂,ℓ₂) = (5,2)`: the slot-1 carry bound

Running the same computation once slot 0 is known gives a SHARP bound with no case split:
`min(dvSupp(a·b), dvSupp(r)) ≤ dvSupp(Φ₂·q₀)` collapses (both `min` arguments equal, by
slot 0) to `Ha+Hb ≤ dvSupp(Φ₂) + Hq₀` (`Hq₀` := the bare quotient digit's own height).
**`dvSupp (s2Frame h2 hq) Φ₂ 5 2 = 10` is ALREADY LANDED**
(`C130np5.dvSupp_composedKey_s2Tower`, reached via the `rfl` bridge
`s2DepthTwoKeyAt_two`) — so the landed-fact-derived bound is exactly `Ha+Hb ≤ Hq₀+10`
(proved as `s2_le_composedKey_quot_add`). This bound is **TIGHT**: nothing landed
excludes the tie `dvSupp(r) = dvSupp(Φ₂·q₀)`, so the bound cannot be sharpened by
re-running the same argument.

`Dv2ResSurv`'s clause 2 at `u₂=5, ℓ₂=2` needs `2(Ha+Hb)+1 ≤ 2Hq₀+5`, i.e.
`Ha+Hb ≤ Hq₀+2` — **8 tighter** than the landed `Ha+Hb ≤ Hq₀+10`.

**BLOCKED-BECAUSE**: the missing statement is precisely a numeral or finer bound the
corpus does not supply — *either* a landed `dvSupp (s2Frame h2 hq) Φ₂ 5 2 ≤ 2` (FALSE:
the landed value is `10`, so this route is dead), *or* a bound on `Hq₀` in terms of
`Ha, Hb` finer than generic ultrametricity gives (needs graded-residual machinery about
`Φ₂`'s leading behaviour relative to a `Ψ`-quotient — the μ₃ apparatus, M3-RP0 onward,
which does not exist in the corpus yet, per `C132nv3`'s own honesty note). This is a
missing-fact gap, not a proof-search failure: the argument was pushed to its sharp
conclusion (`Ha+Hb≤Hq₀+10`, tight) and that conclusion is 8 short of what's needed.

**Cross-check (not part of the charge, included as positive evidence the argument itself
is sound and to pin the exact threshold):** the identical argument closes cleanly at
`(u₂,ℓ₂) = (21,2)` — the SAME numeral pair the μ₃ campaign's own row M3-NV1 already fixes
for `s2Hgt₃` (`dv2Supp L Φ₂ g 21 2`, `C132nv1`), and matching the independently-landed
`s2Hgt₃ Φ₂ = 21`. Proved as `s2_dv2ResSurv_slot1_at_21`. This strongly suggests
`(u₂,ℓ₂)=(5,2)` is simply the wrong numeral pair for this row, and a follow-up node
should confirm whether the μ₃ campaign in fact needs `Dv2ResSurv` at `(21,2)`, not
`(5,2)`.

## What lands (full list)

* `s2_dvSupp_Φ₂` — diagnostic pin: `dvSupp (s2Frame h2 hq) Φ₂ 5 2 = 10` (one-line bridge
  from `C130np5`'s landed value through the `rfl` identity `s2DepthTwoKeyAt_two`).
* `s2_le_composedKey_quot_add` — the sharp `Ha+Hb ≤ dvSupp(Φ₂)+Hq₀` bound.
* Two private helpers (`natDegree_quot_lt`, `s2_dev_one_eq_quot`) establishing that the
  bare quotient `(A·B)/ₘΦ₂` IS `dev Φ₂ (A·B) 1` (degree bookkeeping: the quotient has
  degree `< 4` since `A,B` do, so a second `%ₘΦ₂` is a no-op).

## What was NOT claimed

`Dv2ResSurv ((s2Tower h2 hq).levelDatum h2) Φ₂ 5 2` is NOT stated as discharged — it
cannot be, at `(5,2)`, from landed facts. No new axiom. No statement invented beyond what
is documented in the file's own docstring (which carries the full derivation and the
BLOCKED-BECAUSE explanation verbatim).

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_dvSupp_mul_modByComposedKey_eq`, `dv2Hgt_dev_composedKey_mod_eq`,
`s2_le_composedKey_quot_add`, `s2_dv2ResSurv_slot1_at_21`.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C132nv3b.lean` — CLEAN (exit 0, no
errors, no warnings, no `sorry`; `grep -c sorry` on the file returns `0`). Dependencies
(`C132nv3`, `C130np5`) rebuilt clean first via `lake build` to populate their `.olean`
caches. `#print axioms` on all 5 public declarations:

```
'Uniformity.Density.Tower.C132nv3b.s2_dvSupp_mul_modByComposedKey_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3b.dv2Hgt_dev_composedKey_mod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3b.s2_dvSupp_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3b.s2_le_composedKey_quot_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3b.s2_dv2ResSurv_slot1_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, uniformly. No axiom regression possible (no capstone touches this file
yet). `git status` shows only the new `C132nv3b.lean` plus this verdict file
(`C132nv2.lean`/`C132nv3.lean`, the siblings, untouched). No git commit.
