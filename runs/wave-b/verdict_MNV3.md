# Verdict — unit MNV3: μ₃ campaign node M3-NV3 (the μ₂ survival core at `Φ₂`) — CLOSED

Date: 2026-08-27 · Plan: `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-NV3 ("For
coefficients of degree `< 4`, prove that reduction modulo `Φ₂` preserves the product
endpoint value; derive it from nonzero μ₂ normalized residuals and `s2NormRes_mul`"),
GENUINELY-NEW class. File created (the ONLY repo file touched):
`leanfinal/Uniformity/ChapC/C132nv3.lean` (node tag `[M3-NV3, 2026-08-27]`; 3 public
declarations + 2 private helpers; not added to any roll-up; `C132nv2.lean` (a sibling's
file) NOT touched; no leanspec/ or other units' files touched; NO git commit).

## What the row asks vs. what was actually needed

The row's target is the `hsurv`-shaped fact the ported (`dv2Supp`) generic endpoint theorem
(M3-NV2, not yet landed at investigation time) needs: for `a := dev Φ₂ g jg`,
`b := dev Φ₂ z jz` (each of degree `< deg Φ₂ = 4` automatically, by `degree_dev_lt`),
`dvSupp ((a·b) %ₘ Φ₂) 5 2 ≤ dvSupp a 5 2 + dvSupp b 5 2`. At depth 1 the analogous fact
(`C130nv3.s2_stageHeight_mul_modByMonic_le`, degree `≤ 1` mod `Φ′ = X² − 2`) is proved by
an EXPLICIT remainder formula + parity, which is NOT available here: `composedKey`'s only
landed facts are `Monic` and degree (`C130kp5.lean:94`: "No irreducibility of `composedKey`
... is claimed" as a bare polynomial fact — deciding it needs FGMN's residual-polynomial
machinery, explicitly flagged open there). Checked first (and confirmed load-bearing): the
claim is genuinely FALSE without SOME primality-flavored fact about `Φ₂` — if `Φ₂ = p·q`
for `0 < deg p, deg q < 4`, taking `a := p, b := q` gives `(a·b) %ₘ Φ₂ = 0` (⊤) against a
finite RHS.

## The mechanism actually used

`Φ₂ := s2DepthTwoKeyAt h2 hq 2` is ALREADY a certified `S2KeyPoly`
(`s2KeyPoly_composedKey`, `C130kp5.lean:353-357`) — i.e. `μ₂`-MINIMAL and `μ₂`-IRREDUCIBLE
in FGMN's graded sense (`S2MuMinimal`/`S2MuIrreducible`, `C130kp0.lean`), a strictly weaker
and already-certified notion than plain polynomial irreducibility, built from the landed
`s2NormRes` machinery (`Φ₂`'s own residual `R₃(Φ₂) = X + 1` has nonzero scalar and
automatically-irreducible degree-one shape). New content of this node: for nonzero
`a, b` of degree `< 4`, writing `a·b = Φ₂·q₀ + r` (`Polynomial.modByMonic_add_div`), IF the
survival bound failed, the `dvSupp` ultrametric bank (`C130s6`'s
`min_dvSupp_le_dvSupp_add`/`dvSupp_add_eq_of_lt`) forces `dvSupp(Φ₂·q₀) = dvSupp(a·b)` with
`dvSupp(r)` STRICTLY above it — exactly `S2InitialEquiv (a·b) (Φ₂·q₀)` — witnessing
`S2MuDvd h2 hq Φ₂ (a·b)`. `S2MuMinimal` (at `a, b`, degree `< deg Φ₂ = 4`) rules out
`Φ₂ ∣_µ a` and `Φ₂ ∣_µ b`; `S2MuIrreducible`'s prime clause then rules out `Φ₂ ∣_µ (a·b)`
too — contradiction. No new axiom, no plain-polynomial irreducibility claim about `Φ₂`.

## What lands

* `s2Φ₂_keyPoly` — `Φ₂` (at the `s2DepthTwoKeyAt` numeral) is a valid `S2KeyPoly` (one-line
  transport of `s2KeyPoly_composedKey` through the `rfl` identity `s2DepthTwoKeyAt_two`).
* ★ `s2_dvSupp_mul_modByComposedKey_le` — the core survival law at the `dvSupp`/`s2Frame`
  level, universal in `a, b` (zero cases ride the `⊤` conventions).
* ★ `dv2Hgt_dev_composedKey_mod_le` — the consumable `dv2Hgt`-shaped corollary at the
  endpoint digits `dev Φ₂ g jg`/`dev Φ₂ z jz`, matching M3-NV2's expected `hsurv` premise
  verbatim (via the `dv2Hgt`/`dvSupp` bridge `toZ_inj (s2Hgt₂_eq_dv2Hgt ▸ s2Hgt₂_eq_dvSupp)`,
  the same anti-drift pin `C132nv1` already used).

## What was deliberately NOT claimed

No plain-polynomial `Irreducible Φ₂` (only the weaker graded `S2MuMinimal`/
`S2MuIrreducible`, already packaged inside `S2KeyPoly`). No `dv2Supp`/`FGMNSourceData`
assembly — this node supplies exactly the one survival fact M3-NV2's endpoint theorem
needs, not the endpoint theorem itself (M3-NV2's job) or any packaging (M3-FD0/M3-SG's).

Flagged for human review (new statements): `s2_dvSupp_mul_modByComposedKey_le` and its
`dv2Hgt` corollary — both new, machine-checked results not previously stated anywhere in
the corpus.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C132nv3.lean` — CLEAN (exit 0, no errors,
no `sorry`). `#print axioms` on all 3 public declarations:

```
'Uniformity.Density.Tower.C132nv3.s2Φ₂_keyPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3.s2_dvSupp_mul_modByComposedKey_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv3.dv2Hgt_dev_composedKey_mod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no new axiom, no `unsafe`, no statement invented beyond the row's sketch.
`git status` shows only the new `C132nv3.lean` plus this verdict file (`C132nv2.lean`, the
sibling's node, untouched — never existed at any point during this unit's run). No git
commit.
