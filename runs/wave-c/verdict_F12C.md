# UNIT F12C verdict — F1.2 CLOSED via the mixed law; F1.7 landed on re-attempt (2026-08-28)

## Re-grounding

`runs/wave-c/verdict_FRT.md` landed F1.2's clauses 1+3 and the quotient bridge
(`C134frt.context_split_quotient : f /ₘ blockFactor L f = g₂ * Wf`) but recorded clause 2
BLOCKED — "transporting `g₂`'s non-`L.r`-divisibility through multiplication by the merely
point-sided `Wf`" — citing only the OLD product laws (both-factors-`IsDvPure` + degree
fences). The orchestrator dissented (commit 00e397a5): the NEW unconditional mixed law
`C133mh3.dvResPoly_mul_gen` (Theorem M clause 3, τ = 1) needs only `g ≠ 0`, `z ≠ 0` +
side pins + the frame pack, and `C133mh14.residual_transport` already exhibits the
point-sided-factor-residual-is-a-unit mechanism. **The dissent is correct.** New file:
`leanfinal/Uniformity/ChapC/C134f12c.lean` (imports `C134frt`, `C130in`, `B04`).
Verified: `timeout 580 lake env lean Uniformity/ChapC/C134f12c.lean`, exit 0, zero
warnings, zero `sorry`.

## Row table — LANDED (namespace `Uniformity.Density.Tower.C134f12c`)

| row | what landed | route | footprint |
|---|---|---|---|
| (transport, charge step 1) | `notdvd_dvResPoly_mul_pointSided` — for ANY `r`: `g₂`'s ∀-pin non-`r`-divisibility + `Wf` point-sided (`dvSideDeg = 0`, only `Wf ≠ 0` beyond that) ⟹ the ∀-pin non-`r`-divisibility of `R(g₂·Wf)` | `dvResPoly_mul_gen` factors `R(g₂·Wf) = R(g₂)·R(Wf)`; `R(Wf)` is a nonzero constant (C.26's `natDegree_dvResPoly` (ii)+(iii) at the point side), hence a unit of `K[Z]`; unit cancellation = `residual_transport`'s divisibility step run in reverse | **Lean core only** |
| F1.2 clause 2 | `quotient_residual_notdvd` — `∀ pins, ¬ L.r ∣ dvResPoly … (f /ₘ blockFactor L f) …` | `context_split_quotient` (FRT bridge) + `dvResPoly_congr` (pin transport across the quotient identity) + the transport lemma | core + `exists_dvDissection` |
| **F1.2 FULL** | `block_complement_notdvd` — **the signed statement, conclusion byte-as-is** (leanspec `ChapC.lean:1623-1631`; byte-check: the 6-line signed conclusion is a verbatim substring of the file). Binder delta: the standing `hh : 0 < F.h` only (verdict_CFS convention) | clause 1 = `C134frt.testKey_dvd_iff_dvd_blockFactor`; clause 2 = `quotient_residual_notdvd`; clause 3 = `C134frt.quotient_dvSupp_ne_top` | core + `exists_dvDissection` |
| **F1.7 (re-attempt: LANDED)** | `dv2_length_sum` — **the signed statement, conclusion byte-as-is** (leanspec `ChapC.lean:2320-2328`; byte-checked; `hh` delta only) | The CFS/FRT chain (F1.1 + F1.6) was ROUTE-based, not statement-forced: the signed conclusion mentions `blockFactor L f` ALONE, so no translation identity is needed. Clause 1: `dev Ψ bf 0 = bf %ₘ Ψ ≠ 0` from `hnd` + `modByMonic_eq_zero_iff_dvd`, then `C130s6.dvSupp_ne_top_of_ne_zero`. Clause 2: the monic block has exact degree `keyDeg₂·mult₂` (`C134cfs.blockDeg_eq`, landed by CFS) = `mult₂·deg Ψ` (test-key degree conjunct), so its top `Ψ`-digit is `1` (`C130in.dev_top_eq_one`), and `C133mh9.dvSupp_one` reads the unit's support as `0`. Clause 3: any `j > mult₂` has `dev Ψ bf j = 0` (`B04.dev_eq_zero_of_lt`), so `dv2Pin = ⊤` (`C130s6.dvSupp_zero_eq_top`), violating `Dv2OnSide`'s finiteness guard; `Finset.max'_le` closes | core + `exists_dvDissection` |

Local plumbing: `isKey_X`, `localFieldStageField`, `floor_assoc`, `exists_pin`,
`dvResPoly_congr` are credited byte-identical copies of `C133mh14` Part-0 privates (same
convention as CSX); `dv2OnSide_of_mem'` is the level-2 twin of MH14's `dvOnSide_of_mem'`.
No landed file edited.

## Row table — re-attempted, still BLOCKED-BECAUSE (exact subgoal; not forced)

The F1.2 leg of every downstream block is now CLEARED. What remains for F1.3–F1.6 is
LEVEL-TWO multiplicative structure, which the level-one mixed law does not touch. Re-derived
against the current corpus (not carried over from FRT):

| row | exact missing subgoal |
|---|---|
| F1.3 `dv2Supp_translation` | TWO statements: (i) a **frame-generic `Dv2ResSurv L Ψ u₂ ℓ₂` discharge** — every landed level-2 product law (`C132nv2.dv2Supp_mul_of_endpoint_le`, `dv2Supp_add_le_dv2Supp_mul`, `dv2OnSide_mul_endpoint`) carries this survival hypothesis (`C132nv2.lean:227`), and its only landed discharge is the S2 numeric instance `C132nv4.s2_dv2ResSurv_at_21` (`Dv2ResSurv (s2Tower…) Φ₂ 21 2`; `C132nv3b`: slot-1 "BLOCKED at (5,2)" generically); (ii) the **complement's `dv2`-profile collapse** (`dv2Pin_mul_complement`, unwritten, plan 70-120 lines): the RHS constant `ℓ₂ • complementConst L f` requires the complement's level-2 side to collapse to abscissa 0 with pin `(dvSupp F g L.u L.ℓ).toNat` — i.e. relating `dvSupp F (g %ₘ Ψ)` to `dvSupp F g`, which IS the no-interaction analysis; nothing landed does this |
| F1.4 `dv2ResPoly_scalar` | F1.3's translated pin + the cocycle telescope on per-slot `dv2Res` reads — same level-2 digit analysis, one refinement deeper; no independent route |
| F1.5 `dv2ResPoly_radical_eq` | F1.4 (unit-scalar cancellation over `K₂`); even its degree clause alone would need F1.6 |
| F1.6 `mult₂_readable` | F1.3's mechanism verbatim (a constant vertical shift of the level-2 polygon preserves side data); the conclusion compares `f` against `blockFactor L f`, so — unlike F1.7 — the translation is unavoidable |
| F1.8 `level2_peel` | OUT OF SCOPE per the charge (C.61 at general `ℓ` + leanspec defect D13; orthogonal, unchanged from C40/FRT) |

**Recommended next decomposer:** the two F1.3 subgoals above are now the ONLY gate for the
whole F1.3–F1.6 chain. Subgoal (ii) (`dv2Pin_mul_complement`) is the narrower and unlocks
the translation shape; subgoal (i) (frame-generic `Dv2ResSurv`) is the NV-chain's
continuation (`S2_SOURCE_PLAN_2026-08-24.md` NV-3/NV-4) and is also what would eventually
retire the endpoint hypothesis family.

## Verification record

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134f12c.lean
# exit 0, zero warnings, zero errors
```

Per-decl footprints (AxCheck footer): `notdvd_dvResPoly_mul_pointSided` —
`[propext, Classical.choice, Quot.sound]` (**Lean core only**);
`quotient_residual_notdvd`, `block_complement_notdvd`, `dv2_length_sum` — each exactly
`[propext, Classical.choice, Quot.sound, Uniformity.Density.Tower.exists_dvDissection]`
(the one allowlisted C.33 cite, inherited through `context_split`/`blockFactor_spec`).
Byte-checks: both signed conclusions verified as verbatim substrings against
`leanspec/Leanspec/ChapC.lean` (mechanical Python check). Zero `sorry`; no landed file
edited; no new axiom; ChapI untouched.

## Scoreboard after this unit (the F1 family)

F1.1 (+riders) LANDED (CFS) · **F1.2 LANDED IN FULL (this unit)** · F1.3–F1.6 BLOCKED on
the two level-2 subgoals above · **F1.7 LANDED (this unit)** · F1.8 blocked on C.61/D13
(out of family).
