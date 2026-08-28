# UNIT DV2G verdict — BOTH level-2 subgoals LANDED, frame-generic (2026-08-28)

## Re-grounding

`runs/wave-c/verdict_F12C.md` reduced the remaining F1.3–F1.6 chain to exactly two
level-2 subgoals: **(i)** a frame-generic discharge of `C132nv2.Dv2ResSurv` (the survival
hypothesis every landed level-2 product law carries; only the S2 numeric instance
`C132nv4.s2_dv2ResSurv_at_21` existed), and **(ii)** `dv2Pin_mul_complement` — the
complement's dv2-profile collapse relating `dvSupp F (g %ₘ Ψ)` to `dvSupp F g` (the
no-interaction node, BLOCKERS_PLAN pricing 70–120 lines).  New file:
`leanfinal/Uniformity/ChapC/C134dv2g.lean` (667 lines; imports `C132nv2`, `C133mh3`,
`C134cfs`, `C141defs`).  Verified: `timeout 580 lake env lean Uniformity/ChapC/C134dv2g.lean`,
**exit 0, zero errors, zero warnings, zero `sorry`**.

## The mechanism (why generic became possible tonight)

`C132nv3b`'s S2 proof had three S2-specific inputs; each now has a generic supplier:

1. `s2_dvSupp_mul` (S2 `dvSupp` multiplicativity) → **`C133mh3.dvSupp_mul`** (Theorem M
   clause 1, landed 2026-08-28): all nonzero factors, any frame, under `hπ`, `hh : 0 < F.h`,
   a pin, `0 < ℓ`, floor `ℓ·(e₁f₁·h) < u`.  At the level datum's inner pair `(L.u, L.ℓ)`
   the floor IS `L.hκ` (associativity bridge `inner_floor`).
2. `S2KeyPoly Φ₂` → the new generic predicates **`MuEquiv`/`MuDvd`/`MuMinimal`/`MuPrime`/
   `IsMuKey`** — FGMN published Def 1.2/1.4 (C130kp0's shapes) restated at the generic
   level valuation `dvSupp F · L.u L.ℓ` (ℕ∞-valued; the S2 versions read the same values
   through `toZ`).  Taken as ONE honest hypothesis `hkey : IsMuKey L Ψ`.
3. `dvSupp Φ₂ = 10` + `2·10 < 21` → the abstract key grade `hKΨ : dvSupp F Ψ L.u L.ℓ = KΨ`
   and the **OUTER floor `hfence : ℓ₂·KΨ < u₂`** — the exact level-2 twin of the level-1
   floor `ℓ·(D′h) < u`.

## Row table — LANDED (namespace `Uniformity.Density.Tower.C134dv2g`)

| what | statement | route | footprint |
|---|---|---|---|
| μ-predicates | `MuEquiv`/`MuDvd`/`MuMinimal`/`MuPrime`/`IsMuKey` at the level valuation | FGMN Def 1.2/1.4, C130kp0's byte-shapes one frame up | Lean core |
| survival core `≤` | `dvSupp_mul_modByKey_le` — digit-bounded `a,b`: `µ((a·b) %ₘ Ψ) ≤ µ(a)+µ(b)` | C132nv3's tie analysis + μ-primality + μ-minimality, `dvSupp_mul` replacing `s2_dvSupp_mul` | Lean core |
| survival core `=` | `dvSupp_mul_modByKey_eq` | C132nv3b Half 1's tie exclusion (μ-minimality on the remainder) | Lean core |
| sharp slot-1 bound | `dvSupp_add_le_key_quot_add` — `µ(a)+µ(b) ≤ µ(Ψ) + µ((a·b) /ₘ Ψ)` | C132nv3b Half 2's min-collapse, generic | Lean core |
| **★ SUBGOAL (i)** | `dv2ResSurv_of_muKey : Dv2ResSurv L Ψ u₂ ℓ₂` from `hπ, hh, IsMuKey, hKΨ, 0 < ℓ₂, ℓ₂·KΨ < u₂` — LITERALLY C132nv2's predicate, any frame/datum/key/outer pair | slot-0 = the `=` core; slot-1 = sharp bound + the outer floor (`ℓ₂(Ha+Hb)+1 ≤ ℓ₂Hq₀+u₂` from `Ha+Hb ≤ KΨ+Hq₀` and `ℓ₂KΨ < u₂`) | **Lean core** |
| digit floors | `dvSupp_le_modByKey`, `dvSupp_le_divByKey_add`, `dvSupp_le_dev_add` (`µ(g) ≤ µ(dev Ψ g j) + j·KΨ`) — the level-2 MacLane expansion inequality C132nv2's docstring recorded as having "no level-2 analogue"; now derived from Theorem M + μ-minimality | one-step tie exclusion + induction on `j` (`dev`'s recursion) | Lean core |
| complement slot-0 pin | `dvSupp_modByKey_eq_of_not_muDvd` — `¬ Ψ ∣µ g ⟹ µ(g %ₘ Ψ) = µ(g)` (the exact `%ₘ` relation F12C named) | floor (≥) + initial-form transfer (≤) | Lean core |
| abscissa-0 collapse | `dv2Supp_collapse_of_not_muDvd` — `dv2Supp L Ψ g u₂ ℓ₂ = ℓ₂ • dvSupp F g L.u L.ℓ` | ≤ at slot 0 via the pin; ≥ per slot via the digit floor + outer floor | Lean core |
| attainment | `dv2SideSet_nonempty_of_ne_zero` (the dv2 twin of `C34.dvSideSet_nonempty`; C132nv4's honesty note had left it underived) | `Finset.exists_mem_eq_inf` + `dv2Supp_ne_top_of_ne_zero` | Lean core |
| **★ SUBGOAL (ii)** | `dv2Pin_mul_complement` — `dv2Supp L Ψ (b·g) u₂ ℓ₂ = dv2Supp L Ψ b u₂ ℓ₂ + ℓ₂ • dvSupp F g L.u L.ℓ` for any nonzero `b`, any `g` with `¬ MuDvd L Ψ g` | subgoal (i) fires `C132nv2.dv2Supp_mul_eq_add_of_endpoint_le` (side data from attainment + `exists_dv2SideMin_height`), then the collapse | **Lean core** |
| F1.3 CARRIER | `dv2Supp_translation_of_muKey` — **NODE C.37's signed conclusion byte-as-is** (`dv2Supp L Ψ f u₂ ℓ₂ = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞)`; mechanical substring check against leanspec `ChapC.lean:1640-1641` PASSED) from `BlockContext` + the three honest premises (`IsMuKey`, grade+fence, complement `¬ MuDvd`) | `C134cfs.blockFactor_spec` (F1.1) splits `f = blockFactor·complement`; subgoal (ii) translates; `ENat.coe_toNat` reads `complementConst` | core + `exists_dvDissection` (the one allowlisted cite, via F1.1) |

Cross-check against the S2 instance: at `L = (s2Tower).levelDatum`, `Ψ = Φ₂`,
`(u₂,ℓ₂) = (21,2)` the generic hypotheses match the landed certificates —
`s2Φ₂_keyPoly` (through the `toZ` value bridge), `s2_dvSupp_Φ₂ = 10`, `2·10 = 20 < 21`
(the same one-unit margin C132nv3b pinned).  The `toZ`-bridge instantiation itself is
NOT landed in Lean (the generic theorems stand alone; `C132nv4`'s S2 discharge remains
the landed S2 instance — nothing regressed).

## Row table — F1.3–F1.6 as SIGNED: re-attempted, still BLOCKED-BECAUSE

Per the F12C discipline no signed name is declared; the miss is now exactly THREE named
premises (re-derived against tonight's corpus, recorded verbatim in the file's Part 7):

| missing premise | content |
|---|---|
| **(P1)** `IsTestKey L Ψ ⟹ IsMuKey L Ψ` | the Montes "test keys are key polynomials at the level valuation" theorem — μ-minimality + μ-primality for a generic test key.  Only the S2 certificate chain exists (`C130kp5.s2KeyPoly_composedKey`).  The ONE genuinely new mechanism left. |
| **(P2)** `¬ MuDvd L Ψ (f /ₘ blockFactor L f)` | the μ-shadow of F1.2's landed residual clause (`C134f12c.block_complement_notdvd` clause 2).  Residual-non-divisibility → μ-non-divisibility is the level-2 residual↔initial-form correspondence, not landed generically. |
| **(P3)** the fence gap | the engine needs `ℓ₂·KΨ < u₂` with `KΨ = L.ℓ·L.seam` (test-key grade, `C131aa.dvSupp_testKey`); the SIGNED statements carry only `hseam : ℓ₂·L.seam < u₂` — an `L.ℓ`-factor weaker (coincide iff `L.ℓ = 1`; at S2: signed `10 < 21` vs needed `20 < 21`).  Slot-1's landed bound is TIGHT (C132nv3b), so this is a statement-level gap: either the signed forms gain the stronger fence or the μ₃ `M3-RP0` graded-residual apparatus supersedes the bound.  **Flagged for the leanspec owner-review queue.** |

F1.4/F1.5 additionally need the per-slot `dv2Res` cocycle telescope (one refinement below
the support level — untouched).  F1.6 additionally needs level-2 minimizer/maximizer
additivity as an EQUALITY (only `C132nv2.dv2SideMin_mul_le` is landed; the level-1
equality is Theorem M clause 2, a full MH-scale lift one level up) — though this unit's
collapse + fence would pin the complement's side set at `{0}` once that lands.

**Recommended next decomposer:** (P1) is the high-value node — it is ALSO what F1.2's
consumers eventually want (test keys enter every row), and with it (P2) likely follows
from the same correspondence apparatus.  (P3) is an owner decision, not a proof.

## Verification record

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134dv2g.lean
# exit 0, zero errors, zero warnings, zero sorry
```

Per-decl footprints (AxCheck footer, 18 decls printed): every Part 1–5 declaration —
including both stars `dv2ResSurv_of_muKey` and `dv2Pin_mul_complement` — exactly
`[propext, Classical.choice, Quot.sound]` (**Lean core only**);
`dv2Supp_translation_of_muKey` exactly
`[propext, Classical.choice, Quot.sound, Uniformity.Density.Tower.exists_dvDissection]`
(inherited through `C134cfs.blockFactor_spec`; the only dissection occurrence in the log).
Byte-check: the carrier's conclusion is a verbatim substring of leanspec's signed
`dv2Supp_translation` (mechanical Python check).  Zero `sorry`; no landed file edited;
no new axiom; statements flagged for human review listed in the file header.

## Scoreboard after this unit (the F1 family)

F1.1 (+riders) LANDED (CFS) · F1.2 LANDED IN FULL (F12C) · **the two level-2 subgoals
gating F1.3–F1.6 LANDED frame-generic (this unit)** · F1.3 signed = carrier + (P1)+(P2)+(P3)
· F1.4–F1.6 signed blocked on the same three + their own extras (telescope / minimizer
equality) · F1.7 LANDED (F12C) · F1.8 out of family (C.61/D13).
