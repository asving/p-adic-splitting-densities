# UNIT A23E — amendment A-C.23 ENACTED: `refine_invariants` (C.56(i)) re-signed to the source-faithful M4 package, landed as a THEOREM

**Date:** 2026-08-28 · **Charge:** enact A-C.23 per `runs/wave-c/verdict_RB3R.md` (the
signed `IsTestKey` conjunct is a statement-level overclaim of `EFF.GENTOW1.28`,
codex-confirmed 5/5): adjudicate the repaired conclusion, re-sign in leanspec, land the
repaired statement as a theorem if provable, ripple the consumers, records.

**OUTCOME: ENACTED IN FULL, and the repaired C.56(i) is CLOSED as mathematics.** The
re-signed statement is a sorry-free, axiom-free THEOREM
`Uniformity.Density.Tower.refine_invariants`
(`leanfinal/Uniformity/ChapC/C150rb5.lean`, 436 lines, footprint
`{propext, Classical.choice, Quot.sound}`), byte-identical to the re-signed leanspec
axiom (premises AND conclusion). No axiom form survives anywhere for this node's (i)
clause. The C93 census row (2) flips BLOCKED → LANDED (now 5 of 7).

---

## 1. Adjudication of the repaired conclusion (charge item 2)

RB3R offered two candidate carriers for the repaired third conjunct: the **M4
perturbation package** (C133mh0 MH.6's conclusion shape: `IsDvPure` + pinned height +
`dvResPoly` byte-unchanged) and **`IsMuKey`** (C134dv2g's FGMN valuation-theoretic
key-hood). Decision: **the M4 package**, by the end-to-end criterion. Four legs:

* **(a) Source faithfulness.** `EFF.GENTOW1.28` (spec/EFF-GENTOW1.md:879) claims, for
  `Φ₂⁺`: "monic of degree D2; level-1 development one-sided of slope kappa2 with
  residual psi2 and side digits byte-unchanged (what's slots sit at weight lam > E2,
  strictly above the key's side)". In landed dv-vocabulary that IS: monic ∧
  `natDegree = D₂` ∧ `IsDvPure F Φ₂⁺ u₂ e₂` (one-sided at slope κ₂ = u₂/e₂) ∧ pinned
  side-min height unchanged (`f₂·u₂`) ∧ `dvResPoly = towerLabel T` (the ψ₂-label,
  byte-equal to `Φ₂`'s own residual by C131aa's `dvResPoly_testKey`). `IsMuKey` asserts
  something the source clause does not (μ-minimality/μ-primality); signing it would be a
  new overclaim in a different direction.
* **(b) Direct consumers.** `refine_kills` (C.56(ii)), `refineDom`/`refineCod`/
  `refine_bijection`/`refine_transported_event` (C.57) consume the carrier `Φ₂⁺` ONLY
  through `dv2Pin (T.levelDatum hπ) Φ₂⁺ f j` reads — monic + degree (both landed in
  C150rb4 hypothesis-light) are all their well-definedness needs. Repo-wide `rg`:
  NO signed statement consumes `IsTestKey Φ₂⁺` or `IsMuKey Φ₂⁺`.
* **(c) The "hence" chain.** The source's forcing rerun ("Φ₂⁺ irreducible with carrier
  (e1e2, f1f2), GENTOW-1 + GENHN-2' verbatim") consumes `HasLabel`-shaped data — monic,
  positive degree, `IsDvPure`, residual a power of the label (C.29, C.61 `tier1_typeOf`)
  — exactly the M4 package's shape, not μ-key-hood.
* **(d) Provability.** The M4 package is provable NOW against landed atoms (§3).
  `IsMuKey Φ₂⁺` has no landed route: P1 (`isMuKey_of_isTestKey`, closed at P1D)
  transports from `IsTestKey` — and `Φ₂⁺` is exactly NOT `IsTestKey` (the RB3R finding);
  a direct μ-key proof for `Φ₂⁺` would be new mathematics no consumer asks for.

The signed conclusion also keeps `dev F.key Φ₂⁺ (e₂·f₂) = 1` (the top side digit
byte-unchanged — part of the source's "side digits byte-unchanged", landed
unconditionally as `C150rb4.corrected_top_digit`). NOT included (deliberately): the
source's x-polygon clause — the pre-amendment axiom never claimed it either, and adding
it would EXPAND the signed claim (minimal-diff discipline); it remains available as
future mathematics if a consumer materializes.

## 2. The re-signed statement (A-C.23, leanspec `Leanspec/ChapC.lean` NODE C.56)

Premises byte-unchanged (all nine binders + 2 instances, including the deliberately
carried event hypotheses `hf`/`hs`/`hne`/`hres` — RB3R §0's structural fact stands: the
conclusion mentions `f` nowhere). Conclusion: conjuncts 1–2 byte-unchanged; the
`IsTestKey` conjunct REPLACED by

```lean
    dev F.key (composedKey T - k2DigitLift T s lam) (T.e₂ * T.f₂) = 1 ∧
    IsDvPure F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ ∧
    ∃ hne' : (dvSideSet F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂).Nonempty,
    ∃ hp' : dvHgt F (composedKey T - k2DigitLift T s lam)
        (dvSideMin F (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ hne')
        = ((T.f₂ * T.u₂ : ℕ) : ℕ∞),
      dvResPoly F H₀ hpin (composedKey T - k2DigitLift T s lam) T.u₂ T.e₂ hne'
        (T.f₂ * T.u₂) hp' = towerLabel T
```

The full dated numbered record (WHY + the adjudication) sits as a comment block at the
node; the node header now reads `[signed: A-C.1; (i)'s conclusion re-signed: A-C.23]`.
Pre-amendment text archived at commit `523c8a7b`. The blueprint
(`blueprint/CHAP-C_tower_grammar.md` NODE C.56) is deliberately untouched — the
A-C.21/A-C.22 precedent keeps amendment records in leanspec; the blueprint's "hence
IsTestKey-hood … reruns verbatim" sentence is where the overclaim entered and is now
superseded by the leanspec record. `refine_kills` (C.56(ii)) and all of C.57 are
untouched.

## 3. What landed (charge item 4): `leanfinal/Uniformity/ChapC/C150rb5.lean`

436 lines, sorry-free, axiom-free. The main theorem `refine_invariants` sits in the ROOT
namespace `Uniformity.Density.Tower` (census-checkable); helpers in
`Uniformity.Density.Tower.C150rb5`:

| declaration | content |
|---|---|
| `towerSolve_mod_eq` (public) | the C.83 solve's congruence `towerSolve u e k · u ≡ k (mod e)` on a coprime pair (existence via `ZMod`, success via the `List.find?` case analysis) |
| `gaussVal_C'`, `addVal_pi_pow`, `le_addVal_of_pow_dvd` (private) | coefficient-valuation atoms (`addVal(π^a·d) ≥ a`) |
| `le_stageHeight_C_mul_X_pow` (private) | the monomial digit floor `dv(C c·X^p) ≥ e₁a + hp` when `π^a ∣ c` |
| `dvSupp_zero'`, `le_dvSupp_finset_sum` (private) | sum floors via `C130s6.min_dvSupp_le_dvSupp_add` |
| `le_dvSupp_C_mul_X_pow_mul_key` (private) | per-term floor `dvSupp(C c·X^p·Φ′^q) ≥ ℓ(e₁a+hp) + uq` (dev trichotomy at abscissa `q`) |
| `n2Exp_fst_eq`, `xexp_lt'` (private) | definitional bridge for `n2Exp`'s first component; re-derivation of C150rb4's private X-exponent bound |
| `n2Exp_grade_eq_of_le` (private) | ★ the exact grade equation `e₂(e₁a₀ + h·i) + u₂b = M` — both ℕ-divisions exact (`towerSolve_mod_eq` + `slotIdx_spec`'s congruence), both ℕ-subtractions genuine |
| `dvSupp_k2DigitLift_ge` (public) | ★ the lift's grade floor `W(k2DigitLift T s lam) ≥ lam` — the ONE new mathematical ingredient; the EFF.GENTOW1.27 `a₀ ≥ 0` audit inequality (`E₂ ≥ (e₁−1)e₂h + (e₂−1)u₂ + 1`) closed from `T.hfloor` |
| `refine_invariants` (root) | assembly: MH.6 (`C133mh0.dv_pure_add_of_lt`) at `x := composedKey T`, `y := −k2DigitLift T s lam` (transported across `sub_eq_add_neg`); pinned data from `composedKey_isTestKey` (C47) → `isTestKey_isDvPure` / `dvResPoly_testKey` (C131aa: min = 0, height `f₂u₂`, grade `E₂`, residual = label); conjunct 3 from `C150rb4.corrected_top_digit` |

The proof consumes the landed engine exactly as RB3R priced: the M4 perturbation law
needed only the lift's grade floor as new input (RB3R §3's ~100–250-line item); RB3R's
separately priced "clause 5b slot-exactness" (~150–300 lines) was NOT needed — MH.6's
internal `twistRead_add_eq_left_of_lt` covers the residual preservation once the floor
is supplied, confirming the repaired conclusion is the natural carrier.

C150rb4's conjunct theorems and the off-lattice/zero-slot refutation record are
UNCHANGED — nothing weakens or supersedes the record that forced the amendment.

## 4. Ripple (charge item 5)

Repo-wide `rg refine_invariants` inventory and disposition:

* `leanfinal/Uniformity/ChapC/C135c93.lean` (C93 census, row (2)) — **UPDATED, BLOCKED
  → LANDED**: `import Uniformity.ChapC.C150rb5`, live `#check @refine_invariants`
  (elaborates), dated A-C.23 update block in the docstring ("now 5 of 7"); the original
  C93T row text retained verbatim as the pre-amendment record.
* `leanfinal/Uniformity/ChapC.lean` (chapter roll-up) — C150rb5 import added.
* leanspec `#check @refine_invariants` (census section, `:4026`-region) — unchanged,
  still elaborates against the re-signed axiom.
* `C150rb3.lean:35`, `notes/RESCHEDULE_C56*.md`, `scratch/DEC4_check.lean` — historical
  dispatch/probe records, deliberately untouched (do-not-rewrite-history precedent;
  superseded by RB3R → this unit, chain visible via verdicts).
* `docs/PROJECT_STATE.md` — A23E ledger row flipped to DONE.

## 5. Records (charge item 6)

* `docs/REVIEW_QUEUE_2026-08-26.md` Tier 2 — new TOP row A-C.23 (old form, new form,
  machine evidence, pointers).
* `docs/AXIOM_FAITHFULNESS.md` — NO update, correctly: no axiom form survives in
  leanfinal (the repaired statement is a Lean-core theorem; leanspec's `axiom` is the
  spec registry's stub form per the leanspec lifecycle, not a trusted-axiom
  declaration).

## 6. Verification record

* `timeout 580 lake env lean Uniformity/ChapC/C150rb5.lean` — exit 0, zero
  errors/warnings; AxCheck: `towerSolve_mod_eq`, `dvSupp_k2DigitLift_ge`,
  `refine_invariants` all `[propext, Classical.choice, Quot.sound]` (orchestrator
  re-ran after the composer).
* `lake build Uniformity.ChapC.C150rb5` — success (8755 jobs; the two `linter.style.show`
  notes are pre-existing in `StrongHensel.lean`/`LocalData.lean`, untouched by this
  unit).
* leanspec: `timeout 580 lake env lean Leanspec/ChapC.lean` — exit 0 with the re-signed
  C.56(i) (gate `#guard`s/`#check`s all pass).
* `timeout 580 lake env lean Uniformity/ChapC/C135c93.lean` — exit 0; the live
  `#check @refine_invariants` prints the elaborated signature;
  `partial_floor_and_datum_of_floor` footprint unchanged (Lean-core).
* Chapter roll-up: `lake build Uniformity.ChapC` — success (8909 jobs).
* No git operations performed (per charge).

## 7. Downstream (for the ledger)

The GenhnTow1At `n ≥ 8` supply chain (C93Census consumer) now has 5 of the 7 census
names landed; the remaining blockers are item (4)'s frame-opening floor (clause (a) of
`partial_floor_and_datum`) and item (6)(β) (`towerLocus_depth3_floor`, the C.54/C.55
node-floor family) — unchanged by this unit, already inventoried in C135c93.
