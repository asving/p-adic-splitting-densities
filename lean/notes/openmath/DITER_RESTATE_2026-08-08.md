# D-ITER RESTATED — the countermodel-pinned statement of record: the single-ζ′ cyclic presentation retired (22/28 refutation), the measured two-constant ITER-LAW installed as the operative form

**Unit:** D-ITER restatement (SYNTHESIS_PASS5 queue #9 — hygiene, PRECEDES any
`DIterJunctionSupplier` work; the F4 fence honored: character law ≠ digit-algebra
iteration, NO TR3-S2/TWIST-LAW material touched).  **Authority:** countermodel-pinned
restatement under the standing statement-change authority (Asvin 2026-08-05); the
pinning countermodel is the strata probe's Family-B adjudication
(`verification/openmath/strata_probe.py`, output/JSON committed alongside; record
`lean/notes/openmath/STRATA_PROBE_2026-08-08.md` §S2; ledger entry 2026-08-08).
**Author:** Fable restatement unit, campaign date 2026-08-08 (wallclock 2026-08-02).

## S1. The refutation of record (what pins the restatement)

GRB S5.3's open D-ITER presentation claim — "the composite is the cyclic algebra
F′[u′]/(u′^{e_b′} − ζ′)" with a SINGLE structure constant — operationalized at the
canonical (dig-consumed) anchor alphabet (single non-1 cocycle value + carry pattern
realizable by some relabeling of ℤ/E₂), is **ADJUDICATED FALSE at mixed stacked
ramification**: NOT-CYCLIC at **22 of the 28** towers with e₀ ≥ 2 AND e₁ ≥ 2 (all
bug-detector and sealed rows green; exit 0; seed 20260815, exact arithmetic).  Two
witnessed failure genres: (i) ≥ 2 distinct non-1 cocycle values — kill-shot designed
row N (2;2,1,1;2,1,2), where K₂ = K₁[z̄] is a genuine degree-2 extension and the value
set {z₁, z̄, z̄z₁^b} admits no single ζ′ (likewise J, L, M); (ii) single value but the
mixed δ₁/δ₂ carry pattern is the carry of NO ℤ/E₂ relabeling (C/K/E over p = 3).  The
6 cyclic mixed towers are exactly the twist-blind small-field collapses.  NOT refuted
(honesty display): the ABSTRACT crossed-product iso K₂[U]/(U^{E₂} − ζ*) is automatic
and carries no information; the refutation is alphabet-specific BY DESIGN — the
canonical alphabet is the consumed one (IFACE(c)), and any competing distinguished
alphabet now has 22 exact tables to match (JSON on file).

## S2. D-ITER — THE STATEMENT OF RECORD (restated; standalone)

**Setting (order 2; the tower data).**  A two-read OM tower with reads (e₀,h₀,ψ₀)
then (e₁,h₁,ψ₁); E₂ := e₀e₁ > 1; residue tower K₁ (level 1, containing the frame
letter z₁) and K₂ := K₁[z̄]/(ψ₁) via y ↦ z̄; ℓ₀ := the NORMALIZED Bézout inverse
(0 ≤ ℓ₀ < e₀, ℓ₀h₀ ≡ 1 mod e₀ — the standing GMN-convention hypothesis, TR3-S1 S0);
w₁(Φ₁) = e₀g₀h₀; γ₂ := e₁·w₁(Φ₁) + h₁ (the weight of the level-2 abscissa-step
generator — tower datum; harness: `grb_order2_check.py:510`).

**The canonical anchor alphabet (the dig-consumed basis; iterated eq-(12-int)
split).**  For γ in the anchor window: γ = e₁γ₁ + s₂γ₂ with (s₂,u₂) = eq12(γ,e₁,h₁),
γ₁ = u₂ − s₂·w₁(Φ₁), (s₁,u₁) = eq12(γ₁,e₀,h₀); anchor φ_γ := π^{u₁}Φ₀^{s₁}Φ₁^{s₂},
with φ_{γ+E₂} = π·φ_γ exactly.  Class values val(φ) := (R_{2,w₂(φ)}(φ))(y ↦ z̄) ∈ K₂;
cocycle c(γ,γ′) := val(φ_γ·φ_{γ′}) / val(φ_{γ+γ′}) (gauge-free: numerator and
denominator at the same weight).

**D-ITER (restated).**  The degree-0 composite digit algebra of gr(w₂) on the
canonical anchor alphabet is the ITERATED TWISTED GROUP ALGEBRA

    𝒟₂ = ⊕_{γ ∈ ℤ/E₂} K₂·u_γ,   u_γ·u_{γ′} = c(γ,γ′)·u_{γ+γ′},

with the two-constant structure cocycle

    (ITER-LAW)   c(γ,γ′) = z̄^{δ₂} · z₁^{(s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀γ₂δ₂)/e₀},
                 δ₂ := ⌊(s₂(γ)+s₂(γ′))/e₁⌋.

Two independent structure constants — the OUTER carry contributes z̄ (the last-read
wrap, as in D-REAL), the INNER carry contributes z₁ (the frame's letter) — plus the
FIBRATION term ℓ₀γ₂δ₂: an outer wrap dumps γ₂ ≡ h₁'s worth of abscissa (mod the
e₀-track) into the s₁-coset — the genuine "ℤ/E₂ fibred by the old" of MOVES §F.2.
The exponent is integral: (s₁-defect + ℓ₀γ₂δ₂) ≡ 0 mod e₀ (probe row B1, sealed).
Degenerations: e₀ = 1 ⟹ c = z̄^{δ₂} — Lemma D-REAL verbatim (ζ′ = z̄, s₂-relabeling);
e₁ = 1 ⟹ c = z₁^{δ₁}.

**Status: OPEN LEMMA (conjecture level), instance-true.**  Confirmed exact at
0/804 anchor pairs over all 52 tower instances (13 rows × 4 base rings
{ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]}; E₂ ≤ 6, deg Φ₂ ≤ 24), with the e₀ = 1 leg theorem-backed
(Lemma D-REAL, GRB S5.3).  Proof route on record: the same CARRY-1/W-MULT bookkeeping
that proved D-REAL, run in the fibred index ℤ/E₂ → ℤ/e₁ with inner track ℤ/e₀ (the
probe header's derivation from W-MULT + val(φ_γ) = ǫ₁(γ₁) is essentially the
computation).  Orders ≥ 3: the iterated form is the conjectured TEMPLATE (the
fibration composes stage-over-stage); unmeasured, OPEN — no claim.

**[STATUS BRACKET (2026-08-08, wallclock 2026-08-03; applied at ROOT r35 per the
ITER-LAW unit's S9 owed list; ADDITIVE — the record text above stands): the
status line above UPGRADES. (ITER-LAW) is now PROVED AT ATTEMPT GRADE ON THE
HARNESS TOWER CLASS — standard-lift towers, exactly the class this section's
setting pins, and the class the ENTIRE instance base (0/804 strata-probe +
0/840 JUNCFORGE) inhabits — as a finite-algebra identity by the recorded
CARRY-1/W-MULT fibred route; proof note `lean/notes/openmath/
ITERLAW_2026-08-08.md`; two-commit seal honored (runner sealed pre-run at
ab7c31c; run ALL GREEN FIRST PASS exit 0 at 242ba1e — 35,232 samples / 0
violations, F1–F10 + CERT, Case-II coverage MET, row-X NOT-CYCLIC 4/4 with
exact value-set match). HONEST RESIDUALS: (ITER-LAW-LIFT) — general lawful
(non-standard) lifts remain OPEN exactly at g₀ = 1 ∧ δ₁ = 1 (the one
lift-form-consuming step, PAIR-VAL Case II); the gr(w₂) semantics wrapper
rides the accepted GRB retarget (consumer-side, not consumed by the theorem);
orders ≥ 3 stay OPEN as displayed above. ACCEPTANCE COUNTER 0 — the
hostile-pass arc is the acceptance bar and is IN FLIGHT; until it closes,
consumers cite "proved-on-class at attempt grade", never "accepted". §S3's
consumable spec is unchanged in content; its conditionality display may cite
ITER-LAW as proved-on-class instead of displayed hypothesis PROVIDED the
instance is standard-lift (all compiled ones are).]**

**The retired form (fenced).**  "𝒟′ = F′[u′]/(u′^{e_b′} − ζ′) with a single ζ′" at
the canonical alphabet: REFUTED per S1.  It survives ONLY as: (a) the e_b = 1 /
E_i = 1 stratum (D-REAL's proved scope — MOVES "ζ′ = z̄ when e_b = 1" stands there);
(b) the information-free abstract crossed-product iso.  No proof unit, Lean kernel,
or consumer may bake the cyclic form at composite stages.

## S3. The consumable form (what `DIterJunctionSupplier` will consume)

The named open `DIterJunctionSupplier` (`H1/GlueRun.lean:875`; stated, never
asserted) is the junction-bundle supplier: at a stage σ₁ reached along f with a deep
`SideReads` bundle, some junction node hosts f's deep read with the full bundle.  Its
future discharge computes f's deep digits through the iterated development, i.e. IN
𝒟₂ above.  Binding obligations for any discharge (the docstring fence, restated here
as the consumable spec):

1. **Carrier**: digits valued in the iterated twisted algebra 𝒟₂ on the canonical
   anchor indexing (ℤ/E₂ fibred: outer s₂-track mod e₁, inner s₁-track mod e₀) —
   never in a single-constant cyclic F′[u′]/(u′^{E₂} − ζ′) carrier.
2. **Cocycle**: multiplication per (ITER-LAW) — BOTH constants (z̄ outer, z₁ inner)
   AND the fibration term ℓ₀γ₂δ₂; the degenerations of S2 are the only collapses.
3. **Sanity gates** any Lean/proof instance must reproduce: the B0a cocycle
   (associativity) identity; the D-REAL degeneration at e₀ = 1; NOT-CYCLIC on the
   row-N value pattern (the {z₁, z̄, z̄z₁^b} table is the compiled falsifier target).

Until (ITER-LAW) is PROVED (S2's open lemma), a discharge may consume it only as a
displayed hypothesis — the supplier's conditionality then names ITER-LAW explicitly.

## S4. Display-site census (grep `D-ITER|DIter` + cyclic-form sweep, 2026-08-08)

Sites DISPLAYING the refuted cyclic form, with dispositions:

| site | disposition |
|---|---|
| `lean/notes/MOVES_2026-07-24.md:1601–1615` (§F.2 "The new stage": 𝒟′ = F′[u′]/(u′^{e_b′} − ζ′)) | **BRACKETED this unit** (additive, in-bullet; record text untouched) |
| `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:696–711` (§S5.3 open sub-member D-ITER; the presentation clause) | **BRACKETED this unit** (POST-ACCEPTANCE style, REV-15/16/17 + §S3.4 bracket-A precedent; acceptance counters NOT reset) |
| `lean/notes/openmath/GRB_ORDER2_2026-08-05.md:942–946` (S8 open-lemma roster item 2) | **BRACKETED this unit** (short pointer bracket) |
| `lean/notes/MOVES_2026-07-24.md:1727–1735` (pass-8 verifier critical 3 quotes the form) | NO EDIT — adverse context (the critique that faulted it; now ANSWERED at order 2 by measurement, per STRATA_PROBE §S2) |
| `lean/notes/openmath/STRATA_PROBE_2026-08-08.md:114,138` | NO EDIT — the refutation record itself |
| `lean/LeanUrat/Scaffold/HDischarge/H1/GlueRun.lean:46–57,852–884` (`DIterJunctionSupplier` docstring) | NO EDIT — already compliant (ITER-LAW operative, cyclic form displayed as ADJUDICATED FALSE) |
| `docs/PROJECT_STATE.md:1677–1678`, `docs/ROOT_ASSEMBLY_2026-08-02.md:517,528–530,2964,5005`, `docs/SYNTHESIS_PASS5_2026-08-08.md` | NO EDIT — already record the refutation + "restatement owed"; owed-flag retirement rides the next r-fold (orchestrator-owned files) |
| `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` (D-ITER mentions passim) | NO EDIT — append-only ledger; refutation entered 2026-08-08; THIS unit's entry appended |
| All other grep hits (GRB passes 2–21, TR3S1/TR3S2 scope boxes, H1_BM1/BM2, HARDEST_FIRST §Tier 3, SiteExhProbe/TruncatedRun headers) | NO EDIT — name D-ITER as open/fenced WITHOUT displaying the cyclic form (several already cite ITER-LAW) |

## S5. What this unit does NOT do

No `DIterJunctionSupplier` discharge or Lean work (queue #11, blocked on this unit +
priced with the forge).  No proof of (ITER-LAW) — it remains an OPEN LEMMA with a
displayed route.  No TR3-S2/TWIST-LAW edits (F4 fence).  No orders-≥ 3 claim.  No
edit to accepted records beyond additive brackets; acceptance arcs stand
byte-unchanged.
