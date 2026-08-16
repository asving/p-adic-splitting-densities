# OM-6 — window pinning (HYP.24) + the `EFF.GENHN.29` partial-transcription gap — unit note, 2026-08-16

**Charge.** The supplier of GENHN-3's cap clauses that chapter I's COND resolution I.14
routes through H.89 + `hwin`, flagged by the chapter-I composer (honesty item I-11(ii),
orchestrator item O-2) as only PARTIALLY transcribed in committed chapter H: *"`LEMMA
GENHN-3`'s cap/consultation clauses (`EFF.GENHN.29`) are consumed by committed H only at
the (c) congruence bound (H.51)"*. Mandate: inventory the un-transcribed remainder with
quotes, certify each clause (exact numerics, both primes, both characteristics,
constructed-counterexample attacks), prove certified steps at transcription grade (math
language + Lean where the landed vocabulary reaches), record HYP.24's honest post-unit
disposition. Fences honored: `hwin` is HYP.36 CARRY per GC-5's table — this unit does
NOT discharge `hwin`; H.89's `e₁ = 2`-only fence stays; D.62/D.63 are another unit's
concurrent re-signing and are untouched.

**Statuses used:** PROVED / CERTIFIED-OPEN / REFUTED(+repair) / REDUCES-TO(<node>) /
CITE-CANDIDATE.

**Verdict summary** (details §3; certifications §2; landings §4):

| item | verdict |
|---|---|
| GAP-1 — GENHN-3(c), the general-`e₁` consulted-height congruence bound (the two displayed inequalities) | **PROVED** (Lean, `H89w.lean`: `consulted_le_cap`, `cap_le_string_end`, `consulted_inside_string`; general `e₁`, no genre hypothesis, Lean-core footprint) |
| GAP-1's "— inside the string" reading, unpinned | **REFUTED(+repair)** — constructed counterexample `(e₁,h,m) = (3,2,1)`: `m ≡ i(m)h (mod e₁)` and `m < e₁N` hold with `i(1) = 2`, but `m` is NOT an occupied height of the class-2 string (`a(m) = −1`); same scope defect EFF.GENHN.28's second conditionality records for the normalizer display. Repair: the occupied form `m = e₁v + ih, v ≥ 0` (landed, `consulted_inside_string`); the two INEQUALITIES survive the attack unrepaired |
| GAP-2 — GENHN-3(b), general raggedness (string end `e₁(N−1) + ih`, band cardinality) | **PROVED** (Lean: `string_end_le`/`string_end_mem`/`string_ends_ragged`, `bandCard` `= min(⌊ih/e₁⌋, N)`; specializes to H.46's `raggedBand_card` value `t` at `(e₁,i) = (2,1)`, machine-checked instance) |
| GAP-3 — GENHN-3(a) interior criterion (rider-corrected: SUFFICIENT direction) + the undercut/no-tie computation | **PROVED** (Lean: `out_window_dv_ge`, `interior_min_stable`, `no_tie_at_cap` (coprimality load-bearing — counterexample at `gcd(h,e₁) = 2`), `cap_undercuts`); the residue-tie independence leg (GENHN-2's F_Q-independence) is NOT re-proved — REDUCES-TO(H.51 + `EFF.GENHN.27`), consumed as the corpus consumes it |
| GAP-4 — GENHN-3(a) band clause at `f₁ ≥ 2` beyond the `(1,2)` frame: the `[r2]` band geometry + `CAP-GEN`'s census | **PROVED for the arithmetic layer** (Lean: `compVis` + interior/band/beyond laws, census tie to landed H.44 `pinCensus`, the committed `(1,3,2)` instance numbers `3·2¹³ + 2¹³ = 2¹⁵`, `7·2¹⁸ + 2¹⁸ = 2²¹` machine-checked); the reader-rule clauses (CAP-GEN 1–3, dictionary-constancy) remain **CERTIFIED-OPEN** — chapter H's standing decision (§16 item 3: the reader is not formalized) is upheld, not overturned |
| GAP-5 — GENHN-3(d), S6 triangularity ("carries move upward only, both ring types") | **PROVED for the update-map core** (Lean: `recenter_descends` — recentering descends to `R/I` for EVERY commutative ring, so both characteristics at once; `recenter_coeff_hasse` — the coefficient-axis triangularity via Hasse derivatives); the chain-iteration reading (deep histories) REDUCES-TO the per-step statement + GENIND-2(a), as the display itself says |
| `hwin` (StageInterface, general genres) | **UNCHANGED: CARRY** (HYP.36, GC-5). Nothing here weakens or discharges it |
| HYP.24 post-unit disposition | **CARRY, gap narrowed** — pinning half: `e₁ = 2` discharged (H.89, unchanged), the elementary supplier's arithmetic clauses now transcribed (H89w); still carried: CAP-GEN's reader rule + the general-genre `hwin` content. Dated ARC NOTE added to the ledger row |

---

## §1. HIGH-LEVEL OUTLINE (mandated order)

### 1.1 What HYP.24's row demands (spec/HYPOTHESIS_LEDGER.md, verbatim)

> HYP.24 `[H-e]` decision plus window pinning
> STATEMENT: Separable order≥2 residuals decide σ for all disc≠0 lifts, and all consumed
> read data are pinned inside the stage window by the [H-a]/[H-b] leg.
> PROPOSED DISPOSITION: CARRY — GMN supplies only decision; project-internal pinning
> remains. **SUPPLIER RE-SOURCED (v4, COR-WFA preview item iv):** … On the route actually
> walked the pinning is supplied **elementarily**, by `LEMMA GENHN-3` (caps, raggedness,
> consultation — `GENHN_PROOF_2026-08-08.md` L741–770) together with GENIND-2's
> consulted-height bound. **The conjunct itself does not move.**

Two halves. The DECISION half is out of this unit's scope (CHAP-I's row: order 1 =
B.58/B.79–B.82; order ≥ 2 = C §10 + E's ladder; `μ ≥ 3` = HYP.81). The PINNING half is
the COND conjunct `COND:H-e)-window-pinning`, resolved at CHAP-I NODE I.14 as: formal
carriers I.05 (`WindowPinningAt`, stub) + H.89 (the `e₁ = 2` discharge) +
`StageInterface.hwin` (the carried general field), **supplier gap recorded**: EFF.GENHN.29
beyond H.51's (c)-bound consumption = orchestrator item O-2. This unit is O-2's booking.

### 1.2 What EFF.GENHN.29 states (spec/EFF-GENHN.md L1618 ff.) — the cap clauses in full

Canonical statement, LEMMA GENHN-3 (GENHN_PROOF_2026-08-08.md L741–763), verbatim:

> **LEMMA GENHN-3 (caps, raggedness, consultation).** (a) A computed dv-value is
> LIFT-STABLE iff < e₁N: an out-of-window O-digit at height v = N in class i = 0 gives
> dv = e₁N, undercutting every in-window value ≥ e₁N and tying none below it; conversely
> all in-window slot digits agree across lifts. For f₁ ≥ 2 the boundary band (value
> readable, K-residue needing an out-of-window component) is adjudicated as GENH4-CAP(F)
> **[e2-E1 2026-08-09: as CORRECTED at GENH4 r3 (frozen pin 4b0d946) — the band read is a
> trichotomy of which ONLY the even branch exits UND …]**. (b) The class-i slot string of
> a coordinate ends at e₁(N−1) + ih: RAGGED across classes; the band beyond min-class end
> is free depth on every leaf locus. (c) Every digit consulted by a readable event sits
> strictly inside its class's window: a consulted height m satisfies m < e₁N and
> m ≡ i(m)h mod e₁, hence m ≤ e₁N − e₁ + (i(m)h mod e₁) ≤ e₁(N−1) + i(m)h — inside the
> string. (d) Along chains, every update (S6) determines new digits at height d from old
> digits at heights ≤ d: carries move upward only, both ring types. Hence deep histories
> never consult the ragged band, and the per-node laws are uniform below the caps. ∎

The correction chain the spec compiles (EFF.GENHN.29 CONDITIONALITY): frozen (a)/(b) →
`[e2]` ERRATUM E1 (the band-exit clause transcribed GENH4-CAP(F)'s pre-r2 FALSE phrasing;
corrected to the r3 trichotomy) → `[r2]` annex (the f₁ ≥ 3 band transport DERIVED at
`(μ, e₁) = (2, 1)`; E2's readability parenthetical scoped to the FIRST band height) →
R4 F-1 riders + **LEMMA GENHN-CAP-GEN** (EFF.GENHN.79, TERMINAL): *"Read GENHN-3(a)'s
'iff < e₁N' as the sufficient interior criterion together with GENHN-CAP-GEN's exact
boundary criterion"*; *"Read 'the ragged band is never consulted' … as 'the unread
component cells of the ragged band are never consulted'"* (the height-interval reading is
FALSE — a first-band height can support a lift-stable terminal decision).

The OTHER named supplier (HYP.24 v4): GENIND-2's consulted-height bound
(GENIND_PROOF L288–331): consulted heights at abscissa j are ≤ (m−j)(N−1)/m < N − jk —
the ghost-zone separation, whose OB-a boxing (GENIND L1295–1310) is exactly what GENHN-3
resolves genre-generically.

### 1.3 What committed CHAP-H carries vs omits

CARRIED (landed, sorry-free, Lean-core):
* **H.51** (`class_sep`, `class_sep_bij`) — GENHN-2's class separation mod `e₁`, the (c)
  bound's INGREDIENT; SOURCE cites EFF.GENHN.29(c) — the bound itself is not stated.
* **H.89** (`consulted_ram`/`consulted_twoSided`/`consulted_refine`/`band_not_consulted`,
  at the A-H.1/D8-repaired guards) — the consulted-height ledger **at `e₁ = 2` only**
  (source EFF.GENH4.21, the quartic shadow); its own fence: *"THIS IS (OB-a)'s DISCHARGE
  AT e₁ = 2 AND ONLY THERE"*.
* **H.88** (`capBranch`, `capBranch_trichotomy`, `capBranch_seven_three`) — the
  E1-corrected band-exit trichotomy at the `(e₁,f₁) = (1,2)` frame (source EFF.GENH4.18).
* **H.44** (`pinCensus q c = q^c − 1` + genre clauses) — CAP-GEN's COUNT-TRANSPORT census
  at the quartic comp values (1 and 2), source cites EFF.GENHN.79.
* **H.46** (`slotOdd`/`slotEven`, `raggedBand_card` `= t`, `raggedBand_empty_of_h_one`) —
  the (b) clause's strings and band **at genre E (`e₁ = 2`) only** (source EFF.GENH4.17).
* **H.09 `StageInterface.hwin`** — the general-genre CARRY. Note precisely: `hwin` is
  `(CS-1Q.a)` (`e₁(N−1−H) ≤ stageWindow + stageLoss`), the window-SUPPLY inequality —
  the carried general pinning is the field's *content read through CAP-GEN's COUNT
  TRANSPORT* ("CS-1 and CS-2 hold … without a new box"), not a pinning Prop per se.
  GC-5: HYP.36 CARRY, "NO universal discharge anywhere".

OMITTED (the O-2 gap, clause by clause) — see §3 for dispositions:
* **GAP-1**: (c)'s general-`e₁` congruence bound (both displayed inequalities).
* **GAP-2**: (b)'s general string-end law + band cardinality (only `e₁ = 2` landed).
* **GAP-3**: (a)'s interior criterion (rider-corrected sufficient direction), the
  undercut computation and the no-tie clause.
* **GAP-4**: (a)'s band clause beyond the `(1,2)` frame — the `[r2]` band geometry
  (`comp(m)`: interior/band/beyond), the census law at general `comp`, the committed
  `(1,3,2)` instance numbers; and CAP-GEN's three-clause reader rule.
* **GAP-5**: (d)'s triangularity (the update-map descent; "both ring types").

### 1.4 Where the new content goes (precedents)

Landing vehicle: `leanfinal/Uniformity/ChapH/H89w.lean` — an H.89-adjacent appendix file
per the H09w precedent (a non-node file with an explicit header contract), which is
exactly O-2's *"candidate: an H-appendix node next to H.89"*; registered by dated
blueprint amendment **A-H.3** (the A-H.1/A-H.2 dated-append precedent) + a dated ARC NOTE
on HYP.24's ledger row (the chapter-G v7 ARC NOTE precedent) + a dated addendum line in
CHAP-I marking O-2 booked (the OM-4 addendum precedent).

**D-gate interaction (noted, not touched).** I.05's stub body is `True` — the same
vacuous-carrier neighborhood as D-D12's exact-height finding. This unit gives the future
real body concrete content to bind to (H89w's general clauses quantified over H.09's
stage data) but does NOT edit I.05 (stub-stage, BLOCKED-UNTIL-RESOLUTION, chapter-I
composer's file). D.62/D.63 (concurrent re-signing unit): no contact — H89w imports only
ChapH modules; no D vocabulary is consumed.

---

## §2. CERTIFICATIONS (script: `verification/om6_window_pinning_check.py`)

[TO BE FILLED — CERT-1..CERT-5 results with exact counts.]

---

## §3. PER-GAP ANALYSIS AND STATUSES

[TO BE FILLED — per-gap: source quote, certification pointer, proof/refutation, status.]

---

## §4. LANDINGS

[TO BE FILLED — Lean file, amendment, ledger note, commit hashes.]

---

## §5. LEDGER EFFECT (HYP.24's honest post-unit disposition)

[TO BE FILLED.]
