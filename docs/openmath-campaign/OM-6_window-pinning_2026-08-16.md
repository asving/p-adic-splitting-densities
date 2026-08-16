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

## §2. CERTIFICATIONS (script: `verification/om6_window_pinning_check.py` — 26/26 PASS)

**CERT-1 — GENHN-3(c), general congruence bound.** Grid `e₁ ∈ [1,6]`, `h ∈ [1,9]` coprime,
`N ∈ [1,10]`, all classes, all `m < e₁N` in class: both displayed inequalities hold on all
**6,325** cells; the occupied form (`m = e₁v + ih < e₁N ⟹ v ≤ N−1`) on **5,017** cells.
* **ATTACK (occupancy) — LANDS.** `(e₁, h, m) = (3, 2, 1)`: `i(1) = 2` (`1 ≡ 4 mod 3`), all
  hypotheses hold, but `1 = 3v + 4` has no solution `v ≥ 0` — `m` is an UNOCCUPIED height,
  so the display's *"— inside the string"* is FALSE as a membership claim. The two
  INEQUALITIES survive at the attack point (checked `N ∈ [1,10]`). This is the same defect
  family as `EFF.GENHN.28`'s second conditionality (`a(m) ≥ 0` fails at unoccupied heights,
  witness `(3,1,2,1)`; post-D2b `D′h < m` scope pin). **Repair adopted:** membership landed
  only in the occupied form. Finding recorded as **F-OM6.1** in AMENDMENT A-H.3; GENHN's
  frozen text NOT edited (WZ-BOX-7 discipline).
* **ATTACK (coprimality) — LANDS.** `(e₁, h) = (4, 2)`: class residues `[0, 2, 0, 2]`
  collapse — `i(m)` ill-defined without `gcd(h, e₁) = 1` (H.51's hypothesis is load-bearing).

**CERT-2 — GENHN-3(b), raggedness.** **1,540** strings: end `= e₁(N−1) + ih` exactly;
band count `= min(⌊ih/e₁⌋, N)` exactly; ends pairwise distinct across classes (RAGGED).
Genre-E specialization reproduces H.46's `raggedBand_card` value `t` on `t ∈ [0,4]`,
`N ∈ [2t+2, 2t+7]`. Bonus identity: total band over classes `= (e₁−1)(h−1)/2` at
`gcd = 1`, `N` large (classical reciprocity) — verified `e₁ ∈ [1,7]`, `h ∈ [1,11]`; at
`e₁ = 2` this is H.46's `t = (h−1)/2`, single class.
* **ATTACK (clamp) — LANDS.** `(e₁, i, h, N) = (2, 1, 21, 3)`: band card `= N = 3`, not
  `⌊ih/e₁⌋ = 10` — the `min(·, N)` clamp is real; an unclamped transcription would be false.

**CERT-3 — GENHN-3(a) interior + undercut.** Valuation-layer model (in-window digits fixed,
out-of-window digits exhaustively completed; `q ∈ {2,3}`; genres `(e₁,h) ∈
{(1,1),(2,1),(2,3),(3,2)}`, `N ∈ {2,3}`): **1,496** in-window states.
`dv < e₁N ⟹` constant over ALL completions (stability); `dv ≥ e₁N ⟹` completions
DISAGREE — the undercut is realized at every such state (instability); no occupied
in-window value ever ties `e₁N` (no-tie, `gcd = 1`). The residue-tie independence behind
"in-window slot digits agree across lifts" is GENHN-2's F_Q-independence — CITED
(`EFF.GENHN.27`), not re-derived; the model certifies the valuation layer only (honest
scope: this layer is characteristic-blind by construction).
* **ATTACK (no-tie needs `gcd = 1`) — LANDS.** `(e₁, h) = (2, 2)`: the in-window value
  `2(N−1) + 1·2 = 2N` TIES the cap — coprimality is load-bearing in `no_tie_at_cap`.

**CERT-4 — the `[r2]`/CAP-GEN band layer.** `comp(m)` regimes exact on `f₁ ∈ [2,4]`,
`k ∈ [1,3]`, `N ∈ [2,10]` (interior `= f₁`; band `∈ [1, f₁)`; beyond `= 0`); census
`= q^comp − 1` by exhaustive span enumeration (`q ∈ {2,3}`). Committed instance numbers
reproduced exactly (`[r2]`(4) / `EFF.GENHN.32` / H.44's audit): `(1,3,2)` at `N = 7`:
`comp(N) = 2`, `RAM(7) = 3·2¹³ = 24,576`, `UND = 2¹³ = 8,192`, total `2¹⁵ = 32,768`; at
`N = 8`: interior pin `comp = 3`, `RAM(7) = 7·2¹⁸ = 1,835,008`, `UND = 2¹⁸ = 262,144`,
total `2²¹ = 2,097,152`; `(1,2,2)` at `k = 1`: band `= {N}` (the GENH4-CAP(F) frame).
Trichotomy antecedents pairwise disjoint + exhaustive on `[0,60]²`; `capBranch(7,3) =
2SIDED` with the committed `384 + 128 = 512 = 2⁹` partition.
* **ATTACK (the r2 defect reproduced) — LANDS.** The RAM clause WITHOUT its side condition
  `N ≤ 2w` double-fires with (a) (e.g. `(N,w) = (1,0)`) — the ledgered lesson ("re-derive,
  never transcribe a verifier's phrasing") is confirmed by construction.

**CERT-5 — GENHN-3(d), triangularity, BOTH characteristics.** Char 0: `ℤ/p^M` with carries,
`p = 2` EXHAUSTIVE at `M = 3, μ = 2` (all `f`, all `s`, all height-`≥ D` perturbations,
`D ∈ {1,2}`), `p = 3` thinned — new digits at heights `< D` never move. Char `p`:
`𝔽_q[t]/t^M` (no carries), `q = 2` EXHAUSTIVE at `M = 2, μ = 2`, `q = 3` thinned — same.
The downward-carry search IS the exhaustive leg: 0 violations.
* **Tightness — LANDS.** A height-1 old-digit change moves a height-1 new digit
  (`p = 2, s = 1, f = 1`): "heights ≤ d" cannot be improved to "< d".

---

## §3. PER-GAP ANALYSIS AND STATUSES

**GAP-1 — (c) general congruence bound: PROVED.** The display's two inequalities, verbatim
scope, general `e₁` (H.51 supplies only the ingredient; H.89 only the `e₁ = 2` shadow):
`consulted_le_cap` (`m < e₁N ∧ m ≡ ih (mod e₁) ⟹ m ≤ e₁N − e₁ + (ih mod e₁)`) and
`cap_le_string_end` (`… ≤ e₁(N−1) + ih`), both ℕ-truncation-safe (the A-H.1/D8 lesson:
`e₁ = 0` and `N = 0` handled inside, no spurious guards). The "inside the string"
conclusion: **REFUTED unpinned (F-OM6.1)**, PROVED in the occupied form
(`consulted_inside_string`), refutation machine-checked (`unoccupied_height_witness`).

**GAP-2 — (b) general raggedness: PROVED.** `string_end_le` + `string_end_mem` (the class-i
string ends at exactly `e₁(N−1) + ih`), `string_ends_ragged` (ends strictly increase across
classes), `bandCard` (`= min(⌊ih/e₁⌋, N)` — generalizes H.46's `raggedBand_card`, gate-tied
to its genre-E value `t`). The R4 F-1 rider is honored: nowhere does the transcription say
"the band is never consulted" as a height-interval claim; the docstrings carry the corrected
"unread component cells" reading.

**GAP-3 — (a) interior criterion: PROVED at the rider-corrected strength.** The R4 F-1
TERMINAL wording replaces the frozen "iff `< e₁N`" by "the sufficient interior criterion
together with GENHN-CAP-GEN's exact boundary criterion". The sufficient direction is landed
(`out_window_dv_ge` + `interior_min_stable`); the undercut computation is landed as the
witness pair (`no_tie_at_cap`, coprimality load-bearing + `cap_undercuts`). What this does
NOT claim: the boundary criterion (CAP-GEN clause 2) — see GAP-4. The residue-independence
tie-break: REDUCES-TO(H.51 + `EFF.GENHN.27`), consumed as the corpus consumes it.

**GAP-4 — (a) band clause beyond the `(1,2)` frame: split verdict.**
* The `[r2]` band GEOMETRY and the CAP-GEN census clause: **PROVED** (`compVis` + three
  regime laws; census through landed H.44 `pinCensus`; the committed `(1,3,2)` instance
  partitions machine-checked — three independent derivations of the census now agree in
  Lean as they did in the spec's audit: E2's clause, CAP-GEN COUNT TRANSPORT, CR-3).
* CAP-GEN's three-clause READER rule (undercut test / dictionary-constancy on the
  completion set / complete-pin recursion) and the `[r2]` trichotomy transport at
  `f₁ ≥ 3`: **CERTIFIED-OPEN.** The mathematics is corpus-derived (EFF.GENHN.79, part of
  the A2 wave, itself awaiting sol discharge-confirmation per its ledger line) and its
  arithmetic consequences are certified here (CERT-4), but the reader is not formalized —
  CHAP-H §16 item 3's standing decision, which this unit UPHOLDS rather than overturns:
  formalizing the reader is a chapter-scale unit, not an appendix. The un-formalized
  remainder is exactly what `StageInterface.hwin` carries (HYP.36 CARRY).

**GAP-5 — (d) triangularity: PROVED at the update-map core.** `recenter_descends`: the S6
recentering descends to `R⧸I` for EVERY commutative ring — instantiating `I = (π^{d+1})`
gives "new digits at heights `≤ d` are a function of old digits at heights `≤ d`", and the
`∀ R` quantifier IS "both ring types" (stronger than checking two instances).
`recenter_coeff_hasse`: the coefficient-axis triangularity (GENIND-2(a)'s "binomial update
matrix is triangular with unit diagonal") via `Polynomial.taylor_coeff`/`hasseDeriv`. The
chain-iterated reading ("deep histories never consult …") REDUCES-TO the per-step statement
+ GENIND-2(a)'s ghost-zone argument, which is how the display itself argues ("(d) is S6's
triangularity"); the iteration is not separately transcribed.

---

## §4. LANDINGS

* **Lean:** `leanfinal/Uniformity/ChapH/H89w.lean` — 17 declarations (15 in
  `Uniformity.Density.Induction` + 2 ring-generic), sorry-free; `#print axioms`: every
  declaration within `{propext, Classical.choice, Quot.sound}` (several smaller;
  `string_end_mem` axiom-free). Compiled standalone AND registered in the `ChapH.lean`
  roll-up; full `lake build Uniformity.ChapH.H89w` green (8,569 jobs). Header carries the
  H09w-style contract: appendix file, not a node; fences quoted.
* **Script:** `verification/om6_window_pinning_check.py` — 26/26 (§2).
* **Blueprint:** CHAP-H **AMENDMENT A-H.3** (dated append; registers H89w, records
  F-OM6.1, restates the four carried fences). CHAP-I **dated addendum** (O-2 DISCHARGED at
  its named candidate home; I.14's resolution unchanged).
* **Ledger:** HYP.24 dated **ARC NOTE** (disposition unchanged: CARRY; gap narrowed;
  pointers to A-H.3, H89w, this note).
* **Commits (all scoped-add verified):** `2f8f0f5d` skeleton · `69cbef3a` certification
  leg · `d526fb61` H89w.lean · `da97f23d` roll-up registration · `db0df19c` bookkeeping
  (A-H.3 + CHAP-I addendum + HYP.24 ARC NOTE) · final: this note completed.

---

## §5. LEDGER EFFECT (HYP.24's honest post-unit disposition)

**HYP.24 stays CARRY.** What changed and what did not, exactly:

* **Discharged before this unit, unchanged:** the pinning half at `e₁ = 2` (H.89, its
  A-H.1/D8-repaired guards intact); the `(1,2)`-frame band trichotomy (H.88); the quartic
  census (H.44); the genre-E band (H.46).
* **Newly transcribed (this unit):** the elementary supplier's OWN clauses at general
  `e₁` — the (c) bound, (b) raggedness, (a)-interior with undercut/no-tie, the
  `[r2]`/CAP-GEN band-census arithmetic, (d)'s descent. The supplier-gap sentence of I.14
  ("consumed by committed H only at the (c) bound (H.51)") is now false in the good
  direction; O-2 is discharged.
* **Still carried (why the row cannot move):** (i) the general-genre pinning content as
  CONSUMED by the count laws is `StageInterface.hwin` — HYP.36 CARRY, no universal
  discharge exists (obstructed for embedded/mixed genres, `EFF.GENIND.197/.199`), and
  GC-5 assigns per-genre instances only; (ii) `GENHN-CAP-GEN`'s reader rule — the exact
  boundary criterion that would upgrade GAP-3's sufficient direction to the full
  adjudication — has no Lean form (CHAP-H §16 item 3, upheld); (iii) EFF.GENHN.79 itself
  is part of GENHN's A2 repair wave, "await[ing] sol discharge-confirmation" (its ledger
  line) — a transcription cannot outrun its source's own acceptance state; (iv) the
  DECISION half of HYP.24 is other units' scope entirely.
* **Interaction notes for the orchestrator:** (a) I.05's `WindowPinningAt` stub (`True`
  body) is in the D-D12 vacuous-carrier neighborhood; at resolution time its real body
  should quantify H.09's stage data and assert the `hwin` clause per genre — H89w now
  supplies the general-`e₁` vocabulary the body can gate against (the I composer's call,
  not made here). (b) The Display-A adjudication unit re-signing D.62/D.63: no contact
  (H89w imports ChapH only). (c) F-OM6.1's occupancy scope pin joins EFF.GENHN.28's
  `a(m) ≥ 0` defect as the second instance of the same unoccupied-height family — if a
  future GENHN erratum wave lands, both should be pinned by one scope clause.
