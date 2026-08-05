# GRTJB — J-B, THE TREE JUNCTION: the expansion identity, the polygon identity through the displayed shear, the division-step correspondence (the [RMG] tree = the classifier's own division arithmetic, with LED-Λ's line face as the polygon bookkeeping), and the (C-READ) transport with the ε-carry collapse

**Unit:** J-B COMPOSER (weld dependency order: W-2 and J-A composed and
consumable at attempt grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`
§S2.2 (J-B) and §S3.1 rows W-3/W-5). **Genre: PROOF NOTE at attempt grade
(acceptance counter 0/2; no gate fires; no acceptance arc opened), with
sealed-runner machine brackets** (`verification/openmath/grt_jb_checks.py`,
two-commit seal). ~~**[r1] S-STATUS: attempt grade, acceptance counter 0/2,
ONE hostile pass RUN (JB-PE1, commit 85a8dc9 — 1 CRITICAL + 9 gaps, NOT
CLEAN) and REPAIR ROUND r1 applied against it (block below); no gate fires;
the next acceptance attempt is a fresh hostile pass on the post-r1 text.**~~
~~**[r2] S-STATUS (CURRENT, supersedes the struck r1 line): attempt grade,
acceptance counter 0/2, TWO hostile passes RUN and TWO repair rounds applied.
Arc: JB-PE1 (85a8dc9 — 1 CRITICAL + 9 gaps, NOT CLEAN) → r1 (4c97649,
46f9452) → JB-PE2 (`GRTJB_passPE2_report.md`, committed by that pass —
0 CRITICAL + 7 gaps, NOT CLEAN, PE1's F1 confirmed CURED) → r2 (this round,
block below). No gate fires; no acceptance arc is open. A repair round is NOT
a pass, so the counter stays 0/2, and JB-PE3 — a fresh hostile pass on THIS
post-r2 text — is the next acceptance attempt.**~~

**[r3] S-STATUS (CURRENT, supersedes both struck lines): attempt grade,
acceptance counter 0/2 (ZERO clean passes), THREE hostile passes RUN and
THREE repair rounds applied. Arc: JB-PE1 (85a8dc9 — 1 CRITICAL + 9 gaps, NOT
CLEAN) → r1 (4c97649, 46f9452) → JB-PE2 (`GRTJB_passPE2_report.md` — 0
CRITICAL + 7 gaps, NOT CLEAN, PE1's F1 confirmed CURED) → r2 (67bf0c4,
888e293) → JB-PE3 (`GRTJB_passPE3_report.md`, commit 2fd271e — 0 CRITICAL +
8 gaps, NOT CLEAN; the FIRST acceptance attempt, which did not land) → r3
(this round, block below: THE CONDITIONALITY-MATRIX NORMALIZATION, §0M). No
gate fires; no acceptance arc is open. A repair round is NOT a pass, so the
counter stays 0/2, and JB-PE4 — a fresh hostile pass on THIS post-r3 text —
is the next acceptance attempt. All four machine instruments are BYTE-FROZEN
in r3 (md5s in the front-matter blocks; r3 is note-only, no script and no
artifact is touched).**

## §0M. **[r3] THE CONDITIONALITY MATRIX — the single surface every grade statement in this note is generated from**

**[REPAIR ROUND r3, STEP 1 — why a table replaces a fourth sweep.** Per-site
fence patching has not converged. The SAME defect — a proviso present in a body
proof and absent from a surface a downstream unit reads alone — was found in
every round of this note's arc: PE1/G-9 → PE2/G2-1 → PE3/F-1 **and** PE3/F-1B,
the last two of them at surfaces r2's own mandated re-grep had just certified
"already consistent". A fifth sweep would find a sixth site. So r3 builds the
matrix ONCE, filling every cell from the BODY PROOF (not from any existing
grade line), and then REGENERATES every grade surface from it: the grade cap,
the four ∎ Grade lines, the seven §7.2 rows, §7.3's consequence display, and
JB-BOX-2's enumeration. **After r3 no grade surface in this note may carry a
conditionality claim that is not a cell of this table, and none may omit one.**
A hostile pass audits ONE table plus the regeneration; that is the whole point
of the round.]**

**The columns (each proviso defined once, here).**

  **(a1) SHARED-KEY PERIMETER, `P<q`** — §1's second name: Φ_j^har =
  φ_{j+1}^cls byte-for-byte for every 1 ≤ j ≤ q−1, **nothing required at
  j = q**; equivalently the level range 0 ≤ q ≤ qcap with
  qcap := min(n, shared_upto+1) = the runner's own `qcap_of(T,G)`. This is
  J-A's perimeter instantiated AT LEVEL q, and it is exactly what a JA-VAL
  consumption at level q needs.

  **(a2) BYTE-EQUAL CHAIN THROUGH q, `P≤q`** — §1's first name: Φ_j^har =
  φ_{j+1}^cls for every j ≤ q. Equivalently: **J-A's perimeter instantiated at
  level m = q+1.** STRICTLY STRONGER than `P<q`; the two differ exactly at the
  top level q = qcap = shared_upto+1, where `P<q` holds and `P≤q` FAILS by the
  definition of shared_upto. Consumers: JB-DEV(ii)'s byte clause **and — [r3,
  F-4, NEW — JB-DEV(iii)'s (RES) layer**, which is JA-RES at read level
  m = q+1 and therefore needs J-A's perimeter at m, i.e. through j = q. (This
  corrects §1's r2 sentence "no statement cites §1 for the through-q condition
  except JB-DEV(ii)'s byte clause"; see the [r3] amendment there.)

  **(b) [JA-r1] u ≥ 0** — JA-GRID(a)'s inline J-A repair proviso
  u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 on the quantified window,
  **CARRIED AND UNDISCHARGED** (r2, G2-5; r1's "discharge" retracted). It is
  NOT one of JA-BOX-1..5. JA-GRID(c) — the carry clause LEMMA JB-EPS consumes
  — carries NO proviso.

  **(c) (VD-m) level fence** — J-A §3.4's EVALUATED dictionary. **Unconditional
  at m ≤ 1 ONLY** ((VD-1) = W2-L3); at every m ≥ 2 a HYPOTHESIS (JA-VDIND's
  ABSOLUTE character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every attained
  abscissa); at m ≥ 3 implied by the per-digit proviso / (R-coll) of JA-BOX-2.
  Distinct from JA-RES, the PER-SLOT law, which is unconditional at m = 2 and
  carries its own per-digit proviso at m ≥ 3 — the r1/F1 reading fence.

  **(d) W2-C1 representative restriction** — the statement is made at the
  representative φ_{q+1} := Φ_q^har, admissible by W-2 clause 1 on W-2's own
  perimeter (W2-C1a for the window object; W2-C3 for the transported chamber).
  W-2 clause 1's own conditionality rides. `YES*` = inherited, i.e. the clause
  speaks about objects a `YES` clause produced.

  **(e) [RMG] recital** — which clauses of the (RM-m) box / the S2.x displays
  the claim consumes. **[r3, F-5]** §5's recital is restored to the COMPLETE
  S0.2 box (both dropped Ĉ_m clauses), so the word "verbatim" is true of it
  again, and the JB-EPS application instance is licensed (§5, and row 20).

  **(f) machine-evidence class** — **IND** / **SAME** / **NONE**, defined
  immediately below. This column grades EVIDENCE, never truth: a `NONE` cell
  says the battery is silent, not that the clause is false.

  **(g) other scope** — T-scope(m), g_m = 1, the v ≠ 0 stratum, LED-Λ's attempt
  grade, and each instrument's own coverage cut.

**The three evidence classes (used verbatim from here on).**

    IND   INDEPENDENT-LEG — the family compares two GENUINELY DIFFERENT
          computations (a different code path, or the print engine against the
          harness engine) and a disagreement is REACHABLE.
    SAME  SAME-COMPUTATION — the family re-executes ONE pure function on
          BYTE-EQUAL arguments, behind a guard that has already forced
          agreement: the violation is UNREACHABLE and the leg carries NO
          information. (PE1/G-1's disease. Named wherever it occurs; never
          counted as evidence, never advertised as a second engine.)
    NONE  NO-LEG — no family, in the sealed battery or in any post-seal
          instrument, keys this clause.

**THE MATRIX (28 claim rows × 8 proviso columns = 224 cells; `—` = not
consumed / free).**

| # | claim (body site) | (a1) `P<q` | (a2) `P≤q` | (b) u ≥ 0 | (c) (VD-m) | (d) W2-C1 | (e) [RMG] | (f) evidence | (g) other scope |
|---|---|---|---|---|---|---|---|---|---|
| 1 | **JB-DEV(i)** same division, §2(i) | — | — | — | — | **YES** (admissible representative) | — | **IND** `jb_dev`: `fresh_dev` vs `PolyO.dev`, 893 · **+ SAME** sub-leg ⟨n1⟩ | — |
| 2 | **JB-DEV(ii)** byte clause, §2(ii) | — | **YES — this IS its hypothesis** | — | — | — (W-2 clause 2, not clause 1) | — | **IND** `jb_keyeq` byte census, 25 rows (3 VACUOUS: T.n = 0, r1/G-3) | TH-BASE gives q = 1 always; W-2 (C-coll)/recursion split |
| 3 | **JB-DEV(iii)(VAL)**, §2(iii) | **YES** | — | — | — | YES\* (via row 1) | — | **IND** cross-engine `G.vgen(q+1,A)` vs `T.wlev(q,A)` inside `jb_dev`, over 0 ≤ q ≤ qcap | — |
| 4 | **JB-DEV(iii)(GRID)**, §2(iii) | **YES** | — | **YES — UNDISCHARGED** | — | YES\* | — | carry half **IND** (`jb_eps` keys JA-GRID(c)); grid/attained-abscissa half **NONE** | W2-L0 consumed |
| 5 | **JB-DEV(iii)(RES)**, §2(iii) | insufficient — see (a2) | **YES [r3, F-4]** | — | — ⟨n4⟩ | YES\* | — | **NONE** — no family keys (RES) anywhere ⟨n4⟩ | JA-RES's OWN fence: unconditional at m = q+1 = 2, per-digit proviso at m ≥ 3 (JA-BOX-2) |
| 6 | **JB-DEV(iv)** cross-key fence, §2(iv) | — | — | — | — | — | — | **NONE** (a displayed fence: nothing to key) | J-A §4(i) cited; W-2 clause 2/3 the only lawful transport |
| 7 | **LEMMA JB-AFF**, §3 | — | — | — | — | — | — | **NONE** as a lemma — its content is exercised inside rows 9/10 | unconditional, two lines |
| 8 | **JB-VTX(a)** pointwise shear | **YES** | — | — | — | **YES** | — | **IND** print ordinates (`G.vgen`/`G.vkey`) vs harness ordinates (`T.wlev`/`T.gam`), 893 | second half cites print `propertiesv` item 3 |
| 9 | **JB-VTX(b)** vertex-for-vertex | **YES** (via row 8) | — | — | — | **YES** | — | **IND** fresh lower hulls of BOTH frames + vertex bijection | — |
| 10 | **JB-VTX(c)** slope/length | **YES** (via row 8) | — | — | — | **YES** | — | **IND** `hull_sides` per-side slope/length law | — |
| 11 | **JB-VTX(d1–d3)** the THREE min ties | **YES** (the two print-side ties machine-restricted further to q ≤ shared_upto) | — | — | — | **YES** | — | **IND** three tie assertions ⟨n3⟩ | — |
| 12 | **JB-VTX(d4)** attained abscissas = read grid | **YES** | — | **YES — UNDISCHARGED** | — | **YES** | [ILN]† S0.2 read assembly | **NONE [r3, F-3]** ⟨n3⟩ | — |
| 13 | **JB-VTX(e)** window clause | YES\* (via row 8 at f = Φ_{q+1}^har) | — | — | — | **YES — W2-C1a** | — | **NONE** (none claimed) | subject is the KEY, not the quantified f (r1, G-4) |
| 14 | **JB-ID** — (ID-(i+1)) as the key's own development, §4(ii) 1st sentence | — | — | — | — | — | **YES** S2.2 (ID-(i+1)); P_i := e_i·g_i from S0.1 **[r3, F-7]** | **IND** `jb_id`: identity + digit list by fresh arithmetic, plus a genuinely print-side leg on the print chain's OWN keys | — |
| 15 | **JB-TREE(i)** tree = the classifier's division | — | — | — | — | **YES** (representative reading; W2-C3 chamber off the byte perimeter) | **YES** T-TERM, L-EXACT, L-CANON (L-CANON needs deg Ĉ_m < deg Φ_m — restored, r3/F-5) | **IND** fresh tree walk vs `fresh_divmod`; **+ IND** post-seal walker leg A (84 print-keyed walks) · **+ SAME** sub-leg ⟨n2⟩ · 8 chamber walks **NONE** | T-scope(m), g_m = 1 |
| 16 | **JB-TREE(ii)** each edge = one division step | — | — | — | — | — | **YES** S2.2 + L-NORM splits + L-CELL | **IND** `jb_id` digit list + `jb_tree`'s L-NORM exactness/reducedness assertions | — |
| 17 | **JB-TREE(iii)** λ_E face = the polygon bookkeeping | **YES** | — | — | — | YES\* | **YES** L-LINE(iv), S3.2 | **IND** `jb_line`: λ_E quanta recomputed FRESH per edge + leaf line == wlev == vgen (the vgen half gated on qcap ≥ m) | **LED-Λ at ATTEMPT grade — the tie's grade rides it** |
| 18 | **JB-TREE(iv)** (RM-m) as the transported instance | **YES** | — | — | **YES for the (C-READ) leg** (it transports as §5) | YES\* | **YES** all four box clauses | (C-W_R) **IND** (`jb_cread`'s w_m(R) = λ+γ_{m+1} pin); (C-W_Q) **NONE**; (C-READ) **IND** on the scored stratum | T-scope(m), g_m = 1 |
| 19 | **LEMMA JB-EPS**, §5 | — | — | — | — | — | JA-GRID(c) = (C-EPS) | **IND** `jb_eps`, 955: ℓ-FREE `s_geo` + fresh Bézout against the ℓ-form t_m, then the field form | **unconditional at every m ≥ 1** |
| 20 | **JB-EPS APPLIED at (V,V′) = (λ, γ_{m+1})** (inside §5's display) | — | — | — | inherits row 21's context | — | **YES — the RESTORED clause w_m(Ĉ_m) = γ_{m+1} licenses the instance [r3, F-5]** | **IND** — the leg quantifies PLAIN integers 0 ≤ V,V′ < 25, a superset of the lattice instance | — |
| 21 | **JB-CREAD** ρ_m(R) = c_m·ρ_m(f), v ≠ 0 | — for the STATEMENT (a legitimate conditional at any level) ⟨n5⟩ | — | — | **YES — the governing fence** | — (no representative claim in §5) | **YES** (C-READ), (C-W_R), the complete Ĉ_m clause list, L-CELL(i)/(ii) = (B-READ) | **IND** end-to-end cross-engine (print residuals via the sealed `GmnLeg`, harness division/reads via ITL, τ/ε′ fresh integers) on the SCORED stratum: 104 scored / 21 boundary disclosed · **+ IND** teeth MJB-CREAD (22) | v ≠ 0 stratum; g_m = 1; T-scope(m) |
| 22 | **JB-CREAD, v = 0 branch** | — ⟨n5⟩ | — | — | **YES** ((VD-m) at f) | — | **YES** — (C-READ) gives the TARGET read only | **NONE — machine UNEXERCISED** (v = 0 census: 0 rows; disclosed in §7.1) | read-at-target (0 = 0) only; the ρ-form is NOT claimed |
| 23 | **JB-BOX-1** blueprint carry placement | — | — | — | inherits row 21 | — | (C-READ) is the HARNESS-frame form | **IND** teeth MJB-CREAD — the carry-bearing reading must FAIL, and does, on all 22 designated samples over 14 towers | — |
| 24 | **JB-BOX-2** the carrier box | records rows 3,4,5,8–13,17,18 | records row 5 | records rows 4,12 | records rows 21,22 | records rows 1,8–13,15 | — | n/a (record) | — |
| 25 | **JB-BOX-3** cross-key fence | — | — | — | — | — | — | n/a (record) | no cross-representative operator or byte identity anywhere; SideReads/TreeModel consumed nowhere |
| 26 | **JB-BOX-4** tree scope | — | — | — | — | — | **YES** ([RMG]'s fences inherited verbatim) | n/a (record) — the FRESH λ_E re-verification of row 17 is the decorrelation this box claims | T-scope(m), g_m = 1, W-WIN unconsumed, LED-Λ ATTEMPT |
| 27 | **JB-BOX-5** instance perimeter | — | — | — | — | — | — | n/a (record) — **evidence caveat: F_p[[t]] rows have NO external (PARI) oracle leg** (JA-BOX-4 inherited) | the 16-tower roster + 5 QO shapes + 4 fresh d₀ ≥ 2 shapes |
| 28 | **JB-BOX-6** standing fences | — | — | — | — | — | — | n/a (record) | no gr/carrier (J-C), no count/menu/density (J-D), P0 gate stands, counter 0/2 |

**Cell notes (the five cells that need a sentence).**

⟨n1⟩ **Row 1, column (f) — [r3, F-2].** `jb_dev`'s genuine second computation
is `fresh_dev` (this runner's own schoolbook division) against `T.P.dev`, and
its genuine CROSS-ENGINE content is row 3's digit-weight tie. Its third leg —
`G.P.dev(f, G.phi[q+1])`, advertised in r0–r2 as "compared against **both
engines'** digit lists" — is **SAME**: `iterlawn_pe_reimpl.PolyO` carries only
`self.R`, and `gmn_from_tower` builds `GmnLeg(T.R, …)` whose `self.P =
ITL.PolyO(R)` holds THE SAME ring object, so `G.P.dev` and `T.P.dev` are the
identical method; the leg is guarded by `tuple(G.phi[q+1]) == key`, so the
arguments are byte-equal too, and it sits AFTER a `continue` on `dvF != dvI`,
so it is reached only once agreement is already forced. **The violation
`'fresh dev != print dev'` is unreachable.** There is ONE engine comparison in
this family, not two.

⟨n2⟩ **Row 15, column (f) — PE1/G-1, already corrected in r1's wording at
three sites and kept here as a matrix cell.** The sealed tree family's
print-key leg is `fresh_divmod` re-executed on byte-equal arguments behind the
`byteeq` guard: **SAME**. The independent print-key evidence is the post-seal
walker's leg A (§7.4(B), 84 walks, its own keys/correction digits/divisor/
division code), and it does not reach the four byte-unequal CHAMBER rows
(8 walks, **NONE**, disclosed at §7.4).

⟨n3⟩ **Rows 11/12, column (f) — [r3, F-3].** `jb_shear_vtx` contains exactly
THREE tie assertions: `minH == T.wlev(q+1,f)` (d2), and under `q <= L` both
`minU == G.vgen(q+1,f)` (d1) and `minH == G.vgen(q+2,f)` (d3). Clause (d)'s
FOURTH tie — the attained abscissas on the realized side are the read grid
s(λ) + j·e_q and the level-(q+1) read is assembled from the on-line digits at
those slots — **has no leg in any family**: `jb_dev` keys only the (VAL) weight
tie, `jb_line` keys line == wlev == vgen on reduced cells, `jb_cread` evaluates
(VD-m), and `jb_eps` keys JA-GRID's **carry** clause (c), which is the OTHER
half of the (GRID) layer and the half that carries no proviso. So the single
sub-clause with no machine leg is also the single sub-clause riding the
undischarged u ≥ 0 proviso (row 12 columns (b) and (f) together). Every surface
that used to say "all four min/read ties" now says **three keyed, (d4)
unkeyed**.

⟨n4⟩ **Row 5, columns (a2)/(c)/(f) — [r3, F-4].** (RES) is JA-RES at read level
m := q+1. J-A's perimeter is level-indexed — "Shared-key perimeter at level m:
Φ_q = φ_{q+1} byte-for-byte for all q ≤ m−1" — so at m = q+1 it requires
agreement for j ≤ q, i.e. `P≤q`, NOT `P<q`. r2 fenced all three layers of
§2(iii) with `P<q`, which is correct for (VAL) (JA-VAL at level q) and one
level short for (RES); the two differ exactly at q = qcap, where `P≤q` fails by
definition. (RES) does NOT consume (VD-m) — it is the PER-SLOT law — but it
carries JA-RES's own fence: unconditional at m = 2, per-digit proviso at m ≥ 3
(JA-BOX-2). No machine leg can catch the mis-fencing because no family keys
(RES) at all. Nothing inside §3–§5 consumes (RES), so the note's internal chain
is unaffected; what was over-supplied is JB-DEV(iii)'s (RES) layer as handed to
a downstream unit through §7.3.

⟨n5⟩ **Rows 21/22, column (a1).** §5's print-side content enters ONLY through
the (VD-m) hypothesis, so THEOREM JB-CREAD is a legitimate conditional at any
level and needs no key perimeter of its own. Disclosure, not a fence: the
INSTRUMENT cuts reduction levels at `qcap_of(T,G)` before `jb_tree`/`jb_cread`,
and the off-perimeter counter is **0** on the roster, so nothing was scored
outside that cut.

**What the matrix shows that no earlier surface stated.** (1) Three cells hold
an open proviso with NO machine leg beside it — rows 5 (RES), 12 (d4), 22
(v = 0) — and one of them (row 12) is the u ≥ 0 rider; those three are the
note's honest evidence frontier. (2) Exactly two rows consume `P≤q` (2 and 5),
and only one of them was ever fenced that way. (3) Exactly two rows consume the
u ≥ 0 proviso (4 and 12), and every surface must therefore name JB-VTX(d)'s
grid content as well as JB-DEV(iii)(GRID). (4) The (VD-m) fence reaches exactly
rows 18 (its (C-READ) leg), 21, 22 and 23 — nothing in §2–§4 rides it.

**Grade cap (read first) — [r3, STEP 2: SURFACE 1 of 14, REGENERATED FROM
§0M's MATRIX.** Every fence below is a cell of that table; the table carries
no fence this cap omits. The r0/r1/r2 cap is retained in full immediately
after this one, ENTIRELY SUPERSEDED and no longer authoritative — it is
retained as a quoted block rather than struck inline only because it already
contains r1/r2 strike markup, which cannot nest.**]**

* **JB-DEV (§2) — PROVED at attempt grade, one perimeter PER LAYER.**
  **(i)** same division at every level q ≥ 0, at the W2-C1 admissible
  representative φ_{q+1} := Φ_q^har (row 1). **(ii)** byte clause on the
  **BYTE-EQUAL CHAIN THROUGH q** (`P≤q`, §1); TH-BASE gives q = 1 always
  (row 2). **(iii)** three layers, each on its OWN perimeter — this split is
  the r3 correction: **(VAL)** on the **SHARED-KEY PERIMETER** `P<q`
  (0 ≤ q ≤ qcap), off which (VAL) is FALSE, not merely unproved (row 3);
  **(GRID)** on `P<q` **and** on JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso, which
  is CARRIED AND UNDISCHARGED (row 4; r2/G2-5, JB-BOX-2); **(RES)** on the
  **BYTE-EQUAL CHAIN THROUGH q** — `P≤q`, one level deeper than r2's fence,
  because (RES) is JA-RES at read level m = q+1 (row 5, **[r3, F-4]**) — plus
  JA-RES's own fence (unconditional at m = 2, per-digit proviso at m ≥ 3,
  JA-BOX-2 inherited); (RES) is NOT the evaluated dictionary (VD-m) (r1/F1's
  reading fence stands). **(iv)** a displayed fence, cited (row 6).
* **JB-VTX (§3) — PROVED at attempt grade on `P<q`** (0 ≤ q ≤ qcap,
  `qcap_of(T,G) = min(T.n, shared_upto(T,G)+1)` — the runner's own quantifier;
  off that perimeter clause (a)'s JA-VAL input is unavailable and (a) is FALSE,
  not merely unproved), every statement at the harness key as the W2-C1
  admissible representative; the shear is DISPLAYED (the GD-2/T-F convention
  pin made explicit — the unsheared identification is FALSE and is this note's
  teeth family). Clause-level: (a)/(b)/(c) and the **THREE** min ties (d1–d3)
  ride `P<q` + W2-C1 only (rows 8–11); **clause (d)'s FOURTH tie — attained
  abscissas = the read grid — additionally rides the UNDISCHARGED u ≥ 0
  proviso and has NO machine leg** (row 12, **[r3, F-1 + F-3]**); (e) is at
  f = Φ_{q+1}^har (W2-C1a), not at the theorem's quantified f (row 13).
* **JB-TREE (§4) — PROVED at attempt grade on [RMG]'s own scope** (T-scope(m)
  termination fence, g_m = 1 rows for the Ĉ_m instance), consuming [RMG] as
  ACCEPTED and LED-Λ at ATTEMPT grade (its λ_E face is cited as the polygon
  bookkeeping — the grade rides). Clause-level: **(i)/(ii) are
  PERIMETER-FREE** (rows 15–16); **(iii)/(iv) are asserted only at levels
  m ≤ qcap** (`P<q` read at level m), since they consume JA-VAL (rows 17–18) —
  **[r3, F-1B: this fence, which r2 added at §4 and §7.2 while certifying this
  cap "already consistent", now reaches this cap and JB-BOX-2]**; (iv)'s
  (C-READ) leg additionally rides §5's (VD-m) fence, and its (C-W_Q) clause has
  NO machine leg.
* **JB-CREAD (§5) — PROVED on the (VD-m) perimeter ∩ {v ≠ 0}.** (VD-m) is
  UNCONDITIONAL AT m ≤ 1 ONLY ((VD-1) = W2-L3); at every m ≥ 2 it is a
  HYPOTHESIS (JA-VDIND's absolute character-triviality, ⊇ (R-coll)/per-digit at
  m ≥ 3, JA-BOX-2), so **JB-CREAD has NO unconditional stratum above m = 1**:
  the note's own sealed runner machine-evaluates (VD-2) FALSE on 10 of its 13
  roster boundary rows (T3A/T3B/T3C/T3D; §7.1, r1/F1). The v = 0 branch is the
  read-at-target statement only and is machine UNEXERCISED (row 22).
* **LEMMA JB-EPS — UNCONDITIONAL at every m ≥ 1** (row 19), and its
  application inside §5 at (V, V′) = (λ, γ_{m+1}) is LICENSED by [RMG]'s
  clause w_m(Ĉ_m) = γ_{m+1}, restored to §5's recital in r3 (row 20,
  **[r3, F-5]**).
* **ONE BLUEPRINT DISPLAY IS CORRECTED (JB-BOX-1):** J-B(iii)'s "shifts the
  classifier's residual read by τ_m with the level-m EPS-carry z_m^{ε′}" — in
  the print's own twisted coordinates the carry CANCELS (the shift constant is
  c_m = ψ_{m,0}, = −z_{m+1} one level up); the carry-bearing form is the
  HARNESS-frame statement ([RMG] (C-READ) itself).
* **Standing.** Nothing here fires any gate, touches any accepted text, makes
  any gr/carrier (J-C) claim, or advances any density (J-D) statement.
  Acceptance counter 0/2.

**[r3 — SUPERSEDED r0/r1/r2 GRADE CAP, retained verbatim for the record. NOT
authoritative; where it differs from the cap above, the cap above (and §0M's
matrix) governs. Its three known defects: JB-TREE carries no perimeter (PE3
F-1B), JB-VTX's clause-(d) proviso is absent (PE3 F-1), and the (RES) layer is
fenced with `P<q` instead of `P≤q` (PE3 F-4).]**

> **Grade cap (read first).** JB-DEV (§2) is PROVED at attempt grade — its
byte clause exactly on the W-2 byte-equality perimeter, its representative
clause on W-2 clause 1's perimeter, its residual layer at J-A's grades
(**[r1, G-9]** the (VAL)/(GRID)/(RES) layers quantified on the shared-key
perimeter q ≤ qcap, not over all q ≤ n; **[r1, F1]** the PER-SLOT law
JA-RES unconditional at read level 2 with a per-digit proviso above —
JA-BOX-2 inherited — which is NOT the evaluated dictionary (VD-2), see
§2(iii)(RES); **[r2, G2-5]** and the (GRID) layer carries JA-GRID(a)'s
`[JA-r1]` proviso u := (V − s·h)/e ≥ 0 as an UNDISCHARGED inherited
hypothesis — r1 claimed a discharge, r2 RETRACTS it, see JB-BOX-2).
JB-VTX (§3) is PROVED at attempt grade **[r1, G-9] at every
level of the shared-key perimeter (0 ≤ q ≤ qcap, `qcap_of(T,G) = min(T.n,
shared_upto(T,G)+1)` — the runner's own quantifier; off that perimeter
clause (a)'s JA-VAL input is unavailable and (a) is false, not merely
unproved)** ~~at every level~~, stated at the harness key as the W2-C1
admissible representative; the shear is DISPLAYED (the GD-2/T-F convention
pin made explicit — the unsheared identification is FALSE and is this
note's teeth family). JB-TREE (§4) is PROVED at attempt grade on [RMG]'s own
scope (T-scope(m) termination fence, g_m = 1 rows for the Ĉ_m instance),
consuming [RMG] as ACCEPTED and LED-Λ at ATTEMPT grade (its λ_E face is
cited as the polygon bookkeeping — the grade rides). JB-CREAD (§5) is PROVED
on the (VD-m) perimeter ~~(unconditional at m ≤ 2; per-digit proviso /
(R-coll) at m ≥ 3)~~ **[r1, F1 — SUPERSEDED: the struck parenthetical was
FALSE. The honest perimeter is: UNCONDITIONAL AT m ≤ 1 ONLY ((VD-1) =
W2-L3); at every m ≥ 2 conditional on JA-VDIND's absolute
character-triviality (⊇ (R-coll)/per-digit at m ≥ 3, JA-BOX-2). JB-CREAD has
NO unconditional stratum above m = 1: the note's own sealed runner
machine-evaluates (VD-2) FALSE on 10 of its 13 roster boundary rows
(T3A/T3B/T3C/T3D), see §7.1 and the r1 block]** intersected with the
non-degenerate read stratum v ≠ 0 (the v = 0 branch displayed at the
theorem), with the ε-collapse lemma JB-EPS unconditional. ONE BLUEPRINT DISPLAY IS CORRECTED (JB-BOX-1):
J-B(iii)'s "shifts the classifier's residual read by τ_m with the level-m
EPS-carry z_m^{ε′}" — in the print's own twisted coordinates the carry
CANCELS (the shift constant is c_m = ψ_{m,0}, = −z_{m+1} one level up);
the carry-bearing form is the HARNESS-frame statement ([RMG] (C-READ)
itself). Nothing here fires any gate, touches any accepted text, makes any
gr/carrier (J-C) claim, or advances any density (J-D) statement.

**[r3 — end of the superseded grade cap.]**

**Literature and consumption discipline.** Classifier side = the GMN print
`docs/references/HigherNewton.tex`, consumed as literature through the
SEALED probe transcription `grt_weld_probe.GmnLeg` (no new print
transcription in this unit; the runner's fresh legs are its own division/
hull/integer recomputations). Print anchors used here beyond J-A's list:
the order-r polygon definition N_r(f) from the φ_r-adic development with
ordinates u_i := v_r(a_i φ_r^i) = v_r(a_i) + i·v_r(φ_r) (tex ~1370–1376,
"We define the Newton polygon N_r(f) … Note that we consider the v_r-value
of the whole monomial"); the principal part N_r^−(f) = negative-slope sides
(tex 1377); Lemma `shape` items 1–2 (min_i u_i = v_r(f), ℓ(N_r^−) = ω_r;
tex ~1395–1414); Definition `t(i)` (tex 1431), `rescoeff` (tex 1447),
`defresidual` (tex 1497); Proposition `propertiesv` item 3 (tex 1028).
Consumed notes: **[RMG]** = `RMENGINE_2026-08-08.md` ACCEPTED (**[r3, F-7 —
S0.1 ADDED to this list: the abbreviation P_l := e_l·g_l, which §4(ii) and
§7.4's PW-ID/PW-WALK rows use, is scoped "local to this note" in [RMG] S0.1
and was consumed here without being cited or defined]** S0.1 the period
abbreviation P_l := e_l·g_l; S0.2 the
(RM-m) box verbatim incl. (C-READ)/(C-EPS); S2.1 cells/lines/L-CELL/L-NORM;
S2.2 (ID-(i+1)) + the E1-priority tree + L-EXACT + L-CANON; S3.2 L-LINE;
S4 T-TERM on T-scope(m)); **[ILN]†** S0.1/S0.2 (accepted; class pin,
canonical lifts, REALIZE/WELL-DEF incl. the g_m = 1 form
Φ_{m+1} = Φ_m^{e_m} + Ĉ_m); **W-2** = `GRTW2_PROOF_2026-08-08.md` at
ATTEMPT grade (clause 1 admissibility W2-C1/C1a; clause 2 byte law §3.4(3)
+ (C-coll) split; clause 3 transport W2-C3; W2-L0/L2/L3); **J-A** =
`GRTJA_PROOF_2026-08-08.md` at ATTEMPT grade, arc 0/1 clean (JA-PIN,
JA-VAL, JA-EPS, JA-GRID, JA-RES/(VD-m)/JA-VDIND with JA-BOX-1..5);
**LED-Λ** = `LEDGERLAMBDA_2026-08-08.md` at ATTEMPT grade (the S1 quantum
table's λ_E column, LED-Λ(A1)/(B), L-MONO's edge signs). Every consumption
is at the source's own grade; nothing is upgraded here.

**Machine bracket:** `grt_jb_checks.py` — both sides of every §2–§5
equality on the weld-probe roster (16 towers) + the 5 concrete QO shapes +
the 4 fresh d₀ ≥ 2 shapes (engine_ext standing rule honored in-unit),
LAW-KEYED with teeth; transported-chamber re-instantiation on every tower
with a nontrivial W-2 transport ledger. Verdict in §7 (commit 2).

**[r1] POST-SEAL SUPPLEMENTARY MACHINE LEGS — NOT part of the sealed
battery.** Two instruments were written AFTER the JB-PE1 verdict and are
evidence for a REPAIR, not sealed predictions:
`verification/openmath/grt_jb_printwalk.py` (+ its committed
`grt_jb_printwalk_output.txt` / `_results.json`) — the independent PRINT-KEY
tree walker finding G-1 asks for, carrying its own mini two-commit seal
(prereg comment block committed BEFORE any full run); and
`verification/openmath/grt_jb_r1_levelcensus.py` (+ its committed output) —
the LEVEL-KEYED recomputation of the JB-CREAD boundary census that F1 turns
on. The sealed runner `grt_jb_checks.py` is BYTE-UNTOUCHED by this round
(md5 `55f4911eaddd8524fd91368b30ed71bd`, unchanged from seal 7f6759d), and so
is `grt_jb_checks_results.json`. Verdicts in §7.4. **[r2] A THIRD post-seal
instrument is added in r2: `verification/openmath/grt_jb_printwalk2.py` (+ its
committed output) — the GATE REPAIR for the r1 walker's cross-frame family
(PE2's G2-2), carrying its own mini two-commit seal. BOTH earlier instruments
are byte-untouched by r2 as well: `grt_jb_printwalk.py` md5
`f53e23e8d1c79f084a1e34eee857e37c` and `grt_jb_r1_levelcensus.py` md5
`2bcb44fdbf839d367f0e11033a5d3fd7`, unchanged from r1 (PE2 verified both at
HEAD and re-ran all three legs bit-identically). Verdict in §7.4(C).**

**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against JB-PE1 (hostile pass, fresh context, read-only, fixes nothing;
report `GRTJB_passPE1_report.md`, commit 85a8dc9: **1 CRITICAL + 9
JUSTIFICATION GAPS, VERDICT NOT CLEAN**; ledger entry
`BRIDGE_ADJUDICATIONS_2026-07-30.md`, "LIFT r1 REPAIRED-WITH-PROOF … + JB-PE1
fresh verdict"). PE1's machine leg reproduced BIT-IDENTICALLY (exit 0, 18/18
families GREEN, 6,700 samples, 0 violations, every census verbatim; the
regenerated JSON differs from the sealed artifact in the `elapsed_s` field
alone) and all four charged re-derivations SURVIVED — LEMMA JB-EPS line by
line, THEOREM JB-CREAD's five-line chain including the VERBATIM ε′ match
against [RMG] (C-READ), the JB-VTX shear as DERIVED (not asserted, slope law
included), LEMMA JB-AFF. **No §2–§5 identity moved in this round.** What
moved is the note's GRADE SURFACE (F1) and its machine-evidence wording
(G-1..G-9). Dispositions, each edit carrying a dated `[r1, F1]` / `[r1, G-#]`
bracket and SUPERSEDED IN PLACE (the r0 text is quoted as struck, then
replaced — nothing is silently rewritten):

* **F1 (CRITICAL — grade surface; 4 sites + 1 census sentence).** The r0 text
  claimed (VD-m) "unconditional for m ≤ 2 (m = 2 by JA-RES)". That CONFLATES
  J-A's PER-SLOT law JA-RES (c_i = z_{m−1}^{−i·A_{m−1}}·C_i, genuinely
  unconditional at m = 2) with the EVALUATED dictionary (VD-m), which J-A
  supplies only through COROLLARY JA-VDIND's ABSOLUTE character-triviality
  hypothesis (z_{m−1}^{i·A_{m−1}} = 1 at every attained abscissa). RE-FENCED
  at all four sites (§5 theorem parenthetical, the grade cap below, §7.2's
  JB-CREAD row, JB-BOX-2) to: **(VD-m) unconditional at m ≤ 1 only
  ((VD-1) = W2-L3); at every m ≥ 2 conditional — JA-VDIND's collapse
  condition, ⊇ (R-coll)/per-digit at m ≥ 3 (JA-BOX-2)**; and §7.1's census
  sentence is re-attributed from "the JA-BOX-2/(VD-m)-proviso geography (the
  m ≥ 3 box)" to the true level split. **JB-CREAD has NO unconditional
  stratum above m = 1.** The refutation is the note's OWN sealed runner, and
  r1 re-verified it independently of PE1 (`grt_jb_r1_levelcensus.py`,
  replicating `jb_cread`'s control flow level-by-level over the 16-tower
  roster): the 13 roster boundary rows are **m = 1: 0 · m = 2: 10 (T3A 3,
  T3B 3, T3C 1, T3D 3) · m = 3: 3 (I4B)**, ZERO of them an evaluator
  scope-out (all 13 are machine-evaluated FALSE instances of (VD-m)), against
  56 roster scored rows (m = 1: 45, m = 2: 8, m = 3: 3); the committed sealed
  JSON pins the same totals from the other side (roster boundary 13 +
  chamber 8 = 21 = the `JB-CREAD-BOUNDARY` census field). So ten of the
  thirteen sit INSIDE the stratum the r0 text called unconditional.
* **G-1 (tree evidence).** The r0 text advertised the tree identity "harness
  AND print keys"; the sealed runner's print-key leg fires only under
  `byteeq`, i.e. it re-executes ONE pure `fresh_divmod` on EQUAL arguments —
  no independent print-key reading, and none at all off the byte-equal set.
  Wording corrected everywhere (§4 machine bracket, §4 grade line, §7.1
  table) to what the runner establishes, AND the missing evidence was
  supplied post-seal by `grt_jb_printwalk.py` (§7.4): a walker whose keys,
  correction digits, multiplicand and divisor are all print-side and which
  never calls the sealed runner's `fresh_divmod`. **[r2, G2-2 — true of LEG A
  (84 walks), which is what closes G-1's substance on the base rows. Its LEG B
  (the cross-frame family PW-XFRAME) is 45 cross-frame walks + 27 walks that
  re-execute PW-DIV on byte-identical arguments — the same disease, disclosed
  in §7.4 and repaired by leg (C).]**
* **G-2** "22 scored samples … across 7 towers" → 22 samples across **14
  towers / 21 teeth-positive JSON rows** ("7" was the runner docstring's
  smoke-probe designation list, i.e. the 7 teeth-positive CHAMBER rows).
* **G-3** "q = 1 byte-equal on all 25 rows" → **22 rows**, the other 3
  VACUOUS (T.n = 0 ⇒ empty census ⇒ TH-BASE unexercised).
* **G-4** JB-VTX clause (e) restated with its true subject Φ_{q+1}^har (as
  literally read with the theorem's quantified f its first half is FALSE).
* **G-5** JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso — consumed at §2(iii)(GRID),
  carried by no box in r0 — is now named in JB-BOX-2 ~~with its discharge
  argument~~ **[r2, G2-5 — the "discharge argument" is RETRACTED: it was an
  assertion, not a derivation. The proviso is CARRIED, DISCHARGE OWED; see the
  r2 block and JB-BOX-2]**.
* **G-6** "reproduces the probe's F1 pattern row-for-row" → exact agreement
  on the **12 junctions both instruments walk**; the 16 roster top junctions
  (carrying 12 of the probe's 18 F1 REDs) are outside JB-KEYEQ's q ≤ n range.
* **G-7** notation: m_{q+1}^GMN defined in-note at first use; (B-READ)
  resolved to its [RMG] source at the load-bearing step; the s_m(·) overload
  declared and split into s_m^wt(·) / s_m^ini(·).
* **G-8** the T-F figures 41,720 / 7,472 are re-attributed to their true
  instrument (the O1thr rev-3 runner, cited BY GD-2/GD-3), and an erratum
  line records that seal commit 7f6759d's message says "note + runner" while
  that commit contains the runner only (the message is immutable; the seal
  property itself HOLDS — predictions on record at 5a72b62, runner
  byte-frozen seal→verdict, no §1–§6 movement between them).
* **G-9** JB-VTX's and JB-DEV(iii)'s quantifiers are restated to the
  runner's own shared-key perimeter `qcap_of(T,G) = min(T.n,
  shared_upto(T,G)+1)`, which is what clause (a)'s JA-VAL consumption
  actually needs.

Acceptance counter unchanged at **0/2** — a repair round is not a pass. State
after this round: attempt grade, ONE hostile pass run (JB-PE1) with findings,
r1 applied; ~~round r2 (a fresh hostile pass on THIS text) is the next
acceptance attempt~~ **[r2 — nomenclature corrected: the fresh hostile pass on
the post-r1 text was JB-PE2 (0 CRITICAL + 7 gaps); "r2" is the REPAIR ROUND
applied against it, below; the next acceptance attempt is JB-PE3]**.]**

**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against **JB-PE2** (hostile pass, fresh context, read-only, fixes nothing;
report `GRTJB_passPE2_report.md`, committed by that pass: **0 CRITICAL + 7
JUSTIFICATION GAPS, VERDICT NOT CLEAN, PE1's F1 CONFIRMED CURED**; ledger
entry `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "LIFT r2 LANDED … + JB PE2").
PE2 re-ran ALL THREE machine legs (sealed runner, level census, print walker)
and reproduced every one **BIT-IDENTICALLY** — the sealed
`grt_jb_checks_results.json` regenerated with a zero diff including
`elapsed_s`, all three md5 seals intact at HEAD — and it re-derived the F1
level split **13 = 0/10/3, 56 = 45/8/3 from the committed sealed JSON alone**,
without calling `vd_eval`: F1's factual core now has a decorrelated leg.
**No §2–§5 identity moves in this round either.** What moves is again the
GRADE SURFACE (G2-1), one machine-evidence disclosure (G2-2/G2-3), one
retraction (G2-5), one definition (G2-6), one refuted explanation (G2-4) and
two record figures (G2-7). Dispositions, each edit carrying a dated
`[r2, G2-#]` bracket and SUPERSEDED IN PLACE (the r0/r1 text is quoted as
struck, then replaced — nothing is silently rewritten):

* **G2-1 (grade surface — the recurring disease).** r1's `qcap` re-fence (G-9)
  reached five BODY surfaces and neither of the two SURFACES A DOWNSTREAM UNIT
  ACTUALLY READS. Carried in r2 to: §7.2's **JB-VTX row** (was "at the W2-C1
  representative" with no perimeter) and **JB-DEV row** (was bare), §7.3's
  **"W-3 in full"** and **"W-5 in full"** (both scoped: full in CONTENT, not
  full in q), and — found by the mandated re-grep of every grade line in the
  note — three more. **RE-GREP RESULT: 8 grade-surface hits inconsistent with
  the r1/r2 body fences, all 8 fixed**:

    1. §2 ∎ Grade line   — graded JB-DEV without separating clause (iii)
    2. §7.2 JB-DEV row   — bare "consumptions at their own grades"
    3. §7.2 JB-VTX row   — "at the W2-C1 representative", no qcap
    4. §7.3 "W-3 in full"— pre-G-9 perimeter restored by omission
    5. §7.3 "W-5 in full"— (VD-m) perimeter not carried into the display
    6. §3 ∎ Grade line   — clause (d) consumes JA-GRID, so it rides the
                           u ≥ 0 proviso; the line did not say so (r2, G2-5)
    7. §4 ∎ Grade line   — clauses (iii)/(iv) consume JA-VAL, hence hold at
                           levels m ≤ qcap; r1 fenced §2/§3 and left §4 bare
    8. §7.2 JB-TREE row  — the same §4 fence at the claims-table surface

  Hits 6–8 were NOT in PE2's list: they are the same disease found by the
  mandated sweep, and all three corrections MOVE IN THE DIRECTION OF MORE
  CONDITIONALITY (no statement is widened anywhere in r2). ~~The grade cap, the
  §5 grade line and JB-BOX-2 were already consistent and are untouched except
  for the G2-5 proviso.~~ **[r3, F-1B — THE STRUCK SENTENCE WAS FALSE WHEN
  WRITTEN, and it is the round's honesty defect, not a mere omission. The grade
  cap and JB-BOX-2 were consistent only BEFORE hit 7; hit 7 created the
  inconsistency in this same round by fencing JB-TREE(iii)/(iv) at m ≤ qcap
  while the grade cap graded JB-TREE with no perimeter and JB-BOX-2's
  enumeration omitted JB-TREE entirely — and this sentence then certified the
  absence of exactly that inconsistency. Correct record: r2's sweep found 8
  hits and fixed 8 hits, but it did NOT close the surface set — it left the
  u ≥ 0 proviso off §7.2's JB-VTX row and §7.3's polygon half (PE3 F-1) and its
  own new fence off the grade cap and JB-BOX-2 (PE3 F-1B). "All 8 fixed" is a
  count of hits found, not of surfaces made consistent. r3 replaces the sweep
  genre altogether: §0M's matrix is the single record, and all 14 grade
  surfaces are REGENERATED from it rather than patched.]**
* **G2-2 (MANDATORY DISCLOSURE — the repair instrument reproduced the disease
  it was written to repair).** `grt_jb_printwalk.py`'s cross-frame family
  PW-XFRAME is gated on `chain_eq` alone, and `chain_eq` already forces the
  leg-B divisor to be byte-equal to the print key; on the sub-family that also
  has `chat_eq` the leg-B call is byte-identical to leg A's PW-DIV call, so
  **27 of the 72 PW-XFRAME walks (9 rows) are re-executions of PW-DIV** and
  carry no cross-frame content. Disclosed in §7.4 with the 9 rows listed and
  the mechanism displayed: **the cross-frame evidence rests on the 45
  non-degenerate walks; the 27 are VACUOUS for cross-frame purposes.** The
  print walker is under its own mini-seal and was NOT edited (md5
  `f53e23e8d1c79f084a1e34eee857e37c`, unchanged). The corrected leg is a NEW
  script, `verification/openmath/grt_jb_printwalk2.py`, with its own mini
  two-commit seal (sealed UNRUN at r2 commit 1 `67bf0c4`): it re-gates on
  `chain_eq` ∧ ¬`chat_eq`, certifies the degeneracy of the complement instead
  of re-running it, and reconciles row-for-row against the r1 JSON. **RESULT
  (§7.4(C)): ALL THREE FAMILIES GREEN, every sample count on its prediction —
  PW2-XFRAME 45/45 agreed with a non-degeneracy certificate per sample,
  PW2-DEGEN 27 certified vacuous, PW2-RECON 28 rows reconciled with NO
  disagreement anywhere.** Its own disclosed limitation: it imports the frozen
  r1 walker's machinery on purpose (gate repair, not decorrelation).
* **G2-3 (coverage over-claim).** §7.4's boldface verdict said "including on
  every junction the sealed battery left unchecked". FALSE: the sealed `tree`
  block has **eight** `byteeq: false` rows, not four — four base rows (reached,
  12 walks) and four CHAMBER rows `T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at
  m = 2 (2 walks each, **8 walks UNREACHED**, since the walker builds no
  chambers). Restated to the script's own honest wording ("off the byte-equal
  set") with the unreached set enumerated.
* **G2-4 (mechanism claim refuted by the note's own roster).** Both r1
  characterisations of the (VD-2) failure geography are STRICKEN, not replaced:
  "the e₀ ≥ 2 character-visible towers" (T3E has e₀ = 2 and scores 6/6) and
  "exactly where A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses" (T3D and T3E share
  the level-0 read (e₀,h₀,g₀) = (2,1,2) and the same ψ₀, hence the same A_1 and
  the same z₁ of order 3, and still split). **The mechanism of the m = 2 split
  is NOT IDENTIFIED.** The roster is displayed as DATA in §7.1 with the one
  surviving implication (e₀ = 1 ⇒ A_1 = 0 ⇒ (VD-2) holds, so e₀ ≥ 2 is
  necessary and not sufficient) and an explicit ban on predicting from it. Also
  fixed at the two other sites carrying the same gloss (§2(iii)'s F1 fence,
  JB-BOX-2). NOTE for the record: this gloss entered the note from JB-PE1's own
  §1.3 remark — a verifier's unforced explanatory claim; r2 treats no verifier
  as a source.
* **G2-5 (an asserted discharge, RETRACTED).** r1 claimed to discharge
  JA-GRID(a)'s `[JA-r1]` proviso u := (V − s·h)/e ≥ 0 by "V is a level-m weight
  of a nonzero polynomial in the window, so V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})".
  No derivation was given and the implication is not plausible as stated (this
  note's quantifiers admit units, whose level-m weight is 0, while the bound is
  positive at r ≥ 2); the `s_geo` remark certifies the s-value, not the sign of
  u. **The discharge is retracted at both sites (§2(iii), JB-BOX-2); the
  proviso is CARRIED as an explicit inherited hypothesis of §2(iii)(GRID) and
  everything consuming it, with the exact requirement for a real discharge
  written out** (derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}), ~~equivalently~~
  **[r3, F-6(a) — "equivalently" is WRONG here and the correction matters for
  what a discharge must prove: J-A presents V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) as a
  SUFFICIENT print-side bound ("the proviso holds at every consumption site BY
  the print's own hypothesis"), while the genuine equivalence is
  u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}. Read: **or directly**]**
  V ≥ s_m^wt(V)·h_{m−1}, on the whole quantified window, units included).
* **G2-6 (the perimeter, stated ONE way).** §1's definition ("for all j ≤ q")
  and the r1 restatements that cite it ("keys shared strictly below q") differ
  by exactly the level q = qcap, which is the level the `+1` exists for. §1 now
  defines TWO conditions under separate names — the **byte-equal chain THROUGH
  q** (what JB-DEV(ii)'s byte clause means) and the **shared-key perimeter**
  = the runner's own `qcap_of(T,G) = min(T.n, shared_upto(T,G)+1)` with
  `range(0, qcap+1)`, i.e. keys shared strictly below q, level range
  0 ≤ q ≤ qcap, nothing required at j = q. Every r1/r2 citation now names the
  second one and reads identically.
* **G2-7 (record figures).** "scored 104 (66 roster + 38 chamber)" and the r1
  bracket's "56 roster rows" named the same census with the same word: the
  decomposition **non-chamber 66 = 16-tower roster 56 + QO leg 2 + d₀ leg 8**
  is now displayed where both numbers appear. The walker's "458 samples" is
  split into **362 law samples + 96 coverage-counter increments** at the
  verdict line.

**PE2 findings NOT requiring an edit** (recorded so the next pass can see the
whole disposition): PE2's §4 "checked and clean" list is accepted as read; its
one wording note (L274 "nothing above m = 1 is unconditional", which out of its
(VD-m) bracket would contradict JB-EPS's own unconditional grade) is fixed
anyway as `[r2, hygiene]`; its observation that `small=True` changes the sealed
QO/d₀ pool CONTENT as well as its size (so the walker's 5 extra walks are not a
strict superset) is recorded here rather than in §7.4, since the counts the
note quotes are unaffected and the "walk-for-walk" gloss is already restricted
to the roster rows.

Acceptance counter unchanged at **0/2** — a repair round is not a pass. State
after this round: attempt grade, TWO hostile passes run (JB-PE1 1C+9G, JB-PE2
0C+7G), r1 and r2 applied, no gate fired, nothing consumed at proof grade;
**JB-PE3 — a fresh hostile pass on this post-r2 text — is the next acceptance
attempt.**]**

**[REPAIR ROUND r3 — 2026-08-08 campaign (wallclock 2026-08-05). THE
CONDITIONALITY-MATRIX NORMALIZATION.** Applied against **JB-PE3** (hostile
pass, fresh context, read-only, fixes nothing; report
`GRTJB_passPE3_report.md`, commit 2fd271e: **0 CRITICAL + 8 JUSTIFICATION
GAPS, VERDICT NOT CLEAN** — the FIRST acceptance attempt, which did not land;
ledger entry `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "LIFT r3 LANDED … + JB PE3:
0C/8G — the fence-propagation disease named"). PE3 re-ran ALL FOUR machine
instruments and reproduced every one BIT-IDENTICALLY with all four md5 seals
intact at HEAD, re-derived JB-VTX(a) in full from the print source (including
the `propertiesv` item-3 half and the index shift), re-derived JB-ID, matched
ε′ VERBATIM against [RMG] S0.2 a second time, confirmed G2-4's refutation from
the committed roster with a STRONGER witness (T3D/T3E share ψ₀, A_1 = 2 and
ord(z₁) = 3 and still split), recounted every figure decomposition exactly, and
audited walker2's code as correct with its limitation honoured everywhere.
**No §2–§5 identity moves in this round either; r3 is NOTE-ONLY and all four
scripts plus every artifact are byte-frozen.** What moves is the GRADE-SURFACE
GENERATION MECHANISM, one citation license, two evidence classifications and
three small record defects.

**The diagnosis r3 acts on (orchestrator, ledgered): per-site patching does not
converge.** PE1/G-9, PE2/G2-1, PE3/F-1 and PE3/F-1B are one defect found four
times — and F-1/F-1B were introduced or missed BY r2's own mandated re-grep,
which certified the grade cap and JB-BOX-2 "already consistent" in the same
round its hit 7 made them inconsistent. r3 therefore does not patch sites:

* **STEP 1 — §0M, THE CONDITIONALITY MATRIX (new section, before the grade
  cap).** 28 claim rows × 8 proviso columns, every cell filled from the body
  proof: the shared-key perimeter in its TWO named variants (`P<q` for JA-VAL
  consumers, `P≤q` = through-q for JA-RES consumers and JB-DEV(ii)), the
  `[JA-r1]` u ≥ 0 proviso, the (VD-m) level fence, the W2-C1 representative
  restriction, the [RMG] recital, the machine-evidence class
  (IND/SAME/NONE) and the other scope fences. Five cell notes carry the
  sentences that do not fit a cell.
* **STEP 2 — EVERY GRADE SURFACE REGENERATED FROM THE MATRIX**, wholesale, not
  patched: the grade cap (surface 1), the four ∎ Grade lines (§2/§3/§4/§5 =
  surfaces 2–5), the seven §7.2 rows (surfaces 6–12), §7.3's consequence
  display (surface 13) and JB-BOX-2's perimeter enumeration (surface 14). Each
  superseded surface is retained in place, marked SUPERSEDED (struck with `~~`
  where it carries no nested r1/r2 strike markup, and quoted as a retained
  block where it does — `~~` cannot nest). **This kills F-1, F-1B and the
  recurrence class: there is now exactly one place to audit.**
* **STEP 3 — F-5, the citation license.** §5's recital, labelled "the (RM-m)
  box verbatim", had dropped two of [RMG]'s Ĉ_m clauses. Both are restored
  VERBATIM from `RMENGINE_2026-08-08.md` S0.2 (the display is quoted and cited
  at §5), and the one-line derivation licensing LEMMA JB-EPS at
  (V, V′) = (λ, γ_{m+1}) is displayed there.
* **STEP 4 — the evidence reclassifications and the small defects.**
  **F-2:** JB-DEV's "compared against both engines' digit lists" is
  RECLASSIFIED as SAME-COMPUTATION (one `PolyO.dev` on one ring object behind a
  guard that already forced agreement — the violation is unreachable) and the
  wording is corrected at every site (§2's machine bracket, §7.1's JB-DEV row,
  §7.2's JB-DEV row); what remains, and is stated, is one genuine second
  implementation (`fresh_dev` vs `PolyO.dev`) plus one genuine cross-engine tie
  (`G.vgen(q+1,A) == T.wlev(q,A)`). **F-3:** "all four min/read ties" →
  **three keyed**; the fourth (attained abscissas = the read grid) is named
  MACHINE-UNKEYED at both surfaces, with the coincidence disclosed that it is
  also the sub-clause riding the undischarged u ≥ 0 proviso. **F-6:**
  "equivalently" → "or directly" at the two sites that conflated J-A's
  SUFFICIENT print bound with u ≥ 0, and §7.4(C)'s "machine-established rather
  than argued" is softened by the purity step. **F-7:** P_i := e_i·g_i is
  defined at first use in §4, with [RMG] S0.1 added to the consumption list.

**F-4's disposition, stated separately because it is the one MATHEMATICAL
movement in r3** (in the direction of MORE conditionality, as every r3 change
is): §2(iii)'s (RES) layer is RE-FENCED from `P<q` to `P≤q` (the BYTE-EQUAL
CHAIN THROUGH q), because JA-RES at read level m = q+1 needs J-A's perimeter at
m, i.e. agreement through j = q. The alternative repair — arguing that the
representative pin φ_{q+1} := Φ_q^har discharges J-A's j = q requirement — is
NOT taken: it is not derived anywhere in this note, and adopting it would also
weaken what (VAL)'s fence is doing. §1's r2 sentence claiming that only
JB-DEV(ii) cites the through-q condition is corrected in place. Nothing inside
§3–§5 consumes (RES), so no downstream statement of this note moves.

Acceptance counter unchanged at **0/2** — a repair round is not a pass. State
after this round: attempt grade, THREE hostile passes run (JB-PE1 1C+9G,
JB-PE2 0C+7G, JB-PE3 0C+8G), r1/r2/r3 applied, no gate fired, nothing consumed
at proof grade; **JB-PE4 — a fresh hostile pass on this post-r3 text — is the
next acceptance attempt.**]**

---

## §1. Setting, indexing, and the two frames (fixed once)

Harness and P-index dictionary VERBATIM from J-A §1 (itself from W-2
§1.1–1.2): [ILN]† S0.1 class pin; GMN level i = harness read i−1; GMN keys
φ_i = harness Φ_{i−1}; v_i = w_{i−1} (THEOREM JA-VAL, consumed); GMN
order-q residual R_q pairs with the harness level-q read R_q v; pins
(P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the probe. ~~**Shared-key
perimeter at level q**: Φ_j^har = φ_{j+1}^cls byte-for-byte for all j ≤ q.~~
**[r2, G2-6 — TWO DISTINCT CONDITIONS, defined once, named apart. The struck
line conflated them and was cited (at §2(iii) and at the JB-VTX theorem) for
the other one; the two differ by exactly the level q itself, which is the
level the `+1` in `qcap` exists for. Both names below are used verbatim from
here on.**

    BYTE-EQUAL CHAIN THROUGH q :  Φ_j^har = φ_{j+1}^cls byte-for-byte for
        every j ≤ q — the condition of the W-2 §3.4(3) byte law, consumed by
        JB-DEV(ii) (it is what makes Φ_q^har the classifier's OWN key at
        level q). This is the struck line's content, retained under its own
        name.

    SHARED-KEY PERIMETER (the runner's own `qcap_of`) :  keys shared STRICTLY
        BELOW q, i.e. Φ_j^har = φ_{j+1}^cls byte-for-byte for every
        1 ≤ j ≤ q−1 — NOTHING is required at j = q. Equivalently, with
        shared_upto := max{L ≥ 0 : Φ_j^har = φ_{j+1}^cls for all 1 ≤ j ≤ L}
        and qcap := min(n, shared_upto + 1), the perimeter is the LEVEL RANGE

            0 ≤ q ≤ qcap ,      qcap = min(n, shared_upto + 1),

        which is exactly `qcap_of(T, G) = min(T.n, GJA.shared_upto(T,G) + 1)`
        with the runner's loops `for q in range(0, qcap_of(T,G) + 1)`. The top
        level q = qcap = shared_upto + 1 IS in scope, and at it the keys need
        NOT agree at j = q — the perimeter is a condition below q, never at q.

~~**Every r1/r2 restatement (§2(iii), the JB-VTX theorem and grade line,
JB-BOX-2, §7.2, §7.3) now cites the SHARED-KEY PERIMETER in this second sense,
`j < q`, 0 ≤ q ≤ qcap, and no statement cites §1 for the through-q condition
except JB-DEV(ii)'s byte clause, which means the first.**~~
**[r3, F-4 — THE STRUCK SENTENCE IS FALSE IN ITS SECOND HALF, and the error is
a level slip, not a wording slip. J-A's perimeter is LEVEL-INDEXED ("Shared-key
perimeter at level m: Φ_q^har = φ_{q+1}^cls byte-for-byte for all q ≤ m−1"), so
instantiating it at each layer's OWN level gives TWO different conditions
inside §2(iii): (VAL) is JA-VAL at level q and needs j ≤ q−1 = the SHARED-KEY
PERIMETER `P<q`; (RES) is JA-RES at read level m = q+1 and needs j ≤ m−1 = q,
i.e. the BYTE-EQUAL CHAIN THROUGH q. So there are exactly TWO consumers of the
through-q condition, not one: JB-DEV(ii)'s byte clause AND JB-DEV(iii)'s (RES)
layer. CORRECTED STATEMENT, which §0M's matrix column (a2) now carries as the
single record: every restatement of the (VAL)/(GRID) layers and of all of
JB-VTX and JB-TREE(iii)/(iv) cites the SHARED-KEY PERIMETER `P<q`
(0 ≤ q ≤ qcap); the (RES) layer and JB-DEV(ii)'s byte clause cite the
BYTE-EQUAL CHAIN THROUGH q. The two differ exactly at the top level
q = qcap = shared_upto+1 — the level the `+1` exists for — where `P<q` holds
and `P≤q` fails by definition of shared_upto, so at that one level per tower
r2's single fence over-supplied (RES) by exactly one level. No machine leg can
catch this: the runner keys (VAL) over `range(0, qcap+1)` and keys (RES)
NOWHERE (§0M row 5, cell note ⟨n4⟩).]**]**
Read data A_m := ℓ_{m−1}g_{m−1}γ_m, W_m := w_mΦ_m as in W-2/J-A.

**The two frames.** Fix a level q (0 ≤ q ≤ n) and nonzero f ∈ O[x] with
Φ_q-development f = Σ_i A_i·Φ_q^i (iterated division by the monic Φ_q).

    PRINT FRAME    U(f) := { (i, u_i) : A_i ≠ 0 },
                   u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})
                   — the print's own N_{q+1}-ordinates (tex ~1370).

    SHEARED FRAME  H(f) := { (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }
                   — the harness eq-(12) ordinates (the S0.2 weight
                   recursion's arguments; the GD-2 frame normalization).

    THE SHEAR      Σ_q : (i, u) ↦ (i, e_q·u + h_q·i).

The names are load-bearing: ~~GD-2's T-F machine check (41,720 instances)~~
**[r1, G-8 — instrument re-attributed]** the T-F machine check of the O1thr
rev-3 runner (`O1thr_phaseB_verifybrief_rev3.md` §9, family T-F: 41,720
site-instances, 0 violations of WGEO/(M6c); the runner is CITED BY GD-2/GD-3,
it is not GD-2's own instrument) verified the polygon tie in the SHEARED frame
and measured 7,472 violations of the unsheared identification — every polygon
statement below displays which frame it lives in, and the shear itself is a
theorem clause (§3(a)), never a silent convention. (Both figures were
re-checked against that source in JB-PE1 and are current, not stale.)

---

## §2. THEOREM JB-DEV (the expansion identity = blueprint J-B(i) first half; W-3)

**THEOREM JB-DEV.** Level q ≥ 0, f ∈ O[x] nonzero, notation §1.

**[r1, G-7 — notation, defined here at first use.]** m_{q+1}^GMN := the GMN
print's KEY DEGREE at level q+1, i.e. deg φ_{q+1} = d₀·∏_{j<q} e_j g_j
(the print's own recursion: deg φ_1 = d₀ = deg Φ_0^har and
deg φ_{r+1} = e_r f_r · deg φ_r with (e_r, f_r) the print's level-r
ramification/residual pair = the harness (e_{r−1}, g_{r−1})). The identity
deg Φ_q^har = m_{q+1}^GMN is a consequence of the P-index dictionary of §1,
not an extra hypothesis. (The symbol was used undefined in r0.)

**(i) [same division].** Φ_q^har is monic of degree m_{q+1}^GMN, and the
print's φ_{q+1}-adic development of f AT THE REPRESENTATIVE
φ_{q+1} := Φ_q^har is the harness Φ_q-development digit-for-digit: both
are THE canonical division chain by the same monic polynomial (uniqueness
of division with remainder). Under W-2 clause 1, Φ_q^har is a GMN Def-2.12
admissible representative on W-2's perimeter (of the ξ-conjugate class at
the pinned (P-ell) convention; of the type itself when the character is
support-trivial; STRICT at every level of the transported chamber, W2-C3)
— so the left side is a legitimate print development, not a harness-only
object.

**(ii) [byte clause].** If the junction chain is byte-equal through q (the
W-2 §3.4(3) byte law from read data; TH-BASE gives it always at q = 1),
then φ_{q+1}^cls = Φ_q^har byte-for-byte and (i) is the classifier's OWN
expansion at its own construct key. On the weld roster the byte-equal set
is the probe's F1 verdict pattern (12 GREEN / 18 RED of 30 walked
junctions, reproduced by W-2's CK-BYTE from read data alone — consumed).

**(iii) [coefficient correspondence, three layers].** **[r1, G-9 —
quantifier restated to the perimeter the proofs need.]** This clause is
asserted ONLY on the SHARED-KEY PERIMETER of §1: levels q with
Φ_j^har = φ_{j+1}^cls byte-for-byte for all j < q, i.e. q ≤ qcap :=
min(n, shared_upto + 1) — the runner's own `qcap_of(T, G)` quantifier. Off
that perimeter the print frame is computed with keys that differ from
Φ_0..Φ_{q−1}, and (VAL) is then FALSE, not merely unproved (J-A grades JA-VAL
"PROVED unconditionally ON THE SHARED-KEY PERIMETER"). r0 inherited the
theorem's blanket "level q ≥ 0" here; the machine evidence always quantified
the narrower statement. **[r3, F-4 — ONE PERIMETER IS NOT ENOUGH FOR THREE
LAYERS. The sentence above is correct for (VAL) and (GRID), which are JA-VAL /
JA-GRID at level q. It is ONE LEVEL SHORT for (RES), which is JA-RES at read
level m := q+1: J-A's perimeter is level-indexed, so at level m it requires
Φ_j^har = φ_{j+1}^cls for all j ≤ m−1 = q — the BYTE-EQUAL CHAIN THROUGH q of
§1, not the shared-key perimeter. THE FENCE, PER LAYER (§0M rows 3/4/5): (VAL)
and (GRID) on `P<q` = the SHARED-KEY PERIMETER 0 ≤ q ≤ qcap; **(RES) on the
BYTE-EQUAL CHAIN THROUGH q (`P≤q`)**, which is strictly stronger and excludes
exactly the top level q = qcap. This moves toward MORE conditionality: r2's
single fence asserted (RES) at one level per tower beyond the hypothesis of the
theorem it cites. No machine leg is affected — the runner keys (RES)
nowhere.]** For the common digit list (A_i):

    (VAL)  w_q(A_i) = v_{q+1}(A_i) for every i           [JA-VAL, consumed]
    (GRID) the on-line attained abscissas lie on the print's T-side grid
           s + j·e_q, and the plain carry = the side-lattice crossing
           indicator                                  [JA-GRID/W2-L0, consumed]
    (RES)  at read level m := q+1 ≥ 2 the print residual coefficients obey
           the per-slot character-gauge law c_i = z_{m−1}^{−i·A_{m−1}}·C_i
           against the harness packed digits C_i — unconditional at m = 2,
           per-digit proviso at m ≥ 3            [JA-RES, consumed with
                                                  JA-BOX-1/BOX-2 verbatim]
           **[r3, F-4] — this layer alone is asserted on the BYTE-EQUAL CHAIN
           THROUGH q (`P≤q`, §1), i.e. J-A's perimeter at its own read level
           m = q+1; NOT on the shared-key perimeter `P<q` the two layers above
           it use. (RES) is also the ONE layer with no machine leg (§0M row 5).**

**[r1, F1 — the reading fence that r0 lacked, and that §5 got wrong.]**
(RES)'s "unconditional at m = 2" is a statement about JA-RES, the PER-SLOT
character-gauge law on residual coefficients. It does **NOT** transfer to the
EVALUATED dictionary (VD-m) of J-A §3.4 (the identity
z_m^{τ_m(A)}·R_m^cls(A)(z_m) = ε_m(β)·R_m v(A) between assembled read
values). The per-slot law implies (VD-m) only through COROLLARY JA-VDIND,
whose hypothesis is ABSOLUTE triviality of the slot character on the attained
abscissas (z_{m−1}^{i·A_{m−1}} = 1 for every attained i; sufficient:
A_{m−1} = 0, i.e. e_{m−2} = 1, or ord(z_{m−1}) | A_{m−1} plus the abscissa
condition — single-slot support alone is NOT sufficient). At m = 2 that is
z_1^{i·A_1} = 1 with A_1 = ℓ₀g₀γ₁, ~~which FAILS on towers with e₀ ≥ 2 and a
nontrivial z₁ — and the sealed runner exhibits ten such in-roster failures
(§7.1, §7.4)~~ **[r2, G2-4 — the struck clause asserted a failure SET and the
note's own roster refutes it (T3E has e₀ = 2 with a nontrivial z₁ and scores
6/6). What is actually available here is ONE implication, in one direction:
e₀ = 1 ⇒ A_1 = 0 ⇒ z_1^{i·A_1} = 1 at every abscissa ⇒ (VD-2) holds (J-A's own
displayed sufficient condition, consumed). Its contrapositive is all the
geography this note may claim: an m = 2 failure REQUIRES e₀ ≥ 2, but e₀ ≥ 2
does NOT predict failure, and no condition in this note separates the failing
from the scoring e₀ ≥ 2 towers. The sealed runner exhibits ten m = 2 in-roster
failures (§7.1, §7.4) — the DATA, not a characterisation]**. Every
(VD-m)-consuming statement in this note is fenced accordingly; **[r2,
hygiene]** nothing (VD-m)-DEPENDENT above m = 1 is unconditional (this
sentence is about (VD-m) only — LEMMA JB-EPS is unconditional at every
m ≥ 1, as its own grade line says).

**[r1, G-5 — the (GRID) layer carries an inherited PROVISO.]** JA-GRID(a) is
graded in J-A with the `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 (the
bare V ∈ ℤ_{≥0} quantifier was FALSE at small V); that proviso is an inline
J-A repair, not one of JA-BOX-1..5, so JB-BOX-2's blanket "rides J-A's boxes
verbatim" did not carry it in r0. It is now named in JB-BOX-2 ~~with its
discharge: at every consumption site here the argument V is a level-m weight
of a nonzero polynomial in the tower's own window, so V ≥ e_{r−1}f_{r−1}
v_r(φ_{r−1}) — J-A's own hypothesis for u ≥ 0 — and the runner's `s_geo`
leg recomputes s from the geometry with no ℓ at all.~~ **[r2, G2-5 — THE
DISCHARGE IS RETRACTED. The struck text asserted an implication it never
proved ("V is a level-m weight of a nonzero polynomial in the window, SO
V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})"), and the implication is not plausible as
stated: this note's own quantifiers are "f ∈ O[x] nonzero" (§2) and
"deg f < deg Φ_m" (§4/§5), both of which admit UNITS, whose level-m weight is
0, while e_{r−1}f_{r−1}v_r(φ_{r−1}) is positive at r ≥ 2. J-A grounds that
bound in the PRINT's own hypothesis at the site where `construct` is invoked;
J-B has no such site hypothesis and supplied no substitute. The `s_geo` remark
was a red herring: `s_geo` recomputes s geometrically (ℓ-free), which
certifies the s-VALUE, not the sign of u. STATUS: the proviso is CARRIED, NOT
DISCHARGED — an explicit inherited hypothesis of §2(iii)(GRID) and of every
statement consuming it, listed in JB-BOX-2. What a real discharge requires:
derive V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) (or directly V ≥ s_m^wt(V)·h_{m−1},
which is what u ≥ 0 says) for EVERY V in the quantified window — units
included, i.e. either exclude V = 0 and the small positive weights from the
window or prove the bound at them. Two facts frame the residual: at V = 0 one
has s^wt = 0 and u = 0 ≥ 0, so no counterexample to the proviso is exhibited
by units; and J-A's own counterexample lives at small positive V
((e,h) = (2,3), V = 1 ⇒ u = −1), which nothing in this note excludes from the
level-m weight lattice. So the proviso may well hold at every site — this note
does not show it.]** (JB-EPS is unaffected:
it cites JA-GRID(c), which carries no proviso.)

**(iv) [cross-key fence, displayed not claimed].** For a DIFFERENT strict
representative φ′ of the same type, blanket digit equality and blanket
operator equality are FALSE (J-A §4(i): v_{r+1}(φ − φ′) = e_r·v_r(φ) —
the standard MacLane representative-dependence); the lawful transport
across representatives is W-2 clause 2's covariance (slot-ratio characters)
and clause 3's chamber re-instantiation, never a byte identity. This is
the JuncForge parity-wall lesson honored: J-B is stated against the
semantic development objects at a NAMED representative; no SideReads/
TreeModel transcription is consumed.

*Proof.* (i) Uniqueness of quotient and remainder in division by a monic
polynomial over any commutative ring: the print's development (tex
`phiradic` genre) and the harness development are the same recursion; the
representative legitimacy is W-2 clause 1 consumption. (ii) W-2 §3.4(3)
byte law + TH-BASE, consumed. (iii) consumption as displayed. (iv) cited.
∎ Grade: ~~PROVED at attempt grade with the displayed consumptions; no
clause here upgrades W-2/J-A.~~ ~~**[r2, G2-1 — the perimeter carried onto this
grade line, where r1 left it in the body only: clauses (i)/(ii)/(iv) are at
every level q ≥ 0 (with (ii) on the BYTE-EQUAL CHAIN THROUGH q, §1); clause
(iii) is asserted ONLY on the SHARED-KEY PERIMETER 0 ≤ q ≤ qcap (§1) — off it
(VAL) is FALSE, not merely unproved — and its (GRID) layer additionally
carries JA-GRID(a)'s undischarged u ≥ 0 proviso (r2, G2-5).]**~~

**[r3, STEP 2 — SURFACE 2 of 14, REGENERATED FROM §0M rows 1–6 (the struck
r2 line above is superseded; its only defect of substance was (iii)(RES)'s
perimeter). ∎ GRADE: PROVED at attempt grade with the displayed consumptions;
no clause here upgrades W-2/J-A. PER CLAUSE:**

    (i)         every level q ≥ 0; at the W2-C1 admissible representative
                φ_{q+1} := Φ_q^har.                              [row 1]
    (ii)        on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`, §1); TH-BASE gives
                q = 1 always.                                    [row 2]
    (iii)(VAL)  on the SHARED-KEY PERIMETER (`P<q`), 0 ≤ q ≤ qcap — off it
                (VAL) is FALSE, not merely unproved.             [row 3]
    (iii)(GRID) on `P<q` AND on JA-GRID(a)'s `[JA-r1]` u ≥ 0 proviso,
                CARRIED AND UNDISCHARGED (r2, G2-5).             [row 4]
    (iii)(RES)  on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — one level deeper
                than r2's fence, F-4 — plus JA-RES's own fence (unconditional
                at m = q+1 = 2, per-digit proviso at m ≥ 3, JA-BOX-2). NOT
                the evaluated dictionary (VD-m).                 [row 5]
    (iv)        a displayed fence, cited; no level condition.    [row 6]

**]** ~~[Machine: JB-DEV — the development recomputed
by this runner's OWN schoolbook division (fresh leg, decorrelated from the
shared PolyO.dev used by both engines) and compared against both engines'
digit lists at every shared level; JB-KEYEQ — byte-equality census tied to
the W-2 read-data byte law; teeth MJB-DEV.]~~

**[r3, F-2 — MACHINE BRACKET RESTATED to exactly what the code establishes;
the struck bracket's "both engines" is WITHDRAWN. [Machine, classified as in
§0M column (f): JB-DEV — TWO legs carry information. (1) ONE genuine second
implementation (IND, 893 samples): the development recomputed by this runner's
OWN schoolbook division `fresh_dev` against the engine's `PolyO.dev` on the
same key. (2) ONE genuine CROSS-ENGINE tie (IND): the (VAL) digit-weight
identity `G.vgen(q+1, A) == T.wlev(q, A)`, the print engine's valuation
recursion against the harness's, at every digit and every level 0 ≤ q ≤ qcap.
A THIRD leg carries NO information and is disclosed as such: `G.P.dev(f,
G.phi[q+1])` is the SAME `PolyO.dev` bound to the SAME ring object — `PolyO`
carries only `self.R`, and `gmn_from_tower(T)` builds `GmnLeg(T.R, …)` whose
`self.P = ITL.PolyO(R)` holds the tower's own ring — it is guarded by
`tuple(G.phi[q+1]) == key`, so its arguments are byte-equal, and it is reached
only after a `continue` on `dvF != dvI` has already forced agreement. The
violation `'fresh dev != print dev'` is therefore UNREACHABLE: SAME-COMPUTATION
(PE3 F-2 = PE1/G-1's disease at its third site). There is ONE engine comparison
in this family, not two. JB-KEYEQ — byte-equality census tied to the W-2
read-data byte law (25 rows; 3 VACUOUS, T.n = 0, r1/G-3); teeth MJB-DEV
(garbled key, 3/3 caught).]]**

---

## §3. THEOREM JB-VTX (the polygon identity = blueprint J-B(i) second half; W-3)

**LEMMA JB-AFF (two lines, displayed).** Let Σ : (i, u) ↦ (i, a·u + b·i + c)
with a > 0, b, c ∈ ℚ. Then Σ maps lower convex hulls to lower convex hulls
and vertices to vertices, bijectively, preserving abscissas. *Proof.* Σ is
affine and abscissa-preserving, so it maps segments to segments and
preserves "lies strictly below the chord": a·u + b·i + c < a·u′ + b·i + c
⟺ u < u′ at equal i, since a > 0. Hulls, faces, and strict-vertex
conditions are defined by these two relations. ∎

**THEOREM JB-VTX.** Level q with read (e_q, h_q) defined ~~(0 ≤ q ≤ n)~~
**[r1, G-9 — PERIMETER RESTATED AT THE THEOREM: 0 ≤ q ≤ qcap, where
qcap := min(n, shared_upto + 1) is the SHARED-KEY perimeter of §1 (keys
shared strictly below q), the runner's own `qcap_of(T,G)`. This is not
cosmetic: clause (a) consumes JA-VAL for the digits AND for the key
(v_{q+1}(φ_{q+1}) = w_qΦ_q), and J-A grades JA-VAL "PROVED unconditionally
on the shared-key perimeter"; off it the print frame U(f) is computed with
keys ≠ Φ_0..Φ_{q−1} and clause (a) is FALSE, not merely unproved. r0's grade
line named only W-2 clause 1, which does not carry this]**,
f ∈ O[x] nonzero, frames as §1, all statements at the representative
φ_{q+1} := Φ_q^har (legitimate by W-2 clause 1 on its perimeter; on
byte-equal chains this is the classifier's own key, JB-DEV(ii)).

**(a) [the shear is exact, pointwise].** H(f) = Σ_q(U(f)) with
Σ_q(i, u) = (i, e_q·u + h_q·i): indeed e_q·u_i + h_q·i =
e_q·v_{q+1}(A_i) + i·(e_q·v_{q+1}(φ_{q+1}) + h_q) = e_q·w_q(A_i) + i·γ_{q+1}
by JA-VAL and the weight recursion γ_{q+1} = e_q·w_qΦ_q + h_q (JA-PIN
clause 7). Moreover e_q·u_i + h_q·i = v_{q+2}(A_i·Φ_q^i) (propertiesv
item 3 at a single digit): THE SHEARED FRAME IS THE PRINT'S OWN NEXT-LEVEL
BOOKKEEPING — the harness ordinates are the v_{q+2}-values of the
monomials, the print ordinates their v_{q+1}-values.

**(b) [vertex-for-vertex].** By (a) and JB-AFF, the harness development
polygon (lower hull of H(f)) equals Σ_q(N_{q+1}(f)) vertex-for-vertex,
same abscissas; equivalently N_{q+1}(f) = Σ_q^{−1}(harness polygon). This
is GD-2's displayed clause with the shear EXPLICIT. The unsheared
identification (hull of {(i, w_q(A_i))} against N_{q+1}(f)) is FALSE in
general — the T-F 7,472-violation genre; teeth family MJB-VTX.

**(c) [slope/length translation].** A print side of slope σ over abscissas
[i₀, i₁] maps to a sheared side of slope e_q·σ + h_q over the same
[i₀, i₁]; lengths (abscissa runs) are preserved. In particular:
the REALIZED side σ = −h_q/e_q maps to slope 0 — the sheared frame is the
frame in which the read side is HORIZONTAL, at height
min_i(e_q·w_q(A_i) + i·γ_{q+1}) = w_{q+1}(f) — exactly the eq-(12)
presentation of the level-(q+1) read; a side of print slope −h/e in lowest
terms has its lattice data preserved: degree d = (abscissa run)/e is the
same integer in both frames (the print's d(S) = the harness grid count).
The print principal part N^−_{q+1} (σ < 0, tex 1377) corresponds to
sheared slopes < h_q; the weld's type-quantification consumes only the
principal sides (JA-PIN clause 2's Hensel/L1 dispatch, displayed there).

**(d) [min/read ties].** min ordinate of U(f) = v_{q+1}(f) (print Lemma
`shape` item 1, tex ~1395); min ordinate of H(f) = w_{q+1}(f) = v_{q+2}(f)
(the weight recursion + JA-VAL one level up); the attained abscissas on
the realized side are the read grid s(λ) + j·e_q, and the level-(q+1)
read is assembled exactly from the on-line digits at those slots (S0.2
consumed; JA-GRID). So the polygon identity carries the READ data — the
harness read of f and the print's side data (s_{q+1}(f), attained set,
side degree) are the same integers under Σ_q.

**(e) [window clause].** ~~Restricted to the junction window i ≤ e_q·g_q
(the lift comparison window), one-sidedness holds in both frames
simultaneously (Σ_q preserves sides)~~ **[r1, G-4 — SUBJECT CORRECTED. As
literally read with the theorem's quantified f the struck sentence is FALSE
(a general f's polygon restricted to i ≤ e_q g_q is not one-sided). The
clause's subject is the KEY, and it reads: APPLIED AT f = Φ_{q+1}^har (the
next-level lift, whose window development is the W2-C1a object), restricted
to the junction window i ≤ e_q·g_q, one-sidedness holds in both frames
simultaneously (Σ_q preserves sides, LEMMA JB-AFF)]**: this is W2-C1a's
polygon leg —
v-correct, one-sided, support {0, e_q g_q} ∪ attained grid slots — i.e.
the "window polygon" of the blueprint IS N_{q+1}(Φ_{q+1}^har) restricted
to its single side, vertex-for-vertex under Σ_q.

*Proof.* (a) displayed arithmetic + consumptions; (b) JB-AFF; (c)(d)
displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is
also re-verified by machine through the second development route — see
runner family JB-SHEAR); (e) W2-C1a consumed at f = Φ_{q+1}^har (r1, G-4).
~~∎ Grade: PROVED at attempt grade **[r1, G-9] on the shared-key perimeter
0 ≤ q ≤ qcap (stated at the theorem)**; unconditional GIVEN the
representative legitimacy (W-2 clause 1's perimeter and conditionality ride;
on byte-equal chains no W-2 input is needed beyond TH-BASE) **AND given the
shared-key perimeter for the JA-VAL consumption in (a)/(d). The machine
evidence quantifies exactly this: the runner runs the shear/vertex/slope
families over 0 ≤ q ≤ `qcap_of(T,G)` and restricts the PRINT-side min ties
of (d) further to q ≤ `shared_upto(T,G)`; the off-perimeter counter is 0 on
the roster, so nothing was silently scored outside the fence.** **[r2, G2-1
re-grep — one fence this line was missing: clause (d)'s read-grid/attained-
abscissa content consumes JA-GRID, so it also rides JA-GRID(a)'s UNDISCHARGED
`[JA-r1]` u ≥ 0 proviso (r2, G2-5; carried in JB-BOX-2). Clauses (a)/(b)/(c)
and the min ties themselves do not.]**~~

**[r3, STEP 2 — SURFACE 3 of 14, REGENERATED FROM §0M rows 7–13. ∎ GRADE:
PROVED at attempt grade on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap,
stated at the theorem), every statement at the W2-C1 admissible representative
φ_{q+1} := Φ_q^har — W-2 clause 1's perimeter and conditionality ride, and on
byte-equal chains no W-2 input is needed beyond TH-BASE. PER CLAUSE:**

    LEMMA JB-AFF  unconditional, two lines; its content is exercised inside
                  (b)/(c)'s machine legs.                        [row 7]
    (a)(b)(c)     `P<q` + W2-C1 only; off `P<q` clause (a)'s JA-VAL input is
                  unavailable and (a) is FALSE, not merely unproved.
                                                            [rows 8–10]
    (d1)(d2)(d3)  the THREE min ties: `P<q` + W2-C1; the runner restricts the
                  two PRINT-side ties further to q ≤ `shared_upto(T,G)`.
                                                                [row 11]
    (d4)          attained abscissas = the read grid s(λ) + j·e_q, and the
                  level-(q+1) read assembled from the on-line digits at those
                  slots: `P<q` + W2-C1, **AND JA-GRID(a)'s UNDISCHARGED
                  `[JA-r1]` u ≥ 0 proviso** (r2, G2-5; JB-BOX-2), **AND it has
                  NO MACHINE LEG** (r3, F-3).                   [row 12]
    (e)           at f = Φ_{q+1}^har, the W2-C1a window object — NOT at the
                  theorem's quantified f (r1, G-4); no machine leg claimed.
                                                                [row 13]

**The runner runs the shear/vertex/slope families over 0 ≤ q ≤ `qcap_of(T,G)`
and the off-perimeter counter is 0 on the roster, so nothing was silently
scored outside the fence.]** ~~[Machine: JB-VTX — fresh lower hulls of both
frames, vertex bijection, per-side slope/length translation; JB-SHEAR —
pointwise shear + all four min/read ties, with v_{q+1}(f) computed BOTH
as min u_i and by the vgen recursion through the φ_q-development (two
different developments, one value — Lemma shape item 1 machine-keyed);
teeth MJB-VTX on designated rows.]~~

**[r3, F-3 — MACHINE BRACKET RESTATED; "all four min/read ties" is WITHDRAWN.
[Machine, classified as in §0M column (f): JB-VTX — fresh lower hulls of BOTH
frames, vertex bijection, per-side slope/length translation (IND, 893).
JB-SHEAR — the pointwise shear plus **THREE** of clause (d)'s four ties, not
four: the code's assertions are `minH == T.wlev(q+1, f)` (d2) and, under
q ≤ shared_upto, `minU == G.vgen(q+1, f)` (d1) and `minH == G.vgen(q+2, f)`
(d3) — so v_{q+1}(f) IS computed both as min u_i and by the vgen recursion
through the φ_q-development (two different developments, one value; Lemma
`shape` item 1 machine-keyed). **THE FOURTH TIE (d4) HAS NO LEG IN ANY FAMILY
OF ANY INSTRUMENT:** `jb_dev` keys only the (VAL) weight tie, `jb_line` keys
line == wlev == vgen on reduced cells, `jb_cread` evaluates (VD-m), and
`jb_eps` keys JA-GRID's **carry** clause (c) — the other half of the (GRID)
layer, and the half that carries no proviso. **Disclosed coincidence:** (d4) is
also the only sub-clause of JB-VTX riding the undischarged u ≥ 0 proviso, so
the clause with the open inherited hypothesis is the clause with zero machine
evidence (§0M row 12; the same disclosure genre as r1/G-3's three VACUOUS
JB-KEYEQ rows). teeth MJB-VTX on designated rows (unsheared frame, 3/3
caught).]]**

---

## §4. THEOREM JB-TREE (the division-step correspondence = blueprint J-B(ii); W-5)

Setting: reduction level m (1 ≤ m ≤ n), [RMG] T-scope(m) (its termination
fence), g_m = 1, Ĉ_m := Φ_{m+1} − Φ_m^{e_m} (WELL-DEF g_m = 1 form,
consumed); f ∈ O[x] nonzero, deg f < deg Φ_m. The [RMG] S2.2 objects
(cells, (ID-(i+1)), the E1-priority tree, L-NORM splits, L-EXACT, L-CANON,
L-LINE) are consumed as ACCEPTED displays.

**THEOREM JB-TREE.** Under the J-A dictionary (and W-2 clause 1 for the
representative reading; clause 3's chamber off the byte perimeter):

**(i) [the tree computes the classifier's division].** The E1-priority
tree on the initial cells of f·Ĉ_m terminates (T-TERM, consumed) with
Σ R-leaves = R and Σ exit cofactors = Q for THE canonical division
f·Ĉ_m = R + Q·Φ_m (L-EXACT + L-CANON, consumed) — and by JB-DEV(i) at
level m this IS the classifier's division step at the admissible
representative (its own key on byte-equal chains): R = the 0-th digit and
Q = the once-divided cofactor of the print's φ_{m+1}-adic development
algorithm applied to f·Ĉ_m. One tree = one classifier division step,
executed inside the expansion arithmetic.

**(ii) [each edge = one classifier division step].** **[r3, F-7 — NOTATION,
DEFINED HERE AT FIRST USE (it was used undefined in r0–r2, and it is
load-bearing for the digit-list claim below).**

    P_i := e_i · g_i     — the level-(i+1) PERIOD: the abscissa at which the
                           key power Φ_i^{P_i} sits in the Φ_i-adic
                           development of Φ_{i+1}. Verbatim from [RMG] S0.1
                           ("P_l := e_lg_l (the level-(l+1) period)"), whose
                           scope is declared "local to this note" there and
                           which is therefore added to this note's [RMG]
                           consumption list in the header.

**The value is what the proof of (ii) turns on: every correction abscissa
e_i·k with k < g_i satisfies e_i·k < e_i·g_i = P_i, so the digit list below is
supported below the key power and the Φ_i-adic development reads off
uniquely. §7.4's PW-ID and PW-WALK rows use the same symbol (and P_l) in this
same sense.]** The identity
(ID-(i+1)): Φ_i^{P_i} = Φ_{i+1} − Σ_{k<g_i} C_k^{(i)}·Φ_i^{e_ik} IS the
statement that the φ_{i+1}-adic development of the KEY φ_{i+2} = Φ_{i+1}
has digit list {C_k^{(i)} at abscissa e_i·k (k < g_i), 1 at abscissa P_i}
(uniqueness of division; the C_k^{(i)} are reduced, REALIZE R1). So every
in-tree edge applies the classifier's own key-expansion relation exactly
once: a promotion edge carries one key power up one level (the division
algorithm's carry), a Φ_m-exit emits one quotient summand (a division
step's quotient write), and a correction edge substitutes the key's lower
development digits (the remainder write), L-NORM-split into its L/π-junk/
Φ₀Y-junk children. The tree is the classifier's division arithmetic made
cell-local; the blueprint's "each cell = a set of expansion slots" is
L-CELL: every node is a sum of reduced cells = multiadic expansion slots
(iterated JB-DEV at levels m−1, …, 0).

**(iii) [the polygon bookkeeping = LED-Λ's line face, one citation].**
On reduced cells, line(C) = w_m(C) ([RMG] L-LINE(iv)) = v_{m+1}(C)
(JA-VAL): THE LEDGER'S LINE FUNCTIONAL IS THE CLASSIFIER'S MacLANE
ORDINATE. Hence LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the
complete per-edge polygon bookkeeping of the division in classifier
coordinates: promotions raise v_{m+1} by exactly the quantum q_{i+1} > 0,
correction-main edges are v_{m+1}-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀
(Y), exits pay w_mΦ_m ([LED-Λ] S1 table, λ_E column; L-MONO = the
division never descends below the polygon — the print's
division-stability genre read through the dictionary). Where earlier
units re-derived these per edge, J-B cites the ledger ONCE; LED-Λ is
consumed at ATTEMPT grade and the tie's grade rides it.

**(iv) [(RM-m) as the transported instance].** On this scope the four
(RM-m) box clauses ([RMG] ACCEPTED) become classifier statements: (C-W_R)/
(C-W_Q) are polygon statements about the classifier's R and Q digits
(their v_{m+1}-values, via JA-VAL), and (C-READ) transports as §5. No
clause of [RMG] is re-proved or touched.

*Proof.* (i) consumption chain as displayed + JB-DEV(i). (ii) dev of
Φ_{i+1} by Φ_i: the right side of (ID-(i+1)) has every C_k^{(i)}Φ_i^{e_ik}
of degree < deg Φ_{i+1} with the C_k reduced (REALIZE R1), so the digit
list reads off; uniqueness of division. (iii) the two displayed equalities
+ LED-Λ citation. (iv) composition. ~~∎ Grade: PROVED at attempt grade on
the displayed scope. Scope fences: T-scope(m) (the [RMG] d₀ ≥ 2 flat
corners stay fenced — the weld inherits them, blueprint S5's cross-cutting
row); g_m = 1 for the Ĉ_m instance; W-WIN not consumed (window-free legs
only, as in [RMG]).~~ ~~**[r2, G2-1 re-grep — a fence r1 carried into §2/§3 and
left out of this grade line, although this section consumes the same input:
clauses (iii) and (iv) use JA-VAL (line(C) = w_m(C) = v_{m+1}(C); the
v_{m+1}-values of the R and Q digits), which J-A grades "PROVED
unconditionally ON THE SHARED-KEY PERIMETER" — so (iii)/(iv) are asserted at
levels m ≤ qcap = min(n, shared_upto+1) (§1), and off that perimeter the
v_{m+1}-reading of the print side is a different object. Clauses (i)/(ii) are
perimeter-free: (i) consumes JB-DEV(i) (every q) and (ii) is uniqueness of
division at the print's own keys.]**~~

**[r3, STEP 2 — SURFACE 4 of 14, REGENERATED FROM §0M rows 14–18. ∎ GRADE:
PROVED at attempt grade on the displayed scope. SCOPE FENCES ON EVERY CLAUSE:**
T-scope(m) (the [RMG] d₀ ≥ 2 flat corners stay FENCED — the weld inherits them,
blueprint S5's cross-cutting row); g_m = 1 for the Ĉ_m instance; W-WIN not
consumed (window-free legs only, as in [RMG]). **PER CLAUSE:**

    JB-ID / (ii)  PERIMETER-FREE — uniqueness of division at the print's own
                  keys. Consumes [RMG] S2.2 (ID-(i+1)) + L-NORM + L-CELL, and
                  S0.1's P_i = e_i·g_i (r3, F-7).           [rows 14, 16]
    (i)           PERIMETER-FREE (it consumes JB-DEV(i), which holds at every
                  q); W2-C1 representative reading, W2-C3's chamber off the
                  byte perimeter; [RMG] T-TERM + L-EXACT + L-CANON — and
                  L-CANON's hypothesis deg Ĉ_m < deg Φ_m is one of the two
                  [RMG] clauses restored to §5's recital in r3 (F-5).
                                                                [row 15]
    (iii)/(iv)    at levels **m ≤ qcap** only (`P<q` read at level m), since
                  both consume JA-VAL (line(C) = w_m(C) = v_{m+1}(C); the
                  v_{m+1}-values of the R and Q digits), which J-A grades
                  "PROVED unconditionally ON THE SHARED-KEY PERIMETER"; off it
                  the v_{m+1}-reading of the print side is a different object.
                                                           [rows 17, 18]
    (iii)         LED-Λ is consumed at ATTEMPT grade and the tie's grade rides
                  it (the runner re-verifies the λ_E quanta FRESH).  [row 17]
    (iv)          its (C-READ) leg transports as §5 and therefore rides §5's
                  (VD-m) fence IN FULL; its (C-W_Q) clause has NO machine leg.
                                                                [row 18]

**[r3, F-1B — the (iii)/(iv) perimeter (r2's re-grep hit 7) now ALSO reaches
the grade cap and JB-BOX-2's enumeration. r2 introduced this fence and in the
same round certified those two surfaces "already consistent"; that claim was
false when written and is corrected in the r2 block above.]]** [Machine: JB-TREE — a FRESH from-note tree walker
(this unit's own implementation of S2.1/S2.2 on ITL towers: cells,
E1-priority, L-NORM via divmod, signed reassembly) checked against (1)
exact reassembly f·Ĉ_m = R₀ + QΦ_m, (2) ~~the canonical division by the
harness key AND by the print-side key where byte-equal~~ **[r1, G-1 —
CORRECTED to what the sealed runner establishes: the canonical division BY
THE HARNESS KEY (one fresh `fresh_divmod`), plus, where the print key is
byte-equal to it, the same division re-executed on the print key's bytes —
a CONSISTENCY RE-CHECK, not an independent print-key reading: `fresh_divmod`
is a pure function of (R, f, key), so on equal tuples the second call cannot
fail unless the first does, and off the byte-equal set the sealed battery runs
NO print-key tree check at all. The genuinely independent print-key evidence
is the POST-SEAL walker of §7.4 (`grt_jb_printwalk.py`), which builds the
tree from the print chain's own keys and correction digits and never calls
`fresh_divmod`]**, (3) R-leaf
reducedness; JB-ID — (ID-(i+1)) as the key's own development, both
engines; JB-LINE — line(C) = wlev = vgen on reduced cells + the per-edge
λ_E quanta recomputed fresh (LED-Λ's table row keyed); teeth MJB-TREE.]

---

## §5. THEOREM JB-CREAD (the (C-READ) transport = blueprint J-B(iii); W-5)

Setting: ~~the (RM-m) box verbatim ([RMG] S0.2, ACCEPTED on its scope):
level m, g_m = 1, Ĉ_m the canonical correction digit
(R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m), f ≠ 0 with
deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and the canonical division
f·Ĉ_m = R + Q·Φ_m.~~

**[r3, STEP 3 = F-5 — THE RECITAL RESTORED, and with it the citation license
LEMMA JB-EPS's application needed. The struck recital called itself "the (RM-m)
box verbatim" while DROPPING two of the three parenthetical clauses [RMG]
states about Ĉ_m. Both are restored here, quoted from the source display —
`RMENGINE_2026-08-08.md` §S0.2, "THE STATEMENT UNDER PROOF — the (RM-m) box,
quoted verbatim (operative-site paste)", itself byte-frozen there from [ILN]†
S4.6 — which reads:**

> **(RM-m) [READ-MULT with the canonical correction, level m], 1 ≤ m.**
> Setting: level m of a class tower with g_m = 1, Ĉ_m the canonical
> correction digit of WELL-DEF-(n)(ii) (deg < deg Φ_m, w_m = γ_{m+1},
> R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}c_m). Input: f ∈ O[x],
> f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f) its read. Claim:
> there exist R, Q ∈ O[x] with deg R < deg Φ_m, deg Q < deg Φ_m, and
>
>   f·Ĉ_m = R + Q·Φ_m,   w_m(R) ≥ λ + γ_{m+1},
>   w_m(Q) ≥ λ + γ_{m+1} − w_mΦ_m   (Q = 0 allowed),
>   R_{m,λ+γ_{m+1}}(R) = z_m^{ε′}·v·τ_m,
>   ε′ := ⌊(s_m(λ) + s_m(γ_{m+1}))/e_{m−1}⌋  [the level-m EPS-carry].

**SO §5'S SETTING, NOW COMPLETE: level m, g_m = 1, and Ĉ_m the canonical
correction digit of WELL-DEF-(n)(ii) with ALL THREE of its clauses —**

    (Ĉ-deg)   deg Ĉ_m < deg Φ_m                      [RESTORED in r3]
    (Ĉ-wt)    w_m(Ĉ_m) = γ_{m+1}                      [RESTORED in r3]
    (Ĉ-read)  R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m

**— together with f ≠ 0, deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and
the canonical division f·Ĉ_m = R + Q·Φ_m. (Ĉ-deg) is not decoration: [RMG]
L-CANON's three hypotheses are Φ_m MONIC, deg f < deg Φ_m and (Ĉ-deg), so the
restored clause is exactly what makes "THE canonical division" canonical at
this site.**

**THE LICENSE (what F-5 charged). LEMMA JB-EPS below is quantified over
V, V′ ≥ 0 IN THE LEVEL-m WEIGHT LATTICE, and THEOREM JB-CREAD's display applies
it at (V, V′) = (λ, γ_{m+1}). Both memberships now follow in one line each:**

    λ = w_m(f)  with f ≠ 0        ⇒  λ is the level-m weight of a NONZERO
                                     polynomial, hence in the level-m weight
                                     lattice (which contains every value of
                                     w_m on nonzero polynomials).
    γ_{m+1} = w_m(Ĉ_m) by (Ĉ-wt), and Ĉ_m ≠ 0 because its read
    R_{m,γ_{m+1}}(Ĉ_m) = τ_m is NONZERO by (Ĉ-read) (τ_m = ε_m(γ_{m+1})^{−1}c_m
    with c_m = ψ_{m,0} ≠ 0, the class pin)
                                  ⇒  γ_{m+1} is likewise the level-m weight of
                                     a nonzero polynomial, hence in the
                                     level-m weight lattice.  ∎

**Before r3 the second line was UNAVAILABLE in this note: γ_{m+1} appeared only
as the DEFINED INTEGER γ_{m+1} := e_m·w_mΦ_m + h_m of §1's read data, and
(Ĉ-wt) — the clause that identifies that integer as a weight — was the clause
the recital had dropped. The lemma itself was never in danger (its proof uses
only s^wt(β) ≡ ℓ_{m−1}β mod e_{m−1} and JA-GRID(c), and `jb_eps` quantifies
PLAIN integers 0 ≤ V,V′ < 25, a superset of the lattice), so r3 restores the
LICENSE rather than widening the lemma: the quantifier stands as written and the
cited instance is now provably inside it. §0M rows 19/20.]**

Here c_m = ψ_{m,0}, the constant coefficient of the
degree-1 modulus ψ_m(y) = y + ψ_{m,0} (from WELL-DEF's g_m = 1 lift form
and REALIZE R3, consumed) — so in K_{m+1} = K_m[z_{m+1}]/(ψ_m),

    c_m = ψ_{m,0} = −z_{m+1}    (the classifier's NEXT residual letter).

**[r1, G-7 — the s_m(·) OVERLOAD, declared and split.]** r0 wrote one symbol
s_m(·) for two different integers, undefined in-note:

    s_m^wt(V) := (ℓ_{m−1}·V) mod e_{m−1}   for a level-m WEIGHT V
                 — the eq-(12) abscissa; equivalently the least x ∈
                 [0, e_{m−1}) with (V − x·h_{m−1}) ≡ 0 (mod e_{m−1}),
                 which is the runner's ℓ-FREE `s_geo(V, e, h)`;
    s_m^ini(A) := the INITIAL ATTAINED ABSCISSA of a POLYNOMIAL A on its
                 own realized side (the print's s₀ = the least abscissa of
                 the realized side of N_m(A)) — the integer (VD-m) and
                 τ_m(A) are written with.

They differ by a multiple of e_{m−1} in general (J-A's own
s₀ = s_m^wt(β) + ν·e_{m−1}, ν ≥ 0 the grid offset), so the two readings are
NOT interchangeable. From here on LEMMA JB-EPS is stated with s_m^wt ONLY
(its arguments are weights) and (VD-m)/τ_m with s_m^ini; no step of §5 mixes
them, and the r0 proof did not (this is a notation repair, not a
mathematical one).

**LEMMA JB-EPS (the ε-cocycle collapse; unconditional, pure read data).**
For every m ≥ 1 and V, V′ ≥ 0 in the level-m weight lattice, with
t_m(β) = (ℓ_{m−1}β − s_m^wt(β))/e_{m−1} the print twist exponent (JA-EPS's
convention) and ε′ := ⌊(s_m^wt(V) + s_m^wt(V′))/e_{m−1}⌋:

    t_m(V + V′) − t_m(V) − t_m(V′) = ε′ ,   hence
    ε_m(V+V′) · ε_m(V)^{−1} · ε_m(V′)^{−1} = z_m^{−ε′} .

*Proof.* The numerator telescopes (all s's are s_m^wt): ℓ(V+V′) − s(V+V′) −
ℓV + s(V) − ℓV′ + s(V′) = s(V) + s(V′) − s(V+V′) = e_{m−1}·ε′ by the carry
clause (JA-GRID(c) = (C-EPS), graded in J-A PROVED and unconditional, and
carrying no u ≥ 0 proviso); divide by e_{m−1} (legitimate: t_m(β) ∈ ℤ since
s_m^wt(β) ≡ ℓ_{m−1}β mod e_{m−1}). The field form is JA-EPS (ε = z^{−t}). ∎
[Machine: JB-EPS, integers + field elements, every roster level.]

**THEOREM JB-CREAD.** Suppose (VD-m) (J-A §3.4's evaluated dictionary)
holds at f and at R — ~~unconditional for m ≤ 2 (VD-1 = W2-L3; m = 2 by
JA-RES), per-digit proviso / (R-coll) at m ≥ 3 (JA-BOX-2)~~ **[r1, F1 —
SUPERSEDED; the struck parenthetical was FALSE and the note's own sealed
runner refutes it. THE HONEST PERIMETER: unconditional at m ≤ 1 ONLY
((VD-1) = W2-L3); at every m ≥ 2 the hypothesis is CONDITIONAL — it needs
JA-VDIND's absolute character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every
attained abscissa (sufficient: A_{m−1} = 0, i.e. e_{m−2} = 1; or
ord(z_{m−1}) | A_{m−1} with the abscissa condition), which at m ≥ 3 is
implied by the per-digit proviso / (R-coll) of JA-BOX-2. "m = 2 by JA-RES"
conflated J-A's PER-SLOT law (unconditional at m = 2) with the EVALUATED
dictionary (VD-2), which JA-RES alone does not give: on the sealed roster
(VD-2) is machine-evaluated FALSE at 10 of 13 boundary rows
(T3A/T3B/T3C/T3D ~~— the e₀ ≥ 2 character-visible towers~~ **[r2, G2-4 — the
struck gloss is a MECHANISM CLAIM and the note's own roster refutes it: T3E
also has e₀ = 2 (reads e = 2,1,2) and scores 6/6. The four towers are the
OBSERVED failing rows, listed as data; no property in this note distinguishes
them from the scoring e₀ ≥ 2 rows, see §7.1]**), §7.1/§7.4]** — and
suppose v ≠ 0 (THE NON-DEGENERATE READ STRATUM; the v = 0 branch is displayed
after the proof). Define the print's TWISTED EVALUATED READ
ρ_m(A) := z_m^{τ_m(A)}·R_m^cls(A)(z_m) (R_m^cls the print residual
operator at A's own realized side, τ_m(A) = (s_m^ini(A) −
ℓ_{m−1}w_m(A))/e_{m−1} as in (VD-m), with s_m^ini the initial attained
abscissa of §5's notation block, r1/G-7). Then w_m(R) = λ + γ_{m+1} exactly,
and

    ρ_m(R)  =  c_m · ρ_m(f)  =  ψ_{m,0} · ρ_m(f) .

**The transport, stated.** [RMG]'s (C-READ) — "multiplying a read digit by
the canonical correction digit shifts the read by τ_m with the level-m
EPS-carry z_m^{ε′}" — transports to the classifier as: THE CLASSIFIER'S
TWISTED RESIDUAL READ SHIFTS BY THE CONSTANT c_m, WITH NO CARRY FACTOR.
The z_m^{ε′} carry of the harness frame is EXACTLY the coordinate change
between the print twist t_m and the harness ε-kit (LEMMA JB-EPS); it
reappears verbatim when the identity is written in ε-coordinates — that
form IS [RMG] (C-READ), consumed not re-proved.

*Proof (displayed in full).* By (VD-m) at f: ρ_m(f) = ε_m(λ)·v. Since
v ≠ 0 and τ_m is a unit, (C-READ) gives R_{m,λ+γ_{m+1}}(R) =
z_m^{ε′}·v·τ_m ≠ 0, so some cell of R sits on-line on-grid at
λ + γ_{m+1} (B-READ) **[r1, G-7 — tag resolved: (B-READ) is [RMG] S2.1's
LEMMA L-CELL clause (ii) — a nonvanishing level-m read at a weight forces an
on-line on-grid cell at that weight — whose parent L-CELL is in this note's
header consumption list; clause (i) (w_m = the minimum line over cells) is
what turns that into the weight inequality. r0 used the bare tag, which is
unresolvable from this note alone]**, forcing w_m(R) ≤ λ + γ_{m+1}; with
(C-W_R)'s ≥
this pins w_m(R) = λ + γ_{m+1} EXACTLY — so (VD-m) at R is an identity
at the (C-READ) target:

    ρ_m(R) = ε_m(λ+γ_{m+1}) · R_{m,λ+γ_{m+1}}(R)
           = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · τ_m            [(C-READ)]
           = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · ε_m(γ_{m+1})^{−1} · c_m
           = [ε_m(λ+γ_{m+1}) ε_m(λ)^{−1} ε_m(γ_{m+1})^{−1}] · z_m^{ε′}
             · c_m · ε_m(λ)·v
           = z_m^{−ε′} · z_m^{ε′} · c_m · ρ_m(f)            [JB-EPS]
           = c_m · ρ_m(f) .                                  ∎

**The degenerate branch (v = 0), displayed.** There ρ_m(f) = ε_m(λ)·v = 0
by (VD-m) at f, and (C-READ) gives only the TARGET-read vanishing
R_{m,λ+γ_{m+1}}(R) = 0; R's OWN weight can sit strictly above λ + γ_{m+1}
with a nonzero own-side print residual, so the ρ-form identity is NOT
claimed at v = 0 — the transport there is the read-at-target statement
(0 = 0) only. This stratum split is the theorem's own scope, not a gap;
the runner scores v ≠ 0 rows and censuses the v = 0 rows (checking
ρ_m(f) = 0 on them, which does hold).

~~Grade: PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0} **[r1, F1 —
the perimeter spelled out: (VD-m) is free only at m ≤ 1; at every m ≥ 2 it is
a HYPOTHESIS (JA-VDIND's collapse condition, ⊇ (R-coll) at m ≥ 3), so
JB-CREAD has no unconditional stratum above m = 1. The theorem is
hypothesis-guarded and its algebra is untouched by this correction — JB-PE1
re-derived all five displayed lines and the verbatim ε′ match against [RMG]
(C-READ) — what was wrong in r0 was the advertised SIZE of the perimeter]**;
the ingredient grades ride ([RMG] ACCEPTED; J-A/W-2 attempt).~~

**[r3, STEP 2 — SURFACE 5 of 14, REGENERATED FROM §0M rows 19–23. GRADE:
PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0}. PER FENCE:**

    (VD-m)     unconditional at m ≤ 1 ONLY ((VD-1) = W2-L3); at every m ≥ 2 a
               HYPOTHESIS — JA-VDIND's ABSOLUTE character-triviality
               (⊇ (R-coll)/per-digit at m ≥ 3, JA-BOX-2) — so JB-CREAD has NO
               unconditional stratum above m = 1. Required at BOTH f and R.
                                                                  [row 21]
    v ≠ 0      the non-degenerate read stratum. The v = 0 branch is the
               read-at-target statement (0 = 0) only, the ρ-form is NOT claimed
               there, and it is machine UNEXERCISED (v = 0 census: 0 rows).
                                                                  [row 22]
    key perim. NONE — §5's print-side content enters ONLY through the (VD-m)
               hypothesis, so the theorem is a legitimate conditional at any
               level. Disclosure, not a fence: the instrument cuts reduction
               levels at `qcap_of(T,G)` and the off-perimeter counter is 0 on
               the roster.                                 [rows 21/22, ⟨n5⟩]
    u ≥ 0      NOT consumed — LEMMA JB-EPS cites JA-GRID(c), which carries no
               proviso.                                            [row 19]
    [RMG]      (C-READ) + (C-W_R) + the COMPLETE Ĉ_m clause list (restored in
               r3, F-5) + L-CELL(i)/(ii) = (B-READ), on [RMG]'s own scope
               (T-scope(m), g_m = 1).                        [rows 20, 21]
    JB-EPS     UNCONDITIONAL at every m ≥ 1; its application at (λ, γ_{m+1}) is
               LICENSED by the restored (Ĉ-wt) (r3, F-5).    [rows 19, 20]

**The ingredient grades ride ([RMG] ACCEPTED; J-A / W-2 / LED-Λ at attempt).
The theorem is hypothesis-guarded and its algebra is untouched by every
correction in this arc: JB-PE1 re-derived all five displayed lines, JB-PE2
confirmed them, and JB-PE3 re-matched ε′ VERBATIM against [RMG] S0.2 a second
time. What was wrong in r0 was the advertised SIZE of the perimeter.]** **[r1,
hygiene] τ_m is a unit because c_m = ψ_{m,0} ≠ 0 (the class pin: ψ_j monic
irreducible with ψ_j(0) ≠ 0, [ILN]† S0.1 / J-A §1, enforced in the engine's
ψ search) and ε_m(γ_{m+1})^{−1} is a unit — r0 asserted the unit property
without the citation.** [Machine: JB-CREAD — both
sides computed end-to-end (print residuals by the sealed GmnLeg
transcription, harness division/reads by ITL, τ/ε′ by fresh integers) with
the (VD-m) instances at f and R MACHINE-EVALUATED per row: scored where
they hold, boundary census disclosed; JB-CM — c_m = ψ_{m,0} and
embed_{K_{m+1}}(c_m) = −z_{m+1}; teeth MJB-CREAD — the spurious-carry
reading ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f) must FAIL on designated ε′ ≥ 1 rows.]

**Remark (the carry seed; fence).** ρ_m(R) = −z_{m+1}·ρ_m(f) in K_{m+1}:
on twisted residual reads, multiplication by the canonical correction
digit IS multiplication by the negative of the classifier's next residual
letter. This is the semantic germ the J-C carrier block (W-6..W-9) needs —
displayed here as an identity of READ VALUES only; no graded-ring (gr)
object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.

---

## §6. Honest boxes

* **JB-BOX-1 (blueprint correction, review-owed).** Blueprint J-B(iii)
  displays the classifier transport WITH the carry ("shifts the
  CLASSIFIER's residual read by τ_m with the level-m EPS-carry z_m^{ε′}").
  CORRECTED: in the print's twisted coordinates the carry cancels
  (THEOREM JB-CREAD); the shift constant is c_m (not τ_m), and the
  τ_m-with-carry form is the HARNESS-frame statement ([RMG] (C-READ)).
  The blueprint display conflated the two frames; both are displayed
  above with the coordinate change (JB-EPS) between them.
* **JB-BOX-2 (inherited conditionality, quantified).** Every print-residual
  statement rides J-A's boxes verbatim: ~~the (VD-m)/per-digit proviso at
  m ≥ 3 (JA-BOX-2 — (R-coll) sufficient, converse unsealed)~~ **[r1, F1 —
  RE-FENCED, this was the mis-scoped line: the (VD-m) conditionality bites
  from m = 2 UP, not from m = 3. Correct statement: (VD-1) = W2-L3 is free;
  at EVERY m ≥ 2 (VD-m) is conditional on JA-VDIND's absolute
  character-triviality on the attained abscissas; at m ≥ 3 that is the
  per-digit proviso / (R-coll) box JA-BOX-2 ((R-coll) sufficient, converse
  unsealed); at m = 2 it is ~~the e₀ ≥ 2 / nontrivial-z₁ boundary~~ **[r2,
  G2-4 — RE-WORDED: JA-VDIND's absolute character-triviality condition
  ITSELF, with no known characterisation. The only implication available is
  e₀ = 1 ⇒ A_1 = 0 ⇒ the condition holds; e₀ ≥ 2 is therefore NECESSARY for an
  m = 2 failure but is NOT sufficient (T3E, e₀ = 2, scores 6/6)]**, where the
  sealed runner exhibits 10 in-roster FALSE instances of (VD-2). So the
  boundary geography of §7.1 is the JA-VDIND collapse condition at m = 2 plus
  JA-BOX-2's box at m = 3 — r0 attributed all of it to JA-BOX-2]**, the
  unpinned-ℓ orbit (JA-BOX-3: all displays at the pinned (P-ell)
  representative; §4.3-orbit transport per J-A §4(ii)), and W-2's
  (C-coll)/recursion split for the byte law. **[r1, G-5 — one inherited
  proviso that is NOT one of JA-BOX-1..5 and rode in uncarried in r0:
  JA-GRID(a)'s `[JA-r1]` repair proviso u := (V − s·h)/e ≥ 0 (the bare
  V ∈ ℤ_{≥0} quantifier was FALSE at small V). It is consumed by §2(iii)'s
  (GRID) layer and is hereby CARRIED BY THIS BOX, ~~with the discharge stated
  at §2(iii): every consumption site's V is the level-m weight of a nonzero
  polynomial in the tower's own window, so J-A's own sufficient hypothesis
  V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) holds there.~~ **[r2, G2-5 — THE DISCHARGE IS
  RETRACTED; the struck sentence asserted an implication with no derivation and
  it is not plausible as stated (this note's quantifiers admit units, of
  level-m weight 0, while the bound is positive at r ≥ 2). STATUS: CARRIED,
  DISCHARGE OWED. Every statement consuming §2(iii)(GRID) — JB-DEV(iii)'s
  (GRID) layer and, through it, the grid/abscissa content of JB-VTX(d) — is
  conditional on this proviso in addition to its other fences. A real discharge
  must derive u := (V − s_m^wt(V)·h_{m−1})/e_{m−1} ≥ 0 — ~~equivalently~~
  **[r3, F-6(a) — "equivalently" WITHDRAWN here as at the r2 block's G2-5
  bullet: the genuine equivalence is u ≥ 0 ⟺ V ≥ s_m^wt(V)·h_{m−1}, while J-A's
  print bound is SUFFICIENT only. Read: **for which it SUFFICES to derive** —]**
  V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}) in J-A's own form, for EVERY V in the
  quantified window with units included; see the retraction block at §2(iii)
  for what is and is not known (V = 0 gives u = 0, so units are not a
  counterexample; J-A's own (e,h) = (2,3), V = 1 ⇒ u = −1 is not excluded by
  anything this note says).]** JA-GRID(c) — the carry clause
  LEMMA JB-EPS consumes — carries NO proviso and is unconditional.]**
  ~~**[r1, G-9]** The (VAL)/(GRID)/(RES) layers and all of JB-VTX are
  quantified on the SHARED-KEY perimeter q ≤ qcap (J-A grades JA-VAL on it;
  off it the print frame is a different object) — restated at §2(iii) and at
  the JB-VTX theorem.~~

  **[r3, STEP 2 — SURFACE 14 of 14: THIS BOX'S PERIMETER ENUMERATION,
  REGENERATED FROM §0M. The struck r1/G-9 sentence had two defects PE3 named:
  it omitted JB-TREE(iii)/(iv) (F-1B — r2 fenced them at §4 and §7.2 in the
  same round it certified this box "already consistent"), and it put all three
  layers of §2(iii) on ONE perimeter (F-4). THE COMPLETE ENUMERATION, which is
  §0M's columns (a1)/(a2) read down:**

    on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap; J-A grades JA-VAL on it,
    and off it the print frame is a different object):
        §2(iii)(VAL) and §2(iii)(GRID)                      [rows 3, 4]
        ALL of JB-VTX — (a), (b), (c), (d1)–(d3), (d4), and (e) through
        (a) at f = Φ_{q+1}^har                            [rows 8–13]
        JB-TREE(iii) and JB-TREE(iv), read at level m       [rows 17, 18]
    on the BYTE-EQUAL CHAIN THROUGH q `P≤q` (strictly stronger; they differ
    exactly at q = qcap):
        §2(ii)'s byte clause                                    [row 2]
        §2(iii)(RES) — added in r3, F-4                         [row 5]
    on NO key perimeter:
        §2(i), §2(iv), JB-AFF, JB-ID, JB-TREE(i), JB-TREE(ii), JB-EPS,
        JB-CREAD (a legitimate conditional at any level; its instrument's own
        level cut is disclosed at §5 and §7.1)
                                                [rows 1, 6, 7, 14–16, 19–22]

  **And the u ≥ 0 proviso of this box reaches EXACTLY TWO claims: §2(iii)(GRID)
  (row 4) and JB-VTX's clause (d4) — the attained-abscissa/read-grid tie, which
  is also the ONE sub-clause of JB-VTX with no machine leg (row 12, r3/F-3).
  No other statement in this note consumes JA-GRID(a).]**
  JB-CREAD's own stratum
  split (v ≠ 0 scored; v = 0 = the read-at-target branch only, ρ-form
  not claimed) is displayed at the theorem. W2-OPEN-1 (the value layer
  on transported lifts) is consumed NOWHERE (independently re-verified in
  JB-PE1: no §2–§5 statement touches W-2 §5.3's K5/K6/K7/K12 battery).
* **JB-BOX-3 (cross-key fence).** No cross-representative operator or
  byte identity is claimed anywhere (JB-DEV(iv)); transport across
  representatives is W-2 clause 2/3 covariance only. The JuncForge
  parity-wall lesson is honored structurally: every §2–§5 statement is
  against the semantic development/polygon/tree/read objects; SideReads/
  TreeModel are consumed nowhere.
* **JB-BOX-4 (tree scope).** JB-TREE inherits [RMG]'s fences verbatim:
  termination on T-scope(m) (d₀ = 1 ∨ non-degenerate below top; the
  d₀ ≥ 2 flat corners stay FENCED and are quantified over nowhere here);
  g_m = 1 for the Ĉ_m instance; W-WIN consumed by nothing. LED-Λ is
  ATTEMPT grade (acceptance counter 0) — the §4(iii) citation's grade
  rides it, and the runner therefore re-verifies the λ_E quanta FRESH
  rather than trusting the ledger (decorrelation, not redundancy).
* **JB-BOX-5 (instance perimeter).** Machine evidence = the §7 roster
  (16 towers, reads ≤ 4 + top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀
  leg; 5 QO shapes; 4 fresh d₀ ≥ 2 shapes); F_p[[t]] rows have no PARI
  leg (JA-BOX-4 inherited); mixed-characteristic print, equal-char rows
  ride construction-identity + machine only.
* **JB-BOX-6 (standing fences).** No gr/carrier claim (J-C untouched;
  BLOCKED-ON-CARRIER-TIE stands); no count/menu/density claim (J-D
  untouched); the P0 application gate stands; acceptance counter 0/2 —
  nothing here may be consumed at proof grade before its hostile arc.
  **[r3 — and one procedural fence, added by this round: the COMPLETE
  conditionality of every claim in this note is §0M's matrix. A consumer who
  reads a grade surface (the grade cap, any ∎ Grade line, any §7.2 row, §7.3,
  or any box) is reading a REGENERATION of that table; if a surface and the
  table ever disagree, THE TABLE GOVERNS and the disagreement is a defect to
  report. Any future repair round that adds or moves a fence must edit §0M
  first and re-derive the 14 surfaces from it — the per-site sweep genre that
  produced PE1/G-9, PE2/G2-1 and PE3/F-1 + F-1B is retired.]**

---

## §7. Records (commit 2 — from the sealed artifacts)

### 7.1 Machine bracket — **ALL 18 FAMILIES GREEN, 6,700 samples, 0 violations, every sealed prediction hit exactly** (`grt_jb_checks_output.txt` / `grt_jb_checks_results.json`, elapsed 0.7 s; seal commit 7f6759d)

**[r1, G-8 — SEAL-RECORD ERRATUM (the commit message is immutable; the note
carries the correction).** Seal commit `7f6759d`'s message says "note +
runner sealed with preregistered predictions", but that commit contains ONLY
`verification/openmath/grt_jb_checks.py` (990 insertions); the note itself was
committed one commit EARLIER, at `5a72b62`, with the predictions written in
prose ("Sealed predictions (commit 1): EXT-GATE 0 · JB-DEV 0 · …"). The seal
PROPERTY that matters is unaffected and was independently verified in JB-PE1:
predictions on record before the battery; runner md5
`55f4911eaddd8524fd91368b30ed71bd` identical at seal, at verdict and at HEAD;
and `git diff 7f6759d f5578d0` on the note touches §7.1 ONLY — no §1–§6 law
statement, box or grade moved between seal and verdict. Only the message
wording was imprecise.]** **[r1] The r1 round did not re-run and did not
modify this battery; all figures in §7.1 are the sealed ones, with the
wording corrections marked inline.**

| family | claim keyed | samples | verdict |
|---|---|---|---|
| EXT-GATE | engine_ext pins + agreement gate re-run (standing rule) | 1 | GREEN |
| JB-DEV | ~~fresh schoolbook dev == both engines + digit weight ties~~ **[r3, F-2 — RESTATED to the code's content; "both engines" WITHDRAWN. fresh schoolbook dev (`fresh_dev`) == the engine's `PolyO.dev` (IND: one genuine second implementation) + the (VAL) digit-weight tie `G.vgen(q+1,A) == T.wlev(q,A)` (IND: the genuine cross-engine leg). The third leg, `G.P.dev` on the print key, is SAME-COMPUTATION — the same `PolyO.dev` on the same ring object with byte-equal arguments, behind a guard that already forced agreement, so its violation is UNREACHABLE and it carries no information (§0M row 1, cell note ⟨n1⟩)]** | 893 | GREEN |
| JB-KEYEQ | byte census + TH-BASE (~~q = 1 byte-equal on all 25 rows~~ **[r1, G-3]** q = 1 byte-equal on **22 of the 25 rows**, and the other 3 are VACUOUS, not confirmations: `QO:x3-3/Q3`, `QO:x4+2x2+2/Q2`, `QO:x4-2/Q2` have T.n = 0, so the census loop `range(1, T.n+1)` walks nothing, the census is `{}`, and the TH-BASE guard `if T.n >= 1 and not cen.get(1, True)` is never exercised) | 25 | GREEN |
| JB-SHEAR | ~~pointwise shear + the four min/read ties (Lemma shape 1 through a second development)~~ **[r3, F-3 — RESTATED: pointwise shear + **THREE** of clause (d)'s four min/read ties (d1 `minU == vgen(q+1,f)` and d3 `minH == vgen(q+2,f)`, both under q ≤ shared_upto, and d2 `minH == wlev(q+1,f)`; Lemma `shape` item 1 keyed through a second development). The FOURTH tie (d4: attained abscissas = the read grid, read assembled from the on-line digits at those slots) is MACHINE-UNKEYED in every family of every instrument — and is also the only sub-clause riding the undischarged u ≥ 0 proviso (§0M row 12, cell note ⟨n3⟩)]** | 893 | GREEN |
| JB-VTX | vertex bijection + per-side slope/length law, fresh hulls | 893 | GREEN |
| JB-ID | (ID-(i+1)) exact + key-dev digits + print-key grid/shear-constancy | 34 | GREEN |
| JB-TREE | ~~fresh tree walk == canonical division, harness AND print keys~~ **[r1, G-1]** fresh tree walk == the canonical division BY THE HARNESS KEY (one fresh division), plus a byte-equality-gated RE-EXECUTION of that same division on the print key's bytes (a consistency re-check, NOT an independent print-key reading; no print-key check at all off the byte-equal set — the independent print-key evidence is §7.4's post-seal walker) | 79 walks (125 with chambers) | GREEN |
| JB-LINE | λ_E quanta per edge + leaf line == wlev == vgen | 194 | GREEN |
| JB-EPS | ε-cocycle collapse, integers + field | 955 | GREEN |
| JB-CM | c_m = ψ_{m,0} = −z_{m+1} (28 eligible (T, m) rows) | 28 | GREEN |
| JB-CREAD | ρ(R) = c_m·ρ(f) + w_m(R) pin, scored stratum | 79 | GREEN |
| JB-QO / JB-D0 | 5 concrete shapes / 4 fresh d₀ ≥ 2 shapes (engine_ext) | 5 / 4 | GREEN |
| TW-JB | chamber re-instantiation (all 16 towers, nontrivial ledgers) | 2,480 | GREEN |
| MJB-DEV / MJB-VTX / MJB-TREE / MJB-CREAD | teeth (garbled key / unsheared frame / corrupted correction / spurious carry) | 3/3/3/3 rows | GREEN (all caught) |

Censuses (the note's displayed conditionality, quantified): JB-CREAD
**scored 104 (~~66 roster~~ **[r2, G2-7 — the word "roster" named two
different sets in this paragraph; the decomposition, recounted from the
committed sealed JSON, is displayed once here and used consistently:
NON-CHAMBER 66 = 16-tower ROSTER 56 + QO leg 2 + d₀ leg 8, so the "56 roster
rows" of the r1 bracket below and this 66 are the same census at two different
scopes]** non-chamber 66 = roster 56 + QO 2 + d₀ 8, + 38 chamber),
0 violations; boundary 21 —
ALL on the character-visible/interior-twist towers T3A, T3B, T3C, T3D,
I4B and their transported chambers**, ~~exactly the JA-BOX-2/(VD-m)-proviso
geography (T3B/I4B = the W-2 collapse-boundary pair)~~ **[r1, F1 — CENSUS
RE-ATTRIBUTED; the struck clause read the census as an m ≥ 3 phenomenon and
so read this disclosure as CONFIRMING the (now retracted) "uncond. m ≤ 2"
line, when it is the evidence AGAINST it. THE TRUE LEVEL SPLIT, recomputed in
r1 by re-keying `jb_cread`'s own control flow level-by-level
(`grt_jb_r1_levelcensus.py`, §7.4): of the 13 ROSTER boundary rows, **m = 1:
0 · m = 2: 10 (T3A 3, T3B 3, T3C 1, T3D 3) · m = 3: 3 (I4B)**, and NOT ONE is
an evaluator scope-out — all 13 are machine-evaluated FALSE instances of
(VD-m). Scored: 56 roster rows (the 16-tower part of the non-chamber 66,
r2/G2-7) at m = 1: 45, m = 2: 8, m = 3: 3. ~~So the
geography is the JA-VDIND COLLAPSE BOUNDARY at m = 2 (the e₀ ≥ 2 towers with
a nontrivial z₁: T3A e = 2,2,2; T3B e = 3,2,2; T3C e = 2,3,2; T3D
F₂[[t]] e = 2,2,2 — while the level-flat T3 rows T3E (e₁ = 1) and T3F
(e₀ = 1) score 6/6, exactly where A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses)
PLUS JA-BOX-2's own box at m = 3 (I4B only).~~ **[r2, G2-4 — THE MECHANISM
CLAIM IS STRICKEN, NOT REPLACED. Both struck characterisations are refuted by
the roster this note is describing (read off `GWP.TOWERS`, reads = (e, h, g)):

    tower ring  p  e        h        g        d₀   (VD-2) at m = 2
    T3A   Zp    2  2,2,2    1,1,1    1,1,1    2    BOUNDARY (3 rows)
    T3B   Zp    3  3,2,2    1,1,1    1,1,1    1    BOUNDARY (3 rows)
    T3C   Zp    3  2,3,2    1,2,1    1,1,1    1    BOUNDARY (1 row, 2 scored)
    T3D   Fpt   2  2,2,2    1,1,1    2,1,1    1    BOUNDARY (3 rows)
    T3E   Zp    2  2,1,2    1,1,3    2,1,1    1    SCORES 3/3  (6/6 both m)
    T3F   Zp    3  1,3,2    2,1,1    2,1,1    1    SCORES 3/3  (6/6 both m)

  (i) "the e₀ ≥ 2 towers": T3E has e₀ = 2 and scores — five of the six T3 rows
  have e₀ ≥ 2 and only four fail. (ii) "exactly where
  A_{m−1} = ℓ_{m−2}g_{m−2}γ_{m−1} collapses": at m = 2 that reads A_1 = ℓ₀g₀γ₁,
  which by the note's own displayed sufficient condition vanishes iff e₀ = 1 —
  true for T3F ALONE, so it cannot separate the other five. Worse for the
  claim: T3D and T3E share the level-0 read (e₀, h₀, g₀) = (2, 1, 2) and the
  same ψ₀ (⇒ the same A_1 and the same z₁ of order 3 in F₄), and they still
  split — so the failing set is NOT a function of (A_1, ord z₁) at all. THE
  HONEST STATEMENT: the mechanism of the m = 2 split is NOT IDENTIFIED in this
  note. What holds is one implication, e₀ = 1 ⇒ A_1 = 0 ⇒ (VD-2) (consistent
  with T3F), i.e. e₀ ≥ 2 is NECESSARY and not sufficient; the discriminator
  among the e₀ ≥ 2 rows must involve data this note never computes (the
  attained-abscissa set — T3D/T3E differ in the upper reads, e₁ = 2 vs 1 — or
  the ring, Z₂ vs F₂[[t]]). The table above is DATA, not a law: no consumer may
  use it to predict which towers are free at m = 2. The m = 3 boundary (I4B, 3
  rows) is JA-BOX-2's own box.]** T3B/I4B remain the W-2
collapse-boundary pair]**; **v = 0 stratum:
0 occurrences; R = 0: 0; off-perimeter tree rows: 0**. Byte census
(JB-KEYEQ) ~~reproduces the probe's F1 pattern row-for-row~~ **[r1, G-6 —
COVERAGE CORRECTED: the two instruments walk different junction sets. The
weld probe's F1 family is print r ≥ 3 walked up to r = n+2, so it INCLUDES
the top junction; `jb_keyeq` walks q = 1..T.n, i.e. print r = 2..n+1, and
therefore NEVER a top junction. They share 12 junctions (T3× at r = 3, six
rows; I4× at r = 3,4, six rows) and on those 12 the agreement is EXACT (6
GREEN / 6 RED), including every example listed here; but 16 roster F1
junctions — all the top ones, carrying 12 of the probe's 18 F1 REDs — lie
outside JB-KEYEQ's range, so "row-for-row" reproduction of the F1 pattern was
an over-claim. The quoted §2(ii) figure "12 GREEN / 18 RED of 30 walked
junctions" is the PROBE's own and is exact against its committed output]**
(e.g. I4A/I4B
byte-equal through the top; T3A/T3C/T3D/T3E diverge at q = 2; I4C at
q = 2, 3 — and I4C has NO eligible (g_m = 1 ∧ T-scope) reduction level,
so its tree/cread rows are honestly absent, the §4 scope fence in
action). MJB-CREAD teeth material: 22 scored samples with z_m^{ε′} ≠ 1
~~across 7 towers~~ **[r1, G-2 — CORRECTED: across 14 DISTINCT TOWERS (T2A,
T2B, T2D, T2F, T2G, T3A, T3B, T3D, T3E, T3F, I4B, JD3A, JD3C, JD5A) over 21
teeth-positive JSON rows (14 base + 7 chamber); the 22 samples split 15 base +
7 chamber. "7" was the number of teeth-positive CHAMBER rows, which coincides
with the runner docstring's smoke-probe designation list
(T2A/T2D/T2G/T3A/T3D/T3E/I4B) — a smoke-era figure carried into the verdict
text. The claim's substance is UNDERSTATED, not overstated]** — the
spurious-carry reading fails on every one, i.e.
the ε-carry collapse is machine-load-bearing, not a notational
convention.

### 7.2 Claims table (grades)

**[r3, STEP 2 — SURFACES 6–12 of 14: ALL SEVEN ROWS OF THIS TABLE REGENERATED
FROM §0M's MATRIX.** Each grade cell below is the conjunction of that claim's
YES cells in the matrix and nothing else. The r2 table is retained immediately
after, SUPERSEDED; its known defects are PE3's **F-1** (the JB-VTX row carried
no u ≥ 0 proviso although JB-BOX-2 names JB-VTX(d) as a consumer) and **F-4**
((RES) fenced at `P<q`). This is the surface a downstream unit reads alone, so
it is generated, not patched.**]**

| claim | grade — every fence from §0M, and no other |
|---|---|
| **JB-DEV** (expansion identity: same division; byte clause; three-layer coefficient correspondence; cross-key fence) | PROVED (attempt grade 0/2), consumptions at their own grades. **(i)** every q ≥ 0, at the W2-C1 admissible representative; **(iv)** every q ≥ 0 (a displayed fence); **(ii)** on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`, §1); **(iii)(VAL)** on the SHARED-KEY PERIMETER `P<q` = 0 ≤ q ≤ qcap = min(n, shared_upto+1) — off it (VAL) is FALSE, not merely unproved; **(iii)(GRID)** on `P<q` **AND** on JA-GRID(a)'s UNDISCHARGED `[JA-r1]` u ≥ 0 proviso; **(iii)(RES)** on the BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — one level deeper than r2's fence, **r3/F-4** — plus JA-RES's own fence (free at m = q+1 = 2, per-digit proviso at m ≥ 3, JA-BOX-2), and NOT (VD-m). Machine: one genuine second implementation + one genuine cross-engine tie; the advertised "print engine" leg is SAME-COMPUTATION with an UNREACHABLE violation (**r3/F-2**). [§0M rows 1–6] |
| **JB-AFF** (affine ordinate maps preserve hulls/vertices) | PROVED (two lines), **UNCONDITIONAL** — no perimeter, no proviso, no [RMG] clause, no (VD-m); no separate machine leg, its content being exercised inside JB-VTX(b)/(c)'s legs. [row 7] |
| **JB-VTX** (development polygon = Σ_q(N_{q+1}(f)) vertex-for-vertex; slope/length translation; min/read ties; window clause) | PROVED (attempt grade) **on the SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap), every statement at the W2-C1 admissible representative** — off it clause (a)'s JA-VAL input is unavailable and (a) is FALSE, not merely unproved. Clause-level: **(a)/(b)/(c)** and the **THREE** keyed min ties **(d1)–(d3)** ride `P<q` + W2-C1 only (the two print-side ties machine-restricted further to q ≤ shared_upto); clause **(d)'s FOURTH tie** — attained abscissas = the read grid — **ALSO rides JA-GRID(a)'s UNDISCHARGED u ≥ 0 proviso AND has NO MACHINE LEG** (**r3/F-1 + F-3**); **(e)** is at f = Φ_{q+1}^har, the W2-C1a window object, not at the theorem's quantified f (r1, G-4). [rows 7–13] |
| **JB-TREE** (the [RMG] tree computes the classifier's division; edge = division step; cells = expansion slots; λ_E face = polygon bookkeeping) | PROVED (attempt grade) on T-scope(m), g_m = 1, W-WIN unconsumed; LED-Λ cited at ATTEMPT grade and the tie's grade rides it. **(i)/(ii) PERIMETER-FREE; (iii)/(iv) at levels m ≤ qcap ONLY** (`P<q` read at level m), since both consume JA-VAL — **r3/F-1B: this fence now also stands at the grade cap and in JB-BOX-2**; **(iv)**'s (C-READ) leg additionally rides §5's (VD-m) fence in full, and its **(C-W_Q) clause has NO machine leg**. [RMG]: (i) T-TERM + L-EXACT + L-CANON (the latter through the restored deg Ĉ_m < deg Φ_m, **r3/F-5**); (ii) S2.2 + L-NORM + L-CELL + S0.1's P_i = e_i·g_i (**r3/F-7**). The print-key machine evidence for (i) is §7.4's post-seal walker, base rows only, with 8 byte-unequal chamber walks unreached (r1/G-1; r2/G2-2, G2-3). [rows 14–18] |
| **JB-EPS** (ε-cocycle collapse t(V+V′) − t(V) − t(V′) = ε′) | PROVED, **UNCONDITIONAL at every m ≥ 1** — no perimeter, no u ≥ 0 (it cites JA-GRID(c), which carries none), no (VD-m). **Its application inside §5 at (V, V′) = (λ, γ_{m+1}) is LICENSED by [RMG]'s restored clause w_m(Ĉ_m) = γ_{m+1} (r3/F-5); before r3 that instance sat outside the lemma's own quantifier.** [rows 19–20] |
| **JB-CREAD** ((C-READ) transport: ρ_m(R) = c_m·ρ_m(f), carry-free in print coordinates) | PROVED on the **(VD-m) perimeter ∩ {v ≠ 0}**: (VD-m) unconditional at m ≤ 1 ONLY, CONDITIONAL at every m ≥ 2 (JA-VDIND collapse; ⊇ (R-coll)/JA-BOX-2 at m ≥ 3) — **NO unconditional stratum above m = 1** (r1, F1) — and required at BOTH f and R. **No key perimeter** (a legitimate conditional at any level); the instrument's own m ≤ qcap cut is disclosed with off-perimeter rows 0. The **v = 0 branch is read-at-target only and machine UNEXERCISED**. [RMG]: (C-READ), (C-W_R), the complete Ĉ_m clause list, L-CELL(i)/(ii) = (B-READ), on [RMG]'s scope. [rows 21–22] |
| **JB-BOX-1** (blueprint J-B(iii) carry placement) | CORRECTED (frame conflation; both frames displayed). Inherits JB-CREAD's (VD-m) ∩ {v ≠ 0} fence; its machine leg is the teeth family MJB-CREAD, where the carry-bearing reading must FAIL — and does, on all 22 designated samples over 14 towers. [row 23] |

**[r3 — SUPERSEDED r0/r1/r2 §7.2 table, retained for the record. NOT
authoritative.]**

| claim | statement | grade |
|---|---|---|
| JB-DEV | expansion identity: same division; byte clause on the byte law; three-layer coefficient correspondence; cross-key fence | PROVED (attempt grade 0/2), consumptions at their own grades **[r2, G2-1 — the perimeter carried onto this row, where r1 left it in the body: (i)/(ii)/(iv) at every q ≥ 0 ((ii) on the byte-equal chain THROUGH q); clause (iii)'s three layers ONLY on the SHARED-KEY perimeter 0 ≤ q ≤ qcap = min(n, shared_upto+1) (§1) — off it (VAL) is FALSE, not merely unproved — and the (GRID) layer additionally carries JA-GRID(a)'s UNDISCHARGED u ≥ 0 proviso (r2, G2-5)]** |
| JB-AFF | affine ordinate maps preserve hulls/vertices | PROVED (two lines) |
| JB-VTX | window/development polygon = Σ_q(N_{q+1}(f)) vertex-for-vertex; slope/length translation; min/read ties; window clause | PROVED (attempt grade), at the W2-C1 representative ~~(no perimeter)~~ **[r2, G2-1 — AND ONLY ON THE SHARED-KEY PERIMETER 0 ≤ q ≤ qcap = min(n, shared_upto+1) (§1), as the theorem and the §3 grade line have said since r1: off it clause (a)'s JA-VAL input is unavailable and (a) is FALSE, not merely unproved; the (d) print-side min ties are machine-restricted further to q ≤ shared_upto. Clause (e) is at f = Φ_{q+1}^har (r1, G-4), not at the theorem's quantified f]** |
| JB-TREE | the [RMG] tree computes the classifier's division; edge = division step; cells = expansion slots; λ_E face = polygon bookkeeping | PROVED (attempt grade) on T-scope(m), g_m = 1; LED-Λ cited at attempt grade **[r2, G2-1 re-grep — and clauses (iii)/(iv) only at levels m ≤ qcap (§1), since they consume JA-VAL, which J-A grades on the shared-key perimeter; (i)/(ii) are perimeter-free. The print-key machine evidence for (i) is §7.4's post-seal walker, on base rows only (r1, G-1; r2, G2-2/G2-3)]** |
| JB-EPS | ε-cocycle collapse t(V+V′) − t(V) − t(V′) = ε′ | PROVED, unconditional |
| JB-CREAD | (C-READ) transport: ρ_m(R) = c_m·ρ_m(f), carry-free in print coordinates | PROVED on the (VD-m) perimeter ∩ {v ≠ 0} (~~uncond. m ≤ 2~~ **[r1, F1] uncond. m ≤ 1 ONLY; CONDITIONAL at every m ≥ 2 (JA-VDIND collapse; ⊇ (R-coll)/JA-BOX-2 at m ≥ 3) — no unconditional stratum above m = 1**) |
| JB-BOX-1 | blueprint J-B(iii) carry placement | CORRECTED (frame conflation; both frames displayed) |

### 7.3 Consequence display and dependency line

**[r3, STEP 2 — SURFACE 13 of 14, REGENERATED FROM §0M. What J-B supplies (at
attempt grade, acceptance counter 0/2, hostile passes owed), stated so that a
downstream unit reading ONLY this display inherits every fence:**

* **W-3 = both halves of the identity (expansion + polygon, shear explicit) —
  full in CONTENT, not full in q.** The polygon half (JB-VTX (a)/(b)/(c) and
  the three keyed min ties) and the (VAL)/(GRID) layers of the expansion half
  hold on the **SHARED-KEY PERIMETER `P<q` (0 ≤ q ≤ qcap = min(n,
  shared_upto+1))**; off it JB-VTX(a) and JB-DEV(iii)(VAL) are **FALSE**, not
  merely unproved. JB-DEV(i)/(ii)/(iv) hold at every q ≥ 0, with (ii) on the
  **BYTE-EQUAL CHAIN THROUGH q**. **JB-DEV(iii)(RES) holds only on the
  BYTE-EQUAL CHAIN THROUGH q (`P≤q`) — r3/F-4, one level deeper than r2's
  display said — plus JA-RES's own per-digit proviso at m = q+1 ≥ 3.** TWO
  sub-clauses ride JA-GRID(a)'s **UNDISCHARGED u ≥ 0 proviso**: the (GRID)
  layer inside JB-DEV(iii) **and the grid/attained-abscissa content of
  JB-VTX(d) — the polygon half, which r2's display omitted (r3/F-1)**; that
  same JB-VTX(d4) content is also the one sub-clause with **no machine leg**
  (r3/F-3). JB-VTX(e) is at f = Φ_{q+1}^har only (r1, G-4). [§0M rows 1–13]
* **W-5 on [RMG]'s scope (T-scope(m), g_m = 1), with two further fences.**
  (ii) the tree/division correspondence with LED-Λ as the bookkeeping, at
  attempt grade — **(i)/(ii) of §4 perimeter-free, but §4(iii)/(iv) only at
  levels m ≤ qcap, since they consume JA-VAL (r3/F-1B)**, and §4(iv)'s (C-W_Q)
  clause has no machine leg. (iii) the (C-READ) transport in both frames, on
  the **(VD-m) perimeter ∩ {v ≠ 0}**: free of extra hypotheses at **m = 1
  only** (r1, F1 — conditional at every m ≥ 2, and (VD-m) is needed at BOTH f
  and R), with the v = 0 branch a read-at-target statement only and machine
  unexercised. LEMMA JB-EPS is unconditional and its §5 instance is licensed by
  [RMG]'s restored w_m(Ĉ_m) = γ_{m+1} (r3/F-5). [§0M rows 14–23]

**]**

**[r3 — SUPERSEDED r0/r2 consequence display, retained for the record. NOT
authoritative; its defects are F-1 (the proviso attached to the expansion half
only) and F-4 ((RES) at the wrong perimeter).]**

**What J-B now supplies (at attempt grade, hostile passes owed):** the
blueprint's ~~W-3 in full (expansion + polygon identities, shear explicit);
W-5 in full on [RMG]'s scope ((ii) the tree/division correspondence with
LED-Λ as bookkeeping, (iii) the (C-READ) transport in both frames).~~
**[r2, G2-1 — BOTH "in full"s SCOPED; r1
narrowed the quantifiers in the body and left this display at the pre-G-9
perimeter, which is what a downstream unit reads. Corrected:

  * **W-3 = both halves of the identity (expansion + polygon, shear
    explicit), on the SHARED-KEY PERIMETER 0 ≤ q ≤ qcap = min(n,
    shared_upto+1) (§1)** — full in CONTENT (nothing of W-3's two halves is
    missing), NOT full in q: off the perimeter JB-VTX(a) and JB-DEV(iii) are
    FALSE, not merely unproved. JB-DEV(i)/(ii)/(iv) do hold at every q ≥ 0.
    The (GRID) layer inside JB-DEV(iii) rides JA-GRID(a)'s undischarged u ≥ 0
    proviso (r2, G2-5), and JB-VTX(e) is at f = Φ_{q+1}^har only (r1, G-4).
  * **W-5 on [RMG]'s scope (T-scope(m), g_m = 1), and for (iii) additionally
    on the (VD-m) perimeter ∩ {v ≠ 0}** — i.e. (ii) the tree/division
    correspondence with LED-Λ as bookkeeping at attempt grade, (iii) the
    (C-READ) transport in both frames, free of extra hypotheses at m = 1 only
    (r1, F1: conditional at every m ≥ 2).]**
**NOT supplied:** W-1's uncollapsed all-orders dictionary (JA-BOX-2),
W-2's grades (consumed), the J-C block W-6..W-9 (no gr claim;
BLOCKED-ON-CARRIER-TIE stands), J-D counts/menus (W-10..W-12), W2-OPEN-1.
The P0 application gate stands.

**[r1, F1 — what the consequence display now says about (C-READ).** W-5(iii)
is supplied WITH the corrected perimeter: the transport ρ_m(R) = c_m·ρ_m(f)
is free of extra hypotheses only at m = 1; at every m ≥ 2 a consumer must
either carry JA-VDIND's collapse condition (⊇ (R-coll) at m ≥ 3) or work on
the machine-scored stratum. Downstream units that read "unconditional at
m ≤ 2" from r0 — the W-5 row, the J-C germ of §5's remark, the weld ledger's
J-B entry — must re-read this line. The GERM itself (ρ_m(R) =
−z_{m+1}·ρ_m(f)) is unchanged in form and unchanged in grade, but inherits
the same conditionality above m = 1.]**

CONSUMES: [RMG] (ACCEPTED) · [ILN]† (accepted) · W-2 + J-A + LED-Λ at
attempt grade (conditionality verbatim) · GMN HigherNewton as literature
(header anchors) through the sealed probe transcription · engine_ext
(standing rule). CONSUMED BY (intended): the J-C block units (W-6..W-9 —
the §5 remark is their semantic germ), the W-10/J-D count units, the weld
campaign ledger at J-B. Acceptance counter 0/2.

### 7.4 [r1] POST-SEAL SUPPLEMENTARY EVIDENCE — outside the sealed battery

Both instruments below were written AFTER the JB-PE1 verdict (85a8dc9). They
are **evidence for a repair, not preregistered predictions of the sealed
battery**, and they are reported separately for exactly that reason. The
sealed runner and its JSON are byte-untouched by this round. **[r2 — a THIRD
instrument, leg (C), was added in repair round r2 against JB-PE2's G2-2; the
same disclaimer applies to it, and the sealed runner plus both r1 instruments
are byte-untouched by r2 (md5s in the front-matter block).]**

**(A) Level-keyed boundary census — `grt_jb_r1_levelcensus.py`** (read-only;
imports the sealed runner verbatim and replays `jb_cread`'s own control flow,
recording the level m and the failure side of every boundary row instead of
the per-tower aggregate the sealed JSON keeps). Output committed as
`grt_jb_r1_levelcensus_output.txt`. Result on the 16-tower roster:

    m=1  SCORED    45          m=2  SCORED     8        m=3  SCORED   3
                               m=2  BOUNDARY  10        m=3  BOUNDARY 3
    boundary per (tower, m):  T3A m=2: 3 · T3B m=2: 3 · T3C m=2: 1 ·
                              T3D m=2: 3 · I4B m=3: 3
    reasons: R EVAL-FALSE 10, f EVAL-FALSE 3, evaluator SCOPE-OUTS 0
    JSON cross-check: roster boundary 13 + chamber 8 = 21 = the sealed
    `JB-CREAD-BOUNDARY` census field

This is F1's factual core: **10 of the 13 roster boundary rows are
machine-evaluated FALSE instances of (VD-2)**, i.e. inside the stratum r0
advertised as unconditional, and none of the 13 is an evaluator scope-out.

**(B) Independent print-key tree walker — `grt_jb_printwalk.py`**, with its
own mini two-commit seal (prereg comment block + the script committed BEFORE
any full run; verdict below transcribed from the committed
`grt_jb_printwalk_output.txt` / `_results.json`). It answers G-1: the sealed
JB-TREE leg's "print key" family is one `fresh_divmod` re-executed on equal
arguments, so the print-key reading was never independently checked, and never
checked at all off the byte-equal set. The walker takes every key from the
print chain (`GmnLeg.phi`), extracts the correction digits by DIVIDING PRINT
KEYS (the print-side reading of (ID-(i+1))) instead of from
realize(ε^{−1}ψ), builds Ĉ_m^cls = φ_{m+2} − φ_{m+1}^{e_m}, divides by the
print key with its own Horner/synthetic implementation certified per call by
reassembly + degree bound, and never imports the sealed runner.

Mini-seal record: script sealed UNRUN at r1 commit 1 `4c97649`, verdict
appended at r1 commit 2, and the script's md5
`f53e23e8d1c79f084a1e34eee857e37c` is identical at both commits (checked with
`git show <commit>:…`), i.e. it was not touched between its preregistration
and its run.

~~**VERDICT (r1 commit 2, transcribed from `grt_jb_printwalk_output.txt`;
exit 0, elapsed 0.1 s, 458 samples, seal commit 4c97649):
ALL FIVE FAMILIES GREEN — the print-key tree identity HOLDS at print keys,
including on every junction the sealed battery left unchecked.**~~

**[r2, G2-3 + G2-7 — THE VERDICT LINE, RESTATED. Two defects in the struck
line. (1) "every junction the sealed battery left unchecked" is FALSE and is an
escalation of the script's own wording: `grt_jb_printwalk.py` prints
"including **off the byte-equal set**", and the sealed `tree` block has EIGHT
`byteeq: false` rows, not four — the four BASE rows the walker does reach
(T3A m=2, T3C m=2, T3D m=2, T3E m=2; 3 walks each = 12) AND four CHAMBER rows
it does not (`T3A/tw`, `T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2; 2 walks each =
8), because the walker's `main()` iterates `GWP.TOWERS` + `GWP.QO_SHAPES` +
`GJA.D0_SPECS` and builds NO chambers. (2) "458 samples" is the script's
`TOTAL samples` = `sum(COUNTS.values())`, which adds three bookkeeping counters
(`PW-UNEQUAL-WALKS` 12, `PW-CHAIN-DIVERGENT` 12, `PW-XFRAME-AGREE` 72) to the
five law families (38 + 84 + 84 + 84 + 72 = 362). CORRECTED VERDICT:**

**VERDICT (r1 commit 2 artifacts `grt_jb_printwalk_output.txt` /
`_results.json`, re-stated in r2; exit 0, elapsed 0.1 s; 362 LAW samples
(+ 96 coverage-counter increments = the 458 the script prints as its TOTAL);
seal commit 4c97649): ALL FIVE FAMILIES GREEN — the print-key tree identity
HOLDS at print keys, INCLUDING OFF THE BYTE-EQUAL SET on the 12 base-row walks
at byte-unequal junctions (T3A/T3C/T3D/T3E at m = 2), which the sealed
battery's print-key leg never ran. STILL PRINT-UNCHECKED, by both instruments:
the 8 walks on the four byte-unequal CHAMBER rows `T3A/tw`, `T3C/tw`,
`T3D/tw`, `T3E/tw` at m = 2 (sealed leg: `byteeq` false ⇒ no print-key check;
walker: no chambers built). Also unreached by the walker, and NOT part of any
print-key claim: everything the sealed battery scores off the tree families
(no (VD-m)/§5 content, r1's own fence below).**

| family | claim keyed | pred | obs | samples | verdict |
|---|---|---|---|---|---|
| PW-ID | print (ID-(i+1)) read off the print chain: digit 1 at abscissa P_i, digits only at e_i·k (k < g_i), nothing off-grid | 0 | 0 | 38 | GREEN |
| PW-WALK | print E1-priority walk terminates under the cap; every R-leaf reduced (j_l ≤ P_l − 1) | 0 | 0 | 84 | GREEN |
| PW-REASM | signed reassembly Σleaves + (Σexits)·φ_{m+1}^cls = f·Ĉ_m^cls in O[x] | 0 | 0 | 84 | GREEN |
| PW-DIV | tree pair == this script's own certified print-key division (+ the engine's `divmod_monic` as a third leg) | 0 | 0 | 84 | GREEN |
| PW-XFRAME | leg B: on chain-byte-equal rows, the PRINT-keyed tree on f·Ĉ_m^har == the harness-key division | 0 | 0 | ~~72~~ **[r2, G2-2]** 72 = **45 cross-frame + 27 DEGENERATE (vacuous)** | GREEN (45 carry content) |

    COVERAGE  leg-A print-key walks 84 (predicted 79)
              at byte-UNEQUAL junctions 12 (predicted 12 — EXACT)
              leg B fired 72 (predicted 67), agreed 72
                    [r2, G2-2: of which 45 cross-frame, 27 degenerate]
    the 12 byte-unequal walks are exactly the sealed BASE rows with
              byteeq = false  [r2, G2-3: "base" added — the four /tw CHAMBER
              rows are byteeq = false too and are UNREACHED, 8 walks]:
              T3A m=2 (3) · T3C m=2 (3) · T3D m=2 (3) · T3E m=2 (3)
    I4C: no print-eligible reduction level, so no rows — the same scope fence
              the sealed battery reports, reached from the print side

**Honest prediction accounting.** The five LAW predictions hit exactly (0
violations each). The two COVERAGE counts came in 5 HIGH (84 not 79; leg B 72
not 67) — a mis-prediction on my side, in the direction of MORE evidence, with
a fully identified cause: the sealed runner runs its QO and d₀ legs with
`small=True` (2 samples per row), while this walker uses the full 3-sample pool
uniformly, giving +1 walk on the single QO tree row and +4 on the four d₀ rows.
Every other row matches walk-for-walk, and the number that G-1 turns on — the
12 walks at byte-unequal junctions, which the sealed battery's print-key leg
never ran — hit its prediction exactly and is GREEN. **No disagreement with
the tree identity was found anywhere** (had there been one, the script prints
both polynomials' coefficient lists and exits nonzero; the DISAGREEMENT
DISCIPLINE paragraph of its docstring is the standing commitment).

**[r2, G2-2 — MANDATORY DISCLOSURE: PW-XFRAME IS VACUOUS ON 27 OF ITS 72
WALKS, and the defect is exactly the one PE1's G-1 charged against the SEALED
runner's print-key leg — reproduced inside the instrument written to repair
it.** The gate is `chain_eq` alone (`grt_jb_printwalk.py` L374–376). Now
`chain_eq` = (`T.Phi[j] == G.phi[j+1]` for all j ≤ m) already forces the leg-B
DIVISOR `T.Phi[m]` to be byte-equal to the print key `G.phi[m+1]`; so on the
sub-family where the MULTIPLICAND is byte-equal too (`chat_eq`, i.e.
Ĉ_m^cls == Ĉ_m^har) leg B calls `pwalk` and `my_divmod` on arguments that are
BYTE-IDENTICAL to leg A's PW-DIV call, and both are pure deterministic
functions of those arguments: PW-XFRAME cannot fail there unless PW-DIV already
did. Counted from the committed `grt_jb_printwalk_results.json`, the rows with
`chain_eq: true` AND `chat_eq: true` are

    Zp,p=3,T2B|m=1 · Zp,p=2,T2E|m=1 · Fpt,p=3,T2F|m=1 · Zp,p=3,T3B|m=1 ·
    Zp,p=3,T3F|m=1 · Zp,p=2,I4A|m=1 · Zp,p=2,I4A|m=3 · Zp,p=3,I4B|m=1 ·
    QO:x4+4x+4/Q2|m=1                                   — 9 rows × 3 = 27 walks

so **the cross-frame evidence rests on the 45 remaining walks** (15 rows,
`chain_eq` ∧ ¬`chat_eq`), where the harness multiplicand Ĉ_m^har is a
genuinely different polynomial from the print's Ĉ_m^cls and the print-keyed
tree is therefore doing work the print frame does not supply; **the 27
degenerate walks are VACUOUS for cross-frame purposes** and must not be counted
as cross-frame evidence. How it happened, stated plainly: the file's own smoke
disclosure records that the FIRST draft gated on (chain byte-equal) AND
(Ĉ^cls == Ĉ^har) and fired on zero rows; the fix DROPPED the `chat_eq`
conjunct where it should have NEGATED it, which admits the vacuous subset
instead of excluding it. Unaffected: LEG A (84 walks, PW-ID/WALK/REASM/DIV, all
five law predictions 0/0) — that is the evidence which actually closes G-1's
substance on the base rows, and none of it is degenerate (its divisor is the
print key by construction and its multiplicand is print-side). Also unaffected:
every count above; only the READING of PW-XFRAME's 72 changes. The corrected
leg is (C) below.]**

**What this does and does not buy.** It buys: the tree/division
correspondence of JB-TREE(i) now has genuinely print-keyed machine evidence,
decorrelated in keys (print chain), in correction digits (extracted by
dividing print keys, never via realize(ε^{−1}ψ)), in the divisor, and in the
division code; and it buys the 12-walk off-byte-equal stratum the sealed leg
could not reach. It does NOT buy: any change of grade (this is post-seal
evidence, and JB-TREE stays PROVED at attempt grade on [RMG]'s scope), any
claim about chambers (the walker runs the base rows only **[r2, G2-3 — with
the price named: the 8 walks on the four byte-unequal chamber rows `T3A/tw`,
`T3C/tw`, `T3D/tw`, `T3E/tw` at m = 2 are print-unchecked by BOTH
instruments]**), and nothing about
(VD-m) or §5 (a different family entirely). **[r2, G2-2 — and it does not buy
27 of PW-XFRAME's 72 walks: those are re-executions of PW-DIV on byte-identical
arguments; the cross-frame content is the other 45, see the disclosure above
and leg (C).]**

**[r2] (C) THE CROSS-FRAME GATE REPAIR — `grt_jb_printwalk2.py`** (post-seal,
r2's own instrument, with its own mini two-commit seal: the script with its
prereg block committed UNRUN at r2 commit 1 `67bf0c4`, md5
`6c6318f7fc6570a2d454389b38441329`; output/JSON committed at r2 commit 2 and
the verdict below transcribed from them). It re-gates the cross-frame family on
**`chain_eq` AND NOT `chat_eq`** and replaces the degenerate re-execution by a
MECHANICAL DEGENERACY CERTIFICATE (byte-identity of the whole argument tuple:
f·Ĉ^har == f·Ĉ^cls and Φ_m^har == φ_{m+1}^cls), so nothing is re-run where
re-running is vacuous. **Disclosed limitation, stated in the script's own
docstring: this is a GATE REPAIR, not a decorrelated second instrument** — it
imports the byte-frozen r1 walker and reuses its print-side machinery
(`print_corr`/`pcells`/`plnorm`/`pwalk`/`my_divmod`/`cdivmod`/`print_elig`)
precisely so that the ONLY difference from the r1 run is the gate and the
census; it inherits the r1 walker's independence properties and adds nothing to
them. All predictions were read off the committed r1 JSON and are on record
before the run (the blind content is the verdict per family).

**VERDICT (r2 commit 2, transcribed from `grt_jb_printwalk2_output.txt` /
`_results.json`; exit 0, elapsed 0.1 s, 100 law samples, seal commit 67bf0c4):
ALL THREE FAMILIES GREEN, EVERY SAMPLE COUNT ON ITS PREDICTION.**

| family | claim keyed | pred | obs | samples (pred) | verdict |
|---|---|---|---|---|---|
| PW2-XFRAME | HONEST cross-frame (`chain_eq` ∧ ¬`chat_eq`): print-keyed tree on f·Ĉ_m^har == harness-key division, + a NON-DEGENERACY certificate per sample (f·Ĉ^har ≠ f·Ĉ^cls) | 0 | 0 | 45 (45) | GREEN, agreed 45/45 |
| PW2-DEGEN | the complement (`chain_eq` ∧ `chat_eq`): degeneracy CERTIFIED, comparison NOT re-run | 0 | 0 | 27 (27) | GREEN — all 27 confirmed vacuous |
| PW2-RECON | row-for-row reconciliation against the committed r1 JSON (`chain_eq`/`chat_eq`/walks per row; 45+27+12 = 84 = r1's leg-A count) | 0 | 0 | 28 rows (28) | GREEN |

    CENSUS  cross-frame walks 45 over 15 rows (predicted 45) — agreed 45
            DEGENERATE walks   27 over  9 rows (predicted 27) — certified
            chain-divergent    12 over  4 rows (predicted 12) — leg B not
                               claimable (the harness divisor is a different
                               polynomial): T3A m=2, T3C m=2, T3D m=2,
                               T3E m=2 — i.e. exactly the four byte-unequal
                               base rows, where leg A carries the evidence

**NO DISAGREEMENT with the r1 walker anywhere**: every row's `chain_eq`,
`chat_eq` and walk count reproduced, and r1's advertised 72 PW-XFRAME samples
decompose exactly as 45 + 27. **What (C) buys:** the cross-frame claim now
rests on 45 walks each carrying a machine certificate that the multiplicand
genuinely differs between the frames (the positive non-degeneracy leg the r1
walker lacked), and ~~the vacuity of the other 27 is machine-established rather
than argued~~ **[r3, F-6(b) — SOFTENED BY EXACTLY ONE STEP, which is what the
certificate does and does not establish: what `PW2-DEGEN` establishes
MECHANICALLY is the BYTE-IDENTITY of the whole leg-B argument tuple
(`fCh == fC` and `div_har == key`, 27/27); the step from byte-identity to
vacuity is the PURITY of `pwalk`/`my_divmod` as deterministic functions of
those arguments, which is ARGUED in the r2 block and not machine-checked. Read:
**the byte-identity of the argument tuple is machine-certified on all 27, and
their vacuity follows from purity**]**. **What it does not buy:** no new decorrelation (same machinery, by
design), no grade change, still no chambers, and still nothing at the 12
chain-divergent walks (leg B is not claimable there) nor at the 8 unreached
byte-unequal chamber walks (G2-3).

— J-B COMPOSER unit, campaign date 2026-08-08 (wallclock 2026-08-04);
**[r1] repaired 2026-08-08 campaign (wallclock 2026-08-05) against JB-PE1;
acceptance counter still 0/2.** **[r2] repaired again 2026-08-08 campaign
(wallclock 2026-08-05) against JB-PE2 (0 CRITICAL + 7 gaps): grade surfaces
carried (G2-1), the walker's 27/45 cross-frame degeneracy DISCLOSED (G2-2) with
a corrected supplementary leg §7.4(C), the coverage over-claim and the refuted
m = 2 mechanism struck (G2-3/G2-4), the u ≥ 0 "discharge" RETRACTED (G2-5), the
perimeter defined once (G2-6), the record figures decomposed (G2-7). ~~Arc:
PE1 (1C+9G) → r1 → PE2 (0C+7G) → r2 → **JB-PE3 = the next acceptance attempt**;
acceptance counter still **0/2**.~~**

**[r3] repaired a THIRD time, 2026-08-08 campaign (wallclock 2026-08-05),
against JB-PE3 (0 CRITICAL + 8 gaps, the first acceptance attempt, which did
not land). THE CONDITIONALITY-MATRIX NORMALIZATION: §0M built (28 claim rows ×
8 proviso columns, filled from the body proofs) and all 14 grade surfaces
REGENERATED from it — grade cap, §2/§3/§4/§5 ∎ Grade lines, the seven §7.2 rows,
§7.3's consequence display, JB-BOX-2's enumeration — which discharges F-1 and
F-1B and retires the per-site sweep genre (JB-BOX-6 carries the standing rule).
Plus: [RMG]'s two dropped Ĉ_m clauses RESTORED verbatim with the γ_{m+1}
lattice-membership derivation displayed, so the JB-EPS citation is licensed
(F-5); JB-DEV's "both engines" leg RECLASSIFIED as SAME-COMPUTATION with an
unreachable violation (F-2); "all four min/read ties" corrected to THREE, the
fourth named machine-unkeyed and proviso-riding (F-3); §2(iii)(RES) re-fenced
to the BYTE-EQUAL CHAIN THROUGH q (F-4 — the one mathematical movement, toward
more conditionality); the sufficient-vs-equivalent conflation fixed at both
sites and §7.4(C) softened by the purity step (F-6); P_i := e_i·g_i defined at
first use with [RMG] S0.1 added to the consumption list (F-7). **No §2–§5
identity moved; all four instruments byte-frozen; note-only.** Arc:
PE1 (1C+9G) → r1 → PE2 (0C+7G) → r2 → PE3 (0C+8G) → r3 → **JB-PE4 = the next
acceptance attempt**; acceptance counter still **0/2**.**
