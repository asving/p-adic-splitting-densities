# GRTJA pass PE2 — second hostile pass on GRTJA_PROOF_2026-08-08.md (post-r1)

**Verifier:** JA-PE2 (fresh hostile Fable context; fixes nothing).
**Dispatch note (filename):** this pass was dispatched as "pass PE1 — the
FIRST hostile pass of this note's acceptance arc" with report path
`GRTJA_passPE1_report.md`. That path already holds the COMMITTED 2026-08-04
JA-PE1 report (commit 5e70442), which the note's §8 cites by name as the
record of the five repaired gaps. Overwriting it would falsify the note's own
provenance surface, so this report is filed as `GRTJA_passPE2_report.md`; the
collision is graded below (FINDING 4, arc-accounting species). By the note's
own §8 this is round 2 of the arc (the round §8 planned as "the Codex leg").

**Target pin:** note at HEAD 39e1eec, md5 `c0043fb3` == `git show ce0469a:`
(the JA-r1 repair commit; ZERO commits touch the note or any J-A artifact
after ce0469a — verified by `git log ce0469a..HEAD -- <files>` = empty).
Artifacts at HEAD == their seal commits, verified via git: runner
`grt_ja_checks.py` md5 `5972d412` == @696eae8 (commit 1, SEAL);
`grt_ja_checks_output.txt` `0d6d0522` and `grt_ja_checks_results.json`
`13ab52ab` == @1cbf8ca (commit 2, VERDICT). Seal discipline confirmed:
696eae8 = runner + prereg only; 1cbf8ca = outputs + verdict. (Worktree note:
`verification/openmath/grt_w2_checks_results.json` carries a 1-line
parallel-agent modification at report time — outside J-A's artifact set,
untouched by me.)

**Charge executed:** (1) the per-slot character-gauge law re-derived from
scratch + fresh machine re-check; (2) JA-VDIND / (VD-m) / (R-coll) vs the
accepted JB/WM fences, with a constructed-witness probe; (3) the [JA-r1]
u ≥ 0 proviso's origin vs JB's accepted consumption; (4) evidence-class
(IND/SAME/NONE) audit of all 17 machine families against the runner source;
(5) notation-before-use + citation sweep, incl. hostile re-verification of
the r1 repair's own tex anchors. Machine leg re-run in a /tmp sandbox
(committed artifacts untouched).

---

## 1. Machine leg — RE-RUN BIT-IDENTICAL, censuses independently recounted

Re-ran `grt_ja_checks.py` (full battery) in a /tmp copy: **exit 0, all 17
families GREEN, TOTAL samples 10,311, 0 violations, boundary 16, CK-BPREF
26**; stdout differs from the committed output ONLY at wall-clock/timing
lines; regenerated JSON identical to the committed one on every key except
`elapsed_s` (5.5 vs 7.4). Independent recounts from the COMMITTED JSON:

* CK-BPREF 26 = 22 roster hits on exactly **10 rows** (T2A 1, T2C 1, T2D 1,
  T2G 1, T3A 2, T3C 2, T3D 2, T3E 4, T3F 1, I4C 7) + 4 d₀ hits (JD5A/JD3A/
  JD3B/JD3C, one each) — the r1 GAP-2 correction ("12 → 10") is EXACT.
* Boundary 16 = T3B main 4 + transported 3, I4B main 5 + transported 4;
  every other row boundary 0 — §7.1's census sentence exact.
* Designated BPREF rows T2A/T3A/T3E fire (1/2/4); teeth catches 8/9/8
  (MJ-EPS on T2A/T2B/T2D), 11/11 (MJ-VAL on T2A/T2C), 12/18 (MJ-GRID on
  T2A/T2B) — §7.1's teeth row exact ("3/2/2 rows").
* Family samples column matches the JSON cell-for-cell (1/111/1,132/872/
  1,744/3,248/340/443/443/26/444/1,452/5/4/3/2/2). The 10,311 headline is
  the runner's own printed total (family notes + 16 boundary + 23
  transported-BPREF notes) — faithful artifact quote.
* JA-QO: `pari_full` recorded for all 5 shapes in the JSON ((4,1)×3, (2,2),
  (3,1)) — the PARI leg genuinely ran; §7.1's "PARI ties" is backed.
* TW-INST: exactly 20 ledger entries (16 roster + 4 d₀) — §7.1's "all 20
  ledgers" exact.

## 2. Charge (1): the per-slot character-gauge law — RE-DERIVED EXACT

From the note's own pinned definitions: proviso (VD-(m−1)) at digit a_i
gives R_{m−1}(a_i)(z) = z^{−τ_{m−1}(a_i)}·C_i, so c_i =
z^{t(i)−τ_{m−1}(a_i)}·C_i; with u_i = β_i + i·W_{m−1} (JA-VAL at the
on-line digit + JA-PIN clause 7, v_m(φ_m) = W_{m−1}),
t(i) − τ_{m−1}(a_i) = −ℓ_{m−2}(u_i − β_i)/e_{m−2} = −ℓ_{m−2}·i·W_{m−1}/e_{m−2}
= −i·A_{m−1} since W_{m−1} = e_{m−2}g_{m−2}γ_{m−1} and A_{m−1} =
ℓ_{m−2}g_{m−2}γ_{m−1} (§1's displays). **c_i = z_{m−1}^{−i·A_{m−1}}·C_i is
exactly right**; m = 2 unconditionality = (VD-1) = W2-L3. The print-side
transcription (Def `t(i)` tex 1431 under P-index: ℓ_{m−1}^GMN = ℓ_{m−2}^har)
re-checked at source. JA-VDIND forward re-derived (τ_m(A) − ν = (s−ℓβ)/e =
−t_m(β), ε_m(β) = z^{−t_m(β)} by JA-EPS). §4's ORB-RES law re-derived
(t(i) ↦ t(i) − κu_i under ℓ ↦ ℓ+κe; u_i = u₀ − jh on the side ⟹ the
z^{−κu₀}·(z^{κh})^j rescale — the runner's check is this law verbatim, with
G.ell genuinely shifted). FRESH machine leg (my probe, /tmp): the per-slot
law re-verified on **396 scored roster samples, 0 violations** (main roster
only; decorrelated instance count from the runner's 443 which includes
QO/d₀). JA-EPS re-derived from ℓh + ℓ′e = 1 (ε-exponent ℓ′s − ℓu =
(s − ℓβ)/e = −t_m(β)); the r1 SIGN-CONVENTION display verified against the
print (below).

## 3. Charge (2): JA-VDIND / (VD-m) / (R-coll) — THE CRITICAL FINDING

The accepted JB matrix (col (c), §0M; quoted at WM-FENCE (b)) fences the
evaluated dictionary correctly: "(VD-m) … unconditional at m ≤ 1 ONLY; at
every m ≥ 2 a HYPOTHESIS (JA-VDIND's ABSOLUTE character-triviality
z_{m−1}^{i·A_{m−1}} = 1 at every attained abscissa)". The JA note's
JA-VDIND corollary states the same condition and is TRUE (forward direction
re-derived; CK-VDM 443/0 stands; all failure witnesses below have visible
root character — none contradicts JA-VDIND).

The defect is the **(R-coll) display's conclusion** (§3.4): the definition
quantifies the collapse condition over "every level-q instance of the
proviso, **2 ≤ q ≤ m−1**" — i.e. over the recursion nodes BELOW the root —
and WM's accepted WM-FENCE (a) reads it the same way ("(R-coll) at level m
is its every-recursion-node form (2 ≤ q ≤ m−1)"). The level-m (root)
instance of the JA-VDIND condition — z_{m−1}-triviality on A's OWN attained
set — is OUTSIDE the range. From that definition, the displayed conclusion
"On (R-coll): the per-slot law **and (VD-m)** hold at all levels up to m by
induction with base (VD-1)" does not follow at the top level, and is FALSE:

**Constructed machine witnesses (probe in /tmp over the note's own engines,
sample pools, and `vd_eval`):** among roster samples whose per-digit proviso
HOLDS at every attained digit, **(VD-m) evaluates FALSE on 66 instances**
(58 at m = 2, 8 at m = 3, towers incl. T2A/T2D/T2F/T3B/T3D/T3F/I4B/I4C),
every one with the ROOT character visible. Refined at m = 3: **8 instances
ON (R-coll) as literally defined** — every level-2 recursion-node character
trivial (the q = 2 collapse condition, the whole stated range) — with
**(VD-3) FALSE**, e.g. T3B (deg A = 6, attained {1}, A₂ = 7), T3F (deg 12,
attained {0,2}, A₂ = 13), I4B (deg 6, attained {1}, A₂ = 13). At m = 2 the
stated range [2, m−1] is EMPTY, making (R-coll) vacuously all-inclusive
while (VD-2) is false on 58 pool instances (consistent with the note's own
16 boundary records, which are exactly (VD-2)/(VD-3) per-digit failures, and
with accepted JB's "(VD-2) FALSE on 10 of its 13 roster boundary rows").

Consequence for §6: JA-BOX-2's positive clause "At m ≥ 3 the
scalar/**evaluated** forms are PROVED only on (R-coll)" inherits the same
defect for the evaluated form — it is NOT proved (and is false) on (R-coll)
as defined. The per-slot-law half of both displays is TRUE as written (my
witnesses all satisfy it), and §7.2's grade rows (JA-RES "unconditional on
(R-coll)" = the PER-SLOT law; JA-VDIND "forward; converse unsealed") are
correct. The cure is a one-line quantifier extension: the collapse
condition must run THROUGH level m (add the root/q = m instance of the
JA-VDIND condition), after which both displays are true, CK-VDM keys them,
and they coincide with accepted JB's operative fence. Recorded relation
(not graded — JB/WM are accepted): JB col (c)'s subordinate clause "at
m ≥ 3 implied by the per-digit proviso / (R-coll) of JA-BOX-2" and WM's
"(2 ≤ q ≤ m−1)" gloss inherited the same root-exclusive reading from this
note; JB's OPERATIVE fence (root triviality a hypothesis at every m ≥ 2) is
unaffected — nothing accepted consumed the false clause.

## 4. Charge (3): the [JA-r1] u ≥ 0 proviso — object identical, discharge gloss over-broad

Origin verified at the print: Prop `construct`'s hypothesis "Let V be an
integer, V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})" is tex 1167 (anchor "1167–1168"
correct); under it u > 0 indeed (W_m = e·g·γ_m ≥ e·h > (e−1)h ≥ s·h — the
implication is real). The r1 counter-instance ((e,h) = (2,3), V = 1 ⟹
u = −1) checks. The proviso OBJECT the note fences — u := (V − s·h)/e ≥ 0
on the quantified (V; e, h) — is byte-identical to what accepted JB's row 4
/ col (b) consumes, and JA's shared-key perimeter (§1, byte-equality at
q ≤ m−1) is IDENTICAL to JB's (a1) "J-A's perimeter instantiated at level
q". So: fenced identically — YES, at the object level.

The defect is the r1 discharge GLOSS: "**the proviso holds at every
consumption site** by the print's own hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})"
(§3.3). Unquantified, this reads as a universal consumer-facing discharge —
and the accepted JB record contradicts that reading at JB's sites: JB r2
explicitly RETRACTED an r1-claimed discharge of this proviso, carried it
UNDISCHARGED, and only narrowed it via JB's OWN §5 lattice theorem (u ≥ 0
proved at V ∈ 𝒲_{q+1}; open residue = membership at the unbounded-degree
quantifier). At JB's consumption sites V = w_{q+1}(f) is a harness weight
for which tex 1167–1168 supplies nothing. The sentence is TRUE scoped to
THIS note's own print-side sites (§3.3(b), where Prop `construct`'s
hypothesis is in force) — it needs that scoping. GAP.

## 5. Charge (4): evidence-class audit (IND / SAME / NONE), runner vs note

Read the runner end-to-end against every machine bracket in the note:

| family | actual evidence class | note's billing | verdict |
|---|---|---|---|
| EXT-GATE | standing-rule re-run | exact | OK |
| JA-PIN | IND fresh legs (fresh Bézout/weights/no-root scan) vs committed + GmnLeg, clauses 2–7 | exact post-r1 (GAP-5a bracket) | OK |
| CK-VAL | SAME-class (two committed/sealed engines, no third leg) | "both engines on the same samples" | OK (honest) |
| CK-EPS | IND (committed T.eps vs fresh geometric integers) | exact | OK |
| ORB-EPS | **DERIVED from CK-EPS** — checks eps·z^{t+κV} == z^{κV} with the SAME committed eps and the SAME fresh t; algebraically equivalent to CK-EPS on the same (m,V) pairs (1,744 = 2×872); no shifted-ℓ recomputation of any print object | "[Machine: ORB-EPS.]" — no independence claim | OBSERVATION (o1) |
| CK-GRID | IND (ℓ-free geometric scan); checks the INTEGER-ORDINATE characterization, not the print T-side object | disclosed in the r1 GAP-4 bracket | OK |
| CK-RES1/CK-RES/CK-VDM | two-engine comparison + IND fresh gauge exponent (fresh_A); proviso machine-evaluated per digit; scored/boundary split = the theorem's own conditionality | exact | OK |
| CK-BPREF | census on scored samples, gauges non-constant ⟹ refutes slot-independent c (attained ⟹ C_i ≠ 0, so no single scalar works) | exact | OK |
| ORB-RES | genuinely IND for the orbit law (G.ell shifted post-construction, rres recomputed) | exact | OK |
| TW-INST | re-instantiation re-runs **JA-PIN/CK-VAL/CK-RES1/CK-RES/CK-VDM only** (runner docstring: "the field-dependent families"); runs on ALL 16 roster + 4 d₀ towers unconditionally | §4: "the full CK battery re-run … every roster tower with a nontrivial transport ledger" | **FINDING 3** |
| JA-QO / JA-D0 | extraction + PARI (JSON-backed) / engine_ext certificate + committed gate + PARI on ℤ_p rows | exact (F_p[[t]] no-PARI = JA-BOX-4) | OK |
| MJ-EPS/VAL/GRID | teeth, designated rows, all caught | exact | OK |

NONE-class inventory (claims with no machine leg, checked for honest
billing): JA-PIN clauses 1/8 (disclosed, r1), JA-MIN (no family bills it),
JA-GRID(a)'s print-side identification (disclosed, r1), §4(i)'s MacLane
caveat display v_{r+1}(φ−φ′) = e_r·v_r(φ) — hand-true (re-derived here and
at PE1) but the bullet's closing "[Machine: TW-INST]" does not cover it
(TW-INST checks re-instantiation, not that display) — observation (o3).

## 6. Charge (5): notation-before-use + citations; r1 anchors hostile-verified

**The r1 repair's tex anchors re-verified at source** (`HigherNewton.tex`):
child prescription φ_j(y) ≡ y^{(ℓ_{r−2}u_j−𝔰_j)/e_{r−2}}c_j(y) at tex
**1201** ("1200–1201" ✓); the old 1213–1218 range is inside the picture
environment (~1204–1220, drawing code) ✓; Def `t(i)` at tex **1431** with
the OPPOSITE sign (s_{r−1}(a) − ℓ_{r−1}v_r(aφ_r^i))/e_{r−1} ✓; Lemma
`enlarge` at tex **1528** with the (𝔰_i − ℓ_{r−1}u_i)/e_{r−1} exponent and
the T(i)-side ("greatest side … nonnegative integer coordinates") ✓
("~1528–1531"/"1528–1541" ✓); `rescoeff` 1447, `defresidual` 1497 with
(s,u) = initial point of the ACTUAL side S at ~1498 ✓ (the r1 gloss
correction is true); Prop `construct` 1166 + hypothesis 1167 ✓; Def-2.12
representative at 1285 ✓; tex 1291 fixes ℓ_r, ℓ′_r with ℓ_rh_r − ℓ′_re_r = 1
and pins NO representative ✓ (JA-BOX-3's premise; note also the print's
Bézout SIGN convention differs from the harness's ℓh + ℓ′e = 1 — the note's
ε-algebra correctly uses its own normalized pair throughout). Blueprint
J-A(ii) "R_{m,λ} = c·R_λ^GMN with c ∈ F^× slot-independent" quoted
correctly at JA-BOX-1 (blueprint S2.1(ii) verbatim). §5's consumption rows
re-verified at source: GRB REV 11 pins 1/2/3 (ǫ₀ ≡ 1 remark; Lemma 4.3
Bézout / family T0 0/23,111; P12 PARI kill-shot) match the note's
three-ways sentence; GD-3 MIN CORE = ord_{ψ̂_hom}(in(f)) = ord_ψ(R_λ(f))
verbatim at the completion tree (the r1 JA-MIN rescope is faithful); GD-5
row and T-F 41,720/7,472 and GD-8 871/0 figures match tree/blueprint rows.

**Notation defects found:** W̃ in §4(ii)'s transport display is UNDEFINED
(FINDING 5; re-derivation of the u_i-expansion fixes W̃ = W_{m−1}: u_i =
(β₀ + s₀W_{m−1}) + j(e_{m−1}W_{m−1} − γ_m), matching the displayed j-part
exactly). Minor unexpanded vocabulary, observation-grade (o2): [ILN]† never
resolved to a filename or as-of commit pin in-note (the 2026-08-06 as-of-pin
standing rule postdates this note's r1; sibling arcs applied it in their own
rounds — owed at this note's next round/fold); "the level-m weight lattice"
(§3.2) and "attained abscissa" (§3.4) used without in-note definition
(consumed [ILN]†/probe vocabulary).

---

## FINDINGS (1 CRITICAL, 3 gaps, 1 minor)

* **FINDING 1 — CRITICAL (§3.4 (R-coll) display; §6 JA-BOX-2 "evaluated").**
  "On (R-coll): the per-slot law and (VD-m) hold at all levels up to m by
  induction with base (VD-1)" is FALSE as the perimeter is defined: the
  collapse quantifier "2 ≤ q ≤ m−1" excludes the level-m (root) instance of
  the JA-VDIND condition, and **8 explicit machine witnesses at m = 3 sit ON
  (R-coll) as defined (all level-2 node characters trivial) with (VD-3)
  FALSE** (T3B/T3F/I4B; e.g. T3B deg 6, attained {1}, A₂ = 7), plus 58
  witnesses at m = 2 where the stated range is empty; every witness has the
  root character visible, so JA-VDIND itself and the per-slot-law half stand
  (fresh 396/0). JA-BOX-2's "the scalar/evaluated forms are PROVED only on
  (R-coll)" inherits the defect for the evaluated form. WM-FENCE (a) reads
  the same root-exclusive range; accepted JB's operative fence (root
  triviality a HYPOTHESIS at every m ≥ 2) is the correct statement and is
  what JB actually consumes — the false clause has no accepted consumer, but
  it seeded JB col (c)'s subordinate "at m ≥ 3 implied by the per-digit
  proviso / (R-coll)" clause (recorded, not graded). CURE (one line): extend
  the collapse condition through level m (include the root's JA-VDIND
  condition), then both displays are true and CK-VDM keys them.
* **FINDING 2 — GAP (§3.3, the [JA-r1] u ≥ 0 gloss).** "the proviso holds at
  EVERY CONSUMPTION SITE by the print's own hypothesis V ≥
  e_{r−1}f_{r−1}v_r(φ_{r−1})" is unquantified and, read consumer-facing, is
  contradicted by the accepted JB record (proviso CARRIED AND UNDISCHARGED;
  JB r2 retracted exactly such a discharge; JB's own §5 lattice theorem +
  open membership residue do the work at JB's sites, where the print
  hypothesis supplies nothing). True scoped to this note's own print-side
  sites; needs that scoping. The proviso OBJECT and perimeter are fenced
  identically to JB's consumption (charge-3 answer: yes at the object level).
* **FINDING 3 — GAP (§4 transported-chamber bullet, machine-coverage
  overstatement — the PE1 GAP-5a species).** "[Machine: TW-INST — the full
  CK battery re-run on the transported instance …, every roster tower with a
  nontrivial transport ledger]": the sealed runner re-runs ONLY
  JA-PIN/CK-VAL/CK-RES1/CK-RES/CK-VDM inside the chamber (its own docstring:
  "the field-dependent families"); CK-EPS, CK-GRID, ORB-EPS, ORB-RES are NOT
  re-run there. Secondary: the runner runs the transport leg on ALL 16
  roster + 4 d₀ towers unconditionally (the §7.1 row's own "all 20 ledgers"),
  not on a nontrivial-ledger subset.
* **FINDING 4 — GAP (arc-accounting surfaces).** The header still says
  "acceptance counter 0/2; no gate fires; **no acceptance arc opened**"
  while §8 (added at r1) records "round 1 of the acceptance arc" with "Arc:
  **0/1** CLEAN" — an internal contradiction at HEAD plus a counter-
  denominator wobble (0/2 at header/§7.3 vs 0/1 at §8). The same confusion
  reached this dispatch ("pass PE1, the FIRST hostile pass of the arc") and
  its report path, which collides with the committed JA-PE1 report that §8
  cites by name — resolved here by filing as passPE2 (this file).
* **FINDING 5 — MINOR (§4(ii)).** The transport display's symbol W̃ is
  undefined (should read W_{m−1}); the exponents are otherwise exact.

**Ungraded observations:** (o1) ORB-EPS is derivationally implied by CK-EPS
(same committed eps, same fresh t; 1,744 = the same 872 pairs twice) — the
note makes no independence claim, but the family-count/samples headline
carries it as a separate family; (o2) [ILN]†/weight-lattice/attained-
abscissa vocabulary unexpanded and unpinned in-note (as-of-pin rule
postdates r1; owed at the next round); (o3) §4(i)'s MacLane caveat display
is machine-unkeyed though the bullet closes "[Machine: TW-INST]" — display
re-derived true by hand here and at PE1; (o4) §8's "round 2 = the Codex leg
(Thursday window)" is superseded by this Fable dispatch — stale plan
surface, not a defect.

**What survived hostile re-derivation (for the record):** JA-PIN clauses
2–7 at the print anchors; all four operator equalities including the
per-slot law and both ORB transport laws, re-derived exactly; the r1
repair's five brackets each verified TRUE at source (anchors, census 10,
JA-MIN rescope, u ≥ 0 proviso + counter-instance, GAP-5a/5b wordings);
JA-BOX-1's refutation shape and 26 witnesses; consumption grades at every
W-2/N-1/GD-5 site unchanged and faithfully quoted; shared-key perimeter
fencing identical to accepted JB's (a1)/(a2) reading; machine bracket
bit-identical with seals intact.

JA-PE2 FINDINGS: 1 critical, 3 gaps, 1 minor
VERDICT: NOT CLEAN (critical present; counter stays 0 clean)
