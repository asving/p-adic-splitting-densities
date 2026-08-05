> **PROVENANCE (orchestrator, 2026-08-05): NOT A SEALED PASS.** The PE1 verifier
> agent died mid-pass in an API auth outage (workflow wt2786c1o, 401 after ~72 tool
> uses) — the machine leg (§A) and content analysis (§B–D) below are complete as
> written, but the verdict (§E) was never composed and no findings list was ever
> returned. This file is archived as evidence only; the sealed PE1 pass is the fresh
> re-run's report at `GRTJB_passPE1_report.md`. Do not cite this file as a pass.

# GRTJB — hostile verification pass PE1 (fresh context)

**Target:** `lean/notes/openmath/GRTJB_PROOF_2026-08-08.md` (J-B tree-junction composer,
attempt grade 0/2). **Runner:** `verification/openmath/grt_jb_checks.py`.
**Charge:** quote-and-classify (CRITICAL ERROR vs JUSTIFICATION GAP), honesty defects,
notation-before-use, citation naming; mandatory machine re-run; two-commit-seal audit.
Verifier fixes NOTHING.

---

## A. Machine leg (mandatory) — PASS, bit-identical

Re-ran `python3 grt_jb_checks.py` from `verification/openmath/` (2026-08-04 wallclock,
this pass). Results:

* **Exit code 0.**
* **All 18 families GREEN, 0 violations, TOTAL samples 6700, elapsed 0.7s** — matches
  the note §7.1 headline ("ALL 18 FAMILIES GREEN, 6,700 samples, 0 violations", 0.7 s)
  exactly.
* Per-family sample counts match the §7.1 table exactly: EXT-GATE 1, JB-DEV 893,
  JB-KEYEQ 25, JB-SHEAR 893, JB-VTX 893, JB-ID 34, JB-TREE 79, JB-LINE 194, JB-EPS 955,
  JB-CM 28, JB-CREAD 79, JB-QO 5, JB-D0 4, TW-JB 2480, MJB-* 3/3/3/3.
* Censuses line: `scored 104 | boundary 21 | v=0 0 | R=0 0 | off-perimeter tree rows 0`
  — matches the note verbatim.
* Regenerated `grt_jb_checks_results.json` is **md5-identical to the committed sealed
  artifact** (0dc4b015ac520d2bb05094329d7754ba); the committed
  `grt_jb_checks_output.txt` matches the re-run line-for-line (including bracket
  timings).
* JSON-level verification of §7.1 sub-claims:
  - "scored 104 (66 roster + 38 chamber)": non-`/tw` tags sum to 66, `/tw` tags to 38. ✓
  - "boundary 21 — ALL on ... T3A, T3B, T3C, T3D, I4B and their transported chambers":
    boundary by tag = T3A 3 + T3A/tw 2 + T3B 3 + T3B/tw 2 + T3C 1 + T3D 3 + T3D/tw 2 +
    I4B 3 + I4B/tw 2 = 21, no other tags. ✓
  - "79 walks (125 with chambers)": trees sum 79 non-/tw, 125 total. ✓
  - byte census: I4A/I4B all-true, T3A/T3C/T3D/T3E false at q=2, I4C false at q=2,3,
    T3B/T3F true through q=2 — matches the note's quoted examples. ✓
  - "22 scored samples with z_m^{ε′} ≠ 1" — teeth total = 22. ✓ BUT the "across 7
    towers" clause FAILS against the sealed JSON: see Finding 1.

## B. Two-commit seal — PASS

* Order: 17adb80 (skeleton, 22:59:21Z) → 5a72b62 (note, 23:04:06Z) → **7f6759d (SEAL,
  23:16:49Z)** → **f5578d0 (VERDICT, 23:17:44Z)**; `git merge-base --is-ancestor`
  confirms seal precedes verdict.
* Runner md5 **55f4911eaddd8524fd91368b30ed71bd** identical at 7f6759d, f5578d0, HEAD,
  and working tree — the runner was sealed at commit 1 and never touched.
* The note's md5 changed between seal and verdict, and `git diff 7f6759d f5578d0` on the
  note touches **only §7.1** (the sealed placeholder + prediction list replaced by the
  verdict table + censuses). §§1–6, 7.2, 7.3 byte-unchanged across the seal. The sealed
  §7.1 placeholder's prediction list matches the runner docstring's preregistered
  predictions family-for-family (18 families incl. 4 teeth).
* Verdict commit adds only the note delta + the two output artifacts.
* The note's "campaign date 2026-08-08 (wallclock 2026-08-04)" is honest against the
  commit timestamps (2026-08-04).

## C. Findings

**Verdict: 0 CRITICAL ERRORS / 5 findings (3 justification gaps, 2 honesty defects), all
minor.** Every load-bearing derivation (JB-EPS algebra, JB-CREAD chain, JB-VTX shear,
JB-AFF, JB-DEV/JB-TREE consumption chains) verified line by line against the cited
sources; machine leg bit-identical; seal clean.

### Finding 1 — HONESTY DEFECT (stale machine figure), §7.1 censuses

> "MJB-CREAD teeth material: 22 scored samples with z_m^{ε′} ≠ 1 **across 7 towers**"

The count 22 is exact (sealed JSON: teeth total = 22). But the sealed JSON spreads them
across **14 distinct rows**, not 7: roster towers T2A, T2B, T2D, T2F, T2G, T3A, T3B,
T3D, T3E, T3F, I4B (11, counting each tower together with its /tw chamber) plus the
d₀-leg rows JD3A, JD3C, JD5A (3). "7 towers" is the SMOKE-record visibility list
("MJB-CREAD visible on T2A/T2D/T2G/T3A/T3D/T3E/I4B", runner docstring), carried into
the verdict section instead of the full-run geography. Direction is conservative (the
full run has WIDER teeth coverage than claimed), so nothing downstream is inflated —
but the verdict-section figure does not describe the sealed artifact it cites.
Classification: honesty defect (stale quote of machine output), minor.

### Finding 2 — JUSTIFICATION GAP (evidential independence overstated), §4 machine bracket + §7.1 JB-TREE row

> "(2) the canonical division by the harness key AND by the print-side key where
> byte-equal" / table: "fresh tree walk == canonical division, harness AND print keys"

Where byte-equal, `tuple(G.phi[m+1]) == Phim`, so `fresh_divmod(T.R, fC,
tuple(G.phi[m+1]))` (runner lines 500–503) is division by the *same byte string* as the
harness check — deterministically the same computation; the print-key comparison can
never fail independently of the harness comparison. There is ONE division reading; the
print-side content is entirely the byte-equality fact itself (which IS independently
contentful: G.phi is grown by the sealed GmnLeg construct/Thm-phir recursion, not
copied — verified, see D1). The "where byte-equal" fence makes this recoverable, but
"harness AND print keys" reads as two independent verifications where the second is
implied by the first plus JB-KEYEQ. Classification: justification gap (evidence
structure/wording), minor; no mathematical content is wrong.

### Finding 3 — JUSTIFICATION GAP (dictionary-tie perimeter not restated), §3 THEOREM JB-VTX (and §2 JB-DEV(iii) by the same mechanism)

> "**THEOREM JB-VTX.** Level q with read (e_q, h_q) defined (0 ≤ q ≤ n) … ∎ Grade:
> PROVED at attempt grade; unconditional GIVEN the representative legitimacy (W-2
> clause 1's perimeter and conditionality ride; …)"

Clause (a)'s proof consumes JA-VAL (digits AND the key: v_{q+1}(φ_{q+1}) = w_qΦ_q) and
clause (d) consumes JA-VAL "one level up". J-A grades JA-VAL "unconditional **on the
shared-key perimeter**". The JB-VTX header quantifies over all 0 ≤ q ≤ n and its grade
line names only the W-2 clause-1 conditionality — the shared-key (first-divergence)
premise of the consumed dictionary ties is not restated. The runner honors the
narrower perimeter exactly (`qcap_of`: "keys shared strictly below q"; the extra
`q <= L` guard on the (d) ties; chambers only via TW-JB re-instantiation, which is
J-A §4's honest transport), so the machine evidence quantifies the narrower statement.
The note's blanket clause "Every consumption is at the source's own grade" arguably
imports the fence, and §1 displays the shared-key perimeter — but the theorem-level
display is incomplete. Classification: justification gap (fence wording), minor.

### Finding 4 — JUSTIFICATION GAP (fence inventory incomplete), §6 JB-BOX-2

> "**JB-BOX-2 (inherited conditionality, quantified).** Every print-residual statement
> rides J-A's boxes verbatim: … and W-2's (C-coll)/recursion split for the byte law.
> …"

The box that purports to quantify the inherited conditionality lists JA-BOX-2,
JA-BOX-3, the W-2 byte-law split, the v-stratum split, and W2-OPEN-1 — but omits
**W-2 clause 1's representative-admissibility perimeter**, the single most load-bearing
inherited conditionality for §§2–4 (JB-DEV(i) legitimacy, JB-VTX's representative,
JB-TREE(i)'s "admissible representative"). It IS displayed in the grade cap and at
each consuming theorem, so the note as a whole fences it; the §6 inventory does not.
(Same genre as Finding 3: the fences live at the theorems, the boxes under-index
them.) Classification: justification gap (fence-inventory completeness), minor.

### Finding 5 — HONESTY DEFECT (enumeration overstatement), §7.1 JB-KEYEQ row

> "JB-KEYEQ | byte census + TH-BASE (**q = 1 byte-equal on all 25 rows**) | 25 | GREEN"

Three of the 25 rows (QO shapes with zero extracted reads: QO:x3-3/Q3,
QO:x4+2x2+2/Q2, QO:x4-2/Q2) have NO q = 1 junction at all (byte census `{}` in the
sealed JSON); "q = 1 byte-equal on all 25 rows" holds on 22 rows and is vacuous on 3.
The runner's TH-BASE check is correctly guarded (`if T.n >= 1`); only the table's
wording over-claims. Classification: honesty defect (completeness claim over an
enumeration), trivial.

### Checks that PASSED (the note's load-bearing content)

* **JB-CREAD derivation** — every line verified against the verbatim sources:
  (RM-m) box ([RMG] S0.2, lines 308–324: R_{m,λ+γ}(R) = z^{ε′}·v·τ_m with
  ε′ = ⌊(s_m(λ)+s_m(γ_{m+1}))/e_{m−1}⌋; τ_m = ε_m(γ_{m+1})^{−1}c_m verbatim);
  (VD-m) ([JA §3.4]: ρ_m(A) = z^{τ_m(A)}R_m(A)(z_m) = ε_m(β)·R_m v(A),
  τ_m(A) = (s_m(A) − ℓ_{m−1}β)/e_{m−1} — the note's ρ/τ match exactly); the
  B-READ step (= [RMG] L-CELL(ii), covered by the §0 consumption list "S2.1
  cells/lines/L-CELL/L-NORM"; its hypothesis β* ≤ w_m(R) is supplied by (C-W_R),
  which the note holds throughout); the w_m(R) pin (≤ from nonzero read + min-line,
  ≥ from (C-W_R)); the regrouping (commutative field); JB-EPS at (V,V′) = (λ,γ_{m+1})
  with the SAME ε′ formula as (C-READ)'s. R ≠ 0 on the scored stratum is forced by the
  nonzero read (and the runner censuses R=0: 0). The "τ_m is a unit" step rides
  ψ_j(0) ≠ 0, which is [ILN]† S0.1 class-pin clause (line 155) and JA-PIN clause 5
  (print requires ψ ≠ y, tex 829/882/1149) — both consumed by the note's §0 list, and
  c_m ≠ 0 is machine-pinned by JB-CM (28/28).
* **JB-EPS** — algebra sound (see D2); the runner's integer leg uses the geometric
  s_geo (decorrelated from ℓ), 955 samples; the carry clause matches JA-GRID(c)
  verbatim (s(V)+s(V′)−s(V+V′) = e·δ, δ ∈ {0,1}).
* **JB-VTX shear** — derived, not asserted (see D3). The "sheared frame = the print's
  own next-level bookkeeping" identity e_q·u_i + h_q·i = v_{q+2}(A_iΦ_q^i) checks
  against Prop `propertiesv` item 3's displayed formula (tex ~1028–1033:
  v_r(a_iφ^i) = e(v_{r−1}(a_i) + i(v_{r−1}(φ) + |λ|)) = e·v(a_i) + i(e·v(φ) + h))
  under the P-index dictionary.
* **JB-TREE** — (ID-(i+1)) verbatim from [RMG] S2.2 line 499 (the note's display drops
  the ψ_{i,k} ≠ 0 qualifier in the sum; harmless since C_k^{(i)} = 0 there); the
  fresh walker implements the S2.2 display faithfully (E1-priority = lowest level,
  promotion/exit/correction moves with sign flip per the identity's minus, L-NORM
  split with exactness self-check); reassembly and reducedness checked exactly;
  L-LINE(iv) (w_m(C) = line(C) on reduced cells) cited correctly.
* **JB-TREE(iii) quanta** — the note's list (promotion +q_{i+1}, exit −w_mΦ_m,
  correction-main 0, π-junk ≥ E_m, Y-junk ≥ Γ₀) matches BOTH the LED-Λ S1 table's λ_E
  row (line 192) and [RMG] L-LINE(i)–(iii); the runner recomputes them fresh
  (Em/Γ_l/qq from first principles), honoring JB-BOX-4's decorrelation promise.
* **JB-DEV(ii) byte figures** — "12 GREEN / 18 RED of 30 walked junctions" reproduced
  from the committed weld-probe JSON (F1 samples 30, obs 18 RED; greens = 10 towers +
  2 QO = 12); the JB byte census matches the probe's byte_equal pattern **row-for-row,
  0 mismatches** (checked programmatically across all 44 tower junctions).
* **GD-2 figures** — 41,720 / 7,472 confirmed against independent records (GD23
  brief, J-A §7 riding-partials block).
* **JB-BOX-1** — the blueprint J-B(iii) quote is verbatim (blueprint S2.2 lines
  174–176), and the correction is right: the ρ-form is carry-free (proved above),
  the carry-bearing form is [RMG] (C-READ) itself; both frames displayed with the
  JB-EPS coordinate change. The frame-conflation diagnosis is fair to the blueprint
  text.
* **W-3/W-5 supply claims (§7.3)** — blueprint rows 293/295 checked; "W-3 in full
  (shear explicit)" is honest (the blueprint's J-B(i) already meant the GD-2 sheared
  convention, T-F-tested); "W-5 in full on [RMG]'s scope" carries its (VD-m)/v≠0
  conditionality in the same block ("NOT supplied: W-1's uncollapsed all-orders
  dictionary (JA-BOX-2)") and in JB-BOX-2/4.
* **TW-JB** — "all 16 towers, nontrivial ledgers": verified, all 16 transport ledgers
  are nontrivial in the sealed JSON; chambers re-run all families (2,480 samples).
* **Boundary geography** — the 21 boundary rows sit exclusively on T3A/T3B/T3C/T3D/I4B
  + their chambers (JSON); all five diverge at q = 2 in the byte census (=
  character-visible per the W-2 byte law), with T3B/I4B the W-2 collapse-boundary
  pair — the claim as worded checks.
* **I4C fence-in-action** — trees 0, cread 0/0/0, no eligible (g_m = 1 ∧ T-scope) m;
  byte divergence at q = 2, 3 — all as displayed.
* **v = 0 branch** — the theorem's stratum split is displayed at the theorem, the
  runner scores v ≠ 0 rows and checks ρ_m(f) = 0 on v = 0 rows (0 occurrences in this
  battery — disclosed in the census line).
* **Wallclock honesty** — "campaign date 2026-08-08 (wallclock 2026-08-04)" matches
  commit timestamps.

### Minor observations (not findings)

* §4(iii)/§5 notation imported from consumed notes at the citation site (q_{i+1}, E_m,
  Γ₀ from LED-Λ/[RMG]; s(·) used in §3(d) before its §5 display) — consistent with the
  corpus's consumption discipline, but a fresh reader needs the cited notes open.
* τ_m (field element, the Ĉ_m read) vs τ_m(A) (integer twist exponent) collide in §5;
  disambiguated only by the argument. Inherited from [RMG]/J-A usage.
* §7.1 "scored 104 (66 roster + 38 chamber)": "roster" includes the QO/d₀ legs
  (16-tower roster alone scores 56). Consistent with §0's roster definition
  (16 + 5 + 4), noted for precision.

## D. Special-attention items

### D1. JB-TREE "both key families" (runner lines 473–503)

The runner's print-side key `G.phi[m+1]` is NOT a copy of the harness `T.Phi[m]`:
`gmn_from_tower` (grt_weld_probe.py:456–459) hands only the level data (e_i, h_i, ψ_i)
and Φ_0 to `GmnLeg`, which grows its own key chain via the fresh GMN transcription
(`_thm_phir` → `construct`, the Prop-construct/Thm-phir recursion, lines 233–316). So
byte-equality `tuple(G.phi[m+1]) == Phim` is a genuine machine fact (this is the
JB-KEYEQ census), and "the print key" is an independent object. HOWEVER: where
byte-equal, `fresh_divmod(T.R, fC, tuple(G.phi[m+1]))` is division by the *same byte
string* as the harness check — deterministically the same computation, so the second
comparison can never fail given the first. The evidential content of "harness AND
print keys" = (harness division check) + (byte-equality of the independently
constructed print key), not two independent division readings. The note's §4 fence
"AND by the print-side key where byte-equal" makes this recoverable, but the §7.1
table wording overstates independence — see Finding 2.

### D2. Lemma JB-EPS algebra — VERIFIED line by line

With t(β) = (ℓβ − s(β))/e (all at level m−1 data, ℓ = h^{−1} mod e, s(β) = the
mod-e representative ℓβ mod e ∈ [0, e)):
t(V+V′)·e − t(V)·e − t(V′)·e = [ℓ(V+V′) − s(V+V′)] − [ℓV − s(V)] − [ℓV′ − s(V′)]
= s(V) + s(V′) − s(V+V′)  (ℓ-terms cancel by linearity)
= e·⌊(s(V)+s(V′))/e⌋  (since s(V+V′) = (s(V)+s(V′)) mod e and s, s′ ∈ [0, e)) = e·ε′.
Divide by e. Field form: ε = z^{−t} (JA-EPS, consumed) gives
ε(V+V′)ε(V)^{−1}ε(V′)^{−1} = z^{−(t(V+V′)−t(V)−t(V′))} = z^{−ε′}. Sound. The runner's
`jb_eps` checks the same three identities with fresh integers (`s_geo` = the geometric
smallest-abscissa definition, not ℓβ mod e — a genuinely decorrelated leg) plus the
field form on 955 samples. Note ε′ ∈ {0,1} always (two summands); the teeth rows
(z^{ε′} ≠ 1) therefore all have ε′ = 1, which is what MJB-CREAD exercises.

### D3. JB-VTX shear — DERIVED, not asserted

§3(a) chain: e_q·u_i + h_q·i = e_q·v_{q+1}(A_i) + i·(e_q·v_{q+1}(φ_{q+1}) + h_q)
[expand u_i per the tex-1370 definition] = e_q·w_q(A_i) + i·γ_{q+1} [JA-VAL consumed
for the digit; γ-recursion = JA-PIN clause 7, requiring v_{q+1}(φ_{q+1}) = w_q(Φ_q),
which is JA-VAL at the key — see Finding 4]. (c) slope law follows from the affine
map: a segment (i₀,u₀)–(i₁,u₁) of slope σ maps to slope (e·u₁+h·i₁−e·u₀−h·i₀)/(i₁−i₀)
= e·σ + h — derived. σ = −h/e ↦ 0 ✓; print σ < 0 ⟺ sheared < h ✓. LEMMA JB-AFF's
two-line proof is correct (affine + abscissa-preserving + a > 0 preserves below-chord
and strict-turn relations). Runner `lower_hull` implements strict-vertex lower hulls
correctly (pops non-strict turns); `jb_shear_vtx` checks (a),(b),(c),(d) on fresh
hulls, 893 samples each family.

### D4. Fence inventory (six boxes)

See Findings 3, 5.

## E. Verdict

(filled at end)
