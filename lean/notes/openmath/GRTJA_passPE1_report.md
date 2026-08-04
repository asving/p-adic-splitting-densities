# GRTJA pass PE1 — first hostile pass on GRTJA_PROOF_2026-08-08.md

**Verifier:** JA-PE1 (fresh context, hostile; fixes nothing).
**Target:** `lean/notes/openmath/GRTJA_PROOF_2026-08-08.md` at commit 1cbf8ca
(confirmed: worktree note md5 `8489a38beee44f43bef5018478a67595` == `git show
1cbf8ca:` md5; the only commit after 1cbf8ca (77c767e) does not touch the note
or any artifact below). Artifacts verified identical to 1cbf8ca by md5:
`grt_ja_checks.py` 5972d412, `grt_ja_checks_output.txt` 0d6d0522,
`grt_ja_checks_results.json` 13ab52ab, `grt_weld_probe.py` 8f967696,
`grt_w2_checks.py` 3fe28e6f. Seal discipline confirmed: 696eae8 = runner +
prereg only; 1cbf8ca = outputs + verdict.

**Charge executed:** (1) JA-PIN re-derived clause by clause against
HigherNewton.tex at the cited anchors; (2) all four operator equalities
re-derived by hand, hardest-first on the (ii) gauge law, incl. the 26
JA-BOX-1 witnesses from the committed JSON and the m ≥ 3 proviso/(R-coll)
relationship; (3) consumption grades at every W-2/N-1/GD-5 site, the five
boxes, J-C/J-D leak scan; (4) machine re-run read-only (in a /tmp copy) +
one hand-derived equality instance per ring via the NEW `ja_pe1_ext.py`.

---

## 1. Machine bracket — RE-RUN CONFIRMED BIT-IDENTICAL

Re-ran `grt_ja_checks.py` in a /tmp copy (committed artifacts untouched;
the runner writes its JSON next to itself, hence the sandbox). Result:
**exit 0, all 17 families GREEN, 10,311 samples, 0 violations, boundary
census 16, CK-BPREF 26** — and the regenerated `grt_ja_checks_results.json`
is **identical to the committed one on every key except `elapsed_s`**
(5.4 s vs 7.4 s). Independent recount from the committed JSON:

* boundary 16 = T3B main 4 + T3B transported 3 + I4B main 5 + I4B
  transported 4 — exactly the note's "T3B (4 + 3 transported) and I4B
  (5 + 4 transported)". CONFIRMED.
* CK-BPREF 26 = 22 roster hits + 4 d₀ hits (one on each of
  JD5A/JD3A/JD3B/JD3C, so "incl. all 4 fresh d₀ ≥ 2 rows" and "at d₀ = 3
  and p = 5" are exact). The 22 roster hits sit on **10** roster rows
  (T2A, T2C, T2D, T2G, T3A, T3C, T3D, T3E, T3F, I4C) — see GAP-2.
* Designated rows T2A/T3A/T3E all fire (1/2/4). Teeth catches 8/9/8,
  11/11, 12/18 match the note's §7.1 row exactly.
* Runner audit: every family is LAW-KEYED to the note's displayed claim
  (I checked `ck_val`/`ck_eps`/`ck_grid`/`vd_eval`/`ck_res`/`orb_res`
  line by line against §3's statements — the proviso is machine-evaluated
  per attained digit exactly as the theorem's hypothesis reads; scoring
  quantification matches the theorem's own conditionality; CK-BPREF's
  slot-dependence census is the correct refutation shape for the
  blueprint's slot-independent display; ORB-RES shifts exactly the one ℓ
  the law names, keys fixed).

## 2. JA-PIN vs the print (clause-by-clause, anchors re-read)

All anchors were re-read in `docs/references/HigherNewton.tex`:

* λ = −h/e with h, e positive coprime: tex 219 (order one), 828–829 (type
  datum), 912 (order r). ✓ (cited as "220/828/912" — ±1 tolerance).
* Principal polygon = negative-slope sides: tex 448–451 (`shape1`) and
  1377. ✓ Positivity-of-h clause 2 argument sound; slope-0 dispatch fence
  matches the blueprint's own pin verbatim.
* ψ monic irreducible ≠ y: tex 830 (order one), 882 (order r, with
  F_r := F_{r−1}[y]/(ψ_{r−1})). ✓ Clause 5's one-liner (ψ(0)=0 ⟹ ψ=y,
  excluded) is trivially correct; tex 1149 quote verbatim. ✓
* Clause 7: `propertiesv` items 3/4 at tex 1028+ and `vrphir` at tex 1259
  transcribe under P-index to γ_{j+1} = e_j·w_jΦ_j + h_j and
  w_{j+1}Φ_{j+1} = e_jg_jγ_{j+1} — re-derived by hand, EXACT (item 3's
  e_{r−1}(v_{r−1}(a_i) + i(v_{r−1}(φ_{r−1}) + |λ|)) = e_{r−1}v_{r−1}(a_i)
  + i·v_r(φ_{r−1}) via item 4; base v₂(φ₁) = h₁^GMN = γ₁ ✓).
* Prop `construct` at tex 1166 with hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})
  (tex 1167–1168) ✓; Thm `phir` 1257–1283 ✓; representative Definition at
  tex 1285–1288 ✓; Bézout ℓ_rh_r − ℓ′_re_r = 1 with NO pinned
  representative at tex 1291 (and tex 915: "fixed integers", again no
  normalization) — JA-BOX-3's premise CONFIRMED against the print.
* Defs `t(i)`/`rescoeff`/`defresidual` at tex 1431/1447/1497 ✓ (grep on
  labels). Clause 1: print base = 𝒪_L of a finite extension of ℚ_p (tex
  399); "O = ℤ_p is the print's own base" is fine (instance), F_p[[t]]
  correctly deferred to JA-BOX-4.
* Clause 8 = pure consumption: W-2's note grades W2-C1 "PROVED on the §3
  perimeter", W2-C3 "PROVED at attempt grade given §3–§4; machine
  44/44/44"; the three conditionality items ((C-coll)/recursion split,
  §4.3 ℓ-orbit fence, W2-OPEN-1 OPEN) are all carried verbatim in the
  clause. CONFIRMED faithful.

Verdict on JA-PIN: **sound at the stated grade**; every clause is a real
print hypothesis plus a displayed one-liner; the lift clause is honest
consumption with conditionality intact. (One bracket overstatement —
see GAP-5.)

## 3. The four equalities — re-derivations

**(i) JA-VAL.** Re-derived: base w₀ = v₁ (both min coefficient valuation);
step: `propertiesv` item 3 at order m+2 under P-index is
v_{m+2}(A) = min_i(e_m^har·v_{m+1}(a_i) + i·γ_{m+1}) with v_{m+2}(φ_{m+1})
= γ_{m+1} (clause 7); the [ILN]† S0.2 recursion (checked verbatim in
ITERLAWN_PROOF S0.1/S0.2: w_{m+1}(f) := min_j{e_m·w_m(A_j) + j·γ_{m+1}})
is the same integer min; shared keys make the devs identical divisions.
SOUND, correctly scoped to the shared-key perimeter. The §4(i) MacLane
caveat display v_{r+1}(φ − φ′) = e_r·v_r(φ) < v_{r+1}(φ) re-derived: for
two strict reps with different units w ≠ w′ the T-side residuals do not
cancel, so v_r(φ−φ′) = v_r(φ); φ−φ′ is its own i=0 digit in the φ-dev, so
v_{r+1}(φ−φ′) = e_r·v_r(φ) < e_r·v_r(φ) + h_r. CORRECT (the "different
strict units" hypothesis is load-bearing and is stated).

**(iii) JA-EPS.** Re-derived from the harness normalization ℓh + ℓ′e = 1:
ε-exponent ℓ′s − ℓu = (s(ℓ′e + ℓh) − ℓβ)/e = (s − ℓβ)/e = −t_m(β) with
t_m(β) := (ℓβ − s)/e as displayed. TRUE and machine-confirmed (CK-EPS
fresh-integer + geometric leg). The k-grid form is exactly W2-L2 (whose
proof I re-checked: ℓ′𝔰 − ℓu′ = (𝔰 − ℓV)/e, add T — two lines, correct);
hypotheses match (W_m ∈ e_{m−1}ℤ ✓). The ANCHOR GLOSS has two defects —
see GAP-1.

**(iv) JA-GRID.** (a) = W2-L0: integer-ordinate abscissas on the slope
−h/e line at value V are x ≡ ℓV (mod e); smallest nonneg = ℓV mod e ✓.
(c) carry clause re-proved: three values in [0, e), congruent sum, so the
defect is 0 or e, and = e iff s+s′ ≥ e ✓ elementary and correct;
single-level scope fence displayed ✓. Domain edge on (a)'s "V ∈ ℤ_{≥0}"
quantifier and the "tex 1498" gloss — see GAP-4.

**(ii) JA-RES (the hardest; full re-derivation).** With the proviso
(VD-(m−1)) at digit a_i: R_{m−1}(a_i)(z_{m−1}) = z^{−τ_{m−1}(a_i)}·C_i, so
c_i = z^{t(i)−τ_{m−1}(a_i)}·C_i. The exponent:
t(i) − τ = [−ℓ_{m−2}u_i + ℓ_{m−2}β_i]/e_{m−2}, and u_i = v_m(a_iΦ_{m−1}^i)
= β_i + i·W_{m−1} (JA-VAL at the on-line digit + `vrphir`/clause 7), so
t − τ = −ℓ_{m−2}·i·W_{m−1}/e_{m−2} = −i·A_{m−1} since
ℓ_{m−2}W_{m−1}/e_{m−2} = ℓ_{m−2}g_{m−2}γ_{m−1} = A_{m−1}. **The law
c_i = z_{m−1}^{−i·A_{m−1}}·C_i is EXACTLY right**, and its m = 2
unconditionality is exactly W2-L3's unconditional (VD-1). The print-side
transcription (rescoeff order m, t under P-index with ℓ_{m−2}/e_{m−2})
matches tex 1431/1447 verbatim. JA-VDIND forward re-derived (the ν-shift
and τ_m(A) − ν = ε-exponent both check); the "single-slot support NOT
sufficient" caveat is correct (the constant z^{−s₀A} survives); the FULL
conjugation form R_m(A)(y) = z^{−s₀A}·Q_A(ϑ_m y), ϑ_m = z^{−e_{m−1}A_{m−1}}
re-derived (i = s₀ + je expansion). The (R-coll) induction closes (base
VD-1, per-node triviality feeds each level's proviso). **Relation of the
m ≥ 3 proviso to JA-BOX-2:** the theorem's hypothesis is the per-digit
(VD-(m−1)); (R-coll) is the note's named sufficient perimeter closing the
induction; the grade line displays both. Consistent — modulo the "only"
wording in JA-BOX-2 (GAP-5). §4's ORB-RES transport re-derived
(t ↦ t − κu_i; u_i = u₀ − jh on the side ⟹ the displayed
z^{−κu₀}·(z^{κh})^j rescale) and the (ii)-orbit stability display's
exponents re-computed exactly (u_i = (β₀ + s₀W_{m−1}) + j(e_{m−1}W_{m−1}
− γ_m) ✓). ORB-EPS transport (t ↦ t + κβ, s invariant) ✓.

**JA-BOX-1 refutation.** Blueprint display quoted verbatim (checked
against `GRT_WELD_BLUEPRINT_2026-08-08.md` S2.1 (ii): "R_{m,λ} = c·R_λ^GMN
with c ∈ F^× slot-independent"). Refutation shape correct: on samples where
the per-slot law held EXACTLY (scored, 0 violations), the per-slot gauge
z^{−iA_{m−1}} takes ≥ 2 values on the attained set — 26 such witnesses,
recounted from the committed JSON, incl. all 4 d₀ ≥ 2 rows. The visibility
condition in the box (e_{m−2} ≥ 2, ℓ_{m−2} ≥ 1, ord(z_{m−1}) ∤
e_{m−1}A_{m−1}) is the correct adjacent-slot criterion. REFUTED stands.

## 4. Hand-derived instances per ring (via NEW `verification/openmath/ja_pe1_ext.py`)

**ℤ_p leg (T2A, p = 2, reads (2,1,2),(2,1,1); K₁ = F₄, ord z₁ = 3).**
γ₁ = 1, γ₂ = 2·4+1 = 9, ℓ₀ = 1, A₁ = 1·2·1 = 2. Sample with β = w₂(A) = 18,
attained {0, 2}, s(β) = 0. Slot i = 2: β₂ = (18 − 18)/2 = 0,
u₂ = 0 + 2·4 = 8, t(2) = (0 − 8)/2 = −4, τ = (0 − 0)/2 = 0,
t − τ = −4 = −2·A₁ ✓ (hand). Field: z₁^{−4} = z₁² = 1 + z₁ (F₄), C₂ = 1,
so z₁^{−4}·C₂ = 1 + z₁ = c₂ ✓ (hand, against the printed elements).
Slot i = 0: t = τ = −4, c₀ = C₀ ✓.

**F_p[[t]] leg (T2D, p = 2, d₀ = 2, reads (2,1,1),(2,1,1); K₁ ≅ F₄).**
γ₂ = 5, A₁ = 1. β = 10, attained {0, 2}. Slot i = 2: β₂ = 0, u₂ = 4,
t(2) = −2, τ = 0, t − τ = −2 = −2·A₁ ✓; z₁^{−2} = z₁ (ord 3), C₂ = 1,
z₁·1 = z₁ = c₂ ✓ (hand).

**JA-EPS hand instances:** T2A (e,h) = (2,1), V = 7: ℓ = 1, ℓ′ = 0,
s = 1, u = 3, t = 3, ε-exponent = −3 = −t, ε₁(7) = z₁^{−3} = 1 ✓.
T2D V = 5: s = 1, u = 2, t = 2, ε-exp −2 = −t ✓. Both by hand.

## 5. Grades, boxes, leak scan

* **Consumption grades named at every site:** §2 cl. 8 "at attempt grade,
  conditionality verbatim" ✓; §3.2 "W2-L2 consumed proved" ✓ (W-2 table:
  PROVED 0/2); §3.3 "W2-L0, consumed proved" ✓; §3.4 "(VD-1) is W2-L3,
  PROVED (consumed)" ✓; §4 "W-2 §4.3, consumed as convention analysis" ✓
  (matches W-2's own "CONVENTION ANALYSIS, review-owed"); §5 W-2 bullet
  "AT ATTEMPT GRADE (0/2) with full conditionality ledger" ✓; N-1
  "EXECUTED and GREEN at family-ledger scope / ACCEPTED order-2 instance"
  matches GRB_ORDER2 REV 11 note + blueprint W-1 row; N-1's non-coverage
  list (carrier/C15, orders ≥ 3, lifts) ✓; GD-5 "NEARLY CLOSED by
  composition" + residue (S-1 audit + deg-g>1 KEY1) is VERBATIM the
  completion-tree GD-5 row; T-F 41,720/0-vs-7,472 and GD-8 871/0 both
  match their tree/blueprint rows. Nothing consumed above its grade;
  nothing upgraded.
* **Boxes:** BOX-1 precise (see §3); BOX-2 precise modulo one word
  (GAP-5); BOX-3's premise verified in the print (tex 1291 + 915);
  BOX-4 verified (print is mixed-characteristic, tex 399; runner gives
  F_p[[t]] rows no PARI leg — confirmed in code); BOX-5 fences all hold
  against the text (no gr/carrier statement, no count/menu statement, no
  W2-OPEN-1 advance found anywhere in §§1–7 — one borderline sentence,
  GAP-3).
* **J-C/J-D leak scan:** grep + read of every §3–§7 claim. The only
  borderline item is JA-MIN's GD-3 sentence (GAP-3). Otherwise clean:
  the lift-tie bullet consumes W-2 clause 2, the transported chamber is
  re-instantiation only, §7.3's NOT-supplied list is accurate.

---

## FINDINGS (0 critical, 5 gaps)

* **GAP-1 (citation precision, JA-EPS §3.2).** Two defects in the anchor
  gloss for t_m(β): (a) "the same exponent prescribes Prop `construct`'s
  children, **tex 1213–1218**" — those lines are picture-environment
  drawing code; the child prescription
  φ_j(y) ≡ y^{(ℓ_{r−2}u_j−𝔰_j)/e_{r−2}}c_j(y) is at **tex 1200–1201**
  (the same wrong range appears in W-2 §3.1 — inherited). (b) The
  displayed t_m(β) := (ℓ_{m−1}β − s(β))/e_{m−1} carries the CONSTRUCT-
  child sign (ℓu − 𝔰)/e; **Definition `t(i)` (tex 1431) defines the twist
  with the opposite sign** (s_{r−1}(a) − ℓu)/e — calling the displayed
  exponent "the print's twist exponent (Definition t(i))" is sign-loose
  (they differ by −1 and a ν-shift; Lemma `enlarge` tex 1528–1541 is the
  clean print-side object). The equality itself is true as displayed
  (note's own inline definition; hand + 872-sample machine leg) — the
  defect is attribution only. JA-RES §3.4 uses the correct Def-t(i) sign.
* **GAP-2 (census misstatement, §7.1).** "CK-BPREF refuting samples = 26
  across **12 roster rows** + all 4 fresh d₀ rows": the committed JSON
  (and my bit-identical re-run) gives 22 roster hits on **10** roster rows
  (T2A, T2C, T2D, T2G, T3A, T3C, T3D, T3E, T3F, I4C) + 4 d₀ hits. The
  total 26, the d₀ clause, and the refutation itself are unaffected.
* **GAP-3 (over-reach, COROLLARY JA-MIN §3.4).** The derivation
  establishes print-residual ↔ harness-read transfer (units per slot ⟹
  supports/degrees/ord_ψ computability). But GD-3's MIN CORE as defined
  in `docs/MATH_COMPLETION_TREE_2026-08-01.md` is
  **ord_{ψ̂_hom}(in(f)) = ord_ψ(R_λ(f))** — the graded-initial-form leg
  (in(f), a graded-carrier object) is neither derived nor cited here, so
  "The GD-3 MIN CORE at orders ≥ 2 is therefore a theorem WHERE THE
  DICTIONARY REACHES" exceeds the shown content unless "MIN CORE" is read
  as its dictionary half only. Given the note's own no-J-C fence, this
  sentence needs a rescope or an explicit print-side cite for the in(f)
  leg. (Blueprint taxonomy places GD-3 inside J-A(ii), so this is a gap,
  not a fence violation; nothing downstream in the note consumes it.)
* **GAP-4 (domain/citation edge, JA-GRID §3.3(a)).** Stated for all
  V ∈ ℤ_{≥0}, but the print's T-side (endpoints with NONNEGATIVE integer
  coordinates, tex 1176) has initial point = eq12(V) only when
  u = (V − sh)/e ≥ 0 — guaranteed by the print's own hypothesis
  V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1}), false for small V (e.g. (e,h) = (2,3),
  V = 1 ⟹ u = −1: the print-side T has no such point). Every consumption
  site satisfies the print hypothesis, and the machine's geometric leg
  checks the (unconditionally true) integer-ordinate characterization;
  the statement should carry the u ≥ 0 (or print-hypothesis) proviso.
  Also "(same object at **tex 1498**)": the (s,u) at tex 1498 is the
  initial point of the ACTUAL side S (≠ eq12 when the first grid slot is
  unattained); the genuine reappearance of the T-side object is Lemma
  `enlarge`, tex ~1528–1531.
* **GAP-5 (two minor wording overstatements).** (a) §2 proof bracket
  "[Machine: JA-PIN — **every clause** re-verified…]": the runner covers
  clauses 2–7 only (its own docstring and the note's §7.1 table say so);
  clause 1 is not machine-checkable and clause 8 is consumption. (b)
  JA-BOX-2 "the scalar/evaluated forms hold **only** on (R-coll)": by the
  note's own unsealed JA-VDIND converse, the per-digit proviso can hold
  off (R-coll) by cancellation — "are proved only on" is the sustainable
  reading; "hold only on" overstates.

No critical errors: every displayed equality re-derives exactly; the
dictionary theorem's clauses each trace to a real print hypothesis at a
real anchor; the machine bracket is law-keyed, sealed, and reproduces
bit-identically; grades, fences, and the blueprint correction are honest.
The five gaps are citation/wording/census precision items — none breaks a
logical chain, none changes a grade.

JA-PE1 FINDINGS: 0 critical, 5 gaps
VERDICT: GAPS-ONLY
