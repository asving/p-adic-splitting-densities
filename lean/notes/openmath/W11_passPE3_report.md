# W11 passPE3 report — hostile verification of W11_PROOF_2026-08-08.md (post-r2 text)

**Target:** `lean/notes/openmath/W11_PROOF_2026-08-08.md` at HEAD (file
byte-unchanged since r2 commit 31506b3 — verified `git diff 31506b3 HEAD --`
empty; arc: seal 7020ceb / verdict cb05127 → PE1 fbf0a02 2C+2G+2m → r1
8c87fa3 → PE2 473a993 0C+1G+1m → r2 31506b3). **Role:** hostile verifier,
fresh context, fix nothing. Both prior reports and both repair diffs read
first; this pass mined the veins no prior pass had (the r2 edits themselves,
the SPLIT-TAIL derivation, the window-vs-limit bridge, the NEW downstream
consumers W-12/HMENU3, and the deep families re-derived in 𝔽_q[[t]]).

**Verdict: CLEAN — 0 CRITICAL + 0 JUSTIFICATION GAPS + 0 MINOR.**
Every charge item verified; two non-finding remarks recorded (§1). The
acceptance counter advances: this is the FIRST clean pass (1 of the 2
consecutive clean passes required).

---

## 1. FINDINGS

None.

**Non-finding remarks (recorded for the arc, no repair owed):**

* (R-a) In the r2 telescoping bracket (S2.5), the phrase "the split legs at
  A₁-valuation w telescope … adding SPLITEQ(w)" could be misread as placing
  SPLITEQ members at exact A₁-valuation w; SPLITEQ(k = w) members with
  c₁ = 0 have v(A₁) > w. The display never asserts this (the valuation
  clause scopes the 2SIDED/TAIL legs only; SPLITEQ enters as the k = w
  term of a bookkeeping identity), and the identity is correct as written
  — verified including the w-range corner where the geometric sum is empty
  (N = 5, w = 2: 0 + 1_tail = q⁰ ✓).
* (R-b) The r2 bracket's two numeric checks use two different windows (the
  telescope at (q,N,w) = (2,6,1), the smoke-table tie at (Zp,2,4)) — both
  correct (4+2+1+1 = 2³; 8+8 = 16 = INERTDEEP(1) at N = 4, where the
  telescope gives 1+1 = 2 = 2^(4−1−2) ✓); just two independent instances,
  not one.

---

## 2. CHARGE-BY-CHARGE RECORD

### (1a) The r2 telescoping insertion (S2.5) — algebra re-derived, transcription checked

Re-derived from scratch, per node instance at state s, per w: #{A₁ : v = w
exact} = (q−1)q^(N−1−w); split-leg A₀-mass Σ_{u=2w+1}^{N−1}(q−1)q^(N−1−u) +
1_tail = (q^(N−1−2w) − 1) + 1 = q^(N−1−2w) ✓ (the tail cell A₀ ≡ 0 is ONE
class over O/π^N). Hence 2SIDED(w,·)+TAIL(w) = (q−1)q^(N−1−w)·q^(N−1−2w);
SPLITEQ(w) per instance = ((q−1)(q−2)/2)·q^(N−1−2w)·q^(N−1−w) (independently
re-derived from the residual census: c₀ digit fixed ≠ 0 → q^(N−1−2k), c₁
digit fixed → q^(N−1−k), × (q−1)(q−2)/2 pairs); factor (q−1)(1+(q−2)/2) =
q(q−1)/2 = INERTDEEP's census constant ✓; k-ranges agree (2w < N ⟺ w ≤
⌊(N−1)/2⌋ for integer w) ✓; all split mass at w > ⌊(N−1)/2⌋ is undecided
(u would need ≥ N), so the per-w matching is COMPLETE and the every-window
split-decided = inert-decided follows ✓. Consistency with the surrounding
original text: the "whence" now rests on the bracket, and the original
per-node limit fractions re-derived equal (split-deep = X/q + SPLITEQ-mass
= (q/2)·q^(−3s−2)/(q²+q+1)·… = q/(2(q²+q+1)) of μ_s = INERTDEEP's fraction
✓). Transcription vs `W11_passPE2_report.md` @ 473a993 §F1: faithful
(the note adds the precision "per node instance"). Both q = 2 checks ✓
(see R-b). The S2.4 corrected identity feeding this was ALSO re-verified
independently: X = q^(−3s−1)/(q²+q+1); legs qX (RAM), X/q (2SIDED), X
(e = 1, all q(q−1) residual pairs), total ((q²+q+1)/q)X = q^(−3s−2) = μ_s ✓.

### (1b) The r2 v(2) = 1 pins (S1/S2.2/S5) — re-derived, sweep re-run, consumers checked

The Z₂[√2] counterexample re-derived: e₀ = v(2) = 2; RAM(h) member with
w = (h+3)/2 (valid: ≥ (h+1)/2, integer since h odd) has v(disc) =
min(2w, 2e₀+h) = min(h+3, h+4) = h+3 ∉ {h+1, h+2} ✓. The min-attained
parity argument ✓ (2w even/∞, 2e₀+h odd); "never tame" for any e₀ ✓
(min ≥ h+1 ≥ 2 > 1); e₀ = 1 recovers exactly the pinned {h+1, h+2} ✓.
The pin's load-bearing scope re-verified by my own sweep: the {h+1, h+2}
spectrum appears ONLY at the S2.2 RAM bullet and S5 (both pinned); every
other disc law is v(p)-free (p-odd RAM v(disc) = h uses v(4) = 0; 2SIDED/
SPLIT-TAIL 2w₁, SPLITEQ/INERTDEEP 2k are root-valuation computations; the
S2.2 disc = 0 bullet's w = v(2)+v(offset) is generic in v(2)); the proof
of (i)–(iii) never consumes v(p) (S2.3's mixed-2 leg needs v(2s) = e₀+k ≥
k+1, any e₀) ✓ — the pin sentence is exactly right. Battery mixed rows are
Z_p (v(2) = 1) ✓ no machine surface touched ✓.

**Consumers at post-r2 pins (the NEW corpus since PE2):** W-11's file is
byte-identical to 31506b3 at HEAD, so both consumers' "post-r2" pins
denote the text I verified. (i) **W-12** (`W12_PROOF_2026-08-08.md`): S1
inherits the pin VERBATIM-faithfully ("mixed absolutely-unramified
Z_p-type, v(p) = 1 — the W-11 r2 pin inherited; … load-bearing only for
p = 2 disc-spectrum displays, never for counts") ✓; S9 records the true
arc (seal → PE1 → r1 8c87fa3 → PE2 473a993 → r2 = HEAD 31506b3, counter
0/2) ✓; LEMMA W12-L0's six per-instance laws == W-11's S2.1/S2.4/S2.5
per-instance counts term by term (RAM (q−1)q^(N−1−u)·q^(N−(u+1)/2); 2SIDED
(q−1)²q^(2N−2−u−w); SPLITEQ/INERTDEEP census×q^(2N−3k−2); SPLIT-TAIL
(q−1)q^(N−1−w); UNDECIDED q^(N−1−M), M = ⌊(N−1)/2⌋) ✓; its Σ_H recovery of
the bracket q^(k−1) and drainage q^(N−1) per center == W-11 S2.5 ✓; W-12.C
consumes "W-11's exact per-center law q^{N−1}" ✓; S3.3's lower bound uses
the same law ✓; the S7 disc = 0 genre-(i) warrant cites exactly W-11's
MIXED square-block case (true as repaired at r1-F2) ✓. (ii) **HMENU3**
(`HMENU3_PROOF_2026-08-08.md`): S9 pin "@ seal 7020ceb / verdict cb05127 /
r2 HEAD 31506b3" ✓ honest; the β-route block dictionary's domain is
exactly W-11's leaf system (block refine at depth k′; RAM(u); 2SIDED(w,
u−w); SPLITEQ(k′); INERTDEEP(k′); SPLIT-TAIL/UNDECIDED) with parameters as
W-11 states them ✓; "the W-11 bracket q^{s_max} (binomially Σ_t C(s_max,
t)(q−1)^t)" == W-11's bracket q^(k−1) at s_max = k−1 (subset form of the
history sum — re-derived equal; s_max = (u−1)/2, w₁−1, k′−1 all correct) ✓;
S5.3's boundary legs consume "the transported SPLIT-TAIL aggregate
(q−1)q^{N−2} per w and the W-11 undecided q^{N−1}" — both are W-11's
per-center laws verbatim ✓; SPLIT-TAIL ↦ ('DRAIN',) is the CONSERVATIVE
convention, which W-11 itself prices (BOX-5 + the S4.2 alternative law
q^N + q⌊(N−1)/2⌋(q−1)q^(N−2), re-verified) — a disclosed convention
choice on the consumer side, not a misconsumption ✓.

### (2) The unmined derivations: SPLIT-TAIL count + the window-vs-limit bridge

**SPLIT-TAIL(w), from scratch:** definition (S2.4 tail): u ≥ N (A₀ ≡ 0
over O/π^N — one class), v(A₁) = w exact ≤ (N−1)/2. σ = split for EVERY
lift: any lift has v(A₀) ≥ N > 2w, hull = two length-1 sides, slopes w and
u−w > w, two roots at distinct valuations (incl. the A₀ = 0 lift x(x+A₁))
✓. Per node instance (state s < w): (q−1)q^(N−1−w)·1; instance bracket
over s < w re-derived: instances(s) = Σ_t C(s−1,t−1)(q−1)^t = (q−1)q^(s−1),
Σ_{s<w} = q^(w−1); per center (q−1)q^(N−1−w)·q^(w−1) = (q−1)q^(N−2),
w-INDEPENDENT ✓ = clause (ii)'s law. Whole space (q−1)q^(N−1): checked
448 = 7·8² at (Fqt,8,3), 648 at (9,3), 8 at (Zp,2,4), 128·… all == JSON ✓.
**The window-vs-limit bridge (S2.5 NOTE / S4.2):** for every visible row I
verified window count = (limit density)·q^(2N) EXACTLY: RAM q(q−1)q^(2N−h−2)
= (q−1)/q^(h+1)·q^(2N); 2SIDED (q−1)²q^(2N−2−w₁−w₂); SPLITEQ
((q−1)(q−2)/2)q^(2N−2k−2); INERTDEEP ((q−1)/2)q^(2N−2k−1); SEP
((q²−q)/2)q^(2N−2) — zero truncation error on all five shapes ✓. Limit
assembly re-derived: ram Σ = 1/(q+1); 2SIDED-total 1/(q²(q+1)) +
SPLITEQ-total (q−2)/(2q²(q+1)) = deep-split = 1/(2q(q+1)) = deep-inert ✓;
split = inert = q/(2(q+1)); Σ = 1 ✓; S4.2's 1/4 + 1/12 = 1/3 at q = 2 ✓;
drainage per instance q^(⌈(N−1)/2⌉), s-uniform on reachable s ≤ ⌊(N−1)/2⌋,
× bracket q^(⌊(N−1)/2⌋) × q centers = q^N EXACTLY ✓.

### (3) HMENU3 β-route re-entry — covered under (1b)(ii) above; per-center law + dictionary both match W-11's actual statements.

### (4) Deep families re-derived from scratch in 𝔽_q[[t]] (both characteristics)

* **INERTDEEP(1) at (Fqt, q = 8, N = 3), char 2:** center c̄ ∈ F₈ (8
  centers, A₁ = a₁ unchanged in char 2); u = 2, w ≥ 1; residual R = y² +
  c₁y + c₀, irreducible ⟺ c₁ ≠ 0 ∧ Tr_{F₈/F₂}(c₀/c₁²) = 1: 7 × 4 = 28 =
  q(q−1)/2 pairs (Artin–Schreier census re-derived); A₀ = c₀t² exactly
  (1 way = q^(N−1−2k)); A₁: digit₁ = c₁, digit₂ free (8 = q^(N−1−k));
  bracket q⁰ = 1. Per center 28·8 = 224; whole space 1792 == committed
  JSON ✓.
* **INERTDEEP(2) at (Fqt, q = 2, N = 6), char 2, WITH refinement history:**
  k = 2: census pair (c₁,c₀) = (1,1) only (Tr(1) = 1 over F₂): 1 = q(q−1)/2;
  A₀: digit₄ = 1, digit₅ free (2); A₁: digit₂ = 1, digits 3–5 free (8);
  bracket over s ∈ {0, 1(history (1))} = 1 + 1 = 2 = q^(k−1). Per center
  1·2·8·2 = 32; whole space 64 == JSON ✓.
* **2SIDED(1,2) at (Fqt, q = 2, N = 6), char 2:** root node, v(A₁) = 1
  exact (1·2⁴ = 16), v(A₀) = 3 exact (1·2² = 4), bracket q⁰ = 1: per center
  64, whole space 128 == JSON ✓.
* **2SIDED(1,2) at (Fqt, q = 3, N = 4), char 3 (odd equal-char):** recenter
  c̄ = −ā₁/2; v(A₁) = 1 exact (2·3² = 18), v(A₀) = 3 exact (2·3⁰ = 2):
  per center 36, whole space 108 == JSON ✓.

### (5) Extras re-verified this pass

Residual census both characteristics re-derived from scratch ((q−3)/2 vs
(q−1)/2 square-count split at c₁ ≠ 0 / c₁ = 0; Artin–Schreier q/2−1 / q/2;
row sums q(q−1)) ✓; S2.1 trichotomy completeness incl. w = ∞ branches ✓;
S10's bonus displays re-computed ((Zp,2,8) 2SIDED spectrum
2048/…/128 — all nine values ✓, depth-3 count 64 ✓); teeth arithmetic SIGMA
3,020 = 20+80+1344+27+270+250+1029 and TAMEDISC 1,440 = 16+80+1344
re-derived from the closed forms ✓; oracle 8,252 and dlift 1,070 = Σ(q^(2N)
− q^N) ✓; 30-row total 1,235,872 re-summed ✓; all 12 S9 pin hashes resolve
as commits ✓; Lean anchors re-checked at CURRENT HEAD (`gate3_inert_q2` @
`OM/OMCountV2.lean:646`, `omMenu_order0 = rfl` @ :315,
`montes_unconditional_exhaustive`'s `hExhaust` @ `OM/RealInstanceV2.lean:
439–442`) — unchanged, quotes faithful ✓; r2 minimality contract verified
against the diff (exactly the six declared hunks: header, S1, S2.2, S2.5,
S5, S10 echo) ✓.

---

## 3. MACHINE LEG

**Seal verification:** `w11_checks.py` md5 `500aae152bb5b5e9df3712904a6d73a6`
== `git show 7020ceb:…` ✓ byte-identical. Committed artifacts match cb05127
(output.txt `c0b6b10b…`, results.json `72ad1567…`) ✓.

**Sealed-runner re-run:** exit **0** (captured explicitly), verdict
**GREEN**, elapsed 50.8/50.9 s (two runs; committed: 49.9 s). Every number
== §S10: 30/30 census rows; checks **1,250,280**; violations 0 in all six
families (PIN/CENSUS/W10TIE/EXHAUST/TOWER/ORACLE); teeth
MISSING=SHADOW=DRAIN=**30**, SIGMA=**3,020**, TAMEDISC=**1,440**; towers 12
levels (wild 7, beyond-211 1); oracle (2,3):64/0 (2,4):256/0 (2,6):4096/0
(3,2):81/0 (3,3):729/0 (5,2):625/0 (7,2):2401/0. **Artifact diff vs
committed: timing-only** (output.txt `elapsed:` line; `elapsed_s` fields in
results.json — programmatic strip-compare content-identical); artifacts
restored to committed bytes (md5s re-verified above).

**Fresh route (verifier's own, on NEVER-CHECKED rows):**
`/tmp/w11_pe3_fresh.py` — own F₄ arithmetic (multiplication DERIVED from
the polynomial-basis formula (a+bω)(c+dω), not a copied table;
associativity/distributivity/inverse/trace/sqrt self-checked), own window
ring, own classifier written from S1/S2.1/S2.3/S2.4, own closed forms
(§2 above). Rows **(Fqt, q = 4, N = 4)** and **(Fqt, q = 4, N = 5)** —
ABSENT from the sealed 30-row census (Fqt q = 4 stops at N = 3): 65,536 +
1,048,576 monic quadratics, brute-force. Result: **ALL MATCH** — every
(leaf, params) key equals my closed forms on both rows (9 + 13 keys);
sums 4^(2N) exact; drainage undecided = 4^N EXACTLY (256; 1024);
split-decided = inert-decided (26,112 = 26,112; 419,328 = 419,328); max
refine depth = ⌊(N−1)/2⌋ (1; 2) with the depth-2 census 576 = 4 centers ×
(q−1)² instances × 16-member node C(5,3) — predicted before running;
SPLIT-TAIL w-independence visible raw (768 = 768 at N = 5). The exact
q^(−N) drainage law and the every-window σ-symmetry hold on territory no
instrument had ever measured.

---

## 4. SUMMARY FOR THE RECORD

The post-r2 text survives a third hostile pass with ZERO findings. The r2
telescoping identity is correct, faithfully transcribed, and consistent
with its surroundings; the v(2) = 1 pin is exactly load-bearing where the
note says it is, and both downstream consumers (W-12, HMENU3) consume
post-r2 displays that match what W-11 actually states, at honest as-of
pins; the SPLIT-TAIL law and the window-vs-limit bridge re-derive cleanly;
the deep families re-derive from scratch in 𝔽_q[[t]] in both
characteristics, == the committed JSON; the sealed battery re-runs GREEN
and byte-stable; and my own classifier on two never-measured (q = 4)
windows reproduces every closed form, the exact drainage law, and the
window σ-symmetry. **Pass verdict: CLEAN (0/0/0). Acceptance counter: 1 of
2 consecutive clean passes — one more clean pass accepts.**

*Verifier: fresh-context hostile pass PE3, 2026-08-08. Scratch artifacts:
`/tmp/w11_pe3_fresh.py`, `/tmp/w11_pe3_rerun.log`, `/tmp/w11_pe3_rerun2.log`
(not committed).*
