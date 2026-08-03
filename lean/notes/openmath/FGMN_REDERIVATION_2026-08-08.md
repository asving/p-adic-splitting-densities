# FGMN TRANSCRIPTION-SCALE RE-DERIVATION — the [T-5] glue step re-derived from the provenance-pinned print: the window functional lives at the PARENT scale (σ.wPrev), the residual at the GRADED scale (σ.R) — a four-token `SideReads` re-key (PROPOSAL ONLY, Asvin-flag); THE ROW-A SOURCE VERDICT: the source glue step FIRES at row A (the parity wall and the C-e escapee are transcription artifacts, not source facts); PIN-GEN-i DISCHARGED (fresh column-verified extraction at Defs 3.15/3.16/3.18 + 336-site from-print operator tie)

**Unit:** FGMN transcription-scale re-derivation (synthesis-7 queue #2, hardest-first;
charter = `JUNCFORGE_S2_2026-08-08.md` §R3 + the four pass-7 F1 riders,
`docs/SYNTHESIS_PASS7_2026-08-08.md`).  **Genre: design/proposal — STATEMENT-CHANGE
(Asvin-flag).  NOTHING in this note is applied to the corpus.**  Until ROOT
adjudication + the standing flag, the compiled `SideReads` stands as-is and every
JuncForge theorem keeps its exact current meaning.
**Artifacts:** this note; `verification/openmath/fgmn_rederivation_check.py` (the
non-textual leg; 1,093 checks, ALL GREEN first pass; R2 branch REPAIRED at
REVISION 1 and the full battery rerun ALL GREEN — output re-quoted in §S8, console
at `fgmn_rederivation_rerun_r1.txt`) + `fgmn_rederivation_results.json`; the
provenance pins in `docs/references/` (§S0).
No `.lean` file touched.

## S0. Spec gate + provenance pins (rider iii)

Charter located: SYNTHESIS_PASS7 §F1 + queue #2 (dispatch-ready, four riders);
JUNCFORGE_S2 §R3 (task/discipline/product).  Not previously executed (no
`FGMN_REDERIVATION*` note or commit existed).  Riders folded: (i) row-A
satisfiability leg (§S4/§S8), (ii) PIN-GEN-i discharge (§S7), (iii) this section,
(iv) DITER §S3 obligations as fixed points (§S5/§S6).

**The source.**  FGMN = J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual
ideals of MacLane valuations*, arXiv:1305.0775v3 [math.NT], 26 Jul 2013 (title page
of the pinned PDF).  Pins (sha256):

| file | sha256 |
|---|---|
| `docs/references/fgmn_residual_ideals_1305.0775v3.pdf` | `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35` |
| `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt` (fresh `pdftotext -layout`, poppler 22.02.0) | `8d30f15e6d37a52be20634545c95f32e372a233166c5dab8d995c3d5f76e848b` |

PROVENANCE DISCLOSURE (per the rider): the PDF was pinned FROM `/tmp/litunit/fgmn.pdf`
(the literature unit's volatile fetch; byte-identical hash recorded above at pin
time).  No independent re-download was performed this unit; the internal evidence
(title page, section/display numbering consistent with every prior FGMN citation in
the corpus, arXiv stamp in the margin of page 1) identifies the print.  The shared
extraction `/tmp/litunit/fgmn.txt` (sha256 `695412d2…fae1516`) is KNOWN CORRUPTED at
Def 3.15 and was NOT consumed anywhere in this unit; all quotes below are from the
pinned fresh `-layout` extraction (line numbers cite it).

## S1. The source-derived glue step at the read-pair scale

The [T-5] side-read bundle transcribes FGMN's residual-polynomial machinery at one
recorded node.  The load-bearing displays, fresh extraction (`_layout.txt` lines):

* **(A) The polygon is keyed at the PARENT valuation.**  l.869–871: "We consider
  Newton polygon operators  Nᵢ := N_{µᵢ₋₁,φᵢ} : K[x] → 2^{ℝ²},  0 ≤ i ≤ r"; l.384
  (§2): the polygon of g = Σ aₛφˢ is the lower hull of "(s, µ(aₛφˢ))" — at level i
  the ordinate is µᵢ₋₁(aₛφᵢˢ), the PREVIOUS-level valuation (l.937–939: "Denote
  Qₛ := (s, µᵢ₋₁(aₛφᵢˢ)) ∈ Cᵢ, so that {Qₛ | 0 ≤ s} is the cloud of points whose
  lower convex hull is Nᵢ(g)").
* **(B) The window law — eq (13), l.940–944:** off-stride slots sit strictly above;
  at stride slots s = sⱼ, "µᵢ(aₛφᵢˢ) = α if and only if µᵢ₋₁(aₛⱼ) = αⱼ", with
  sⱼ = s(α) + j·eᵢ, αⱼ = α − sⱼ(wᵢ + λᵢ) ∈ Γᵢ₋₁ (l.923, l.934).  The augmentation
  bridge is Lemma 2.3's proof (l.415): "µ′(aₛφˢ) = µ(aₛφˢ) + sλ".
* **(C) The digits — Def 3.16, l.916–923:** for i > 0 the j-th coefficient of
  R_{i,α}(g) is ǫᵢ₋₁(αⱼ)·R_{i−1,αⱼ}(aₛⱼ)(zᵢ₋₁): the digit of the coefficient aₛⱼ is
  read by the PARENT-level operator at the parent-level target αⱼ.  Support law =
  Cor 4.4(2), l.1085–1087: "The j-th coefficient of R_{i,α}(g) is non-zero if and
  only if µᵢ₋₁(aₛⱼ) = αⱼ, or equivalently, the point Qₛⱼ lies on L_α."
* **(D) The twist — Def 3.15, l.910–915** (column-verified, §S7): ǫᵢ(α) =
  zᵢ^{ℓ′ᵢs(α) − ℓᵢu(α)}, (s,u) split by eq (12) (l.881: u(α)eᵢ + s(α)hᵢ = e(µᵢ)α,
  0 ≤ s(α) < eᵢ); ǫ₀ ≡ 1 by convention.
* **(E) THE GLUE-STEP DISPLAY — Theorem 4.2, l.1028–1029:** for α = µ(g),
  "H_µ(g) = ϕᵣ(α)R_{r,α}(g)(yᵣ) = ϕᵣ(g)Rᵣ(g)(yᵣ)" — the residual of g in the
  CURRENT graded algebra Gr(µ) equals the anchor monomial ϕᵣ(g) = xᵣ^{s(g)}pᵣ^{u(g)}
  (Lemma 4.1, l.1017–1019; window endpoint data) times the residual polynomial whose
  coefficients are the parent-level reads of (C).  Normalization Def 3.18
  (l.994–1000): Rᵢ(g) = R_{i,α}(g)/y^{j₀}, j₀ = ⌊s(g)/eᵢ⌋.  Landing tie: Cor 5.6(2),
  l.1263–1265: Rᵢ(φᵢ₊₁) = ψᵢ.  Degenerate stratum: eq (14), l.1004:
  R_{i,α}(φᵢˢ) = y^{⌊s/eᵢ⌋}, Rᵢ(φᵢˢ) = 1.

**The two-scale law IS in the print.**  One node holds BOTH scales, glued by Thm 4.2:
the window/digit side ((A)–(C)) is computed entirely from PARENT-level valuations
µᵢ₋₁ of the development coefficients (values in Γᵢ₋₁); the residual side ((E)) lives
in the CURRENT graded algebra Gr(µᵢ).  This is exactly the stage-1 measured law
(JUNCFORGE_S1 §S2(a): pattern at the read-pair scale, monomial at coarser scales) and
the derivable clause (iii) (`juncforge_clauseIII_derivable`: σ.R f exact at the graded
stage) — both fixed points reproduced by the print, not repaired away.

**Stage-vocabulary translation** (project cumulative ℤ-normalization; MovesC
`RegradeOf` at a read-pair-graded junction stage: σV.wPrev = the parent stage's w
pointwise, σV.w = the (e★,h★)-slot-minimum = e★·wPrev on the coefficient carrier):
with ν.e = eᵢ, ν.h = e(µᵢ)(wᵢ + λᵢ), ν.gam = e(µᵢ)·µᵢ(f), σ.wPrev(B) =
e(µᵢ₋₁)·µᵢ₋₁(B), multiplying (B) by e(µᵢ) gives the source window functional in
Lean tokens:

    e(µᵢ)·µᵢ(Bⱼφʲ)  =  ν.e * ν.σ.wPrev (B j)  +  j * ν.h      (⋚ ν.gam)

— the coefficient weight enters at σ.wPrev, never at the graded σ.w.  (On the
harness side this is verbatim the certified functional `e1*w1(B_j) + j*gamma2` that
carried all 336 stage-1 P3a sites.)

## S2. The transcription diagnosis

The compiled `SideReads` (`lean/LeanUrat/HC2/Defs.lean:280`) reads clauses (i)/(ii)'s
window functional as `(ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ)` — the node
stage's OWN weight σ.w on the coefficient.  At a read-pair-graded junction stage
(the S1 §S5 central pin: build σ₁ AT the read pair, which is what makes clause (iii)
derivable), σ.w = e·σ.wPrev on the coefficient carrier, so the compiled functional
is e·(e·wPrev(Bⱼ)) + j·h — the stride weight is double-scaled by e relative to the
key term.  Row A displays it exactly (slots {0,2}, wPrev(24) = 3, h = 3): corrected
functional {2·3+0, 0+2·3} = {6,6} = gam ✓; compiled functional {2·6+0, 0+2·3} =
{12,6} — no single gam, and forcing it (σ.w(24) = ν.h = 3, odd) collides with the
graded tie σ.w(24) = 2σ.h = 6 (even).  **The JuncForge parity wall
(`juncforge_no_e2_junction`) is the arithmetic shadow of this double-scaling** — a
true theorem about the compiled clause shape, and per §S1 a transcription artifact
relative to the print, which single-scales the stride weight.

**Why every compiled instance was invisible to the defect:** at e = 1 frames and at
identity regrades the two scales agree pointwise on the carrier (`RegradeOf.w_coeff`
at e★ = 1; `U31.bStage` literally sets `w := bw, wPrev := bw`), and the compiled
positive gates (U31's (1,1) base read, HK25's e = 1 recentering seam, every
`gate_*` instance) all live there.  The defect fires exactly at genuinely graded
e ≥ 2 junction frames — the C-e escapee locus, where no compiled instance ever
existed to catch it.

## S3. THE PROPOSAL (verbatim Lean-ready diff; PROPOSAL ONLY — no application)

One definition changes: `SideReads`, clauses (i) SIDE and (ii) DIGITS' functional
leg — `ν.σ.w` → `ν.σ.wPrev` at exactly FOUR tokens.  No other clause, definition,
or statement is touched; `junc_bundle`/`ReadsOf`/`DIterJunctionSupplier` inherit
textually unchanged.

```lean
-- HC2/Defs.lean, def SideReads — clause (i) SIDE:            [OLD]
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ)) ∧
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.w (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)) ∧
-- clause (ii) DIGITS, functional-equality leg:               [OLD]
      (ν.e : ℤ) * ν.σ.w (B (ν.s0 + ν.e * k)) + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ)
        = ν.gam ∧
```

```lean
-- HC2/Defs.lean, def SideReads — clause (i) SIDE:            [NEW — PROPOSED]
  ((∀ j : ℕ, j < Nd → B j ≠ 0 →
      ν.gam ≤ (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ)) ∧
   (∀ j : ℕ, j < Nd → B j ≠ 0 →
      (ν.e : ℤ) * ν.σ.wPrev (B j) + (j : ℤ) * (ν.h : ℤ) = ν.gam →
      ∃ k : ℕ, k ≤ ν.wSide / ν.e ∧ j = ν.s0 + ν.e * k ∧ ν.pat k ≠ 0)) ∧
-- clause (ii) DIGITS, functional-equality leg:               [NEW — PROPOSED]
      (ν.e : ℤ) * ν.σ.wPrev (B (ν.s0 + ν.e * k)) + ((ν.s0 + ν.e * k : ℕ) : ℤ) * (ν.h : ℤ)
        = ν.gam ∧
```

Untouched, with source warrant: clause (ii)'s residual leg (already at
`ν.σ.wPrev` in the T-exponent — consistent with the corrected functional); clause
(iii) ANCHOR/ORDER (σ.R f at the graded stage = Thm 4.2's H_µ(g); the derivable
fixed point); clauses (iv)–(vi); `junc_bundle`'s recentering rider (a CURRENT-scale
key-improvement tie, not a window read).  Equivalent form, displayed not proposed:
at stages satisfying the stretch law w = e·wPrev on the carrier the corrected
functional equals `ν.σ.w (B j) + j * ν.h` (single-scaled); the wPrev form is
preferred because it is SideReads-local (no reliance on an unratified stage law —
the D.7 σV residual-law clauses remain a named open addendum).

**Application-time obligations (for the adjudicated unit, not this one):** (a) the
mandatory gate re-runs — U31 `gate_readsOf_inert2` and every SideReads-consuming
gate must re-discharge; expected verbatim since all compiled positive instances have
w = wPrev pointwise at their stages (§S2), but expectation is not discharge; (b) a
grep census of `SideReads` consumers (U19–U25 projections, ReadsOf, GlueRun,
JuncForge) with per-consumer disposition; (c) the JuncForge theorems are NOT edited
— they bind the old shape and become the historical record of the mis-scale; (d)
per the standing verifier-implementation expectation (pass-7 F2c), the acceptance
verifier should re-implement §S8's battery from this note alone.

## S4. THE ROW-A SOURCE VERDICT (defined term, per the pass-7 F6 template)

**THE ROW-A SOURCE VERDICT** := *at the row-A fiber (classificand fA = X² + 4X + 28
read against a Φ1A = X + 2-keyed junction frame graded at the read pair (2,3), over
ℤ₂ / any char-2 residue instance, landing Φ₂ = X² + 4X + 12), the FGMN glue step —
Def 3.16 at i = 2 composed with Theorem 4.2 — FIRES: both window slots {0,2} are
on-line at the parent scale, R₂(fA) = ψ₁ is the degree-1 residual with nonzero
constant term (Cor 4.4(4)), and the corrected §S3 transcription is numerically
satisfiable at this fiber with record (e,h,gam,s0,wSide,pat,μ,vtx) =
(2,3,6,0,2,(1,1),1,1).  This is a SOURCE-plus-numerics verdict, not a Lean theorem;
no Lean statement is proved or refuted by it.*

Every restatement below uses the term verbatim.  Consequences:

* THE ROW-A SOURCE VERDICT decides the §R3 fork "source glue step refuted at row A"
  vs "transcription mis-scaled" for the SECOND branch: the print contains no parity
  obstruction at eᵢ = 2 with odd parent weight (§S1(B)–(C): all coefficient
  arithmetic stays in Γᵢ₋₁; nothing demands child-graded coefficient ties), and the
  from-print operator computes the row-A residual without incident (§S8, R3/R4).
* The C-e escapee ("no compiled e ≥ 2 junction instance exists to feed GlueRun") is
  a transcription artifact: under the §S3 proposal the S1 §S5 row-A construction
  becomes buildable, per THE ROW-A SOURCE VERDICT.  It is NOT a source fact.
* The parity-wall fixed point is honored in the decided direction: the source says
  the junction is satisfiable at row A, so a correct transcription MUST make it
  satisfiable there — the corrected clause's window/support legs are (R1: a
  scale-sensitive window/support satisfiability check GREEN at all 336 sites, plus
  the row-A record instantiation, §S8; NOT full corrected-bundle satisfiability —
  the Lean-side construction stays owed, §S9), while the compiled clause-(ii)
  equality system admits NO single gam′ at any of the same 336 sites (R2, repaired
  any-gam′ branch, REVISION 1: 0/336 measured; every site has ≥ 2 distinct
  compiled values at its supported slots) exactly as `juncforge_no_e2_junction`
  proved.

## S5. Fixed points — all four reproduced, none repaired away

| fixed point | status under the §S3 proposal |
|---|---|
| stage-1 two-scale law (wPrev vs w at the (2,3) pins; wPrev(24)=3, w(24)=6) | REPRODUCED BY THE PRINT (§S1(A)/(E): window at µᵢ₋₁, residual in Gr(µᵢ)); the corrected clause (ii) sits at the wPrev leg, clause (iii) stays at the w leg |
| `juncforge_clauseIII_derivable` (clause (iii) exact at the graded scale) | UNTOUCHED — the diff does not touch clause (iii); Thm 4.2 is its source warrant |
| the parity wall (row-A e = 2 satisfiability must follow the SOURCE) | DECIDED FROM THE PRINT: source fires (THE ROW-A SOURCE VERDICT); corrected clause's window/support legs satisfiable at row A (numeric check — the full-bundle Lean construction stays owed, §S9), compiled clause stays refuted — the JuncForge theorems keep their exact meaning |
| DITER_RESTATE §S3 supplier obligations (𝒟₂ carrier on canonical anchors; ITER-LAW cocycle with both constants + fibration term; B0a/D-REAL/NOT-CYCLIC gates) | UNCHANGED AS STATED — the diff touches only the window functional's scale; no digit-algebra clause is altered; the corrected bundle remains statable in the supplier's hosting form (§S6) |
| D0 stratum (compiled gate seam f = key) | NOT RESURRECTED: eq (14) (Rᵢ(φᵢˢ) = 1) is the source's own degeneracy — the pure-key residual holds no pattern data; clause (ii)'s B(s0) ≠ 0 demand fails at B₀ = 0 under either scale, so `gate_glue_conditional` stays vacuous at its compiled instance and `juncforge_D0_instanceFalse` keeps its exact meaning |

## S6. What `DIterJunctionSupplier`'s gates become (under adjudication; displayed, not applied)

The supplier statement (`H1/GlueRun.lean:875`) inherits the corrected `SideReads`
textually unchanged: antecedent `σ₁.Φ.natDegree < n` and shape stay verbatim.  What
changes is its DISCHARGE landscape:

1. **The junction legs unblock.**  Under the compiled clause the supplier was
   undischargeable at every genuinely graded e ≥ 2 frame at the row-A read
   (`juncforge_no_e2_junction`); under the §S3 proposal the S1 §S5 row-A instance
   (junction stage σ₁ built at (2,3); ν₁ with the §S4 record; landing Φ₂) becomes
   the first compiled e ≥ 2 discharge candidate — the queue-#9 unit's gates should
   be stated against the corrected clause and re-priced from that spec.
2. **ITER-LAW stays the displayed hypothesis** (DITER §S3: consumable only as a
   named hypothesis until proved).  At the row-A candidate itself e₀ = 1, so the
   cocycle degenerates to the theorem-backed D-REAL leg — the first discharge can
   be ITER-LAW-free with the degeneration displayed (S1 §S5's honest scope).
3. **The three sanity gates carry over verbatim** (B0a associativity; D-REAL
   degeneration at e₀ = 1; NOT-CYCLIC on the row-N value pattern) — nothing in the
   re-key touches the carrier or cocycle, so any discharge instance must still
   reproduce them; the cyclic-form fence stays binding.
4. **The JuncForge refutation theorems become the mis-scale record**: statements
   unedited, meanings unchanged (they bind the OLD clause shape); their display
   text gains a pointer to this note at application time only.

## S7. PIN-GEN-i DISCHARGE (rider ii) — the owed non-textual leg at Defs 3.15/3.16/3.18

TR3-S3's pin: Def 3.15 at level 2, Def 3.16 at i = 3, Def 3.18 at i = 3 were consumed
as level-GENERIC displays with computational discrimination only; owed was a fresh
`pdftotext -layout` re-extraction, hand-verified at the instantiated indices, under a
provenance-pinned PDF.  Discharged here:

* **Fresh decorrelated extraction**: §S0's pinned `-layout` file (sha256 recorded;
  poppler 22.02.0), distinct from the corrupted shared extraction by construction
  and by hash.
* **Def 3.15 corruption located and cured by layout.**  The shared `fgmn.txt`
  (l.1238–1241) orphans the prime on its own line with no column information — the
  exponent's prime placement (which ℓ is primed) is unrecoverable there; that is
  precisely the GRB REVISION-11 artifact.  The fresh `-layout` extraction
  (l.910–912) preserves columns:

      Definition 3.15. For 0 ≤ i < r and α ∈ Γi , we define
                                                         ′
                                          ǫi (α) = (zi )ℓi s(α)−ℓi u(α) ∈ F∗i+1 ,

  The ′ sits at codepoint column 52 = directly above the *i* of the FIRST ℓᵢ
  (columns 51–52), i.e. the print reads ǫᵢ(α) = zᵢ^{ℓ′ᵢs(α) − ℓᵢu(α)} — the
  corrected (mode-C / N-1-certified) reading, now with a hand-verified print leg.
* **Genericity at the instantiated indices, hand-verified**: Def 3.15 is displayed
  for all 0 ≤ i < r (l.910), Def 3.16 for all 0 ≤ i ≤ r (l.916), Def 3.18 for all
  1 ≤ i ≤ r (l.994–995), with r the arbitrary chain length fixed only by §3's
  preamble; the recursions contain no index-special cases beyond i = 0 (base) —
  so the consumed instantiations (ǫ at level 2; Defs 3.16/3.18 at i = 3) are pure
  specializations of the printed displays.  Verified by reading the full §3.4
  block in the fresh extraction (l.869–1006); no footnote or side condition
  restricts i.
* **Numeric cross-check (falsifier, not proof)**: §S8 row R4 — a from-print
  reimplementation of Defs 3.15/3.16/3.18 (transcribed from the fresh displays; a
  DIFFERENTIAL falsifier sharing the certified `Tower` state — `w1`, `res_digit`,
  `K1`, `z1`, the keys and chain parameters — with the certified stack, so
  independent only in its recursion/exponent code, NOT an independently derived
  operator)
  ties the certified reading-C operator at all 336 deep sites, 0 mismatches, and
  the misread exponent (ℓᵢs − ℓ′ᵢu) breaks the tie on EVERY tower row (24–48
  discriminating sites per row) — the prime placement is load-bearing and the
  column reading is the one nature confirms.

Residual honesty: the discharge rests on ONE extraction tool run at ONE tool
version (plus the numeric leg); a second extractor pass was not performed.  The
per-index hand-verification is of the pinned extraction, not of rendered PDF glyphs.

## S8. The numerics record (falsifiers only)

`verification/openmath/fgmn_rederivation_check.py` — preregistered rows in the
script header (predictions sealed pre-run) + the REVISION 1 ADDENDUM (the R2
branch repair, preregistered in the header BEFORE the revision rerun);
deterministic seed 20260816; same ROWS × CONFIGS roster and family builders as
the sealed stage-1 harness (imported, not edited; site structure identical,
random digits regenerated).  REVISION 1 rerun output [REV3: the block below is an EDITED RENDER of the raw file `fgmn_rederivation_rerun_r1.txt` — numbers identical to the raw record MODULO ORDER — the raw file prints the sorted set [6,12]; this render lists per-slot [12,6] at slots [0,2]; both carry the same two values and the same UNSAT conclusion [REV4: the order divergence disclosed at the header, per pass-5 gap]; the raw file is the record] (console saved at
`fgmn_rederivation_rerun_r1.txt`; supersedes the first-pass block, which had the
R2 false-negative branch):

    R0 bug detector: D0 pattern == psi1                     pred 0  obs 0 (  28)  GREEN
    R1 CORRECTED battery (wPrev scale) at deep sites        pred 0  obs 0 ( 336)  GREEN
    R2 COMPILED (ii) any-gam' UNSAT at the same sites       pred 0  obs 0 ( 336)  GREEN
    R3 row-A Lean-shape record + compiled UNSAT display     pred 0  obs 0 (   1)  GREEN
    R4 from-print Defs 3.15/3.16/3.18 == certified R2s      pred 0  obs 0 ( 336)  GREEN
    R5 eq-(14) key-power law (D0 source shape)              pred 0  obs 0 (  56)  GREEN
    deep node-1 sites: 336
    MISREAD-EPSILON METER (mode P != certified), by row: {A:24, B:48, C:24, K:28, L:24, M:48, N:48}
    R2 SUPPORT METER (distinct compiled values at supported slots), by count: {2:264, 3:68, 5:4}
    TOTAL checks 1093   VERDICT: ALL GREEN

    ROW-A record: Phi2=[12,4,1] fA=[28,4,1] (e,h,gam,s0,wSide,mu)=(2,3,6,0,2,1)
                  pat=[1,1] vtx_digit=1
    ROW-A compiled-scale display: old functional at slots [0,2] = [12,6] [REV3: render order corrected per pass-4 gap 3 — §S2 computes {2·6+0, 0+2·3} = {12,6} at slots 0,2 respectively; the UNSAT conclusion unchanged]
                  (needs a single gam; corrected = [6])

Readings: R1+R3 = the rider-(i) acceptance leg — a SCALE-SENSITIVE WINDOW/SUPPORT
satisfiability check (clauses (i-a)/(i-b)/(ii-support)/(iii-window-length),
wPrev-scaled) GREEN at all 336 sites, plus the row-A record instantiation; NOT
full corrected-bundle `SideReads` satisfiability (no σ.R residual-leg
instantiation — the Lean-side construction stays owed, §S9); R2 = the parity wall
reproduced as universal at the compiled scale under the repaired any-gam′ branch
(0/336; the support meter records ≥ 2 distinct compiled values at every site, so
no single gam′ exists anywhere — the wall is the transcription, not the
mathematics); R4+R5 = the from-print operator differential tie (§S7 scope: shared
certified Tower state, independent recursion code) and the source's own D0
degeneracy.  Numerics are falsifiers: a RED anywhere would have killed the
proposal; GREEN does not prove it.

## S9. What this unit does NOT do

No corpus application: no `.lean` file touched; `SideReads` stands as compiled;
every JuncForge/GlueRun/U31 theorem keeps its exact current meaning.  The §S3 diff
is a PROPOSAL awaiting ROOT adjudication + the Asvin statement-change flag (the
standing statement-change authority covers honest Lean statement repairs, but the
charter pins THIS change as proposal-only — the compiled refutation record depends
on the old shape, so supersession must be adjudicated at ROOT, not executed
unilaterally).  No claim that the source glue step is FORMALIZED — THE ROW-A SOURCE
VERDICT is source-plus-numerics, and the Lean-side satisfiability of the corrected
bundle is a construction owed by the queue-#9 unit after adjudication.  No claim at
towers other than the measured roster; no order ≥ 3 claim; ITER-LAW remains the
open lemma of DITER_RESTATE §S2.  PIN-GEN-i's discharge carries the §S7 residual
(single extractor pass).  Anticipated at acceptance (pass-7 F2c standing): a
verifier-owned from-note implementation of §S8's battery.

— FGMN transcription-scale re-derivation, 2026-08-08 (wallclock 2026-08-03).

## REVISION 1 (response to pass 1; wallclock 2026-08-03)

Pass 1 (`FGMN_pass1_report.md`): **0 critical / 4 gaps, VERDICT GAPS-ONLY.**
CONFIRMED by the verifier: the parent-scale diagnosis + double scaling (finding 1),
the row-A arithmetic and record (finding 5), the PIN-GEN-i source leg incl. the
Def 3.15 prime placement and generic ranges (finding 6), and the D0/blast-radius
wording (finding 7) — that perimeter is untouched in this revision.  The four
gaps, quoted and fixed:

* **Gap (finding 2) — R2 false-negative branch.**  Quote: "If `oldvals` is a
  singleton different from recorded `gam`, an alternative single `gam'` exists,
  yet the test reports no violation. … Thus 'compiled 0/336' as an **any-gam**
  discriminator is not established by this script."  FIX: the branch in
  `check_compiled_unsat` repaired to the semantics this note claims — a site is a
  violation iff SOME single gam′ solves the compiled clause-(ii) equality system,
  i.e. iff the compiled values at the supported stride slots collapse to ≤ 1
  distinct value (ANY singleton counts, recorded-gam or not).  Repair + a derived
  sealed prediction preregistered in the script's REVISION 1 ADDENDUM header block
  BEFORE the rerun (derivation: at a supported slot the compiled value is
  e·gam − j·h·(e−1); e = e1 ≥ 2 and h = gamma2 > 0 on every roster row, so
  distinct supported slots give distinct values; every certified pattern has ≥ 2
  nonzero digits via the Def 3.18 strip + nonzero leading digit).  RERUN: ALL
  GREEN, **R2 = 0/336 measured under the repaired branch — the count did NOT
  change** — and the new R2 SUPPORT METER now RECORDS the previously unasserted
  fact: every one of the 336 sites has ≥ 2 distinct compiled values at its
  supported slots ({2: 264, 3: 68, 5: 4}).  Output re-quoted in §S8; console at
  `fgmn_rederivation_rerun_r1.txt`.
* **Gap (finding 3) — "336/336 SAT" overstates R1.**  Quote: "this is a 336-site
  **scale-sensitive window/support check**, not 336 full corrected-bundle
  satisfiability proofs."  FIX: every such occurrence rescoped (§S4 parity-wall
  bullet, §S5 parity-wall row, §S8 readings, artifacts header) to what R1
  actually checks — a scale-sensitive window/support satisfiability check
  (clauses (i-a)/(i-b)/(ii-support)/(iii-window-length)) at 336 sites, NOT full
  corrected-bundle `SideReads` satisfiability; clause (iii)'s σ.R leg is never
  instantiated numerically.  The owed Lean-side construction display (§S9,
  queue #9) stands unchanged.  Rider on §S4's defined term: THE ROW-A SOURCE
  VERDICT's "numerically satisfiable at this fiber" is to be read in the same
  scope — R3's window/support + record numerics (the term's own "SOURCE-plus-
  numerics verdict, not a Lean theorem" sentence already fences this; the
  definition text is confirmed perimeter and is not edited).
* **Gap (finding 4) — R4 independence overstated.**  Quote: "it consumes
  certified `Tower` state and methods including `T.w1`, `T.res_digit`, `T.K1`,
  `T.z1`, keys, and chain parameters … not an independently derived operator in
  the advertised sense."  FIX: §S7's "sharing only ring primitives" rescoped to a
  DIFFERENTIAL falsifier sharing the certified Tower state (w1/res_digit/K1/z1/
  keys/chain parameters), independent only in its recursion/exponent code; same
  supersession recorded in the script ADDENDUM (the sealed header row stays as
  the historical record).
* **Gap (finding 8) — local artifact verification not completed by the
  verifier** (sandbox `bubblewrap` failure; the SHA pins, JSON, and the 1,093
  checks were reconciled, not re-executed).  FIX (as far as this unit can): fresh
  full re-execution this revision (ALL GREEN, counts above), console persisted,
  JSON regenerated (now incl. `r2_support`), and both provenance pins
  re-verified byte-identical this session (`sha256sum`: PDF 651b0cef…f615f35,
  layout extraction 8d30f15e…76e848b).  This is prover-side re-execution, not
  verifier-independent execution — the pass-7 F2c verifier-owned from-note
  implementation stays the acceptance obligation.

Nothing else changed: the §S3 proposal text, THE ROW-A SOURCE VERDICT definition,
§S7's extraction record, and all confirmed-perimeter sections are byte-identical.
**Acceptance counter: 0/2 consecutive clean passes** (a revision does not
advance it); pass 2 verifies this note + the repaired script from scratch.

— FGMN re-derivation REVISION 1, 2026-08-08 (wallclock 2026-08-03).

## REVISION 2 (orchestrator-applied, per pass 3 — Fable, with the independent execution leg)

Pass 3 (FGMN_pass3_report.md, 07c39b4): GAPS-ONLY 0C/4G — the execution leg was EXACT
(battery re-run byte-identical incl. timings; JSON byte-identical; both sha256 pins
verified; the layout extraction independently REGENERATED from the pinned PDF,
byte-identical; Def 3.15's prime col-52 arithmetic recomputed; the §S3 OLD block
verbatim-unique in HC2/Defs.lean and the diff appliable). Fixes:
1. **BLAST RADIUS COMPLETED (pass-3 gap 1)**: the proposal's application perimeter must
   include the DictIII MIRROR LAYER — `SideClauseR1`
   (Scaffold/DictIII/Locality.lean:272, a VERBATIM copy of clause (i)) with its
   definitional tie `sideReads_r1` (:280), plus the Window.lean/Locality.lean σ.w
   restatements — these BREAK (or silently diverge) if the re-key is applied to
   SideReads alone. Any application diff must carry the mirror sites in the same
   change-set.
2. **APPLICATION-MODE ACCOUNT CORRECTED (pass-3 gap 2)**: the prior "statements
   unedited, meanings unchanged" claim is IMPOSSIBLE under an in-place re-key —
   JuncForge's refutation theorems bind `SideReads` BY NAME, so an in-place edit
   re-keys what those theorems assert. The proposal's RECOMMENDED application mode is
   therefore a NEW definition (`SideReads'` at the parent-valuation keying) with the
   glue route re-stated against it, leaving `SideReads` and the JuncForge theorems
   byte-frozen as the historical record of the old transcription; the in-place variant
   is displayed as the alternative WITH its re-keying consequence stated. The choice is
   part of the Asvin-gated decision.
3. Token count corrected: the diff is THREE tokens (Defs.lean 285/287/292), not four
   (pass-3 gap 3); every "four-token" occurrence in this note and the ledger record is
   superseded by this line.
4. §S8's "re-quoted" block relabeled as an EDITED RENDER of the output (numbers
   identical to the raw file; the raw file is the record) (pass-3 gap 4).
Counter stays 0/2; passes 4+5 decide.

## REVISION 3 (orchestrator-applied, per pass 4)

Pass 4 (FGMN_pass4_report.md): GAPS-ONLY 0C/3G; the diagnosis, row-A record, branch
semantics, and all rescopes survived again. Fixes:
1. **Mirror-layer disposition SPECIFIED (pass-4 gap 1)** — under the RECOMMENDED
   new-definition route: the historical mirrors are ALSO byte-frozen; the application
   change-set introduces primed mirrors — `SideClauseR1'` (the verbatim clause-(i) copy
   of `SideReads'`) with `sideReads_r1'` as its definitional tie — and restates the
   supplier/glue route against `SideReads'` (the prior "inherits ... textually
   unchanged" sentence is MODE-CONDITIONAL: it describes only the in-place variant).
   The σ.w restatement sites enumerated exactly: Window.lean:177, :258, :260, :266,
   :544 (the hwS binder) and Locality.lean:98 (comment), :121-:129
   (`σ.w`-hypothesis cluster) — each gets a primed twin or a mode-conditional bracket
   in the application change-set; none is edited before the Asvin gate.
2. The §S8 block is now ACTUALLY labeled as an edited render in place (REVISION 2 had
   described the relabel without performing it — pass-4 gap 2).
3. The §S8 slot-order render corrected to [12,6] at slots [0,2] (pass-4 gap 3; §S2's
   computation was and is correct; the UNSAT conclusion unchanged).
Counter stays 0/2; passes 5+6 decide.

## REVISION 4 (orchestrator-applied, per pass 5 — the verifier's complete DictIII sweep adopted)

Pass 5 (FGMN_pass5_report.md, af88f12; the execution leg again EXACT): CRITICAL 1C/1G —
REVISION 3's "enumerated exactly" was FALSE. The COMPLETE application perimeter, per the
verifier's own DictIII grep, now of record:
- **SideClauseR2** (Locality.lean:735 — the VERBATIM clause-(ii) mirror with the
  re-keyed σ.w functional at :738) + its tie **sideReads_r2** (:744) — the R2 pair
  joins the R1 pair in the primed-mirror set.
- **The (†)/hdag transfer layer**: Locality.lean :322/:381/:398/:658/:794/:828/:847/
  :1327 — at e ≥ 2 the corrected-scale row is STRICTLY STRONGER than the dagger
  supplies, so the primed twins need RE-DERIVED readCeil arithmetic, not renames. The
  application change-set includes those derivations (priced into the Asvin decision).
- **Window.lean :554/:557** endpoint functionals (in addition to :177/:258/:260/:266/:544).
- **The R5 tie family / read_locality assembly** — restated against the primed set.
The REVISION-3 claim "enumerated exactly" is superseded by THIS list, which carries the
verifier's grep as its provenance (af88f12); any residual site found later joins the
change-set under the same rule (the perimeter is defined by the grep discipline, not by
this list's completeness claim). Counter stays 0/2; passes 6+7 decide.

## REVISION 5 (orchestrator-applied, per pass 6)

Pass 6 (FGMN_pass6_report.md, c7df512; execution leg again fully independent, the
REVISION-4 list reconciled EXACTLY on every named site): GAPS-ONLY 0C/2G. Fixes:
1. **The perimeter DEFINITION upgraded (pass-6 gap 1)**: the grep-discipline rule is
   replaced by the REFERENCE-CLOSURE rule — the application perimeter is the identifier
   -reference closure of `SideReads` (grep -rn 'SideReads' over ALL of lean/LeanUrat/,
   not DictIII alone) UNION the σ.w/readCeil/read_locality semantic ring, with the term
   set now PINNED on record: {SideReads, SideClause, sideReads_, σ.w, readCeil,
   read_locality, lastRead_of_readsOf_snoc} [REV8: the un-suffixed form struck — dead under the matcher]. A term-list can miss what its terms cannot see;
   a reference closure cannot miss a by-name binder. Under the upgraded rule the two
   pass-6 sites join the perimeter:
   - `lastRead_of_readsOf_snoc` (Window.lean:506–521 — binds `SideReads` by name).
   - CU1.lean's read_locality/readCeil III-U6 consumer ring (the in-place variant
     silently diverges through it; the new-definition route restates it against the
     primed set).
2. The REVISION-4 "defined by the grep discipline" sentence is superseded by the
   reference-closure rule above (its provenance: pass-6's finding that the discipline's
   terms were not pinned and could not self-repair).
Counter stays 0/2; passes 7+8 decide.

## REVISION 6 (orchestrator-applied, per pass 7)

Pass 7 (`FGMN_pass7_report.md`, 5cdc12a): GAPS-ONLY 0C/2G — the seventh consecutive
substance-clean round; the diagnosis/row-A/branch/meter/rescopes/JuncForge-honesty
perimeter untouched again.  The two gaps, quoted and fixed:

1. **Gap (pass-7 finding 1) — verifier execution blocked.**  Quote: "Both normal and
   non-login-shell attempts failed before execution because the sandbox launcher could
   not find `bubblewrap`.  Consequently, I cannot independently certify the actual
   all-tree reference census, named-site line locations, artifact hashes, or
   1,093-check rerun."  FIX (as far as this unit can — the REVISION-1 finding-8
   pattern): the demanded artifacts executed prover-side THIS revision and placed on
   record so a sandbox-blocked verifier can reconcile textually:
   - **All-tree census on record**: `grep -rn 'SideReads' lean/LeanUrat/` = 260
     reference lines — 246 in `.lean` files across 36 distinct files + 14 in the two
     `MANIFEST.json`.  Top files: HC1/V9_K1nonrec.lean 27, DictIII/Locality.lean 23,
     H1/GlueRun.lean 19, H1/JuncForge.lean 18, H1/SiteBlock.lean 14,
     H6/TerminalRead.lean 13, HK20 13, HK57 11, HK53_e2Ruling 10, HK19 9,
     DictIII/Window.lean 9.
   - **Named-site line verification**: `def SideReads` at HC2/Defs.lean:280 with the
     three σ.w tokens at :285/:287/:292; `SideClauseR1` Locality.lean:272 /
     `sideReads_r1` :280 / `SideClauseR2` :735 (σ.w functional at :738) /
     `sideReads_r2` :744; `lastRead_of_readsOf_snoc` Window.lean:506;
     `DIterJunctionSupplier` GlueRun.lean:875 — all re-read at their recorded lines
     this session.
   - **Hashes + battery**: both sha256 pins re-verified byte-identical (PDF
     651b0cef…f615f35; layout 8d30f15e…76e848b); the 1,093-check battery re-executed
     ALL GREEN, meters identical (misread-ε {A:24,B:48,C:24,K:28,L:24,M:48,N:48}; R2
     support {2:264,3:68,5:4}), and `fgmn_rederivation_results.json` reproduced
     BYTE-IDENTICAL (git-clean after the rerun).
   Honesty rider: this is PROVER-SIDE re-execution, not verifier-independent
   execution — the gap's demand can only be discharged by a verifier pass with a
   working sandbox (passes 3/5/6 each carried independent execution legs; the pass-7
   blockage is environmental, not evidential), and the pass-7 F2c verifier-owned
   from-note battery stays the acceptance obligation.

2. **Gap (pass-7 finding 2) — the closure rule under-specified.**  Quote: "A single
   grep computes direct references, not a transitive identifier-reference closure.
   Downstream consumers that mention only an intermediary such as `ReadsOf` are not
   necessarily returned.  The pinned semantic set also omits `ReadsOf`, `junc_bundle`,
   `GlueRun`, and `DIterJunctionSupplier`."  FIX — the REVISION-5 rule is superseded
   by the report's second offered form, a genuinely RECURSIVE closure with an explicit
   expansion rule:
   - **THE EXPANSION RULE**: SEED = {`SideReads`}.  ROUND: for every identifier t in
     the set, `grep -rn '<t>' lean/LeanUrat/` (all-tree, case-sensitive); every
     declaration (def/theorem/structure/abbrev/instance) whose statement or body
     contains a hit joins the set BY NAME.  ITERATE until a round adds no identifier
     (fixpoint).  The application perimeter = this fixpoint UNION the pinned semantic
     ring.
   - **The pinned term set is EXTENDED** with the four named omissions: {`ReadsOf`,
     `junc_bundle`, `GlueRun`, `DIterJunctionSupplier`} join {`SideReads`,
     `SideClause`, `sideReads_`, `σ.w`, `readCeil`, `read_locality`,
     `lastRead_of_readsOf`}.
   - **Scope repair on the pass-6 sentence**: "a reference closure cannot miss a
     by-name binder" is TRUE of the recursive fixpoint and was NOT established by
     REVISION 5's displayed one-command procedure, which computes round 1 only; that
     display is superseded.
   - **Round-2 evidence on record** (why the recursion is load-bearing): 15 `.lean`
     files reference the four intermediaries yet never mention `SideReads` directly —
     HK52_stretchGate, U19_runCoherent, U1_negWitness, U23_runRealizable, U25_polTotal,
     U27_gateInert, UE_vtxUpper, MovesT/Defs, MovesT/G1_toyGate, DictIII/CU1,
     DictIII/Hyps, H1/RCWitness, H1/RunBinding, H6/EngineConform, H6/RowsK4.  A single
     direct grep returns none of them.
   - The full fixpoint COMPUTATION (per-declaration membership + per-consumer
     disposition) is an application-time obligation and joins §S3's obligation (b);
     this revision pins the RULE and the rounds-1/2 evidence, not the completed set.

Nothing else changed: the §S3 proposal (three tokens, REVISION-2 recommended
new-definition mode), THE ROW-A SOURCE VERDICT, the §S7 extraction record, and every
confirmed-perimeter section are byte-identical.  **Acceptance counter: 0/2** (a
revision does not advance it); passes 8+9 decide.

— FGMN re-derivation REVISION 6, 2026-08-08 (wallclock 2026-08-03).

## REVISION 7 (orchestrator-applied, per pass 8)

Pass 8 (FGMN_pass8_report.md): GAPS-ONLY 0C/2G. Fixes:
1. **The closure rule made OPERATIONAL (pass-8 gap 1)** — the REVISION-6 procedure is
   pinned to an implementer-independent form: (a) matching is by LEAN IDENTIFIER
   boundary — `grep -rnE '(^|[^A-Za-z0-9_'\''])<t>($|[^A-Za-z0-9_'\''!?])'` (not
   substring); comments/docstrings count as references (they carry display obligations)
   but are tagged [doc] in the census; (b) declaration kinds = {def, theorem, lemma,
   abbrev, structure, class, inductive, instance, opaque, example-with-name}; a hit
   inside a declaration's source span joins BY the declaration's fully-qualified name;
   (c) ring entries ARE recursively expanded (same rule); the two prefix entries
   (`SideClause`, `sideReads_`) are declared PREFIX-PATTERNS — they match any identifier
   extending them, and each match joins as itself; (d) the fixpoint is over the union
   (seed ∪ ring) from round 1. Two faithful implementers now compute the same set.
2. The census/computational artifacts remain prover-side pending the F2c
   verifier-owned execution (pass-8 gap 2 = the standing infrastructure item; pass 9
   is a Fable pass WITH execution — it discharges this by construction).
Counter stays 0/2; passes 9+10 decide.

## REVISION 8 (orchestrator-applied, per pass 9 — the closure question SETTLED by delegation to the compiler)

Pass 9 (FGMN_pass9_report.md, f1863d7; the execution leg again EXACT on every pinned
artifact): CRITICAL 1C/2G — the verifier EXECUTED the REVISION-7 closure and proved it
BIMODAL: the FQN-literal reading expands nothing (fixpoint = the 466 round-1 decls);
the base-name reading saturates to 12,199 decls across ~97% of the tree (docstring
[doc] hits admit English prose tokens into the expansion). No textual rule survived
execution. RESOLUTION — the perimeter specification is REPLACED, not patched:
1. **The NORMATIVE perimeter is the Lean elaborator's own dependency closure**,
   computed AT APPLICATION TIME on a scratch worktree: introduce `SideReads'` (the
   new-definition route), re-point the glue-route statements, `lake build`, and follow
   compiler errors to fixpoint. The kernel's reference graph is the exact closure no
   grep can approximate; the application unit's change-set = precisely the files the
   rebuild forces, each dispositioned (primed twin / mode-conditional bracket /
   untouched) in its diff. This is checkable, implementer-independent, and total.
2. **Every grep census in this note (REVISIONS 4-7) is DEMOTED to INFORMATIVE
   PREVIEW** — retained as the reviewer's map of the expected blast radius (the R1+R2
   mirrors, the (†)-transfer sites, Window/CU1, the named binders), no longer claimed
   normative or complete. The pass-9 findings against the REVISION-7 rule (the dead
   ring term `lastRead_of_readsOf`; the 15-vs-14 file count — `U27_gateInert` was a
   substring artifact) stand as recorded defects OF THE PREVIEW and are corrected in
   place: the ring term is struck (its only occurrences are `lastRead_of_readsOf_snoc`,
   which stays); the round-2 list is 14 files.
Counter stays 0/2; passes 10+11 decide on THIS specification.
