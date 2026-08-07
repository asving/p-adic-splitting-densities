# WELDMASTER pass PE9 — hostile verification report (NINTH attempt; the first acceptance attempt after PE8's reset)

**Target:** `lean/notes/openmath/WELDMASTER_2026-08-08.md` AT HEAD (post-r7,
53aa1d9; `git diff 53aa1d9..HEAD` empty on the note, worktree clean; arc:
seal b375f42 → verdict 0baeb3b → PE1 df00707 → r1 90db22d → PE2 1edb104 →
r2 8f1c1f2 → PE3 07acb37 → r3 52d40bb → PE4 39e1eec → r4 14706f5 → PE5
f97bc78 → r5 f8c2c09 → PE6 7c3893f → r6 355a14f → PE7 0a2fb54 CLEAN 1/2 →
ledger 93da1d1 → PE8 8d84d77 0C/1G, counter RESET 0/2 → r7 53aa1d9).
**Verifier:** hostile pass PE9, fresh context, wallclock 2026-08-07.
Nothing fixed; offending passages would be quoted and classified (CRITICAL
ERROR / JUSTIFICATION GAP); fences and honest boxes read as part of every
statement; the bar identical to every pass. Sources extracted at their pins
via `git show`: [JB] 4c4ee56, [JC] 3870bc8, [JA] ce0469a, [W2] 5463f2a,
[ILN] ced7dbb, [SYN] f71cd68, LED-Λ 2ad7505. All EIGHT prior reports read
(routes catalogued: PE1/PE2 the note's own computations + diff/evidence-
class audits; PE3 WM-COB+PERIM vs [ILN]'s displays; PE4 WM-COB(i) by
decomposition; PE5 WM-RHO by the E-pair; PE6 WM-CLASS by the σ-section;
PE7 WM-FENCE by the order-lattice; PE8 WM-RHO by the proof-step/shift
route + WM-CLASS by the cyclic-norm-invariant route). The full r7 diff
read line-by-line.

## VERDICT LINE

**0 CRITICAL ERRORS · 0 JUSTIFICATION GAPS · 0 MINOR. CLEAN — this pass
re-starts the acceptance count: counter 0/2 → 1/2; PE10 is the would-be
accepting attempt.** The r7 diff is verified correct at every edit site,
byte-claim by byte-claim, with the + convention re-verified BY MY OWN
EXTRACTION at all three pinned suppliers AND at the `bez` source itself
(§2). The charged sweep of the remaining SEALED S0/S1 declarations about
pinned objects — the species PE8's F-1 exposed (assertions that are
neither quotes nor display-consumed) — found **no second item**: all 16
S0 declaration sites and every S1 identification cell now carry at least
one independent verification, three of them kernel-grade for the first
time this pass (§3). The fresh route none of PE1–PE8 used — **THE LEAN
KERNEL** — proved the note's integer cochain system as 12 GENERAL
∀-theorems over ℤ (WM-COB(i) both multiplied and quotient forms, the
carry-free key-lattice shift covering the S3 seed identities and WM-RHO's
per-level increment, t-integrality, the `bez` + normalization, the
minus-form falsification GENERAL + both roster instances, A_j = 0 ⟺
e_{j−1} = 1, δ^pl ∈ {0,1}, and the ℓ′s−ℓu ⟷ −t engine-exponent tie):
`lake env lean` **exit 0, zero sorry, Lean-core axioms only** (§4).
Machine leg: sealed battery exit 0 ALL GREEN, both artifacts
byte-identical, every figure exact (§1). Arc accounting consistent and
true at HEAD (§5). Four observations, all nil-weight (§6).

## §1. MACHINE LEGS (mandatory; re-run 2026-08-07)

* **Sealed battery.** Runner md5 `6b406f81c250d25f615f715fa9eff474`
  **intact** at HEAD; engine pins `iterlawn_pe_reimpl.py cae45db2…` /
  `grt_jc_probe.py 03811b69…` intact (= WM-PIN's own values), my own
  `md5sum`. `git status` clean on `verification/` before and after.
  `python3 weldmaster_checks.py` → **exit 0, VERDICT: ALL GREEN**; both
  re-written artifacts **byte-identical to the committed ones**
  (`git diff --exit-code` empty on `weldmaster_checks_output.txt` AND
  `weldmaster_checks_results.json`; elapsed 0.6 s reproduced).
* **Figures vs the note's S5 verdict block — EXACT at every figure:**
  WM-PIN 2/0 · WM-EPS 615/0 · WM-COB-I 1,885/0 · WM-COB-OFFW 513/0 ·
  WM-COB-F 1,885/0 · WM-COB-C 897/0 · WM-RHO 87/0 · WM-FENCE-XI 349/0 ·
  WM-FENCE-EQ 171/0 · WM-SHEAR 804/0 (342 multi-vertex) — Σ = 7,208/0
  (recomputed) = the note's total. Teeth SIGN 374 · DELTA 861 · SHEAR 514
  · XI 47, all fired. Census: fence rows 22 absolute / 9 slot-only / 26
  neither; κ hist {0:292, 1:87, 2:18, 3:37, 4:6, 5:9, 6:2, 7:6}; 29
  towers; 897 pairs scored.
* **Fresh-route leg (this pass's decorrelated component, §4):**
  `/tmp/wm_pe9/wm_pe9_lean_leg.lean` (md5
  `a9c9fe4622298f1098f1b12b8f694562`, 152 lines, source embedded in
  Appendix I) — `lake env lean` from the pinned project toolchain →
  **exit 0, zero `sorry`**; `#print axioms` on all 12 declarations:
  every footprint ⊆ {propext, Classical.choice, Quot.sound} (printed
  log in Appendix I; the only compiler output besides the axiom lines
  is 4 deprecation warnings and 2 intentional unused-hypothesis linter
  notes — the unused hypotheses state the pinned normalization context).

## §2. CHARGE (1) — THE r7 DIFF LINE-BY-LINE: CORRECT AT EVERY EDIT SITE

The r7 commit (53aa1d9, 1 file, +85/−6, the note only — `verification/`
untouched, exactly as the footer claims) has three hunks: the r6-STATUS
strike + the r7 STATUS block; the S0 Bézout-line fix + [r7] bracket; the
tail r7 round record. Every byte-claim checked by my own extraction:

* **The + convention AT THE PINS — verified myself, all three suppliers
  AND the source.** [ILN] ced7dbb line 157 (my `git show` + `grep -n`):
  "Normalized Bézout pairs (ℓ_j, ℓ_j′): ℓ_jh_j + ℓ_j′e_j = 1," wrapping
  to line 158 "0 ≤ ℓ_j < e_j (ℓ_j = 0, ℓ_j′ = 1 at e_j = 1)" — the +
  display, exactly where the bracket cites it. [W2] 5463f2a line 76
  ("… normalized Bézout pairs ℓ_j h_j +", wrapping to 77 "ℓ_j′ e_j = 1
  with 0 ≤ ℓ_j < e_j …") ✓. [JA] ce0469a line 53 ("normalized Bézout
  ℓ_j h_j + ℓ′_j e_j = 1 with 0 ≤ ℓ_j < e_j") ✓ — the restored live
  equation is byte-identical to this variant. The pinned `bez`
  (`iterlawn_pe_reimpl.py` at cae45db2, my read of the source): ℓ = the
  minimal x ∈ [0, e) with xh ≡ 1 (mod e), ℓ′ = (1−ℓh)//e, e = 1 ↦
  (0, 1) — exactly the bracket's parenthetical "(ℓ ∈ [0, e), ℓh ≡ 1 mod
  e, ℓ′ = (1 − ℓh)/e)", and my Lean L4 proves ℓh + ℓ′e = 1 follows in
  general. The minus-form-is-the-print's-convention gloss ✓: [JA] line
  35 "Bézout ℓ_r h_r − ℓ′_r e_r = 1 with NO pinned representative (tex
  1291)"; [W2] line 49 same display.
* **The roster falsification — my own machine run** (fresh script over
  `grt_jc_probe.ROSTER` through `ITL.build_tower` + `ITL.bez`): read
  (3,2) → (ℓ,ℓ′) = (2,−1), ℓh−ℓ′e = 7, plus-form 1; read (2,3) →
  (1,−1), 5, plus-form 1; the towers carrying these reads are EXACTLY
  {C2D, C3C, C3E, I4A, I4B} — the bracket's list, no more, no fewer.
  GENERAL form kernel-checked (Lean L5/L6: ℓh − ℓ′e = 1 − 2ℓ′e, and
  ≥ 3 whenever e ≥ 2, h ≥ 2 under the + normalization — so ∉ {±1}
  everywhere the bracket claims; the e > 1 ∧ h > 1 qualifier is also
  NECESSARY: at h = 1, (ℓ,ℓ′) = (1,0) gives minus-form 1, at e = 1,
  (0,1) gives −1 — the bracket's quantifier is exactly right).
* **Sealed-line provenance.** "present at b375f42, untouched by r1–r6" ✓:
  my grep at all seven commits (b375f42 l.63 / 90db22d l.71 / 8f1c1f2
  l.103 / 52d40bb l.120 / 14706f5 l.144 / f8c2c09 l.167 / 355a14f l.192)
  shows the identical minus-form line. The record's quote of the sealed
  wording "ℓ_j h_j − ℓ′_j e_j = ±1 form as pinned (`bez`)" is byte-true
  wrap-joined at b375f42 (lines 63–64); the header bracket's
  ellipsis-compressed variant ("= ±1 … as pinned") faithful.
* **"the ONLY convention the S0.3 S-chain display below and the S5
  eps-path gloss consume" ✓ engine-verified:** `Tower.constants`
  computes S_{j−1} = D_jγ_j + S_j·(lp[j−1] − l[j−1]·wPhi[j−1]) — the +
  convention's ℓ′ — and `Tower.eps`'s exponent path is ℓ′s − ℓu, whose
  tie to −t is an identity EXACTLY under ℓh + ℓ′e = 1 (my Lean L9:
  e·(ℓ′s − ℓu) = s − ℓβ given β = sh + ue and the + relation; with the
  print's minus-ℓ′ the identity fails). Residue check: "±1" survives at
  HEAD only inside the four [r7] bracket/record sites recording the
  sealed wording (lines 133, 227/230, 995/999); the live setting is +.
* **The r7 STATUS block.** All 17 arc hashes resolve with the stated
  roles in strict clock order (§5). The PE7 compression (0a2fb54 CLEAN
  0C/0G/0m, counter 1/2, ledger 93da1d1) and PE8 compression (8d84d77,
  0C/1G/0m, RESET 1/2 → 0/2, the five faces verified, two fresh routes
  named, 20,398/0 exit 0, five teeth — T-A1 884 · T-A2 1,140 · T-B1 17 ·
  T-B2 12 · T-B3 6 — sealed battery byte-identical) match the two
  report files exactly. Blast-radius sentence = PE8's own verdict,
  quoted faithfully. Exactly ONE unstruck CURRENT status (r7); the r6
  strike is well-formed (opening ~~ at line 86, closing at 110).
* **The tail record.** "PE8 was the first pass to machine-check the S0
  setting identities themselves" = PE8 O-4 ✓; replacement-with-bracket
  per the r5/r6 precedent, correctly reasoned (a strike inside the
  setting sentence would leave the live setting false); "Strike census:
  +1 span, 20 total" ✓ (my count: 40 `~~` tokens = 20 spans);
  "runner + artifacts BYTE-FROZEN … `git diff` on `verification/`
  empty" ✓ re-verified.

## §3. CHARGE (2) — THE SEALED S0/S1 DECLARATION SWEEP (the PE8-F-1 species: assertions about pinned objects, not quotes): NO SECOND ITEM

Sweep universe: every declaration in S0 + the S1 face table that asserts
a convention/normalization/definition OF a pinned object (16 S0 sites;
the S1 identification/conditionality cells). For each: what checked it,
and my own re-verification where the coverage was thin.

* **Now r7-cured:** the Bézout line (§2).
* **Checked by my own extraction THIS pass (previously thin):**
  (i) the split tuple "γ ↦ (s_1..s_{n+1}, u_1) by iterated eq-(12)" —
  matches [ILN] ced7dbb S0.2's iterated eq-(12-int) split block (the
  retained data = the anchor exponents s₁..s_{n+1} + the final residual
  u₁; the β-mirror steps are the pin's own, not re-asserted here) ✓;
  (ii) the S0.3 pair-data transcription δ/S_n/D_j/S_{j−1} + the
  s_j-defect definition — byte-matches [ILN] lines 213–215 + 226–230
  with the note's declared W_j := w_jΦ_j abbreviation substituted ✓;
  (iii) the EXP-KIT(a) quote "(s(β) − ℓβ)/e ∈ ℤ and ε(β) =
  z^{(s(β)−ℓβ)/e}" — byte-true at [ILN] S3 (line 458) ✓; (iv) [ILN]'s
  own S0.2 carrier form ε_m(β) := z_m^{ℓ′s − ℓu} is EQUIVALENT to the
  note's z^{−t} exactly under the + convention — hand-derived and
  kernel-checked (L9) ✓; (v) E_{n+1} := e₀⋯e_n at [ILN] line 170 ✓;
  (vi) weights/letters/z̄ lines vs [ILN] 154–163 ✓.
* **Kernel-graded for the first time this pass:** the "t_j(β) ∈ ℤ
  always" warrant (L1), the "A_j = 0 ⟺ e_{j−1} = 1" parenthetical (L7 —
  the ⟸ direction NEEDS the pinned representative 0 ≤ ℓ < e and the ⟹
  direction needs the Bézout relation, i.e. this line consumes exactly
  the r7-restored normalization), and the eps-path tie (L9).
* **Already covered by prior passes (verified citations, spot-rechecked):**
  the abscissa tie + γ-recursion + W-identity (PE8's S0 identity
  machine-check); the JA-EPS sign-convention gloss incl. "NOT
  Def-`t(i)`'s opposite sign" (PE8 §2 vs pin); the [r1, F-4] JA-EPS
  quantifier sentence (PE1 F-4 + PE8); the [r2, F-3] runner-range gloss
  (PE8 spot-check, runner line 222); every S1 face cell (PE8
  statement-by-statement); the σ-minimality warrant (PE2 F-8 + PE6 +
  PE8); the S2.3 TC-3 sentence (PE8); the roster description (PE1);
  S5 evidence-class labels (PE2 audit).
* **Conclusion:** the sweep is EXHAUSTED on this note's S0/S1 basis —
  every convention/normalization assertion about a pinned object now has
  a named check, none failed. No finding.

## §4. CHARGE (3) — FRESH RE-DERIVATION BY AN UNUSED ROUTE: THE LEAN KERNEL (used by none of PE1–PE8)

All eight prior routes were hand-derivation + Python instruments. This
pass proved the note's integer exponent system as GENERAL ∀-theorems
over ℤ — kernel-checked, beyond both interpolation (emod/ediv are not
polynomial) and exhaustion (unbounded quantifiers) — 12 declarations,
`lake env lean` exit 0, zero sorry, axioms ⊆ Lean core:

* **L2/L2′ (WM-COB(i), the note's one new theorem, integer core):** for
  ALL ℓ, e, β, β′, S ∈ ℤ (L2 needs NO hypothesis; L2′ needs e ≠ 0):
  s(β) + s(β′) − s(β+β′+S) + ℓS = e·(t(β+β′+S) − t(β) − t(β′)), s/t the
  emod/ediv cochain. Instantiated at ℓ_{j−1}, e_{j−1}, β_j, β′_j, S_j
  with [ILN]'s SHIFT-(n) (β″ = β + β′ + S_j, consumed ACCEPTED) and the
  definitional abscissa tie, this IS D_j = (∂t_j)(γ,γ′) — with no window
  hypothesis, matching the claimed "γ, γ′ ∈ ℤ arbitrary, ALL pairs incl.
  DCX" scope, and integrality automatic (the note's D_j-INT refinement
  reading confirmed at kernel grade).
* **L3 (the S3 seed identities + WM-RHO's engine):** t(β + i·e·c) =
  t(β) + iℓc AND s(β + i·e·c) = s(β) for all arguments — at c = g_μγ_μ
  this is the key-lattice first difference t_μ(β + iW_μ) = t_μ(β) + iA_μ
  with carry-freeness (s unchanged); at i = 1, c = E_{j−1} it is
  WM-RHO's per-level increment t_j(β_j + E_j) = t_j(β_j) + ℓ_{j−1}E_{j−1}
  and the "keeps every s_j fixed" proof claim.
* **L4–L6b (the r7 content):** the `bez` construction satisfies the +
  form (L4); ℓh − ℓ′e = 1 − 2ℓ′e (L5 = the [r7] bracket identity); the
  minus-form is ≥ 3 hence FALSE at every e ≥ 2, h ≥ 2 read under the
  pinned normalization (L6, with ℓ ≥ 1 derived from e ∣ 1 absurdity);
  both roster instances (3,2) → 7 and (2,3) → 5 (L6a/L6b).
* **L7 (A_j = 0 ⟺ e_{j−1} = 1), L8 (δ^pl ∈ {0,1} — [ILN] S0.2's plain
  carry, LAW-2's face), L9 (the ℓ′s−ℓu ⟷ −t tie).**

This is the WM arc's first kernel-checked leg (the campaign precedent:
JA PE6's 19-decl leg, W2 PE5's 17-theorem leg). Everything the kernel
touched came out TRUE as displayed. Source + compile log: Appendix I.

## §5. CHARGE (4) — THE ARC-ACCOUNTING SYSTEM: CONSISTENT AND TRUE

All 17 arc hashes + the r7 commit resolve with matching roles and strict
clock order (my own `git log` pull: b375f42 08-06 08:22:56 → 0baeb3b
08:23:59 → df00707 08:55:20 → 90db22d 09:27:15 → 1edb104 10:23:32 →
8f1c1f2 11:42:24 → 07acb37 16:47:28 → 52d40bb 16:59:06 → 39e1eec
19:05:40 → 14706f5 19:30:37 → f97bc78 08-07 08:01:29 → f8c2c09 08:29:46
→ 7c3893f 09:12:43 → 355a14f 09:26:48 → 0a2fb54 14:05:21 → 93da1d1
14:06:40 → 8d84d77 14:36:50 → 53aa1d9 14:44:58). The note at HEAD =
53aa1d9 byte-identical; worktree clean. Exactly ONE unstruck CURRENT
status (r7); r1–r6 struck in place, content preserved; strike census 20
spans = 40 `~~` tokens recounted exact. The r7 STATUS's compressions of
PE1–PE8 match all eight report files. The two live counter surfaces
(status line 143, footer line 1017) read "0/2; PE9 next" — TRUE AS
WRITTEN at r7, and I am PE9. The r7 commit message's claims (one fix,
strike census 20, note-only, md5 verified, counter 0/2) all true.
Counter after this clean pass: **1/2**, recorded per the arc convention
in this report + the ledger, not by editing the note.

## FINDINGS

**None.** No CRITICAL error, no JUSTIFICATION GAP, no MINOR defect
survived verification at HEAD.

## OBSERVATIONS (not findings; all nil-weight)

* **O-1 (wrap-join non-disclosure, r7 record).** The record's [ILN]
  quote "Normalized Bézout pairs (ℓ_j, ℓ_j′): ℓ_jh_j + ℓ_j′e_j = 1,
  0 ≤ ℓ_j < e_j" is byte-true WRAP-JOINED across pin lines 157–158,
  cited as "line 157" without the r5-style "wrap-joined" parenthetical.
  The arc's own sweep standard (PE6/PE7) is explicitly wrap-insensitive
  and head-line citation has precedent; nil.
* **O-2 ("the byte-form at every pinned supplier").** The three
  suppliers carry the + display in three orthographic variants ([ILN]
  "ℓ_jh_j + ℓ_j′e_j", [W2] "ℓ_j h_j + ℓ_j′ e_j", [JA] "ℓ_j h_j + ℓ′_j
  e_j"); the restored live equation is byte-identical to the [JA]
  variant specifically. The bracket's sentence reads as a form-level
  claim (every supplier's bytes display the + convention — TRUE, my
  extraction; no minus display exists at any of the three), and the
  phrase originates in PE8's own prescribed cure, executed verbatim;
  nil.
* **O-3 (post-pin supplier motion since PE8 — pin-protected; fold
  inventory grows by one item in the CONSERVATIVE direction).** The
  5054d69 fold (post-r7) appended to [ILN] the NR-1 rider-rewrite:
  (ITER-LAW-LIFT) now reads "DISCHARGED at attempt grade (capped by the
  W-2 0/2 consumption; ξ = 1 core W-2-free)" per the ACCEPTED
  LIFTCORNER — so WM's S4 stack, which carries (ITER-LAW-LIFT) as an
  open [ILN] residual at the ced7dbb pin, now UNDERSTATES its supplier
  (conservative direction; no WM display rides it). Same fold: two JB
  errata, one being the root-inclusive (R-coll) label — the direction
  WM's r4 already cured. Also JA r5 (f131c53) and W2 r4 (94534df, PE8
  O-2's catalogued item) — no WM sentence rides either. The one
  WEAKENING-direction fold obligation remains PE8 O-2's: the next [W2]
  pin update must carry the W2-C3 re-scope into the (M4) face. LED-Λ
  unmoved (2ad7505 still its last commit — that dated bracket stays
  literally true); [JC] unmoved since the 83f47f4 acceptance.
* **O-4 (fresh-leg by-product, offer only).** The Lean file is the WM
  arc's first kernel-checked leg; if the next fold wants an artifact
  rescue (the JA PE6 precedent: `verification/openmath/
  ja_pe6_lean_leg.lean`), Appendix I is the reproducible source (md5
  a9c9fe4622298f1098f1b12b8f694562). Nothing owed.

## HONESTY GRADE

Above genre par, unchanged from PE7/PE8's assessment: the conditionality
stack still UNDERSTATES (JB/JC carried at 0/2 though ACCEPTED;
(ITER-LAW-LIFT) carried open though supplier-discharged post-pin — both
conservative); the machine bracket reproduces byte-identically including
the elapsed line; the grade-cap, consumption-only, and no-upgrade fences
are honored at every site I probed; the r7 repair is exact, minimal,
disclosure-complete (sealed wording + falsification + provenance all
recorded in place), and executed PE8's prescribed cure verbatim. The
one live-truth defect PE8 found is cured; its species (§3) is swept and
exhausted.

**Counter: 1/2 — this pass is CLEAN and re-starts the acceptance count.
PE10 is the would-be accepting attempt.**

— PE9 verifier, fresh context, 2026-08-07.

## APPENDIX I — the Lean kernel leg (source, verbatim; md5 a9c9fe4622298f1098f1b12b8f694562)

Compile: `cd lean && lake env lean /tmp/wm_pe9/wm_pe9_lean_leg.lean` →
exit 0. Axiom log (verbatim, warnings elided — 4 deprecation notes on
`Int.ediv_add_emod`, 2 unused-hypothesis linter notes on L6's `hle` /
L7's `hh`, both hypotheses kept deliberately to state the pinned
normalization context):

    'WMPE9.t_spec'            [propext, Classical.choice, Quot.sound]
    'WMPE9.wm_cob_i_mul'      [propext, Classical.choice, Quot.sound]
    'WMPE9.wm_cob_i'          [propext, Classical.choice, Quot.sound]
    'WMPE9.t_key_shift'       [propext]
    'WMPE9.bez_plus'          [propext, Classical.choice, Quot.sound]
    'WMPE9.minus_eq'          [propext, Classical.choice, Quot.sound]
    'WMPE9.minus_form_false'  [propext, Classical.choice, Quot.sound]
    'WMPE9.instance_32'       [propext, Quot.sound]
    'WMPE9.instance_23'       [propext, Quot.sound]
    'WMPE9.A_zero_iff'        [propext, Classical.choice, Quot.sound]
    'WMPE9.delta_01'          [propext, Classical.choice, Quot.sound]
    'WMPE9.eps_exponent_tie'  [propext, Classical.choice, Quot.sound]

```lean
/- WELDMASTER PE9 — fresh-route leg: THE LEAN KERNEL (route unused by PE1–PE8).
   The note's integer cochain system as GENERAL ∀-theorems over ℤ — full
   generality (Int.ediv/emod, unbounded quantifiers), beyond interpolation and
   exhaustion. Conventions match the pinned `bez` / eq-12 / S0 weld cochain:
     s(β) := (ℓβ) % e   (0 ≤ s < e for e > 0),   t(β) := (ℓβ) / e = (ℓβ − s(β))/e.
   Verifier-written 2026-08-07; consumed by the PE9 report only. -/
import Mathlib

namespace WMPE9

/-- L1 (t-integrality + s-range): ℓβ = e·t(β) + s(β) with 0 ≤ s(β) < e.
    This is the note's "t_j(β) ∈ ℤ always (s(β) ≡ ℓβ mod e)" warrant. -/
theorem t_spec (l e beta : ℤ) (he : 0 < e) :
    l * beta = e * ((l * beta) / e) + (l * beta) % e
      ∧ 0 ≤ (l * beta) % e ∧ (l * beta) % e < e :=
  ⟨(Int.ediv_add_emod _ _).symm, Int.emod_nonneg _ (ne_of_gt he),
   Int.emod_lt_of_pos _ he⟩

/-- L2 (WM-COB(i), multiplied form — no division, so NO hypothesis at all):
    with β″ := β + β′ + S,
    s(β) + s(β′) − s(β″) + ℓS  =  e·( t(β″) − t(β) − t(β′) ).
    The left side is e·D_j ([ILN] S0.3 definition of D_j via the s-defect);
    the right side is e·(∂t)(γ,γ′). -/
theorem wm_cob_i_mul (l e beta beta' S : ℤ) :
    (l*beta % e) + (l*beta' % e) - (l*(beta+beta'+S) % e) + l*S
      = e * ((l*(beta+beta'+S))/e - (l*beta)/e - (l*beta')/e) := by
  have h1 := Int.ediv_add_emod (l*beta) e
  have h2 := Int.ediv_add_emod (l*beta') e
  have h3 := Int.ediv_add_emod (l*(beta+beta'+S)) e
  linear_combination h1 + h2 - h3

/-- L2′ (WM-COB(i), quotient form): D = ∂t exactly, every ℓ, β, β′, S ∈ ℤ, e ≠ 0. -/
theorem wm_cob_i (l e beta beta' S : ℤ) (he : e ≠ 0) :
    ((l*beta % e) + (l*beta' % e) - (l*(beta+beta'+S) % e) + l*S) / e
      = (l*(beta+beta'+S))/e - (l*beta)/e - (l*beta')/e := by
  rw [wm_cob_i_mul l e beta beta' S, Int.mul_ediv_cancel_left _ he]

/-- L3 (the key-lattice first difference — S3's seed identities + LAW-3 at
    exponent level, and WM-RHO's per-level increment): for W on the key
    lattice, W = e·c (e.g. c = g·γ giving A = ℓgγ, or c = E_{j−1} giving
    ℓE_{j−1}), the shift is CARRY-FREE:
    t(β + i·e·c) = t(β) + i·ℓ·c  and  s(β + i·e·c) = s(β). -/
theorem t_key_shift (l e beta i c : ℤ) (he : e ≠ 0) :
    (l*(beta + i*(e*c))) / e = (l*beta)/e + i*l*c
      ∧ (l*(beta + i*(e*c))) % e = (l*beta) % e := by
  have hexp : l*(beta + i*(e*c)) = l*beta + (i*l*c)*e := by ring
  constructor
  · rw [hexp, Int.add_mul_ediv_right _ _ he]
  · rw [hexp, Int.add_mul_emod_self_right]

/-- L4 (the pinned `bez` normalization is the + convention): if e ∣ (1 − ℓh)
    (the scan's ℓh ≡ 1 mod e) then ℓ′ := (1−ℓh)/e satisfies ℓh + ℓ′e = 1. -/
theorem bez_plus (l h e : ℤ) (hdvd : (1 - l*h) % e = 0) :
    l*h + ((1 - l*h)/e)*e = 1 := by
  have := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdvd)
  linarith

/-- L5 (the [r7] bracket's identity): under the + convention,
    ℓh − ℓ′e = 1 − 2ℓ′e. -/
theorem minus_eq (l l' h e : ℤ) (hbez : l*h + l'*e = 1) :
    l*h - l'*e = 1 - 2*(l'*e) := by linarith

/-- L6 (PE8 F-1 / the r7 falsification, GENERAL): under the + normalization
    with e ≥ 2, h ≥ 2, 0 ≤ ℓ < e, the minus-form value is ≥ 3 — hence the
    sealed "ℓ_j h_j − ℓ′_j e_j = ±1" is FALSE at EVERY read with e > 1, h > 1. -/
theorem minus_form_false (l l' h e : ℤ) (he : 2 ≤ e) (hh : 2 ≤ h)
    (hl0 : 0 ≤ l) (hle : l < e) (hbez : l*h + l'*e = 1) :
    3 ≤ l*h - l'*e := by
  have hl1 : 1 ≤ l := by
    by_contra hcon
    have hl : l = 0 := by omega
    rw [hl] at hbez
    simp only [zero_mul, zero_add] at hbez
    have hdvd : e ∣ 1 := ⟨l', by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have hlh : 2 ≤ l*h := by nlinarith
  linarith

/-- L6a (roster instance, read (3,2) — towers C2D/C3C/I4A/I4B):
    bez = (2, −1); plus-form 1, minus-form 7 ∉ {±1}. -/
theorem instance_32 : (2:ℤ)*2 + (-1)*3 = 1 ∧ (2:ℤ)*2 - (-1)*3 = 7 := by
  norm_num

/-- L6b (roster instance, read (2,3) — tower C3E):
    bez = (1, −1); plus-form 1, minus-form 5 ∉ {±1}. -/
theorem instance_23 : (1:ℤ)*3 + (-1)*2 = 1 ∧ (1:ℤ)*3 - (-1)*2 = 5 := by
  norm_num

/-- L7 (S0's "A_j = 0 ⟺ e_{j−1} = 1", general): with the + normalization,
    e ≥ 1, h ≥ 1, 0 ≤ ℓ < e, g ≥ 1, γ ≥ 1:  ℓgγ = 0 ↔ e = 1. -/
theorem A_zero_iff (l l' h e g gam : ℤ) (he : 1 ≤ e) (hh : 1 ≤ h)
    (hl0 : 0 ≤ l) (hle : l < e) (hbez : l*h + l'*e = 1)
    (hg : 1 ≤ g) (hgam : 1 ≤ gam) :
    l*g*gam = 0 ↔ e = 1 := by
  constructor
  · intro hA
    by_contra hne
    have he2 : 2 ≤ e := by omega
    have hl1 : 1 ≤ l := by
      by_contra hcon
      have hl : l = 0 := by omega
      rw [hl] at hbez
      simp only [zero_mul, zero_add] at hbez
      have hdvd : e ∣ 1 := ⟨l', by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    have hpos : 0 < l * g * gam :=
      mul_pos (mul_pos (by omega : (0:ℤ) < l) (by omega : (0:ℤ) < g))
        (by omega : (0:ℤ) < gam)
    linarith
  · intro he1
    have hl : l = 0 := by omega
    rw [hl]; ring

/-- L8 (the plain carry δ ∈ {0,1} — [ILN] S0.2's δ^pl line, LAW-2's face):
    0 ≤ s < e, 0 ≤ s′ < e ⟹ ⌊(s+s′)/e⌋ ∈ {0,1}. -/
theorem delta_01 (s s' e : ℤ) (he : 0 < e) (h1 : 0 ≤ s) (h2 : s < e)
    (h3 : 0 ≤ s') (h4 : s' < e) : (s+s')/e = 0 ∨ (s+s')/e = 1 := by
  rcases lt_or_ge (s+s') e with hlt | hge
  · left; exact Int.ediv_eq_zero_of_lt (by omega) hlt
  · right
    have hrw : s + s' = (s + s' - e) + 1*e := by ring
    rw [hrw, Int.add_mul_ediv_right _ _ (ne_of_gt he),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    norm_num

/-- L9 (the committed-eps exponent path ⟺ −t, under the + convention ONLY —
    the S5 WM-EPS gloss "the ℓ′s−ℓu exponent path" tied to EXP-KIT(a)):
    given eq-12 data β = sh + ue and ℓh + ℓ′e = 1:  e·(ℓ′s − ℓu) = s − ℓβ.
    (So z^{ℓ′s−ℓu} = z^{−t(β)} once s = (ℓβ) % e — the identity the minus-ℓ′
    would BREAK, which is why the S0 line's convention is load-bearing.) -/
theorem eps_exponent_tie (l l' h e s u beta : ℤ) (hbez : l*h + l'*e = 1)
    (heq : beta = s*h + u*e) : e*(l'*s - l*u) = s - l*beta := by
  have hsub : s - l*beta = s*(1 - l*h) - l*u*e := by rw [heq]; ring
  have h1le : 1 - l*h = l'*e := by linarith
  rw [hsub, h1le]; ring

end WMPE9

#print axioms WMPE9.t_spec
#print axioms WMPE9.wm_cob_i_mul
#print axioms WMPE9.wm_cob_i
#print axioms WMPE9.t_key_shift
#print axioms WMPE9.bez_plus
#print axioms WMPE9.minus_eq
#print axioms WMPE9.minus_form_false
#print axioms WMPE9.instance_32
#print axioms WMPE9.instance_23
#print axioms WMPE9.A_zero_iff
#print axioms WMPE9.delta_01
#print axioms WMPE9.eps_exponent_tie
```
