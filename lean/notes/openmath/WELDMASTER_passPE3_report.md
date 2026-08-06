# WELDMASTER pass PE3 — hostile verification report (THIRD acceptance attempt)

**Target:** `lean/notes/openmath/WELDMASTER_2026-08-08.md` AT HEAD (post-r2,
8f1c1f2; arc: seal b375f42 → verdict 0baeb3b → PE1 df00707 → r1 90db22d →
PE2 1edb104 → r2). **Verifier:** hostile pass PE3, fresh context, wallclock
2026-08-06. Nothing fixed; offending passages quoted and classified (CRITICAL
ERROR / JUSTIFICATION GAP); fences read as part of every statement. Sources:
[JB] read AT THE PIN 4c4ee56 (post-r7) and [JC] AT THE PIN 3870bc8 (post-r5)
via `git show <commit>:<path>` — per the 2026-08-06 standing rule (ledger
5c849a3), a pinned quote is judged at its pin; JB now post-r8 (49f9168) and
JC post-r6 (4b804b4), which the pins make immaterial by construction. [JA],
[W2], [ILN] read at HEAD (none has moved since before the WM seal: JA last
ce0469a = its r1; W2 last 5463f2a; ILN ACCEPTED). Both prior reports and the
full r2 diff read; both engine files at their pinned md5s.

## VERDICT LINE

**0 CRITICAL ERRORS · 0 JUSTIFICATION GAPS · 1 MINOR. NOT CLEAN — the
acceptance counter stays 0/2.** The r2 diff itself is substantively EXACT:
every r2 pin verified against its pinned commit (7 quote byte-checks + the
row-11/(a2)/consumer-list/census content checks + the JC §10.2/[r5, G-2]
round-record structure, all byte-true at the pins); the pin construction
verified (every [JB]/[JC] quote site carries a local [r2] pin; the two dagger
brackets carry the global read-at-commit declarations; zero unpinned [JB]/[JC]
quote sites remain). WM-COB and PERIM-μ re-derive exactly on fresh passes. The
machine leg reproduces byte-identically. The one finding is a quotation-
attribution imprecision at S3(b) that predates r2 but now sits under an r2
pin tag: the quoted byte-string matches [JB] §5's fence display, not the
§0M column (c) cell it is attributed to (semantically identical, both live
at the pin).

## MACHINE LEG (mandatory; re-run 2026-08-06)

* Runner md5 `6b406f81c250d25f615f715fa9eff474` **intact** at HEAD (and the
  r2 commit touched only the note — numstat: 1 file, +105/−18, matching the
  commit message exactly). `git status` on `verification/` clean before and
  after the re-run.
* `python3 weldmaster_checks.py` → **exit 0, VERDICT: ALL GREEN**. The re-run
  wrote artifacts **byte-identical to the committed ones** (diff on
  `weldmaster_checks_output.txt` EMPTY including the elapsed 0.6 s line; the
  results JSON identical — `git status` stayed clean because the re-run
  reproduced the committed bytes exactly).
* All figures vs the note's verdict block: WM-PIN 2/0 · WM-EPS 615/0 ·
  WM-COB-I 1,885/0 · WM-COB-OFFW 513/0 · WM-COB-F 1,885/0 · WM-COB-C 897/0 ·
  WM-RHO 87/0 · WM-FENCE-XI 349/0 · WM-FENCE-EQ 171/0 · WM-SHEAR 804/0
  (342 multi-vertex) — Σ = 7,208/0. Teeth SIGN 374 · DELTA 861 · SHEAR 514 ·
  XI 47, all fired. Census identical: fence rows 22 absolute / 9 slot-only /
  26 neither; κ hist {0:292, 1:87, 2:18, 3:37, 4:6, 5:9, 6:2, 7:6}; 29
  towers; 897 pairs scored. **EXACT MATCH at every figure.**
* WM-PIN's own engine pins (iterlawn_pe_reimpl.py / grt_jc_probe.py md5s)
  pass inside the battery (2 samples, 0 violations).

## CHARGE-BY-CHARGE RESULTS

### (1) The r2 diff line-by-line; pinned quotes byte-checked at the pins

Byte-checks run with `git show 4c4ee56:...GRTJB...` / `git show
3870bc8:...GRTJC...` (more than the charged 4):

* **[col (b) NARROWED quote]** "u ≥ 0 PROVED at V ∈ 𝒲_{q+1}, i.e. DISCHARGED
  for deg f < deg Φ_{q+1} (§5); open residue = MEMBERSHIP at the
  unbounded-degree quantifier" — **BYTE-EXACT** at [JB]@pin §0M rows 4 AND 12,
  column (b) (lines 269/277).
* **[§5 r5-split quote]** "membership V ∈ 𝒲_{q+1} holds by definition exactly
  at deg f < deg Φ_{q+1} — THERE THE PROVISO NOW HOLDS; off that sub-window
  membership is not established by anything this note consumes, and the
  proviso is CARRIED as that membership hypothesis" — **BYTE-EXACT** at
  [JB]@pin lines 1473–1476.
* **[census-FOUR quote]** "the census stays FOUR (rows 4, 5, 12, 22)" —
  **BYTE-EXACT** at [JB]@pin line 1130, and the attribution "r6's own words"
  is correct: the sentence sits in the r6 round block's F-1 disposition
  bullet ("RE-FENCED: §0M row 11 SPLIT …"; the [r7, PE7 m-3] tag three lines
  up is a later annotation inside it, not the sentence's author). The gloss
  "(d3)'s re-fence carries a key perimeter, not an open proviso" matches the
  adjacent bytes ("NO frontier change: (d3) carries a key perimeter, not an
  open proviso"). Census independently confirmed at the pin: rows 4/5/12/22
  are exactly the rows pairing an open-proviso cell with a NONE evidence cell
  (row 4 grid-half NONE; row 5 NONE ⟨n4⟩; row 12 NONE [r3, F-3]; row 22
  NONE — machine UNEXERCISED).
* **[instance-honest relation quote at S4]** "membership implies the needed
  instance — the sufficiency direction, all any consumer uses; the converse
  is INSTANCE-DEPENDENT — EQUIVALENT at m = 1 (above), containment possibly
  strict at m ≥ 2, strictness UNPROVED either way in general (PE6's
  qualifier, restored)" — **BYTE-EXACT** at [JB]@pin lines 215–219, inside
  the [r7, PE7 F-1]-repaired column (b) definition as attributed ("THE
  INSTANCE-HONEST RELATION: …"). The S4 bracket's consequence ("sufficiency
  is all this note's (M1) rider uses, so the carried residue is unchanged in
  substance") is sound: the rider carries the membership hypothesis, and
  membership ⟹ instance is the direction a hypothesis-carrier consumes.
* **[JC-LOC quote at (M3)]** "B *is* the object FGMN's theorems speak about"
  — **BYTE-EXACT** at [JC]@pin (LEMMA JC-LOC header, line 955; also lines
  294/986); the displayed identification B = gr(w)[in(π)^{−1}] ≅ gr_{K[x]}(w)
  matches JC-LOC's own display (gr^O(w)[in(π)^{-1}] → gr^K(w), degreewise).
* **[taxonomy quote at S5]** "SAME … the violation is UNREACHABLE and the leg
  carries NO information … never advertised as a second engine" — all three
  segments **BYTE-EXACT** at [JB]@pin's evidence-class definitions (lines
  253–257).
* **[[RMG] grade-cap quote at (F-c)]** "consuming [RMG] as ACCEPTED and LED-Λ
  at ATTEMPT grade" — **BYTE-EXACT in the LIVE regenerated grade cap** at
  [JB]@pin (JB-TREE bullet, lines 459–461; wraps mid-string, which hides it
  from a single-line grep; the second occurrence at line 515 is the
  [r3]-superseded record cap, retained verbatim).
* **[(M1)/(F-a) row-11 content]** [JB]@pin §0M row 11 (line 276) verified
  cell-for-cell: (d1)/(d2) at `P<q` (a1) with the runner's shared_upto gate
  an instrument cut for (d1); **(d3) = "JA-VAL AT LEVEL q+1" at (a2) `P≤q`
  "the BYTE-EQUAL CHAIN THROUGH q"; "Bites at q = qcap on the 5
  shared_upto < n towers (T3A/T3C/T3D/T3E/I4C)"; "the runner's
  q ≤ shared_upto gate on (d3) IS this fence, so the IND leg covers the full
  re-fenced range"** — every clause of the WM (M1) bracket is at source. The
  (F-a) consumer list "rows 2, 5, and row 11's (d3)" matches [JB]@pin's own
  recount ("THREE `P≤q` consumers: rows 2, 5, and row 11's (d3)", line 1111).
  Rows 8–10 confirmed unchanged at `P<q` (a1); the S5 bracket's (f)-cell
  quote "IND three tie assertions" byte-matches row 11 (f).
* **[JC §10.2 at the pin, S4/F-5 bracket]** The [r5, G-2] annotation is at
  source and says exactly what WM mirrors: "the r0/[r1]/[r2] stack displays
  above are ROUND-RECORDS … The CURRENT stack is therefore the [r2]
  tier-split form with its FGMN entry read as: FGMN (a)(b) + (DMULT-w) on B
  …" ([JC]@pin lines 2624–2641). Both mirrored items ride byte-stable in the
  [r2] stack display (line 2599): "(ITER-LAW-LIFT)" in the [ILN] residual
  list and "GRB/CARRY-1/D-REAL ACCEPTED-conditional (§0 ladder + [T] pins)";
  the LIFTCORNER gloss "open exactly at g_0 = 1 ∧ δ_1 = 1" at line 1960.
  The germ figures at S2.3 ("27 eligible stages", "138/669") byte-stable at
  the pin (lines 1448/2579).
* **Dagger brackets (F-2):** [JB] "(post-r7, 0/2, as of 4c4ee56)" — 4c4ee56
  IS JB r7 ✓, counter 0/2 there ✓; [JC] "(post-r5, 0/2, as of 3870bc8)" —
  3870bc8 IS JC r5 ✓. Timeline claims verified from git: JC r3 = 126c33f
  09:02:29 < WM r1 = 90db22d 09:27:15 < JB r6 = 4607824 10:02:45 (the "35
  minutes" of PE2's drift finding ✓); JB r5 = f9f104e 09:11:08 ✓.
* **WM-EPS range fix (F-3):** runner line 222 is
  `for beta in range(0, 3 * T.e[j-1] * T.h[j-1] + 4)` — β ∈ [0, 3e·h+4),
  bounded non-negative, exactly as the bracket states. The operative
  code-level claim verified by call-graph trace: `Tower.eps` is evaluated
  ONLY at (i) WM-EPS's non-negative range, (ii) WM-COB-F's in-window split
  betas, (iii) WM-FENCE-XI's Wm and e·Wm (≥ 0); `Ecoch` (WM-RHO, WM-COB-C)
  is built from `t_fresh` only (docstring + body), and the OFFW leg uses
  `t_fresh` only — **the fresh-cochain legs never evaluate `Tower.eps` at
  negative β**, exactly as the r2 bracket says.

**The pin CONSTRUCTION verified:** grep of every [JB]/[JC] occurrence in the
note — all 11 quote-bearing sites carry local [r2]/[r2, F-n] as-of tags
((M1)×2, (M3), S2.3×2, S3(b), (F-a), (F-c), S4 stack + bullet + F-5 bracket,
S5×2); the remaining bare [JB]†/[JC]† mentions are citations covered by the
dagger brackets' global "every [JB]/[JC] citation in this note reads at that
commit". 20 `[r2` brackets counted (= the commit message); strike tokens 24
(12 spans), balanced. **No unpinned [JB]/[JC] quote exists**, so JB r8 / JC
r6 landing after WM r2 falsifies nothing — confirmed by construction and by
the byte-checks above all passing at the pins.

### (2) WM-COB and PERIM-μ — fresh re-derivations, both EXACT

* **WM-COB(i).** t_j(β) = (ℓβ − s(β))/e with s(β) = ℓβ mod e is ⌊ℓβ/e⌋ ∈ ℤ
  always. Input (a) s_j(γ) = s(β_j(γ)) re-verified DEFINITIONAL against
  [ILN] S0.2's iterated split at source (eq12(β_j; e_{j−1}, h_{j−1}) with
  abscissa ℓβ mod e); input (b) SHIFT-(n) β″_j = β_j + β′_j + S_j graded
  "PROVED, generic, unconditional" in [ILN]'s clause table (line 270), S2
  header "Throughout S2, γ, γ′ ∈ ℤ are arbitrary" (line 360). Then
  t_j(β_j) + t_j(β′_j) − t_j(β″_j) = [ℓ(β+β′−β″) − (s+s′−s″)]/e =
  [−ℓS_j − defect]/e = −D_j by S0.3's display (transcribed symbol-exact from
  [ILN], W_{j−1} = w_{j−1}Φ_{j−1} included). Exact; footprint claim (SHIFT +
  D_j-INT only) correct — D_j-INT is exactly ∂t_j ∈ ℤ, as the Remark says.
* **WM-COB(ii).** EPS-CLOSED quote byte-exact at [ILN] S3 ("(s(β) − ℓβ)/e ∈ ℤ
  and ε(β) = z^{(s(β)−ℓβ)/e}"), β unrestricted (eq-12-int defined for all
  β ∈ ℤ), ACCEPTED; ε_j = z^{−t_j} ⟹ ε(β)ε(β′)/ε(β″) = z^{t″−t−t′} =
  z^{D_j}. The sign flip between the note's ∂t convention (t″−t−t′) and the
  multiplicative ∂E (E·E′/E″) is CONSISTENT through ε = z^{−t} — checked
  both ways.
* **WM-COB(iii).** β_j(γ+γ′) = β″_j by definition, so the product of (ii)
  over j telescopes to ∂E; substitution into the accepted value law on its
  stratum. The scored-stratum fence carried at the claim, WM4, (M3),
  WM-CLASS ✓. LAW-2 (S ≡ 0 ⟹ D = ⌊(s+s′)/e⌋ = δ^pl = JB-EPS's ε′) and
  LAW-3 (t(β+kW) = t(β)+kA, carry-free: ℓW = ℓegγ ≡ 0 mod e) re-derived in
  one line each.
* **WM-RHO.** Re-keyed directly against [ILN]'s ℤ/E-descent display (lines
  445–450, unconditional): γ ↦ γ+E fixes every s_j and shifts β_j by E_j —
  the identical shift structure; then t_j(β_j + E_j) = t_j + ℓ_{j−1}E_j/e_{j−1}
  = t_j + ℓ_{j−1}E_{j−1} (s_j fixed), each ε_j picks up
  z_j^{−ℓ_{j−1}E_{j−1}}, ρ_T as displayed. γ-independence is exactly what
  the leg samples (3 γ per tower vs ONE precomputed ρ).
* **WM-CLASS (display-grade, checked anyway).** κ ∈ ℤ immediate; κ ≥ 0
  re-derived INCLUDING the scan-set subtlety no prior pass spelled out:
  σν + σν′ ≥ 0 and ≡ r0 := (ν+ν′) mod E forces σν + σν′ ≥ r0 (a smaller
  non-negative member of the class would need r0 − kE ≥ 0, k ≥ 1,
  contradicting r0 < E), so it lies in `window_reps`' upward scan set, is in
  W by WINDOW-(n) ("PROVED, generic, unconditional", [ILN] line 273), hence
  σ(ν+ν′) ≤ σν + σν′. ∂Ẽ = ∂E(σν,σν′)·ρ^κ by WM-RHO iterated; the [c]
  display follows. Honestly DISPLAY/review-owed at S2.2 and WM6 ✓.
* **PERIM-μ.** Seed identities re-derived from EPS-CLOSED + ℓW_μ ≡ 0 mod
  e_{μ−1}: t_μ(β+iW_μ) = t_μ(β) + iA_μ (A_μ = ℓW_μ/e_{μ−1} — matches [JA]
  line 74's display), ε_μ(W_μ) = z^{−A_μ} (s(W_μ) = 0) = c₁ ([W2] line 122:
  "c₁ = z_m^{−A_m} [THE Thm-phir constant]"). **(a)**: JA-VDIND at [JA] HEAD
  (lines 269–272): "trivial ABSOLUTELY on A's attained abscissas:
  z_{m−1}^{i·A_{m−1}} = 1 for every attained i" = (PERIM-(m−1)) at the
  attained set (z^{iA} = 1 ⟺ z^{−iA} = 1); (R-coll) = the
  every-recursion-node form, 2 ≤ q ≤ m−1 ([JA] lines 289–292) ✓.
  **(b)**: [JB]@pin column (c): (VD-m) = JA-VDIND's absolute triviality as a
  HYPOTHESIS at every m ≥ 2, unconditional at m ≤ 1 only ((VD-1) = W2-L3) —
  content verified at the pin (see the finding below for the quote's byte
  form); = (a) at the same attained sets ✓. **(c)**: [W2] §3.4 line 294:
  ξ_{m+1} := χ_m^{γ_{m+1}}·z_m^{−e_m·A_m} — at χ_{Q−1} = 1,
  ξ_Q = z_{Q−1}^{−e_{Q−1}A_{Q−1}} = χ^{(Q−1)}_{e_{Q−1}} = ϑ_Q, matching
  JA's ϑ_m := z_{m−1}^{−e_{m−1}A_{m−1}} index-shifted ✓; (C-coll) "every
  interior junction character is trivial" ([W2] line 250) as consumed ✓;
  slot-grid reading per §3.2's letter-twist ✓. Absolute ⟹ slot-grid
  (ord|A ⟹ ord|eA) ✓; converse honestly open, machine-realized by the 9
  slot-only census rows ✓; the χ-chain + mod-wrap caveat carried ✓.

### (3) Evidence-class SAME/NONE rows — nothing consumes them as evidence

* **WM-SHEAR (SAME) re-confirmed from code:** engine line 270 defines
  `gam[j+1] = e[j]*wPhi[j] + h[j]` (line 267: `gam[1] = h[0]` covers q = 0),
  so shearU_i = (i, e_q·wq + i(e_q·wPhi[q] + h_q)) ≡ Hpts_i point-for-point —
  `hullSU == hullH` is unfalsifiable for any true or false (M1). The runner's
  residual checks are hull-commutes-with-shear (generic, JB-AFF) and the min
  tie, whose own code comment says "sanity leg -- engine's own recursion
  recomputed". SAME is the correct label.
* **Consumption audit:** every machine tag on a display keys an IND family or
  the census only — S2.1 [Machine: WM-RHO] (IND), S2.2 [Machine: WM-RHO + κ
  census; class identity arithmetic, "no separate leg"], S3 [Machine:
  WM-FENCE-XI] (IND), S0's F-4 block cites WM-EPS (IND). WM-SHEAR appears
  only inside S5 (prereg row with the SAME label and WITHDRAWN billing; the
  verdict figures under the [r1, F-2] RECORD bracket; the decorrelation
  block). (M1)'s machine evidence is explicitly re-pointed at [JB]'s own IND
  families (rows 8–11, checked standing at the pin, incl. the r6 (f)-cell)
  and JA-VAL's leg. WM-PIN (NONE) is consumed nowhere as mathematical
  evidence — the verdict block cites it only as "both md5s intact". **No
  display consumes a SAME or NONE row as evidence.**
* Spot re-audit of IND labels in the runner source concurred with PE2's
  10/10 (t_fresh from raw `T.e`/`T.l` vs committed `eps`; `constants`
  recursion vs ∂t_fresh; brute field-exponentiation loop vs divisibility in
  FENCE-EQ; Ecoch-vs-closed-form in RHO).

### (4) Arc accounting at HEAD — CONSISTENT

All hashes resolve with matching content: b375f42 (seal) → 0baeb3b (verdict)
→ df00707 (PE1, 08:55:20, headline 0C/5G+3m ✓) → 90db22d (r1, 09:27:15) →
1edb104 (PE2, headline "0 CRITICAL, 1 gap (freshness DRIFT, not r1's error)
+ 2 minors" ✓) → 8f1c1f2 (r2, 2026-08-06 11:42, note-only ✓ +105/−18 ✓);
sibling pins 4c4ee56/3870bc8/f9f104e/4607824/126c33f all resolve with the
stated roles and timestamps; the standing rule = ledger 5c849a3 ✓; [SYN]
f71cd68 and ledger 7724c20 resolve ✓. The r1 status line is struck with the
r2 status CURRENT; counter 0/2 at header and footer with "PE3 next" at both;
20 [r2] brackets as claimed; runner + artifacts byte-frozen across the r2
boundary (r2 numstat touches only the note). The dagger labels are now DATED
(post-r7/post-r5, as-of pins), curing PE2's F-2 staleness species going
forward: JB r8 (49f9168) and JC r6 (4b804b4) postdate WM r2 and falsify no
pinned quote (both verified: the r8 fix is a report-bracket quotation inside
[JB]'s own round record; the r6 fix is a [JC]-internal pointer annotation —
neither touches a WM-consumed face, and WM reads at the pins regardless).
LED-Λ precedent quote re-verified byte-exact; the unpinned [JA]-at-HEAD
quote (JA-EPS's quantifier "every β ∈ ℤ in the level-m weight lattice")
re-verified byte-exact at [JA] HEAD lines 167–168.

## FINDINGS

### F-1. MINOR (quotation attribution at S3(b): the pinned quote's byte-form matches [JB] §5's fence display, not the §0M column (c) cell it is attributed to)

WM S3(b) (the WM-FENCE(b) citation proof, a live theorem surface):

> JB-CREAD's governing fence consumes JA-VDIND verbatim ([JB]† §0M column
> (c) **[r2: as of 4c4ee56]**: "at every m ≥ 2 a HYPOTHESIS — JA-VDIND's
> ABSOLUTE character-triviality")

At the pin 4c4ee56, §0M column (c)'s bytes are "… at every m ≥ 2 a
HYPOTHESIS **(**JA-VDIND's ABSOLUTE character-triviality z_{m−1}^{i·A_{m−1}}
= 1 at every attained abscissa**)**" (line 224, parenthesis), and the live
grade cap's §5 bullet has the same paren + lowercase form (line 476). The
quoted em-dash form appears byte-exactly (modulo wrap) at exactly one site
of the pinned source: **§5's [r3, STEP 2] regenerated fence display** (lines
2205–2206: "at every m ≥ 2 a / HYPOTHESIS — JA-VDIND's ABSOLUTE
character-triviality"), which cites "[row 21]"; row 21's own column (c) cell
is the pointer "**YES — the governing fence**", not the text. So the quote
is real and byte-true IN the pinned document — and it is in fact the display
of the very object the WM sentence names ("JB-CREAD's governing fence") —
but the parenthetical attributes it to a matrix cell where the byte-check
fails on punctuation. This wording predates r2 (PE1/PE2 checked the content
halves and passed the carriage); what r2 changed is that the quote now
carries an as-of pin tag, i.e. an assertion of byte-fidelity at the pin,
which holds at §5's display and not at the named cell. Same species as JB
PE8's fused-quotation finding, one notch weaker (the string exists
byte-for-byte at one live site of the source). Semantics identical at both
sites; no consumer carries anything wrong; honesty defect NIL. Repair is
one attribution ("§0M column (c)" → "§5's regenerated fence display /
§0M row 21 (c)" or re-quoting the column's own paren form).

## OBSERVATIONS (not findings; recorded for the arc)

* **O-1 (pin coverage is [JB]/[JC]-scoped, as r2 itself states).** Quotes
  from [JA]/[W2]/[ILN]/LED-Λ carry no as-of pins, and S0's F-4 block
  warrants one [JA] quote explicitly "at [JA]† HEAD". All such quotes were
  re-verified byte-true at HEAD this pass ([JA] unchanged since ce0469a, [W2]
  since 5463f2a — both pre-seal; [ILN] ACCEPTED). No falsehood exists at
  HEAD and the r2 claim is honestly scoped to "[JB]/[JC] cross-note
  reference"s, so this is not a defect; but the drift species PE2 caught
  remains structurally open for the unpinned sources should the JA/W2 arcs
  resume mid-WM-arc. A fold could close it with two more pins.
* **O-2 (F-3 is conservative).** WM-COB-F does evaluate committed
  `Tower.eps` at in-window split betas (all non-negative on the roster), so
  the committed-eps identity has more machine key than the F-3 bracket
  credits; the correction erred in the honest direction.
* **O-3 (grep pitfall, for future passes).** Two load-bearing pinned quotes
  wrap mid-string at their sources ([RMG] grade cap "consuming [RMG] as /
  ACCEPTED…", JA-EPS "weight / lattice") — single-line greps report false
  absences; byte-checks must be wrap-insensitive.

## HONESTY GRADE

Above genre par, sustained through r2: the pin round did exactly what it
declared (16 pinned reference sites, 20 [r2] brackets, all verified at the
pins), the (M1)/(F-a) drift repair carries [JB]'s r6 re-fence at full
strength including the strictly-stronger `P≤q` clause and its bite
geography, the F-3 range correction is against interest, and the dagger
labels now carry dates. The one finding is attribution-precision on a
byte-real quote, not a content defect; no displayed identity is wrong; no
face consumes more than its citation proves; nothing is upgraded. The
machine leg is bit-exact.

**Counter: 0/2 (this pass does not count as clean — one MINOR; the r2 diff
itself is verified correct at every site).**

— PE3 verifier, fresh context, 2026-08-06.
