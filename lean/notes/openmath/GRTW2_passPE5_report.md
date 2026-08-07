# GRTW2 passPE5 report — hostile pass 5 on `GRTW2_PROOF_2026-08-08.md` (post-r4; acceptance attempt)

**Verifier:** Fable hostile pass PE5, fresh context, wallclock 2026-08-07.
**Target:** `lean/notes/openmath/GRTW2_PROOF_2026-08-08.md` at HEAD (last note
commit 94534df = the r4 repair round, 2026-08-07 14:20 UTC; working tree
byte-clean, `git status` clean on `verification/`). **Inputs read:** the
PE1/PE2/PE3/PE4 reports (083adff / 79e796b / 9bd938f / e92cb22), the full
r4 diff (79d1d9c → 94534df, note-only +142/−21), the full note at HEAD
(1,330 lines), the sealed runner `grt_w2_checks.py` + committed artifacts +
`iterlawn_pe_reimpl.py` at the cited lines, the PE3 report's construction
block at source. I fixed nothing.

## VERDICT

**0 CRITICAL ERRORS. 0 JUSTIFICATION GAPS. 0 minor defects. CLEAN — the
counter advances 0/2 → 1/2** (a clean pass starts the 2-clean count;
**W2-PE6 is the would-be accepting attempt**). Everything r4 SET OUT to do
is done correctly and faithfully: the five same-species "identification"
surfaces (the three PE4-listed misses §6.3(d) / §5.2 (OPEN-2a) gloss /
§6.4 [r2], plus the two sweep-completing appositive sites §6.2 W2-ID1-row
and W2-OPEN-2-row) are scoped to the proved direction in the r3 wording
family, byte-preserving every struck span (§A); the o-b roster-instance
qualifier, the o-c line-figure fix (verified at the sealed source:
`orbit_scan` def at line 135, `return out` at 163, 164 blank), and the o-e
3-read extension precision are all accurate as written (§A); **my own full
grep of every "identification" token at HEAD (27 hits) confirms the
disposition is complete — the species is exhausted** (§A.2), and a
variant-vocabulary sweep ("coincidence", "proved at m = 1", ⟺/iff tokens)
finds no residual two-sided assertion outside struck spans, dated records,
scoped brackets, roster-instance claims, and different senses. The whole
note is statement-level TRUE at HEAD (§B), with my own census
recomputation from the committed JSON reproducing every figure the fences
carry. The machine leg reproduces (exit 0, 6,403/0, 17 GREEN, results JSON
byte-identical including elapsed_s; §C). A fresh leg by a route unused by
PE1–PE4 — **the Lean kernel: the note's integer-exponent system proved as
17 general ∀-theorems, `lake env lean` exit 0, zero sorry, Lean-core
axioms only** — confirms W2-L0, W2-L2 with its integrality warrants, the
Bézout/A_m facts, the m = 1 closed-form tie, the W2-ID1 exponent chain,
and the counter-instance pins at full generality (§D). Arc accounting is
consistent and true at every surface, including the previously-stale
footer dateline (§E). Three nil-weight observations, no repair owed.

---

## §A. Charge 1 — the r4 diff, line-by-line: FAITHFUL at every edit site

### A.1 The scoped surfaces (all match the r3 wording family)

* **§6.3(d) carry item:** struck span "~~the recorded-ξ/byte-divergence
  identification at m ≥ 2, proved only at m = 1 (W2-ID1),~~" byte-equal to
  the pre-r4 text (diff-verified, wrap-insensitively) ✓; the [r4, PE4-P1]
  replacement asserts exactly the r3 content: forward direction (recorded
  ξ = 1 ⟹ byte-equal), proved at m = 1 (W2-ID1) — TRUE of the direction;
  converse UNPROVED at every m with the §5.2 pointer ✓. The retained
  "instance-exact on the roster" is machine-true two-sidedly (my §B.2
  recomputation: recorded ξ ≠ 1 ⟺ byte-RED at 22/22) ✓.
* **§5.2 (OPEN-2a) opening gloss:** struck span byte-preserves the [r2]
  gloss ✓; the replacement's "IS that identification's forward half
  (recorded ξ = 1 ⟹ byte-equal — the HALF … that every consuming surface
  of this note uses)" matches the r3-corrected W2-ID1 "Consequently"
  wording and the sub-clause statement it glosses (which is unchanged,
  with its exact Status line: PROVED at m = 1, OPEN at m ≥ 2) ✓; the
  appended converse sentence is the r3 formula verbatim in content ✓.
* **§6.4 [r2] record:** inline [r4, PE4-P1] annotation ("= of its FORWARD
  direction only …; the converse is UNPROVED at every m — §5.2 [r3]"),
  original record text preserved un-struck — the dated-record convention
  r3 used at §8 P1(a) (verified present at §8) ✓.
* **§6.2 W2-ID1 row (PE4 o-d):** appositive "(the boundary identification,
  m = 1 case)" struck byte-exact; [r4] replacement "(the FORWARD half …;
  the converse is unproved at every m — §5.2 [r3])" ✓. Statement column
  unchanged and correctly one-directional ✓.
* **§6.2 W2-OPEN-2 row (adjacent label):** "[r4: = its FORWARD direction
  only (recorded ξ = 1 ⟹ byte-equal); §5.2 [r3]/[r4]]" — accurate: the
  (OPEN-2a) sub-clause statement IS the forward direction at m ≥ 2 ✓;
  both cited brackets exist at §5.2 ✓.
* **[r1, F1] block (PE4 o-b):** the universal "ABOVE r₀ … byte-DIFFERENT"
  now carries "[r4, PE4 o-b: roster instance (all 6 above-r₀ SKIP
  junctions byte-RED — PE2/PE4 recomputation); in general UNPROVED …;
  this block's conclusion consumes only the ABSENCE of the byte-share
  warrant, which holds either way]" — every clause verified: my own
  recomputation confirms all 6 SKIPs byte-RED (§B.2); the
  consumes-only-absence logic is sound (the grade split needs the proved
  warrant to be MISSING above r₀, which is the case whether or not the
  keys are byte-different) ✓.
* **o-c:** "lines ~~135–164~~ 135–163" — verified at the sealed source
  this pass: `def orbit_scan` at runner line 135, `return out` at 163,
  line 164 blank; seal 71f8fc90…ba52 intact ✓.
* **o-e:** the [r4] precision inside the [r3] converse flag — verified
  mathematically: the counter-instance chamber has reads 0–1 only, so its
  junctions are r = 2, 3 and its top junction r = 3 IS its r₀; the box's
  range r > r₀ is empty there; appending ANY third read creates the r = 4
  junction with q = r₀ = 3 in the byte-DIFFERENT range while the q = 3
  junction stays byte-equal (lower junction data is computed from lower
  reads only) — falsity instantiated, exactly as written ✓.
* **S-STATUS [r4] + §10 round block + footer:** every arc fact checked
  against git and the PE4 report — see §E. The §10 summary of PE4's
  findings/confirmations is clause-accurate vs the committed report
  (B1–B8, §ADJ's three-point adjudication, 33,408/0, 4,173 × 7, 29,223/0,
  o-a..o-e handling) ✓.

### A.2 The token disposition — COMPLETE (my own grep, 27 hits)

`grep -n identification` at HEAD: **scoped [r3]/[r4] sites** (119, 727,
789, 807/809, 979, 981, 1006, 1036) ✓ each one-directional or
roster-scoped; **struck spans preserved as record** (720, 802–803, 1004)
✓; **historical records quoting the species as the thing cured**
(36 S-STATUS, 1040 §6.4 [r3], 1137/1139 §8 P1, 1217/1221 §9 P1,
1285–1306 §10 itself) ✓; **different senses** (600 §5.1 letter
identification z_old = ξ·z_new; 931 + 1097 §5.4/§7 overflow
identification of the 24 byte-diff pairs) ✓. Variant sweep: "coincidence"
(110, 980 — both inside struck spans; 229, 770 — different senses),
"proved (only) at m = 1" (all sites either struck, records, or attached
to the forward direction/W2-ID1, each TRUE), ⟺/iff tokens (roster
instance-exactness — machine-true, §B.2 — or proved mathematical iffs).
**No residual two-sided surface exists at HEAD.**

## §B. Charge 2 — statement-level truth of the whole note at HEAD

### B.1 The clauses, the lemma, the boxes (re-read + spot re-derivations)

* **W2-C1/W2-C1a** with the [r1, F2] chamber qualifier: accurate (probe F2
  record's 6 vok/onesided failures are exactly what the qualifier fences;
  harness-side content unconditional per the displayed proof) ✓.
* **W2-C2(a)/(b)/(c) + §3.4:** the m = 1 form re-derived by hand
  (ξ = χ₁^{γ₂}·z₁^{−e₁A₁} = z₁^{−e₁ℓ₀g₀h₀} = c₁^{e₁}, w = 1 ✓); the s = 0
  top-slot warrant (e ∣ V ⟹ ℓV mod e = 0) and the W2-L2 identity with both
  integrality warrants re-derived AND kernel-checked (§D) ✓; the (C-coll)
  fencing and W2-BOX-1 accurate; the §3.5 boundary-witness integer
  skeleton independently recomputed (ℓ₀ = 2, ℓ₁ = 1, γ₂ = 13, A₁ = 4,
  A₂ = 13, χ₂ = z₁⁴ = 1, ξ₃ = z₂^{−13} = z₂ = −1) and its group algebra
  kernel-checked (§D) ✓ — consistent with the committed I4B ledger.
* **LEMMA W2-ID1:** statement + proof sound (re-derived: recorded (1, w)
  forces w = 1 at j = 0 since ψ₁(0) ≠ 0; then ξ_f^j = 1 on supp(ψ₁)
  including the monic top; then c·z₁^{A₁e₁j} = ξ_f^{g₁−j} = 1 — rk. 3's
  m = 1 byte law; exponent chain kernel-checked §D) ✓. The [r3]
  "Consequently" is exactly one-directional ✓. The counter-instance block
  TRUE (re-verified: F₄* has order 3 so ξ³ = 1 for every unit —
  kernel-checked for EVERY 4-element field §D; ψ₁ = y³ + ζ irreducible,
  byte-equal junction at e₀ = 1, scan records first satisfying ξ in enum
  order, ζ = (0,1) precedes 1 = (1,0) at the sealed reimpl line 220 —
  read at source this pass) ✓; the PE3 quote spans word-exact at the
  committed PE3 report (bold markers dropped as PE4 disclosed) ✓;
  roster-invisibility ("only g in {1,2} implemented", reimpl line 311 —
  verified) ✓.
* **W2-C3 + the [r1]–[r4] grade machinery:** the 38/44–6/44 split, the
  36 + 2 decomposition, and every consuming surface re-read
  one-directional — all confirmed by my own recomputation (§B.2) ✓.
* **W2-OPEN-2/(OPEN-2a) + W2-OPEN-1:** correctly OPEN; the premise carries
  the [r3] converse flag + [r4] o-e precision + (OPEN-2a) honestly; the
  four-route adjudication stands (PE1/PE2-verified at source; not
  re-opened by r4, no new consumption) ✓.

### B.2 My own census recomputation (committed JSON, own is-one test, own SKIP/walk classification)

44 junction-levels = 16 r = 2 + 28 r ≥ 3 ✓; 22 walked + 6 SKIP, **all 6
SKIPs byte-RED** (T3A/T3C/T3D/T3E r = 4, I4C r = 4, 5 — exactly the 6
above-twist junction-levels) ✓; walked split 12 RED / 10 GREEN (→ 18/10)
✓; **recorded ξ ≠ 1 ⟺ byte-RED at 22/22 walked, 0 exceptions** ✓; every
below-r₀ junction byte-GREEN ✓; first-twist census T2A/C/D/G = 3,
T3A/C/D/E = 3, T3B/F = 4, I4B = 5, I4C = 3, T2B/E/F + I4A none ✓; 38
at-or-below = **36 fully derived + 2 instance-warranted (exactly I4A r = 5,
I4B r = 5)** ✓; I4B ledger [(3, 1), (4, 1), (5, (−1,−1))] with r = 4
byte-equal and r = 5 byte-RED ✓. Every figure carried by the grade cap,
§5.2, §6.1, §6.2 matches.

## §C. Machine leg (re-run this pass)

* **Seals:** `grt_w2_checks.py` sha256 71f8fc90…ba52 byte-identical at
  working tree, seal commit 5463f2a, and HEAD ✓ (git log: untouched since
  5463f2a); `grt_weld_probe.py` 107c92b6…4ea9 ✓; both committed artifacts
  hash-identical at HEAD vs working tree ✓; `git status verification/`
  clean before and after ✓.
* **Re-run (in a /tmp copy of the three sealed modules): exit 0. 6,403
  samples, 0 violations, 17 families GREEN, boundary junctions = 1.**
  Produced results JSON **byte-identical to the committed artifact
  including elapsed_s (3.2)** — `diff` empty; stdout differs only in two
  intermediate timing figures + the JSON-path line (expected from /tmp).
  Per-family counts match §6.1 exactly (CK-MM 4,396 · CK-HR1/VD1 156 ·
  CK-REC 55 · CK-SLOT 44/16 · CK-XI 22 · CK-BYTE 28 · TW-R/A/S 44 ·
  TW-F3/F3b 684 · TW-PARI 12 · TW-QO 7 · CK-T3E 2 · MT-TW 2).
* **Total reconciled this pass** (no earlier report displayed it): the 17
  scored families sum to 6,396; TOTAL 6,403 = 6,396 + 6 CK-REC-SKIP
  (the 6 non-shared junctions) + 1 CK-XI-BOUNDARY (I4B r = 5, recorded
  not scored) — the runner's own note counters; the note's figures quote
  the runner's verdict line and per-family table consistently. CK-XI's
  22 = 21 perimeter (theta-trivial, scored) + 1 boundary as the §6.1 row
  states (code read at runner lines 575–596) ✓.

## §D. Charge 3 — fresh route unused by PE1–PE4: THE LEAN KERNEL

PE1 re-derived the system by hand; PE2 evaluated the m = 1 roster slice;
PE3 walked the full roster with own arithmetic; PE4 exhaustively mapped
the selection geography. THIS pass proved the note's integer-exponent
system as **general ∀-theorems over ℤ (and abstract groups/fields),
kernel-checked**: no sampling, no roster, no pool — full generality where
every prior leg was instance evidence or prose derivation.

**Artifact:** `/tmp/W2PE5_fresh.lean` (source embedded in Appendix I for
durability), compiled against the repo's pinned toolchain + Mathlib:
`lake env lean` **exit 0, zero sorry, 17 declarations**; `#print axioms`
on the load-bearing seven: Lean-core only ({propext, Classical.choice,
Quot.sound} or subsets). Contents:

* **L0_grid_congr + L0_least_abscissa** — W2-L0 in full: x·h ≡ V (mod e)
  ⟺ x ≡ ℓV (mod e) given a Bézout inverse, and s = (ℓV) mod e is the
  least nonnegative solution (0 ≤ s < e, solves, ≤ every nonneg solution).
* **L2_warrant1/L2_warrant2** — the two integrality warrants the note
  uses silently (e ∣ V − 𝔰h and e ∣ ℓu − 𝔰 for u = V + kW, W ∈ eℤ, any
  𝔰 ≡ ℓV): the well-definedness of u′ and T.
* **L2_mismatch** — THE W2-L2 identity T + (ℓ′𝔰 − ℓu′) = (ℓW/e)·k as a
  general theorem with exact-division witnesses, for ANY 𝔰 in the residue
  class (covers the print's ideal abscissa 𝔰_j, not just the canonical
  representative). **L2_element_form** — the ε·z^T = z^{A·k} element form
  in an arbitrary commutative group, A = ℓ·g·γ.
* **bezout_ell_zero_iff + A_nonneg_and_zero_iff** — the §1.1/§1.3 pins:
  under the normalized convention, ℓ = 0 ⟺ e = 1; A_m ≥ 0 and
  A_m = 0 ⟺ e_{m−1} = 1.
* **slot_weight_tie** — §2.1's V_j = β_j under γ = eW + h.
  **top_slot_s_zero** — §3.3(a)'s s = 0 warrant (e ∣ V ⟹ ℓV mod e = 0).
* **m1_xi_is_c1_pow** — §3.4's m = 1 tie z^{−eA} = (z^{−A})^e = c₁^e.
* **id1_chain + id1_w_forcing** — LEMMA W2-ID1's algebra: w forced to 1
  at j = 0 in any field; and ξ^g = 1 ∧ ξ^j = 1 ⟹ ξ^g·(ξ^{−1})^j = 1 —
  rk. 3's byte law — in any commutative group.
* **four_field_cube + orbit_eq_all_units** — the counter-instance pins at
  full generality: in ANY field of exactly 4 elements every nonzero x has
  x³ = 1, and any ξ with ξ³ = 1 gives (ξy)³ + c = y³ + c identically —
  so the ENTIRE unit group of K₁ satisfies ψ₁ = y³ + ζ's orbit equations,
  for every 4-element field and every ζ: the ambiguity the sealed scan's
  enum-order selection resolves spuriously is now a kernel fact, not a
  probe observation.
* **i4b_skeleton + i4b_character** — the §3.5 boundary-witness numbers
  (ℓ₀ = 2, ℓ₁ = 1, γ₂ = 13, A₁ = 4, A₂ = 13) and the character collapse
  (z² = 1 ⟹ z₁⁴ = 1 ∧ z₂^{−13} = z₂) — the note's bracket figures.

All 17 prove on the first-principles statements as displayed in the note
(with the note's own hypotheses, nothing weakened). **0 discrepancies.**

## §E. Charges 1+4 — arc accounting: CONSISTENT AND TRUE at every surface

* **The chain vs git:** composed 5463f2a (08-04 15:59) → PE1 083adff
  (08-06 19:16; report verdict 0C+2G+5m = S-STATUS ✓) → r1 8d5e3fa
  (19:45) → PE2 79e796b (08-07 08:20; 0C+2G+1m ✓) → r2 ffa1e57 (08:35) →
  PE3 9bd938f (09:18; 0C+1G minor ✓) → r3 79d1d9c (09:31) → PE4 e92cb22
  (14:03; 0C+1Gm+1m ✓) → r4 94534df (14:20). Clock-ordered, hashes exact,
  every verdict checked against its committed report ✓.
* **One CURRENT status** ([r4] S-STATUS); counter 0/2 + "W2-PE5 next" at
  all three live surfaces (S-STATUS, §6.4 [r4], §10 freeze) ✓; the dated
  round records §7/§8/§9 retain their contemporaneous pointers per the
  arc convention ✓; the Genre line's struck r0 parenthetical stands ✓.
* **The footer dateline** now complete: "r1 2026-08-06; r2 2026-08-07;
  r3 2026-08-07; r4 2026-08-07" — all four dates git-verified ✓ (PE4's P2
  cured, including the r3 back-fill).
* **Freeze claims:** r4 touched only the note (diff = 1 file) ✓; runner +
  artifacts byte-frozen through all four rounds (hash-verified at
  5463f2a/HEAD/tree this pass) ✓.

**Ungraded observations (nil weight, no repair owed):**
* (o-i) §10's compression of PE4's spurious set — "{(F₄, g = 3,
  supp {0,3}), (F₉, g = 4, supp {0,4})}" — drops PE4 §D's F₉-modulus
  qualifier ("with modulus y²+1"); enumeration order is
  representation-dependent, so the F₉ family is exact relative to PE4's
  fixed field constructions. The dated record cites the report, which
  carries the qualifier.
* (o-ii) §6.3(d)'s [r4] apposition "the FORWARD direction of the …
  identification at m ≥ 2 …, proved at m = 1 (W2-ID1)" reads elliptically
  (the m ≥ 2 sub-clause is not itself an m = 1 statement); the direction
  parenthetical and §5.2's exact Status line disambiguate — no unproved
  statement is asserted proved.
* (o-iii) The 6,403-vs-6,396 total reconciliation (§C) was displayed by
  no earlier pass; recorded here so no future pass re-derives it.

## Repair queue implied

**None.** This pass grades the post-r4 text CLEAN. Counter 1/2; W2-PE6 —
a fresh hostile pass on THIS text, same bar — is the accepting attempt.

---

## Appendix I — the fresh-leg Lean source (compiled exit 0 this pass)

```lean
/- GRTW2 PE5 fresh leg — the note's integer-exponent system as KERNEL-CHECKED
   ∀-theorems (route unused by PE1–PE4: Lean kernel; no sampling, no pool). -/
import Mathlib

namespace W2PE5

theorem L0_grid_congr (e ℓ h V x : ℤ) (hbez : e ∣ (ℓ*h - 1)) :
    e ∣ (x*h - V) ↔ e ∣ (x - ℓ*V) := by
  constructor <;> intro hd
  · have hx : x - ℓ*V = ℓ*(x*h - V) - x*(ℓ*h - 1) := by ring
    rw [hx]; exact dvd_sub (hd.mul_left ℓ) (hbez.mul_left x)
  · have hx : x*h - V = h*(x - ℓ*V) + V*(ℓ*h - 1) := by ring
    rw [hx]; exact dvd_add (hd.mul_left h) (hbez.mul_left V)

theorem L0_least_abscissa (e ℓ h V : ℤ) (he : 0 < e) (hbez : e ∣ (ℓ*h - 1)) :
    0 ≤ (ℓ*V) % e ∧ (ℓ*V) % e < e ∧ e ∣ (((ℓ*V) % e)*h - V) ∧
    ∀ x, 0 ≤ x → e ∣ (x*h - V) → (ℓ*V) % e ≤ x := by
  refine ⟨Int.emod_nonneg _ (ne_of_gt he), Int.emod_lt_of_pos _ he, ?_, ?_⟩
  · rw [L0_grid_congr e ℓ h V _ hbez]
    have h1 : e * (ℓ*V / e) + (ℓ*V) % e = ℓ*V := Int.ediv_add_emod _ _
    exact ⟨-(ℓ*V/e), by rw [mul_neg]; linarith⟩
  · intro x hx hsol
    have hcong : e ∣ (x - ℓ*V) := (L0_grid_congr e ℓ h V x hbez).mp hsol
    have hmod : x % e = (ℓ*V) % e := Int.ModEq.symm (Int.modEq_iff_dvd.mpr hcong)
    have hdiv : 0 ≤ x / e := Int.ediv_nonneg hx (le_of_lt he)
    have hsplit : e * (x / e) + x % e = x := Int.ediv_add_emod x e
    nlinarith [mul_nonneg (le_of_lt he) hdiv]

theorem L2_warrant1 (e ℓ ℓ' h V s : ℤ) (hbez : ℓ*h + ℓ'*e = 1)
    (hs : e ∣ (s - ℓ*V)) : e ∣ (V - s*h) := by
  have hx : V - s*h = (-h)*(s - ℓ*V) + (V*ℓ')*e := by linear_combination (-V)*hbez
  rw [hx]; exact dvd_add (hs.mul_left (-h)) (dvd_mul_left e (V*ℓ'))

theorem L2_warrant2 (e ℓ V u k W' s : ℤ) (hu : u = V + k*(e*W'))
    (hs : e ∣ (s - ℓ*V)) : e ∣ (ℓ*u - s) := by
  have hx : ℓ*u - s = -(s - ℓ*V) + e*(ℓ*k*W') := by rw [hu]; ring
  rw [hx]; exact dvd_add (dvd_neg.mpr hs) ⟨ℓ*k*W', rfl⟩

theorem L2_mismatch (e ℓ ℓ' h V u k W' s x y : ℤ) (he : e ≠ 0)
    (hbez : ℓ*h + ℓ'*e = 1) (hu : u = V + k*(e*W'))
    (hx : V - s*h = e*x) (hy : ℓ*u - s = e*y) :
    y + (ℓ'*s - ℓ*x) = ℓ*W'*k := by
  have key : e*(y + (ℓ'*s - ℓ*x)) = e*(ℓ*W'*k) := by
    linear_combination (-1)*hy + ℓ*hu + ℓ*hx + s*hbez
  exact mul_left_cancel₀ he key

theorem L2_element_form {G : Type*} [CommGroup G] (z : G)
    (e ℓ ℓ' h V u k gγ s x y : ℤ) (he : e ≠ 0)
    (hbez : ℓ*h + ℓ'*e = 1) (hu : u = V + k*(e*gγ))
    (hx : V - s*h = e*x) (hy : ℓ*u - s = e*y) :
    z^(ℓ'*s - ℓ*x) * z^y = z^((ℓ*gγ)*k) := by
  rw [← zpow_add]
  congr 1
  have := L2_mismatch e ℓ ℓ' h V u k gγ s x y he hbez hu hx hy
  linarith

theorem bezout_ell_zero_iff (e ℓ ℓ' h : ℤ) (he : 1 ≤ e) (h0 : 0 ≤ ℓ)
    (hlt : ℓ < e) (hbez : ℓ*h + ℓ'*e = 1) : ℓ = 0 ↔ e = 1 := by
  constructor
  · intro hl
    have hd : e ∣ 1 := ⟨ℓ', by rw [hl] at hbez; linarith [mul_comm e ℓ']⟩
    have := Int.le_of_dvd one_pos hd
    omega
  · intro he1; omega

theorem A_nonneg_and_zero_iff (e ℓ ℓ' h g γ : ℤ) (he : 1 ≤ e) (h0 : 0 ≤ ℓ)
    (hlt : ℓ < e) (hbez : ℓ*h + ℓ'*e = 1) (hg : 1 ≤ g) (hγ : 1 ≤ γ) :
    0 ≤ ℓ*g*γ ∧ (ℓ*g*γ = 0 ↔ e = 1) := by
  constructor
  · positivity
  · rw [← bezout_ell_zero_iff e ℓ ℓ' h he h0 hlt hbez]
    constructor
    · intro hA
      rcases mul_eq_zero.mp hA with h1 | h2
      · rcases mul_eq_zero.mp h1 with h3 | h4
        · exact h3
        · omega
      · omega
    · intro hl; rw [hl]; ring

theorem slot_weight_tie (g j h e W γ : ℤ) (hγ : γ = e*W + h) :
    (g*γ - j*h) - j*(e*W) = (g - j)*γ := by subst hγ; ring

theorem top_slot_s_zero (e ℓ V : ℤ) (hV : e ∣ V) : (ℓ*V) % e = 0 :=
  Int.emod_eq_zero_of_dvd (hV.mul_left ℓ)

theorem m1_xi_is_c1_pow {G : Type*} [CommGroup G] (z : G) (e A : ℤ) :
    z^(-(e*A)) = (z^(-A))^e := by
  rw [← zpow_mul]; ring_nf

theorem id1_chain {G : Type*} [CommGroup G] (ξ zAe : G) (g j : ℤ)
    (hz : zAe = ξ⁻¹) (hg : ξ^g = 1) (hj : ξ^j = 1) :
    ξ^g * zAe^j = 1 := by
  rw [hz, inv_zpow, hg, hj]; simp

theorem id1_w_forcing {F : Type*} [Field F] (w a : F) (ha : a ≠ 0)
    (hw : w * a = a) : w = 1 := by
  field_simp at hw; exact hw

theorem four_field_cube (F : Type*) [Field F] [Fintype F]
    (h4 : Fintype.card F = 4) (x : F) (hx : x ≠ 0) : x^3 = 1 := by
  have := FiniteField.pow_card_sub_one_eq_one x hx
  rw [h4] at this; norm_num at this; exact this

theorem orbit_eq_all_units {F : Type*} [Field F] (ξ c y : F) (h3 : ξ^3 = 1) :
    (ξ*y)^3 + c = y^3 + c := by
  have : (ξ*y)^3 = ξ^3 * y^3 := by ring
  rw [this, h3, one_mul]

theorem i4b_skeleton :
    (2*2) % 3 = 1 ∧ (1*1) % 2 = 1 ∧
    (2:ℤ)*(3*1*2) + 1 = 13 ∧
    (2:ℤ)*1*2 = 4 ∧
    (1:ℤ)*1*13 = 13 := by
  norm_num

theorem i4b_character {G : Type*} [CommGroup G] (z1 z2 : G)
    (h1 : z1^(2:ℤ) = 1) (h2 : z2^(2:ℤ) = 1) :
    z1^(4:ℤ) = 1 ∧ z2^(-13:ℤ) = z2 := by
  constructor
  · have : z1^(4:ℤ) = (z1^(2:ℤ))^(2:ℤ) := by rw [← zpow_mul]; norm_num
    rw [this, h1, one_zpow]
  · have : z2^(-13:ℤ) = (z2^(2:ℤ))^(-7:ℤ) * z2 := by
      rw [← zpow_mul, ← zpow_add_one]; norm_num
    rw [this, h2, one_zpow, one_mul]

end W2PE5
```

(Compile record: `lake env lean /tmp/W2PE5_fresh.lean` exit 0, two
deprecation warnings only (`Int.ediv_add_emod`), zero sorry; `#print
axioms` on L0_least_abscissa / L2_mismatch / L2_element_form /
A_nonneg_and_zero_iff / four_field_cube: Lean-core only; id1_chain:
[propext]; i4b_character: [propext, Quot.sound].)

— PE5, GRTW2 acceptance arc, 2026-08-07.
