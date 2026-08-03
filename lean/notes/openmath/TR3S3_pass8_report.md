# TR3-S3 hostile pass 8 (Fable, fresh context, independence-fenced) — REVISION 4

**Target:** `lean/notes/openmath/TR3S3_2026-08-08.md` (REVISION 4) +
`verification/openmath/tr3s3_check.py` + `tr3s3_check_run2_output.txt`.
**Context consumed:** TR3S1 (ACCEPTED, REV 2 two-clean), TR3S2 (ACCEPTED at
REVISION 1, two-clean), STRATA3, GRB_ORDER2 (REV 14), plus the harness code
(`strata3_probe.py`, `grb_order2_check.py`) and the repository git record.
**Independence fence honored:** no `TR3S3_pass*_report.md` was read; all
verification below is from the note, its parents, the code, and my own
re-derivations/implementations.
**Charge:** quote-and-classify (CRITICAL vs GAP), fix nothing, FULL pass over
the enumerated perimeter. Numerics are falsifiers, never proofs; fgmn.txt is
corrupted at Def 3.15 and was not consulted.

## VERDICT: CLEAN — 0 critical, 0 justification gaps

Every item of the charged perimeter was re-derived or re-executed and found
sound. Three non-classifiable observations are recorded in §9 (display-level;
none touches the logical chain or the record's integrity).

---

## 1. Lemma KER (S3) — VERIFIED

Restated: at every FGMN level i ∈ {1,2,3} of the stratum (e_i^F = 1, e(µ_i) = 1,
Γ_i = ℤ), eq (12) reads u·1 + s·h_i = β with 0 ≤ s < 1, forcing (s,u) = (0,β);
Bézout ℓh_i + ℓ′·1 = 1 with 0 ≤ ℓ < 1 forcing (ℓ,ℓ′) = (0,1); corrected
Def 3.15 exponent ℓ′s − ℓu = 0, so ǫ₁ ≡ ǫ₂ ≡ 1 (ǫ₀ ≡ 1 by convention AND
formula, as in TR3-S1 (A1)). One-line algebra, checked directly; the harness's
`bezout`/`eq12` implement exactly the degenerate branch (`bezout(1,h) = (0,1)`,
`eq12(β,1,h) = (0,β)`), and the stratum consequences (forced abscissa start 0
stride 1; t-exponents lose their ℓu terms; t-integrality trivial) each follow.
The level-index bookkeeping is right: ǫ₂ (consumed inside Def 3.16 at i = 3)
uses FGMN level-2 data (e₂,h₂)^F = (e₁,h₁)^proj — the harness's
`eps2 = z₂^(l1p·s − l1·u)` splits by `(T.e1, T.h1)`, matching TR-5.

## 2. Lemma A3 (S4) — VERIFIED on all five charged sub-items

* **Truncation.** A MacLane chain of µ₃ truncates to one of µ₂ (drop the last
  augmentation; FGMN Def 3.1 is nested by construction), so (H-CHAIN) at depth
  3 supplies it at depth 2; the substate's data (reads ν₀, ν₁; keys Φ₀, Φ₁;
  lawful Φ₁ with w₁(Φ₁) = g₀h₀ and R_{λ₀}(Φ₁) ∼ ψ₀; same K₀, K₁) are verbatim
  the S0 setting's own first-read data, i.e. exactly TR3-S1's S0 inputs at
  e₀ = 1 (with e₁ = 1 a permitted special case of TR3-S1's general e₁, and
  (e_j,h_j)-coprimality automatic at e = 1). The substate lies on TR3-S1's
  stratum; the accepted theorem applies in full.
* **Inheritance.** (A3) is the verbatim instance of TR3-S1's display
  (TR3-S1): σ₁-coefficientwise R^F_{2,γ}(f) = y^{j₀}·R_λ(f), at f := A,
  γ := w₂(A). Checked against the accepted parent's S0/S5(iii).
* **Totality.** TR3-S1's theorem quantifies over EVERY nonzero f ∈ O[x] with
  no degree bound (its S0; its scope note removes the bound from Lemma A) —
  the digit qualifies whatever its degree, and so does f = Φ₂ at S2(ii).
* **j₀ = s₀ at e₁ = 1.** TR3-S1's j₀ = ⌊s₀(A)/e₁⌋ = s₀(A) at e₁ = 1, and
  s₀(A) (TR3-S1 S5(i)'s initial on-line abscissa of the λ-component of
  N₂⁻(A)) is the same datum as GMN's s₂(A) (the note's Def 2.19 pin) — the
  identification of the two on-line notions and endpoints is TR3-S1 S5(i),
  consumed at its accepted state. The m₀-bookkeeping
  m₀ = (s₂(A) − s(β))/e₁ = s₂(A) at s(β) = 0 is forced.
* **Inner-operator identification.** Def 3.16 is level-generic: the inner
  operator inside the i = 3 display is R_{2,γ_j} — the SAME Def-3.16-at-i=2
  family TR3-S1's theorem reads, over the same truncated tower (same µ₂, same
  Φ₀/Φ₁ under TR-5's φ₃ ↔ Φ₂), in the same integer weights (all E_i = 1, so
  no RESCALE dilation mismatch), and at on-line slots the weight γ_j = w₂(A)
  is TR3-S1's own-weight read γ = w₂(f). Exact match; nothing hidden.

## 3. Lemma Z2 (S4) — VERIFIED (both corners + domain direction)

β < w₂(A) ⇒ every nonzero Φ₁-digit has w₁(a_m) ≥ w₂(A) − mγ₂ > β_m (min
defining w₂ at e₁ = 1); every Φ₀-digit then has w₀(b) > δ = β_m − m′h₀; the
reduction of b·π^{−δ} is 0 for all-positive valuations, INCLUDING δ < 0
(π^{−δ} multiplies up; w₀ ≥ 0 > δ) — TR3-S1 (A3)'s corner verbatim. Domain
direction correct: β < w₂(A) = µ₂(A) means A ∈ P_β(µ₂) = {µ₂ ≥ β}, INSIDE
Def 3.16's printed domain (the S9.3 attack point closes). A = 0 reads 0 by
the printed convention. The zero-digit and negative-slot-weight corners in
S5(ii)'s off-line case (γ_j < 0 impossible on-line since w₂ ≥ 0 on O[x])
check out.

## 4. t₂-absorption and the S5(ii) chain — VERIFIED

Def 2.19 at r = 3: t₂(i) = (s₂(A_i) − ℓ₂^{GMN}u_i)/e₂^{GMN}, with GMN level-2
data = project read-ν₁ data under the standing dictionary (the note's
"(ℓ₁, e₁)" in project indexing — declared, and consistent with TR3-S1's
r = 2 instance where GMN level-1 = project ν₀). At normalized ℓ₁ = 0 (KER)
and e₁ = 1: t₂(i) = s₂(A_i), verbatim, integrality trivial. The five-step
chain at an on-line slot re-derived line by line:
ǫ₂ ≡ 1 (KER) → (SQ₂) (σ₂ = quotient of σ₁[y] by (ψ₂^F) ↦ (ψ₁), so
σ₂(P(z₂)) = (σ₁[y]P)(z̄₂)) → Lemma A3 at β = γ_j = w₂(A) → t₂ = s₂(A) +
GMN's inner R₂ = R_λ₂ at the type-fixed λ₂ with Def 2.21 evaluation from the
actual initial abscissa (constant term c^G2_{s₂(A)}, so
z̄₂^{s₂(A)}·R_λ₂(A)(z̄₂) = z̄₂^{t₂(j)}·R₂(A)(z̄₂) exactly) → Def 2.20.
**Nonvanishing:** deg A < deg Φ₂ = g₁·deg Φ₁ confines the window to length
≤ g₁ − 1, so deg R_λ₂(A) < g₁ = deg ψ₁; {1, z̄₂, …, z̄₂^{g₁−1}} is a K₁-basis
of K₂; z̄₂ is a unit (ψ₁(0) ≠ 0). Nonzero at every on-line slot, support
equality follows. The degree bound is consumed exactly where the note says
(and nowhere else). **Assembly:** on-line terms ⊆ [s, s′] with GMN's window
zeros matching the off-line zeros; Σ = y^s·R_λ₃(f); Def 3.18's j₀ (defined
from FGMN's own polygon datum) = s by S5(i), and the observed first nonzero
slot IS j₀ because c^G3_s ≠ 0 — the division is lawful. S5(i)'s support
equivalence at stride 1 (u_i + ih₂ = w₂(A_i) + iγ₃ ≥ γ, equality = on-line
= FGMN slot equality w₂(A_j) = γ_j) re-derived; the only depth-3 novelty is
the (H-v3) ordinate, correctly flagged.

## 5. σ₂ construction (S2) — VERIFIED incl. the Cor 5.6(2) index discipline

ψ₂^F = R₂^F(Φ₂) via Cor 5.6(2) read CHAIN-INTERNALLY at index 2 < r = 3 —
only (H-CHAIN) at depth 3 consumed, NO (KP_i); this exactly mirrors the
accepted TR3-S1's reading of the same corollary at indices 0, 1 < r = 2,
with (KP_i) needed only at the state key (here Φ₃, S6.2 step 1 — displayed
and priced there). σ₀/σ₁ consumed from accepted TR3-S1 at the substate;
indices 0, 1 chain-internal a fortiori at r = 3. Step (ii) is the accepted
theorem at f = Φ₂ (total — no degree bound issue). Step (iii)'s monicity
upgrade re-derived: top Φ₁-digit a_{g₁} = 1 at w₁ = 0, on-line
(u + g₁h₁ = g₁γ₂ = w₂(Φ₂)); digit 1 has s₁(1) = 0, R₁(1) = 1, t₁ = 0, so
c^G2_{g₁} = 1; lawfulness (deg R_λ₂(Φ₂) = g₁) squeezes s₂(Φ₂) = 0 (final
on-line abscissa = g₁ since the development stops there); monic associate of
monic ψ₁ = ψ₁. (SQ₂) is the construction. The S6.2 Φ₃ tie is the same
argument one level up (top digit A_{g₂} = 1, ordinate g₂·w₂(Φ₂), on-line,
s₂(1) = 0, R₂(1) = 1, t₂ = 0, c^G3_{g₂} = 1, squeeze s₀(Φ₃) = 0) — checked;
(KP_i) consumed there and displayed; step 3's Cor 5.15 [T]-properness leg
NOT discharged, exactly as both parents — displayed.

## 6. (H-v3) conditionality — VERIFIED at every consumer site

The derivation sketch checks: Def 2.5 at r = 3 on the stratum gives
v₃(P) = e₂^{GMN}·H₂(S₂(P)) = 1·min_i(w₁(a_i) + i·w₁(Φ₁) + i·h₁)
= min_i(w₁(a_i) + iγ₂) = w₂(P) — IF H₂ is the λ₂-intercept datum in the
same normalization as the pinned r = 2 instance (which gave v₂ = w₁
verbatim, TR3-S1 S1). Keeping it a DISPLAYED HYPOTHESIS (the generic-r
H_{r−1} display was never re-extracted; extraction-corruption discipline) is
the honest call. (H-v3) enters the algebra at exactly one point — the S5(i)
ordinate u_i (which also carries the component; the ℓ₁u_i term of t₂ is dead
by KER) — so the "identity survives as project-facing, only the GMN label
rides (H-v3)" framing is correct, and I confirmed no other consumer of v₃
hides in the r = 3 instance of Defs 2.19–2.21 (inner R₂ is an order-2
object; Def 2.21 evaluation consumes no valuation). Conditionality display
audited at EVERY site: summary-table rows (TR-3′-GEN order-3; TR-3-ORD-X
with (H-v3)+(KP_i)+[T]; consumers row deferring to the exact displayed
forms); S6.1 heading + blockquote + GD3-FULL/OL-B clause; S6.2 conclusion +
consumer clause ((H-v3)+(KP_i)+[T]); S6.3 (inherited triple + the OTHER
OL-1(b) seams kept conditional everywhere); S7 bullet; S9.1. No consumer is
served unconditionally.

## 7. (PIN-GEN-i) — VERIFIED complete at all sites (grep-audited)

All THREE definitions (corrected 3.15 at level 2 / 3.16 at i = 3 / 3.18 at
i = 3) appear in: the S1 pin body (lines 118–119); the discharge recipe
(fresh `pdftotext -layout` at Defs 3.15/3.16/3.18, provenance-pinned PDF,
displayed as OWED not attempted — line 128); the scope sentence (consumed
shapes = ǫ ≡ 1 via KER + the displayed Def-3.16 AND Def-3.18 shapes — line
136, the REV4 fix, present and accurate: S5(iii)'s two-form division indeed
consumes the 3.18 shape); the S7 transcription-scope bullet (450–451); S9
item 6 (580). The pin's scope claim is right: it gates ATTRIBUTION to the
FGMN print, not the finite identity — on-stratum the algebra consumes only
ǫ ≡ 1 (any reading error surfaces in the falsifier P-meters, and the probe's
M1 did discriminate reading P at level 2, 1,641/1,641).

## 8. Fences, falsifier reconciliation, and reproductions — ALL VERIFIED

**Fences.** No e_j ≥ 2 stratum touched; the three stated failure points of
the transport (KER dies at first e_j ≥ 2; A3's citation needs substate
e₀ = 1; t₂-collapse needs ℓ₁ = 0) are each real, per my re-derivation.
(TWIST-3) stays sealed and unconsumed (named only as the next stratum's
conjecture, matching STRATA3 S3's preregistered shape θ₂ = ℓ₁g₁γ₂). Orders
≥ 4 honestly open ("the induction is NOT written"). D-ITER untouched (E₃ = 1
rank-1; probe V3 δ ≡ 0 control). Numerics-as-falsifiers discipline holds: no
proof step cites a numeric.

**Record reconciliation (all exact).**
* Seals: `b4a142b` (2026-08-03 01:40:14; note 497 lines with
  "RESULTS: [RUN PENDING AT SEAL" + sealed script) → `482150b` (01:41:48;
  adds run-1 log/JSON + the results block; run-1 numbers in the note match
  that commit's diff verbatim). Temporal order correct.
* Sealed script == run-1 script (empty diff b4a142b→482150b on
  tr3s3_check.py). Script diff b4a142b→HEAD == EXACTLY the REVISION 1
  ADDENDUM header + the level-1 eq-(12)/l0 leg inside `R2w_at` — the two
  declared legs, nothing else.
* Run-1 vs run-2 outputs: deviations ONLY at the four timing lines, the RI
  count (14,797 → 21,741) and TOTAL (23,869 → 30,813) — the declared
  perimeter; both deltas +6,944.
* TOTAL arithmetic: 2,241+816+21,741+1,141·3+768+816+144+24+816+24 = 30,813
  exactly; per-tower counts reconcile (Z2 = 24·8·4 = 768; W = 24·6 = 144;
  E2B/XV/O = 24·34 = 816; K/CERT = 24).
* Row O: violation branch UNREACHABLE (E2B early-returns unless
  side == glist, which forces fp_ord equality) — the REV2 correction is
  accurate; only its ord-histogram meters are live; E2B carries the
  transport's falsification. Confirmed in code.
* Meters all fire as recorded (m0pos 85, j0pos 173, noff 902, noisy 72,
  holes 64, wfail 0, ord hist 0:744 1:38 2:34).
* The two external legs on record: pass-3's independent implementation
  (93 samples/189 slot checks, REVISION 2 block) and pass-6's (p = 5,
  3 towers, 1,564 checks, REVISION 4 block) — both present.
* Harness semantics audited against the note's displays: `R2w_at`/`fresh_R3`
  implement Def 3.16 at i = 2/3 with (SLOT)/(SLOT-3) weights, honest
  off-line computation (vs the probe's `R3w` which hard-codes them — the
  note's Z2-was-an-assumption claim about the probe is accurate);
  `gmn3` hard-codes (H-v3) + normalized ℓ (declared: the family cannot
  falsify either — correct perimeter statement); RII's abscissa-matched
  comparison is exactly (A3)'s y^{s₂}-shift; RIV rebuilds from gmn2 only;
  K mirrors S6.2 step 1; W's prescriptions + sub-line noise test Z2 +
  linearity end-to-end as claimed.

**Live reproductions (this pass).**
1. Full harness re-run in an isolated /tmp copy: exit 0, output identical to
   `tr3s3_check_run2_output.txt` mod timings; regenerated JSON identical to
   the repo's `tr3s3_check_results.json`.
2. **Verifier-owned from-note implementation** (fresh code, own field
   models, both operators written from the note's S1 pins alone; σ₂ =
   identity of the shared concrete K₂ model, as the harness scopes):
   off-roster p = 7 and p = 11 (roster p ∈ {2,3}; pass 6 used p = 5), fresh
   h-vectors, three towers incl. BOTH degeneracy corners (g₀ = 1: K₁ = K₀;
   g₁ = 1: z₂ ∈ K₁): (TR3-S3-coeff) per-abscissa + support, (TR3-S3-form)
   as lists + j₀ law, Lemma Z2 at β = w₂(A) − k, and the K label tie
   (both side reads of Φ₃ = ψ₂) — **701 checks, 0 failures**; plus a
   dedicated s₂(A) > 0 battery (Φ₁^a·h digits, 19 shifted on-line slots)
   checking the per-slot chain σ₂(C^F3_j) = z₂^{s₂(A)}·R₂(A)(z̄₂) = c^G3_j
   directly — **120 checks, 0 failures**. Total 821/0, recorded here as a
   third external leg (falsifier evidence only, per the discipline).

## 9. Non-classifiable observations (no fix required; recorded for the ledger)

1. **M1/CERT3 compression (S1 transcription-scope display).** "1,641/1,641
   reading-P refutations on PARI-certified order-3 towers" compresses two
   probe rows: the refutations span all 22 P-visible towers (incl. the
   F_p[[t]] rows, which have NO PARI analogue — the probe's honest
   deferral), while CERT3 certifies the 12 ℤ_p instances. STRATA3's own
   headline has the same structure with the 12/12 parenthetical; TR3S3's S7
   gives the exact scope ("M1/CERT3, 24 towers, p ∈ {2,3}"). Operationally
   inert: the leg feeds only (PIN-GEN-i), itself displayed OPEN with the
   owed print leg.
2. **Summary-table consumer row** names (H-v3) alone and defers to "(exact
   forms displayed)"; the ord-riding consumers' exact forms (S6.2/S6.3) add
   (KP_i)+[T]. The consumer sites themselves display the full triple, so no
   misstatement — table-granularity style only.
3. **`tr3s3_check_results.json` mtime (03:09) postdates the run-2 output
   (02:03)** — consistent with a later pass's in-place live rerun; I
   verified the file is byte-identical to what the deterministic script
   produces (my /tmp reproduction), so the record is intact.

## 10. Verdict

**CLEAN — 0 critical, 0 justification gaps.** The finite identity (TR3-S3),
its σ₂ construction, the four route lemmas, the S6 consumer services with
their displayed conditionality ((H-v3); (H-v3)+(KP_i)+[T] on the ord chain),
the scope fences, and the falsifier record are all verified at REVISION 4.
This is a second consecutive clean on the revision that pass 7 (different
model) cleared — the model-diverse 2-clean acceptance bar is met from this
verifier's side; the counter update is the orchestrator's.

— pass 8 verifier (Fable, fresh context), 2026-08-08 campaign date.
