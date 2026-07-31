# O9 Phase-B rev 3 — hostile verification PASS 3 (fresh context, 2026-07-31)

**Charge.** Verify `O9_phaseB_verifybrief_rev3.md` standalone (no prior reports
read): (1) the corrected (ADM) definition and its LED(iii) derivation; (2) the
rescoped automaticity (r = 0 automatic, r = 1 inequality, general withdrawn);
(3) the K6 claims as displayed; (4) the CEN-J scope clause; (5) the standard
census-layer audit. Quote-and-classify; fix nothing.

**Method.** Full read of the rev-3 brief; independent hand re-derivation of
LED(iii)'s increment argument, the (ADM) equivalence, the r = 0/r = 1
automaticity arguments, and every displayed K6 number (E′, s(β), censuses,
thresholds); source audit of `o9_rev3_adm_check.py` against its §10
description; byte-comparison of all three §10 logs against the brief's
headline numbers; one fresh machine-checked brute-force countermodel (script
inline below).

**VERDICT: UNSOUND — 1 critical error, 0 independent justification gaps.**

The four named repairs are each internally correct **as displayed** and the
census layer is clean; but the repair is INSUFFICIENT. The corrected (ADM)
(mere value-attainment, G_{β_k} ≠ 0) still does not deliver what §5.1/§6.3
consume (fiber-uniformity onto all of F_{r+1}, which forces dim G_{β_k} = d).
At an on-line slot with **partial** attainment (0 < dim G_{β_k} < d) — which
(ADM) admits — CEN-W's display is refuted by a brute-force countermodel built
from the note's OWN LED-top(ii) counterexample type. Details as Finding 1.

---

## 1. FINDING 1 — CRITICAL: partial value-attainment breaks CEN-W/CEN-J; the corrected (ADM) is still too weak for its consumers

**Offending passages.**

> §2 (ADM): "Say D is *ledger-admissible* if every on-line lattice slot's β_k
> is VALUE-attained by the slot ledger: (ADM) for every on-line lattice slot
> k: G_{β_k} ≠ 0 — equivalently ∃ ledger index 𝐣 : wt(𝐣) ≡ β_k (mod e) AND
> wt(𝐣) ≤ β_k."

> §5.1: "**Surjective onto F_{r+1}** for attained β: (GR-B)(2′)'s slot clause
> (the per-slot digit read is a BIJECTION of F_{r+1})" and "for EVERY
> z ∈ F_{r+1} (zero included): #{a ∈ W_N : r_β(a) = z} = q^{mN − s(β) − d}."

> §6.3: "each on-line lattice slot contributes, per prescribed digit
> z ∈ F_{r+1}, exactly q^{mN − s(β_k) − d} (§5.1 fiber uniformity —
> z-independent; the surjectivity behind it needs β_k attained, which is
> (ADM) + (GR-B))."

> §0 headline: "the order-r census is REDUCED to exactly two named open
> inputs — (GR-B) ... and (FRESH) ... — plus the per-datum lattice hypothesis
> (ADM) (value-attainment of every on-line β_k ...)."

**The defect.** The note's own proved lemmas force the per-digit count to be
inconsistent with (ADM)-as-defined. The read r_β is additive and factors
through G_β (LED(i)), so its z = 0 fiber is exactly {w > β}, of size
q^{mN − s(β+1)} (LED(ii), proved unconditionally). Fiber-uniformity at the
displayed value q^{mN − s(β) − d} therefore REQUIRES

    s(β_k + 1) − s(β_k) = dim_{F_q} G_{β_k} = d,          (FULL attainment)

whereas (ADM) certifies only dim G_{β_k} ≥ 1 (LED(iii): dim G_β =
#{𝐣 : wt(𝐣) ≡ β (mod e), wt(𝐣) ≤ β}, which ranges over 0..d). At a
PARTIALLY attained slot (0 < dim < d) the read's image is a proper
F_q-subspace of F_{r+1} — the identical phenomenon the rev-3 LED-top(ii)
repair records for the sub-ledger ("in general a PROPER subspace, so NOT onto
F_{r+1}") — and no reading of (GR-B) can rescue the count, because LED(ii) is
proved: either §5.1's bijection gloss overstates GD23's (GR-B), or (GR-B) at
order ≥ 2 is refuted by TRI+LED at these weights. Both horns are fatal to the
displayed reduction on (ADM)-admissible data containing such a slot.

**Concrete countermodel (machine-checked this pass).** The note's own
LED-top(ii) counterexample type, used at the FULL ledger: r = 1, f₀ = 1,
e₁ = 1, f₁ = 2, h₁ = 2 — m = 2, d = 2, e = 1, ledger {1, φ₁} with weights
{0, 2} (w(φ₁) = e₁V₁ + h₁ = 2, V₁ = 0 per (P3)), V̂ = e₁f₁·w(φ₁) = 4.
Datum D: single face (0,6)→(1,5) (slope −1, e_S = 1, d(S) = 1, λ = {(1,1)}),
free box, ℓ = 1, N = 7 ((DET): max(6, 1) ≤ eN − 1 = 6 ✓; reads β_k ≤ 6 ✓).

* β₀ = 6: dim G_6 = #{wt ≤ 6} = 2 = d (FULL). β₁ = 5 − V̂ = 1:
  dim G_1 = #{wt ≤ 1} = 1 < d = 2 (PARTIAL — wt = 2 misses; this is exactly
  the note's recorded V_1 = F_q·in(π) line).
* **(ADM) HOLDS** (e = 1: both β_k ≥ 0 are value-attained; G_1 ≠ 0). The
  datum is inside CEN-W's asserted scope.
* Membership is purely valuation-level (d(S) = 1 vertices force type
  {(1,1)}, exactly as K6's CH4 argues for its own cells): stratum =
  {w(a₀) = 6} × {w(a₁) = 1}.
* s(6) = 10, s(7) = 12, s(1) = 1, s(2) = 2 (weights {0,2}, e = 1).
  **Truth** = (q⁴ − q²)(q^{13} − q^{12}) = q^{14}(q² − 1)(q − 1).
  **CEN-W display** = q^{E′}(q^d − 1)·M_{{(1,1)}}(q²) with
  E′ = (14−10) + (14−1) − 2·2 = 13: q^{13}(q² − 1)².
  Ratio display/truth = (q+1)/q ≠ 1. At q = 2: **display 73728 vs truth
  49152**. Brute force over (ℤ/2⁷)² per slot (w = min(v(c₀), v(c₁)+2), the
  same one-step (P1)/(P2)/(P3) instance K6 uses) confirms: #{w=6} = 12,
  #{w=1} = 4096, truth 49152. The discrepancy localizes exactly at the
  partial slot (slot 0's contribution q²(q²−1) = 12 matches the display;
  slot 1's true q^{12}(q−1) ≠ displayed q^{11}(q²−1)).

Verification script (run 2026-07-31, this pass):

```python
p, N = 2, 7
def v(x, cap=N):
    if x % p**N == 0: return N
    k = 0
    while x % p == 0: x //= p; k += 1
    return k
def w(c0, c1): return min(v(c0), v(c1) + 2)   # (P2)+(P1), w(phi1)=2, e=1
cnt = {}
for c0 in range(p**N):
    for c1 in range(p**N):
        cnt[w(c0, c1)] = cnt.get(w(c0, c1), 0) + 1
truth = cnt[6] * cnt[1]                        # 12 * 4096 = 49152
display = 2**13 * (4 - 1) * (4 - 1)            # q^13 (q^2-1)^2 = 73728
```

**Why every falsifier missed it.** All VALUE gates run at d = 1 (K5: r = 0
with f₀ = 1; K6: both cells d = 1 by construction), where G_β ≠ 0 ⟺
dim G_β = 1 = d — nonvanishing and FULL attainment coincide, so the corrected
(ADM) is exactly right there and everything passes. The FORM checks (K1–K4)
fit exponent vectors in atoms {p, p^g−1, p−1}; a partial-attainment factor
(q^{dim} − 1) at dim = 1 IS the allowed atom (p − 1), so even a g = 2 hit
could fit. §10's d ≥ 2 coverage disclosure is honest but the brief nowhere
identifies partial attainment as the uncovered failure mode — (ADM)'s interior
bullet handles only dim = 0.

**Blast radius (downstream verified assuming a repaired hypothesis).**
Infected as displayed: Theorem CEN-W (both boxes), Theorem CEN-J (step 3's
per-digit q^{−d} and the (FRESH)(b) unit-slope consumption), §7's OL-D remark,
§8's countS/countT, the §0 OL-C/OL-D rows, the §0 headline, and the closing
verdict paragraph — all at r ≥ 1 data containing a partially attained on-line
slot. NOT infected: the r = 0 layer (at r = 0, dim G_β = f₀ = d for every
β ≥ 0, so full attainment is automatic on nonnegative data — the M08
recovery, the (E″) validation, and all of K5 stand); the unconditional
lemmas A1/TRI/LED/LED-top; TYPE-MARCH; (DET); §5.3; the K6 dichotomy itself.
The evident repair — strengthen (ADM) to FULL attainment
s(β_k+1) − s(β_k) = d per on-line slot, still a p-free decidable lattice
check, with the r = 1 inequality replaced by its full-attainment analogue —
is noted, not applied (verifier fixes nothing). Under such a repair the
consumption question of the note's own attack item 4 would read: full
attainment + (GR-B)(2′) is what §5.1 needs; mere value-attainment is NOT.

---

## 2. The four charged items, as displayed (all verified correct in isolation)

**(1) Corrected (ADM) + LED(iii) derivation — VERIFIED.** The per-𝐣 increment
argument is exact: max(0, ⌈(β+1−wt)/e⌉) − max(0, ⌈(β−wt)/e⌉) = 1 iff
β ≡ wt (mod e) and β ≥ wt (checked at the boundary wt = β and below), so
dim G_β = s(β+1) − s(β) = #{𝐣 : wt ≡ β (mod e), wt ≤ β}, and G_{β_k} ≠ 0 is
exactly the displayed ∃𝐣-criterion. The TRI attained-set bullet ({e·v + wt})
is exact. The §2 warning-display arithmetic all re-derives: weights {0,2,4},
V̂ = 6, β = (8,1), s(2) = s(1) = 1, mod-e display E′ = 8 hence q⁸(q−1)² =
256/26244 — all confirmed by hand. The vertex-emptiness and interior-bullet
statements are correct. The defect is not in the definition or its
derivation but in the MATCH to the consumers (Finding 1).

**(2) Automaticity rescope — VERIFIED as stated.** r = 0: all weights 0,
e = 1, value-attained ⟺ β ≥ 0; automatic on nonnegative on-line data;
M08/K5 data qualify; the negative-height edge case correctly yields 0 = 0.
(Even the stronger full-attainment repair stays automatic at r = 0: dim =
f₀ = d.) r = 1: the displayed inequality β ≥ h₁·((h₁^{−1}β) mod e₁) is a
correct characterization of value-attainment against the weight set
{j₁h₁ : 0 ≤ j₁ < e₁f₁} (minimal class witness j₁* = (h₁^{−1}β) mod e₁ < e₁
≤ e₁f₁ always in range; the j₀-part contributes only weight 0 = j₁ = 0's
weight, so the set is unchanged) — re-derived by hand, countermodel
threshold 2·((2⁻¹·1) mod 3) = 4 > 1 confirmed. General withdrawal honest.
CAVEAT from Finding 1: the inequality decides the now-insufficient
predicate; it is the right answer to the wrong hypothesis.

**(3) K6 as displayed — VERIFIED.** `o9_rev3_adm_check.py` (8,778 bytes,
mtime Jul 31 19:48) matches its §10 description clause by clause: w is the
one-step pinned-recursion formula min_j(e₁·v_π(c_j) + j·w(φ₁)) (at m = 3,
r = 1 this IS the single (P2)+(P1) application, as disclosed); CH1/CH2/CH2b
(attained set, LED(ii) counts, measured dim G_β vs the corrected criterion at
every β ≤ 8, G_1 = 0); CH3/CH3b (countermodel census 0 by slot product AND
the naive 2^18-pair loop at p = 2; rev-3 padding prediction 0 = 0; mod-e
display 256/26244 refuted); CH4/CH4b (positive control 16/324 = p⁴(p−1)²,
E′ = 4 re-derived by hand: s(8) = 8, s(4) = 4); CH5 at exactly the four
triples (3,2,1),(3,1,1),(4,3,2),(5,2,1) for β ≤ 30; CH5b. The log
(`o9_rev3_adm_20260731_194858.log`) shows ALL PASS with every number the
brief quotes. Two honesty notes, neither a finding: (a) the "naive loop"
shares the w-formula with the formula side — it independently checks only
the slot-product factorization, not w itself (the brief's wording claims no
more); (b) both K6 cells sit at d = 1 and are structurally blind to
Finding 1, as is every current VALUE gate.

**(4) CEN-J scope clause — VERIFIED.** The clause ("asserted when g_k ≤ β_k
at every on-line slot k ∈ K_D") is well-posed; the vertex-slot emptiness
argument is airtight (a vertex needs w(a_k) = β_k, barred by the floor
g_k > β_k), the §8 padding convention is now explicitly imported so the
"= 0" parse closes, and the interior-slot g_k > β_k variant is honestly NOT
displayed, matching (ADM)'s interior bullet. Off-line slots need no scope
restriction (a floor above a STRICT threshold makes the slot automatic and
the max(0,·) charge 0 — consistent). L′ bookkeeping at monic top consistent.
CEN-J inherits Finding 1 through step 3, not through this clause.

## 3. Census-layer audit — CLEAN

* Logs exist and match: `o9_census_20260731_165908.log` — 10 configurations;
  boxes sum 8,220,994; order-2 instances sum 1,128,288; K1 strata sum 100;
  18 cross-p cells with exactly one g = 2; 0 violations everywhere; run date
  2026-07-31 matches the brief's corrected bookkeeping.
  `o9_rev2_ledger_predict_20260731_175221.log` — 7 data / 11 (D,λ) cells all
  PASS; countermodel 64/64 with E′ = 6 (re-derived by hand this pass);
  rev-0 refutations exactly 256; 128×4; 16×2; 324 vs truths 64×5; 8×2; 108;
  M08 regression Σ(N−c_i) = 3 = E′_monic. `o9_rev3_adm_...log` — item (3)
  above.
* Source-line cite verified: `o9_order2_census_check.py` lines 121–124 are
  the `parent_data` k₀ = 0 drop (`if vs[0] >= M: return None`), as §6.4
  claims.
* K5's membership layer is an independent reimplementation (own F_p[y]
  factorization and strict keying), as claimed.
* §10's coverage-honesty paragraphs (single-face K5 scope, d = 1/K6 limits,
  ε = 0 forced by shape, p ∈ {2,3} underdetermination at 9 cells) are
  accurate — but see Finding 1's "why every falsifier missed it".

## 4. Verdict

**UNSOUND.** One critical error: the corrected (ADM) (value-attainment,
G_{β_k} ≠ 0) is strictly weaker than what §5.1/§6.3/§6.4 consume (FULL
attainment, dim G_{β_k} = d); at partially attained on-line slots — admitted
by (ADM), realized by the note's own LED-top(ii) counterexample type —
CEN-W's display is off by (q+1)/q per such slot (machine-checked: 73728 vs
49152 at q = 2), and the (GR-B) gloss "bijection of F_{r+1} at every attained
β" is refuted by the note's own proved LED(ii)/(iii) at order ≥ 2. The
pass-2 repair fixed the dim = 0 failure (class vs value) but not the
0 < dim < d failure (value vs FULL) — the same family, one rung deeper. The
r = 0 layer, the unconditional lemma stock, TYPE-MARCH, the K6 dichotomy,
the CEN-J scope clause, and the entire census-layer record are sound as
scoped; the headline reduction is not, until (ADM) is restated at full
attainment and the r = 1 decidable check re-derived for it.

— Pass-3 verifier (fresh context), 2026-07-31.
