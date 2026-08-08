# SIGMALAW passPE1 — hostile verification report

**Target:** `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` at HEAD (seal
8064ae3, verdict 59c1ff2; §8 annex applied to GRTW2 at a9f45ab). **Charge:**
fresh-context hostile pass; quote-and-classify; fix nothing; the two
self-flagged §7 pressure points first; machine re-run + fresh route.
**Verifier artifacts (not committed):** `/tmp/slverify/fresh_check.py`
(own χ/ξ/Σ/σ′/u_j/δ implementations written from the note's displays; own
walker; own separator constructions; two fresh genres), outputs
`fresh_oa_sep.txt`, `fresh_f5dbl.txt`, `fresh_results{,2}.json`.

## VERDICT: NOT CLEAN — 0 CRITICAL + 1 GAP + 2 minor

**Every theorem statement survives** — SL-L1, SL-1 (VD-q/Σ-LEDGER, u_j
closed form), SL-L2 (Λ_q = χ_q^{−w}), SL-C1 (δ = ρ/Σ(ρ)), SL-C2
(OPEN-2a-Σ), the §5 separator refutations of both bare-θ variants, and the
§5/§6R involution-degeneracy explanation were all re-derived and/or
independently machine-reproduced, including on an adversarial regime the
sealed battery never samples. The GAP is at exactly the place §7
self-flagged: the (SC-q) REMARK's displayed wrap-invariance input is
**false as stated on part of the claimed scope** (constructed
counter-instances below); the correct input is a stronger eigen-coefficient
law, derivable on-perimeter (derivation displayed below, machine-confirmed
7/7) — so the proof is repairable without touching any theorem statement,
but as written it does not cover the doubly-twisted regime, and neither
does the sealed battery.

---

## FINDING 1 (GAP; the two self-flagged points, one root cause):
## the (SC-q) wrap input "ξ_q^{g_{q−1}−i} = 1 on supp(ψ_{q−1})" is FALSE on part of the shared-below perimeter; the true input is an eigen-coefficient law

**Quoted claim (§3 REMARK):** "the wrap terms (E + ν ≥ g_{q−1}) consume
ξ_q-invariance of the relation: … i.e. **ξ_q^{g_{q−1}−i} = 1 on
supp(ψ_{q−1})** — EXACTLY the byte-share law of the junction below (GRTW2
§3.4 rk. 3 at level q−1, which the shared-below premise supplies at every
interior level) … So (SC-q) holds ON THE SHARED-BELOW PERIMETER."

**Re-derivation of the wrap terms.** Write g = g_{q−1}. For (SC-q) at
E = 1 (general E follows by iteration/bijectivity), the wrapped slot
comparison is, per supported i,

    Σ_{q−1}(y·ψ_{q−1,i}) · ξ_q^{i}  =  Σ_{q−1}(y) · ψ_{q−1,i} · ξ_q^{g}
        for ARBITRARY y ∈ K_{q−1},

equivalently (take y = 1, Σ fixes 1): **Σ_{q−1}(ψ_{q−1,i}) =
ξ_q^{g−i}·ψ_{q−1,i}** plus Σ_{q−1}-multiplicativity against ψ_{q−1,i}.
The note's displayed condition ξ_q^{g−i} = 1 is this ONLY in the special
case Σ_{q−1}(ψ_{q−1,i}) = ψ_{q−1,i} — i.e. when the composite below fixes
the interior modulus coefficients (in particular whenever Σ_{q−1} = id).
The note nowhere states or discharges the fixedness condition. The same
condition is what SL-C1's multiplicativity step really needs: Σ_m must be
a ring automorphism of K_m (the step uses Σ_m(ρ·ψ_j) = Σ_m(ρ)Σ_m(ψ_j)
with ρ an ARBITRARY unit — the "(SC)-type covariance … ε-monomial-times-
class" hedge is not sufficient as stated), and Σ_q is an automorphism iff
the ideal (ψ_{q−1}) is preserved, i.e. iff Σ_{q−1}(ψ_{q−1,i})·ξ_q^{i−g} =
ψ_{q−1,i} — the SAME combined condition. (OA-M1 never met this because σ′
is coefficientwise-trivial below; the composite Σ_m at m ≥ 3 is not.)

**Counter-instance to the displayed input (constructed; the
doubly-twisted regime).** Chamber ℤ₃, reads (2,1,2)+(3,1,4), ψ₀ = y²+y+2
(z₁ primitive, ord 8), ψ₁ = y⁴+z₁^k (k odd): A₁ = 2, ξ₂ = z₁^{−6} = z₁²
of ORDER 4, invisible on supp ψ₁ = {0,4} (m = 1 junction byte-equal).
Third read (1,1,2) with ψ₂ = y² + c·z₂ (c ∈ K₁*): the coefficient c·z₂ is
NOT Σ₂-fixed (Σ₂(cz₂) = ξ₂·cz₂ = z₁²·cz₂), and ξ₃ = χ₂^{γ₃}z₂^{−e₂A₂} =
z₁^{6−5k mod 8} has ξ₃^{g₂−0} = ξ₃² = z₁^{±2} ≠ 1 on the supported slot.
Deg-1 non-monomial top (1,1,1)/ψ₃ = y+(1+z₃) walks the m = 3 junction.
Machine (own code): **8 such towers built; 7 have byte-equal m = 2
junctions, hence SHARED-BELOW walked m = 3 rows, on which the note's
displayed input ξ₃^{g₂−j} = 1 is FALSE, Σ₂ does NOT fix ψ₂'s
coefficients, and ξ₂ ≠ 1** (`fresh_f5dbl.txt` eigen table: 7 × (sharedM3
True, remark-input False, Σ₂-fixes-ψ₂ False, ξ₂-trivial False)). So the
asserted implication "shared-below ⟹ ξ_q-invisibility at every interior
level" is refuted; GRTW2 §3.4 rk. 3's proved display is the m = 1 form
only, and the note over-extends it.

**The theorem SURVIVES there — and the correct input is derivable.** On
all 7 rows the ledger identity AND the δ-law hold with 0 violations (and
each row is a separator: both bare-θ variants fail). The repair, derived
by this pass and machine-confirmed: on the shared-below perimeter, at
every interior junction (level q, byte-equal), (VD-(q−1)) + (SC-(q−1)) +
Thm-`phir` + REALIZE R3 give c·ψ_{q−1,j} = u_j·Σ_{q−1}(ε^{−1}ψ_{q−1,j}),
i.e. Σ_{q−1}(ψ_{q−1,j}) = λ_j·ψ_{q−1,j} with λ_j =
c·z_{q−1}^{k_jA_{q−1}}·U_{q−1}(β_j)^{−1}·ξ_{q−1}^{E(β_j)}; SL-L2 at q−1
(U^{−1}ξ^{E} = χ_{q−1}^{β_j}) and c = z_{q−1}^{−A_{q−1}e_{q−1}g_{q−1}}
collapse this to the **EIGEN-COEFFICIENT LAW**

    Σ_{q−1}(ψ_{q−1,j}) = ξ_q^{g_{q−1}−j} · ψ_{q−1,j}   (j ∈ supp),

exactly the wrap/ideal-preservation condition needed — identically, with
no invisibility assumption. Machine: holds 7/7 on the constructed regime
(where it is non-trivially eigen, not fixed); its eigen-MISMATCH control
(k=3, i=1) builds but FAILS m = 2 byte-equality, 1/1 as predicted. The
note's displayed condition is the Σ_{q−1} = id special case (and then rk. 3
is recovered: λ_j = 1 ⟺ θ^{g−j} = 1 at m = 1). With the eigen-law carried
as an induction clause, Σ_q is an automorphism (ψ_{q−1} ↦ ξ_q^{g}·ψ_{q−1}),
(SC-q)'s wrap terms close, and SL-C1's multiplicativity is sound.

**Scope of the hole in the sealed evidence.** Own scan of every walked
m = 3 row of the full sealed battery (145 rows): census (ξ₂-trivial, g₂,
ψ₂-Σ₂-fixed) = {(True, 2, True): 123, (False, 1, False): 22 — the B3D
genre, whose g₂ = 1 relation is degenerate (Σ₃ = Σ₂, no wrap)}. **Zero
sealed rows have ξ₂ ≠ 1 with g₂ ≥ 2** — the regime where the REMARK's
input fails is exactly the regime the battery never samples; my 7 rows
are its first instances (law green there too).

**Classification: justification gap** (not critical): a false intermediate
claim in the (SC-q) REMARK and an insufficient hedge in SL-C1, with the
conclusion true on all evidence including the adversarial regime, and a
complete on-note repair (the eigen-coefficient law above) that changes no
theorem statement. It infects: (VD-q) for q ≥ 3, SL-L2's Σ_q(z_q^E) step
at general E, and SL-C1 at m ≥ 2 — all repaired by the same clause.
SL-C2 itself is untouched (its own inference needs only bijection-fixing-1,
as the note correctly says).

## FINDING 2 (minor; bookkeeping): §6R family-sample counts and the
## INVREC "221" include teeth-run leakage; genuine battery figures are
## 2,828 / 1,414 / 1,414 / 680 / 218

`run_tooth` restores `VIOL` and pops `ROWS` but never restores `COUNTS`,
so the six mutation runs leak `note()` samples into the family tallies.
Measured leak (teeth re-run in isolation): SL-VDM +26, SL-DELTA +13,
SL-PHIR +13, SL-GAP +8, **SL-INVREC-ROW +3**. Cross-check: Σ|supp| over
all 1,211 walked rows of the committed JSON = 1,414 (OA 1,060 + SEP 354),
and 1,427 − 1,414 = 13, 2,854 − 2×1,414 = 26, 688 − 2×340 = 8 — exact.
Consequences for the §6R display: "(2,854 — both legs, every walked slot,
every m)" overstates the battery coverage by 26 (the true both-legs-every-
walked-slot figure is 2,828); and "SL-INVREC = 221 δ ≠ 1 slot-samples …
of which 218 on the OA-battery geography" — the 3 non-OA samples are NOT
battery rows but artifacts of the TEETH-PR mutation runs (garbled-print δ
on T2C/T3C under `mut_print`), so the genuine census is **218 = exactly
the OA δ ≠ 1 record**, which makes the reconciliation claim STRONGER, not
weaker. No verdict is affected (teeth violations are correctly diverted;
0-violation families are 0 on the genuine samples a fortiori; the 340-gap-
slot and 96/27 separator censuses come from `ROWS`, which IS cleaned, and
are exact). The annex applied to GRTW2 at a9f45ab carries the same
2,854/1,427/688 figures with the same caveat.

## FINDING 3 (minor; display typo): §1's Bézout parenthetical

"ℓ_{m−1}(u_j − β_j)/e_{m−1} = k_j·ℓ_{m−1}g_mγ_{m+1}... = k_jA_m" — the
intermediate should read k_j·ℓ_{m−1}g_{m−1}γ_m (u_j − β_j = k_j·w_mΦ_m =
k_j·e_{m−1}g_{m−1}γ_m); the displayed g_mγ_{m+1} is an index slip. The
final k_jA_m and every downstream use are correct and machine-keyed.

---

## CONFIRMED (all re-derived in full by this pass)

* **SL-L1 / per-node gap cancellation (self-charge 1).** Engine semantics
  verified against code: `GmnLeg.rres` packs from the ATTAINED start s0
  with slot (i−s0)/e and per-digit coefficient z^{t}·R_{q−1}(a_i), t =
  (s_{q−1}(a_i) − ℓ_{q−1}u_i)/e_{q−1} (Def-t(i) faithful); `Tower.read`
  packs ε-corrected exact-weight digits from the eq12 GRID start; ε-exp
  = ℓ′s − ℓu = (s − ℓβ)/e ✓. The τ-normalization τ_q = (s₀−ℓβ)/e =
  (s−ℓβ)/e + ν₀ cancels z^{ν₀} against the attained-start packing exactly
  as displayed; each node's gap cancels inside its OWN evaluator; no
  cross-builder coincidence used anywhere ✓. Attained set = exact-weight
  set via the P-index functional tie (e(v_q + a·v_qφ) + ah = ew + aγ) ✓.
  q = 1 base = W2-L3 verbatim (order-one rescoeff twist-free in code) ✓.
* **(VD-q) at m = 2 and m = 3; u_j's three factors.** m = 2: the (MATCH)
  equation closes with NO wrap input at all (Σ₁ = id, Λ₁ = 1): U₂(β) =
  z₁^{−s(β)A₁} and ξ₂ = z₁^{−e₁A₁} = θ₂^{−1} are FORCED — re-derived ✓.
  m = 3: the ν-part of (MATCH) is [z₂^{−e₂A₂}·ξ₃^{−1}·χ₂^{γ₃}]^ν = 1
  precisely by ξ₃'s §3.4 definition; a bare-θ map leaves the residue
  χ₂^{γ₃ν} — live exactly when χ₂ ≠ 1 and γ₃ odd (SEP-B hand-check:
  ℓ₀ = g₀ = γ₁ = 1 ⟹ A₁ = 1, χ₂ = z₁^{ℓ₁A₁} = −1, γ₂ = 5, w₂Φ₂ = 20,
  γ₃ = 41 odd, A₂ = 10, θ₃ = z₂^{20} = 1 in F₉ — the runner's map is the
  identity on the letter while Σ₃ twists by −1) ✓ matches §5. u_j =
  z_m^{−k_jA_m}·ε_m(β_j)·U_m(β_j): factor 1 from t_j = τ_m − k_jA_m
  (ℓ_{m−1}w_mΦ_m/e_{m−1} = A_m, W2-L2 Bézout), factor 2 from the
  attained-start ε-exponent (W2-L2 𝔰 = s, k = 0), factor 3 from (U-REC)
  = the collected χ-chain — all three re-derived from the cited GRTW2
  §3.4 objects ✓.
* **SL-L2 is a genuine re-derivation, not circular (charge 2).** Both
  exponent computations re-done independently: z-part −s A' + A'(s−ℓw) =
  −A'ℓw; χ-part −(w−sγ_q)/e − γ_q(s−ℓw)/e = w(ℓγ_q−1)/e =
  w(ℓw_{q−1}Φ_{q−1} − ℓ′) via ℓh−1 = −ℓ′e — landing on the §3.4
  χ-recursion as an OUTPUT. The proof chain consumes χ_q/ξ_q/U_q as
  DEFINITIONS + Bézout + grid identities only; the (ξ,w) closed-form
  THEOREM (GRTW2 §3.4 display / CK-XI) is consumed NOWHERE in §§2–4 —
  checked line-by-line ✓. (Its Σ_q(z^E) step at general E rides the
  Finding-1 wrap input; same repair.)
* **Separator refutation (charge 3), own construction.** 12 m = 2 rows of
  the SEP-A genre built with MY OWN specs (k = 5/(3,1) and k = 3/(1,1);
  tops 2+z₂, z₁²+z₂, 1+z₂+z₂², reads (1,1,1)/(2,1,1) — disjoint from the
  runner's candidate list) and 4 m = 3 rows of the SEP-B genre (different
  nonsquares nsq[3:5], read3 (1,1,1)/(3,1,1), tops 2+z₃, 1+2z₃), all
  evaluated with MY OWN Σ/σ′/u_j/δ code: on ALL 16 rows δ ≠ 1, the ξ-law
  δ = ρ/Σ_m(ρ) HOLDS, **both** bare-θ variants ρ^{1∓σ′} FAIL, and δ is a
  non-involution (m = 2: ord(δ) > 64; m = 3: ord(δ) = 5) — which also
  pins the ξ-SIGN (δ² ≠ 1 separates ρ/Σ(ρ) from Σ(ρ)/ρ, and the law holds
  with the note's sign) ✓. SEP-A geometry hand-checked (A₁ = 2, ξ₂ =
  z₁^{−2e₁} of order 4, invisible on supp {0,4}; ψ₀ = y²+y+2 primitivity
  verified by hand: x⁴ = 2) ✓. Gap slots (1–4 per row) present on most
  rows — the law holds on gap rows with no correction, own code ✓.
* **THEOREM OPEN-2a-Σ firing (charge 4).** Proof re-checked: strict ⟹
  δ = ρ (OA-L3) ⟹ Σ_m(ρ) = 1 (SL-C1, ρ a unit) ⟹ ρ = 1 (Σ_m injective +
  fixes 1 — definitional, coordinatewise nonzero characters; OA-M1
  genuinely NOT consumed here) ⟹ byte-equal (OA-L4); recorded ξ = 1 ⟹
  strict per OA-L3's proof. Hidden-fifth hunt: Thm-`phir` enters via
  OA-L2/δ's definition — declared content of OPEN2ATTACK §1 ✓; REALIZE
  R1–R3, (HR-REC), W2-L0 enter via OA-L4 as recorded ✓; the ONLY
  consumption beyond the declared list is the Finding-1 wrap machinery
  inside SL-C1 — no other hidden input found ✓.
* **Involution-degeneracy explanation (charge 5).** Independent walk of
  the reproduced OA battery (own δ/Σ/σ′): δ ≠ 1 slot-samples = **218
  total; 218/218 with Σ_m(ρ) = σ′(ρ); 218/218 involutions (δ² = 1)** —
  the sealed unit's ENTIRE δ ≠ 1 record does sit where the maps coincide,
  as §5/§6R claim (and per Finding 2 the honest census is exactly 218,
  not 221). Row-level tie to the committed OPEN2ATTACK JSON: δ ≠ 1 on
  141 m = 2 + 38 m = 3 rows (B1 115, B1F 26, B3B 25, B3D 13) — matches
  OPEN2ATTACK §4 item 3 verbatim ✓.
* **Consumption/grade honesty.** §3's consumption list and §7's box
  accounting verified against GRTW2/OPEN2ATTACK; the converse and
  above-r₀ scopes correctly left untouched; annex §8 applied to GRTW2 at
  a9f45ab verbatim except the note-designated verdict-hash blank
  (diff-checked) ✓.

## MACHINE LEG

Runner `verification/openmath/sigmalaw_checks.py` at HEAD md5
92e7c22cb2c823909dc5ad6b03f61c32 = seal 8064ae3 byte-identical; committed
artifacts byte-identical to verdict 59c1ff2. **Fresh full re-run
(sandbox): exit 0, 18.8 s, 6,970 samples — output byte-identical
ex-timing, JSON identical ex-elapsed.** 539 towers (389 OA + 96 SEPA + 54
SEPB, 0 rejects), 1,217 rows = 1,211 walked (539/527/145) + 6 SKIP;
SL-VDM 0/2,854 · SL-DELTA 0/1,427 · SL-GAP 0/688 (340 gap slots / 317 gap
rows: 37+197+83) · SL-PHIR 0/1,427 · SEP2 96 (≥ 8) · SEP3 27 (≥ 6) ·
INVREC 221/218 · teeth 2/2 × 3 — all §6R numbers reproduced exactly
(subject to Finding 2's decomposition caveat). Internal arithmetic
closes: 6,970 = 6,402 family + 568 census/skip counters.

## FRESH ROUTE (own code, own genres)

1. **Order-5 twist genre (neither battery used ord ≥ 5):** ℤ₂ chamber,
   ψ₀ = y⁴+y+1 (K₁ = F₁₆, z₁ ord 15), reads (2,1,4)+(3,1,5), ψ₁ =
   y⁵+z₁^k (supp {0,5}; ξ₂ = z₁^{−12} = z₁³ of ORDER 5,
   support-invisible), non-monomial tops: **12/12 rows — ξ-law holds
   (gap slots 1–4 included), both bare-θ variants fail, δ ≠ 1
   non-involution, 0 violations.**
2. **Doubly-twisted wrap genre (Finding 1's regime):** 7/7 shared-below
   m = 3 rows — ξ-law + ledger identity hold, both bare-θ fail, the
   eigen-coefficient law verified, the REMARK's displayed input false.
3. Independent full-battery walk (own Σ/σ′/u_j/δ against engine
   rres/read): OA 0 violations on 2,192 ledger + 1,096 δ + 1,096 phir +
   228 gap-slot samples; my genres 0 violations on 90 + 45 + 45 + 34.

## Disposition

Arc: seal 8064ae3 → verdict 59c1ff2 → **PE1 (this report): NOT CLEAN,
0C + 1G + 2m.** Repair owed (note-only, no statement changes): (i) restate
the (SC-q) REMARK's wrap input as the eigen-coefficient law
Σ_{q−1}(ψ_{q−1,j}) = ξ_q^{g_{q−1}−j}ψ_{q−1,j} with its perimeter
derivation (this report displays one), carried as an induction clause, and
re-point SL-C1's multiplicativity at Σ_m ∈ Aut(K_m) via the same law;
(ii) correct the §6R sample decomposition / INVREC census per Finding 2
(genuine figures 2,828 / 1,414 / 1,414 / 680 / 218-of-218) and mirror in
the applied GRTW2 annex; (iii) fix the §1 index typo. Counter stays 0/2;
PE2 after repair. The (Σ-LAW box) closure and OPEN-2a-Σ's firing are
mathematically intact on all evidence, including the previously-unsampled
doubly-twisted regime.

— passPE1 verifier, 2026-08-08.
