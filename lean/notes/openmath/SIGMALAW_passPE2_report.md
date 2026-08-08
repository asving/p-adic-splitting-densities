# SIGMALAW passPE2 — hostile verification report (post-r1)

**Target:** `lean/notes/openmath/SIGMALAW_PROOF_2026-08-08.md` at HEAD after
r1 (6b24942; seal 8064ae3, verdict 59c1ff2; PE1 report 9b0117d; GRTW2
annex a9f45ab + correction annex 35e6545). **Charge:** fresh-context
hostile pass 2; quote-and-classify; fix nothing; unmined veins = (1) the
r1 (EC-q) transcription itself — independent re-derivation + circularity
hunt in the 3-clause ladder, (2) the doubly-twisted instrument note
reproduced at k ≠ 1, (3) SL-L1 at maximal gap structure, (4) §6R recount
from committed artifacts, (5) the GRTW2 annex-mirror chain; machine
re-run + a fresh route differing from PE1's order-5 genre.
**Verifier artifacts (not committed):** `/tmp/pe2sl/pe2_fresh.py`,
`/tmp/pe2sl/pe2_fresh_cd.py`, `/tmp/pe2sl/teeth_isolated.py` (own
χ/ξ/Σ/U/u_j/λ/EC/δ implementations written from the note's §1/§3-[r1]/§4
displays; own tower constructions; own genres), outputs
`partAB.json`, `partCDE.json`, `cde_out.txt`, `rerun_output.txt`.

## VERDICT: CLEAN ON THE TARGET NOTE — 0 CRITICAL + 0 GAPS + 0 minor in the note text at 6b24942; **1 MINOR finding on the charged annex-mirror surface** (GRTW2 annex #2 @ 35e6545 transposes SL-GAP/SL-PHIR — off-note, post-r1 commit, orchestrator repair owed; Finding 1)

Every charge was pressed and every substantive claim of the r1 note
CONFIRMED: the (EC-q) derivation re-derived independently from sources
(§A), the 3-clause ladder proved well-founded with the base case traced
to rk. 3's m = 1 law (§A.2), the doubly-twisted regime reproduced by own
construction at k = 5 and k = 7 with the derivation's contrapositive
machine-witnessed 8/8 (§B), SL-L1 exercised at gap structure DEEPER than
anything the sealed battery contains (per-slot gap 3 vs battery max 2,
64/64 exact; §C), the §6R corrected counts re-measured to the digit
(§D), and the machine leg bit-identical ex-timing with a fresh order-7
genre 24/24 green (§F). Whether the off-note Finding 1 starts or resets
the 2-clean counter is an orchestrator adjudication; the note text
itself survived this pass with zero findings.

---

## §A. VEIN 1 — the r1 (EC-q) transcription: independently re-derived; the 3-clause ladder is WELL-FOUNDED; no circularity found

**A.1 The derivation, re-done from the sources.** I re-derived (EC-q)
end-to-end from the cited objects, checking every input against its
source text, without consulting PE1's derivation until done:

* **OA-L4** (byte-equal ⟹ ρ_j = 1): OPEN2ATTACK §1 — its proof consumes
  (HR-REC), W2-L0, REALIZE R1–R3 only. **No Σ-content, no byte-share
  law, no rk. 3** — so the chain's entry point is independent of the
  ladder being built. ✓
* **REALIZE R3**: C_j = realize_m(ε_m(β_j)^{−1}ψ_{m,j}, β_j) has read
  ε^{−1}ψ_{m,j}; with ρ_j = 1 both builders' slot digits carry it. ✓
* **Thm-`phir` constant**: GRTW2 §1.3 — c₁ = z_m^{−A_m} (tex 1270),
  c = c₁^{e_m g_m}. At the interior junction at level q (m := q−1):
  c = z_{q−1}^{−A_{q−1}e_{q−1}g_{q−1}} — exactly the note's display. ✓
* **(Σ-LEDGER) at q−1 + u_j closed form**: from (VD-(q−1)); the
  application object P_j is an on-line level-(q−1) object at weight β_j
  (Prop-`construct` child, the standing OPEN2ATTACK §1 setting). ✓
* **(SC-(q−1)) inverse form**: Σ(ε^{−1}y) = ε^{−1}ξ^{−E}Σ(y) follows
  from (SC-(q−1)) by the substitution y ↦ ε^{−1}y alone (Σ(y) =
  Σ(ε·ε^{−1}y) = εξ^{E}Σ(ε^{−1}y)) — no automorphism input needed at
  this step; the note's bare "[(SC-(q−1))]" citation is exact. ✓
* **The collapse**: λ_j = c·z_{q−1}^{k_jA_{q−1}}·U_{q−1}(β_j)^{−1}·
  ξ_{q−1}^{E(β_j)}; SL-L2 at q−1 in the form U^{−1}ξ^{E} = χ^{β_j}
  (from Λ = U·ξ^{−E} = χ^{−w}); then with k_j = j·e_{q−1}, β_j =
  (g−j)γ_q: λ_j = z^{−A'e(g−j)}·χ^{γ_q(g−j)} = [χ_{q−1}^{γ_q}·
  z_{q−1}^{−e_{q−1}A_{q−1}}]^{g−j} = ξ_q^{g−j} by the §3.4 ξ-definition
  — **my exponent algebra agrees term-for-term with the r1 display**. ✓
* **The wrapped slot comparison**: expanding Σ_q(z·x) vs ξ_q·z·Σ_q(x)
  at the wrap coordinate ν = g−1 gives exactly the displayed
  Σ_{q−1}(y·ψ_{q−1,i})ξ_q^i = Σ_{q−1}(y)ψ_{q−1,i}ξ_q^{g} for arbitrary
  y ∈ K_{q−1}; at y = 1 this is (EC-q); with Σ_{q−1} multiplicative it
  is equivalent to (EC-q). ✓ And (EC-q) + Σ_{q−1} ∈ Aut(K_{q−1}) ⟹
  Σ_q ∈ Aut(K_q): the coordinate map is the descent of the ring
  endomorphism Z ↦ ξ_qZ, coeffs ↦ Σ_{q−1} of K_{q−1}[Z], which fixes
  the relation ideal iff φ(ψ_rel) = ξ_q^{g}ψ_rel iff (EC-q) — re-proved. ✓
  (z_q is a unit since 0 ∈ supp by the class pin, so (SC-q) at all
  E ∈ ℤ follows.) ✓

**A.2 Circularity hunt (the charge's specific worry: (EC-q) vs (SC-q)).**
The dependency graph as transcribed:

    (EC-q)  ← (VD-(q−1)), (SC-(q−1)), SL-L2@(q−1), Σ_{q−1}∈Aut [= EC-(2..q−1)],
              OA-L4 + R3 + Thm-phir [Σ-free], byte-equal interior junction at level q
    (SC-q)  ← (EC-q) + Σ_{q−1}∈Aut(K_{q−1})
    SL-L2@q ← (SC-q)          [the Σ_q(z_q^E) step at general E]
    (VD-q)  ← (VD-(q−1)), (SC-(q−1)), SL-L2@(q−1)

Every arrow points to a strictly lower level or strictly earlier in the
within-level order **EC → SC → L2 → VD**; (VD-q)'s own per-ν matching
never touches a wrap (both sides carry ε_q(β) as a common left factor;
the ν-comparison happens inside the faithful basis, U_q(β) ∈ K_{q−1}
is per-coordinate scalar). The induction is genuinely well-founded on
the shared-below perimeter, where every interior junction at levels
2 ≤ q ≤ m is byte-equal — the ladder's byte-equality inputs are all
supplied by the premise, none by the conclusion. **No circularity.**

**Base case traced (q = 2).** Σ₁ = id, (VD-1) = W2-L3, (SC-1)/SL-L2@1
trivial. The (EC-2) derivation instantiates to λ_j = c·z₁^{k_jA₁} =
z₁^{−e₁A₁(g₁−j)} = ξ₂^{g₁−j}, and with Σ₁ = id, (EC-2) reads
ξ₂^{g₁−j} = 1 on supp — **which is verbatim GRTW2 §3.4 rk. 3's m = 1
byte law** (rk. 3: c·z₁^{A₁e₁j} = 1 on supp; c·z₁^{A₁e₁j} =
z₁^{−A₁e₁(g₁−j)} = ξ₂^{g₁−j}). So at the base the ladder re-proves the
one form of the law GRTW2 actually proved, from byte-equality + phir —
consistent, non-circular (rk. 3 itself is consumed nowhere). ✓ The one
silent convention: **ξ₁ is never defined** ((SC-1)'s triviality and the
q = 2 λ-display need ξ₁ := 1); χ₁ = 1 is defined but ξ_q only for
q ≥ 2. Recorded as a remark, not a finding (Σ₁ = id makes every use
degenerate; the machine code paths all special-case q = 1).

**A.3 Consumption-list check.** The r1 [r1]-bracket in §3's Grade &
consumption correctly re-points the sealed "byte-share law" citation at
interior byte-EQUALITY consumed through OA-L4 + Thm-phir — matches the
derivation's actual inputs. ✓ SL-C1's re-pointed multiplicativity step
(Σ_m ∈ Aut(K_m) via (EC) at 2 ≤ q ≤ m) is exactly what the δ_j
factorization needs (Σ_m(ρ·x) = Σ_m(ρ)Σ_m(x) at arbitrary unit ρ); the
sealed hedge's insufficiency is correctly quoted. ✓ SL-C2 consumes only
bijection-fixing-1, unchanged. ✓ No statement display changed by r1
(SL-1/(VD-q)/(Σ-LEDGER)/SL-C1/SL-C2 byte-checked against the seal side
of the diff). ✓

## §B. VEIN 2 — the doubly-twisted regime REPRODUCED by own construction at k ≠ 1, plus the sharp two-sided test

Own towers (own specs, own Σ/EC/δ code; engine TowerX/GmnLeg/
actual_ratios verbatim as instrument): chamber ℤ₃, reads
(2,1,2)+(3,1,4)+(1,1,2)+(1,1,1), ψ₀ = y²+y+2, ψ₁ = y⁴+z₁^k,
ψ₂ = y²+z₁^i·z₂, ψ₃ = y+(1+z₃), for ALL k ∈ {1,3,5,7} × i ∈ {1,2,3,5}
— 16 towers, all built. My own hand-arithmetic first: ξ₂ = z₁^{−6} =
z₁² (ord 4), ξ₃ = χ₂^{γ₃}z₂^{−e₂A₂} with γ₂ = 13, w₂Φ₂ = 156, A₂ = 52,
γ₃ = 157, χ₂ = z₁², z₂^{−52} = z₁^{3k+4 mod 8} ⟹ **ξ₃ = z₁^{3k+6}** —
the instrument note's formula re-derived (machine: ξ₃ == z₁^{3k+6} on
16/16). (EC-3) at ψ₂ = y²+cz₂ reduces to **ξ₃² = ξ₂**, i.e. 6k+4 ≡ 2
(mod 8) ⟺ **k ≡ 1 (mod 4)**, independent of c. Preregistered
predictions and outcomes:

* **k ∈ {1,5} (8 towers):** interior junctions at levels 2 AND 3
  byte-equal; (EC-3) GREEN with NON-trivial eigenvalue (ξ₃² = z₁² ≠ 1);
  the walked m = 3 row is shared-below and byte-RED with **ledger
  identity, δ-law, and Thm-phir all holding (own code), BOTH bare-θ
  variants failing, δ a non-involution, gap slots present (gap 1 on
  both legs) — 8/8.** The k = 5 towers (4 of them) are the charged
  k ≠ 1 reproduction; the instrument note's k = 1 row is confirmed
  independently at i ∈ {1,2,3,5}.
* **k ∈ {3,7} (8 towers):** (EC-3) FAILS (ξ₃² = z₁⁶ ≠ z₁²) — and the
  level-3 interior junction is **byte-RED on all 8**, exactly the
  contrapositive the derivation demands (byte-equal ⟹ EC). The note's
  eigen-MISMATCH control (k = 3, i = 1) is the first of these; my
  8 towers extend its 1/1 to 8/8, including k = 7 which no prior pass
  built.
* **(SC-q) wrap spot-test (Part E, measured):** on byte-equal towers
  (k = 5 i = 1; k = 1 i = 2) the wrap identity Σ_q(z^E y) =
  ξ_q^E z^E Σ_q(y) holds at q = 2 AND q = 3 on random y and wrapped
  E ∈ {1, g, g+1, 2g}; on the k ≡ 3 towers (k = 3 i = 1; k = 7 i = 1)
  it **FAILS at q = 3 and still holds at q = 2** (where (EC-2) is
  automatic: ξ₂⁴ = 1 on supp {0}) — 4/4 predictions. The wrap-terms
  story is thereby confirmed at the exact level the derivation places
  it: (SC-q) closes precisely where (EC-q) holds.

**The λ-identity census (the derivation's collapse, machine-keyed
beyond PE1's 7 towers):** λ_j = c·z_{q−1}^{k_jA_{q−1}}·U^{−1}ξ^{E} ==
ξ_q^{g−j} checked as field elements at every supported slot of every
interior junction of all 16 doubly-twisted + all 16 roster towers:
**46/46, 0 mismatches** — including the mismatch towers, as it must
(the collapse is a character identity; byte-equality enters only to
give Σ(ψ_j) = λ_jψ_j). The engine's thm_c tied to my c-formula at every
interior junction, 0 mismatches.

## §C. VEIN 3 — SL-L1 at gap structure DEEPER than the sealed battery's

First I measured the sealed battery's actual gap depth (all 539 towers,
every walked slot, both legs, `gap_scan` per slot): **the battery's
per-slot maximum is 2** (at B2-11-01, r = 4, j = 0) — so its "340 gap
slots" never exercise a gap ledger deeper than 2. Then I constructed a
genre designed for deeper gaps (top-modulus coefficients with shifted
coordinate support: c₀ ∈ {z₂^t, z₂^t(1+z₂), z₁z₂^t}, t ≤ 3, on the
SEP-A chamber, reads (1,1,1)/(2,1,1)/(1,1,2)/(3,1,1)): **64 walked gap
rows, per-slot gap_scan up to 3 — strictly beyond the battery — with
the ledger identity, the δ-law, and Thm-phir holding on ALL 64 with NO
correction term** (own Σ/u_j/δ code), including nested-gap rows
(gaps (h:1, c:3) — a print-leg node chain with three gap events). SL-L1's
per-node cancellation (the attained-start τ-normalization) is thereby
witnessed outside the battery's gap envelope, as the proof demands —
the mechanism is per-node and depth-independent, and the evidence now
matches at depth 3.

## §D. VEIN 4 — §6R recounted from the committed artifacts; the leak re-measured

* **JSON recount (committed `sigmalaw_results.json`, byte-verified vs
  59c1ff2):** 1,217 rows = 1,211 walked (539/527/145 by m) + 6 SKIP;
  Σ|supp| over walked rows = **1,414** (OA 1,060 + SEP 354); gap rows
  317 (37/197/83), gap slots 340; SEP2 96, SEP3 27; censuses INVREC
  221/218-OA. Arithmetic: 1,427−1,414 = 13, 2,854−2·1,414 = 26,
  688−2·340 = 8 — the r1 block's cross-checks reproduced. ✓
* **Code mechanism verified:** `run_tooth` restores `VIOL`, pops `ROWS`
  by tag, never restores `COUNTS`; the `mut_print` teeth are NOT
  excluded from the `SL-INVREC-ROW` census block (only `mut_dropU`/
  `mut_bareSigma` are), and genre 'TOOTH' cannot leak into
  `SL-INVREC-OA` — all three structural claims of the [r1] block read
  directly off the sealed runner. ✓
* **Leak re-measured in isolation (own harness, the six designated
  tooth runs):** US +10/+5/+5/+4, SB +10/+5/+5/+4, PR +6/+3/+3/+0 on
  VDM/DELTA/PHIR/GAP and **SL-INVREC-ROW +3 arising in the PR teeth
  alone** — totals SL-VDM +26, SL-DELTA +13, SL-PHIR +13, SL-GAP +8,
  SL-INVREC +3. **Genuine figures 2,828 / 1,414 / 1,414 / 680 and
  INVREC = 218 EXACTLY — the r1 [r1] block and the PE1 Finding-2
  decomposition confirmed to the digit.** ✓

## §E. VEIN 5 — the GRTW2 annex-mirror chain: ONE defect found

The a9f45ab annex (SIGMALAW §8 → GRTW2 tail) is verbatim-applied with
the designated blank resolved to 59c1ff2 (re-diffed) and carries the
machine-printed figures — which the note's §8 [r1] caveat discloses and
defers to an orchestrator mirror action. That mirror landed at 35e6545
(GRTW2 tail, "ANNEX 2026-08-08 #2") — **and it transposes two family
labels** (Finding 1 below). All other surfaces checked: OPEN2ATTACK's
pointer-annex carries no counts; PROJECT_STATE's 35e6545 line carries
no counts; the BRIDGE_ADJUDICATIONS annex-applier record quotes the
printed figures but is a dated pre-PE1 historical record (written at
a9f45ab time, before the leak was discovered) — acceptable as history;
the 35e6545 BRIDGE entry itself quotes only "INVREC = 218 exactly" ✓.

## FINDING 1 (minor; bookkeeping; OFF-NOTE surface — the GRTW2 correction annex, not the frozen SIGMALAW note): the 35e6545 mirror transposes SL-GAP and SL-PHIR

**Quoted (GRTW2_PROOF_2026-08-08.md tail, annex #2, 35e6545):** "the
genuine battery figures are SL-VDM 2,828 / SL-DELTA 1,414 / **SL-GAP
1,414 / SL-PHIR 680** (340 gap slots stands)". The genuine figures are
**SL-PHIR 1,414 / SL-GAP 680** (= 688 − 8 = 2×340; PHIR = 1,427 − 13):
the correction annex swapped the last two labels, so the corrected
figures did NOT propagate faithfully to the mirror. Self-inconsistent
on its face ("340 gap slots stands" ⟹ GAP = 680, not 1,414). The
SIGMALAW note's own §6R [r1] block and §8 annex caveat carry the
correct decomposition (2,828/1,414/1,414/680, INVREC 218), so the
defect lives ONLY on the GRTW2 mirror surface — created by 35e6545,
AFTER the r1 target of this pass. No verdict, count, or theorem is
affected; repair is a one-line annex correction (orchestrator action —
GRTW2 is ACCEPTED-FROZEN).

## §F. MACHINE LEG + FRESH ROUTE

* **Runner:** md5 92e7c22cb2c823909dc5ad6b03f61c32 at HEAD == seal
  8064ae3 byte-identical; committed artifacts byte-identical to verdict
  59c1ff2 (md5 a5daabf1…/70e5bd1d…). **Fresh full re-run: exit 0,
  18.6 s, 6,970 samples, ALL FAMILIES GREEN; output byte-identical
  ex-timing; JSON identical except `elapsed_s`.** Printed counts
  2,854/1,427/688/1,427 + SEP 96/27 + INVREC 221/218 + teeth 2/2/2
  reproduced — matching §6R-as-corrected (printed = genuine + the
  measured leak). Artifacts restored after the run (repo clean).
* **Fresh route (differs from PE1's order-5/F16 genre):** THREE legs,
  none previously exercised.
  1. **Order-7 twist genre** (no battery and no prior pass used F₈ or a
     twist of order 7): ℤ₂ chamber, ψ₀ = y³+y+1 (K₁ = F₈, z₁ ord 7),
     reads (2,1,3)+(2,1,7), ψ₁ = y⁷+z₁^k (supp {0}; A₁ = 3,
     ξ₂ = z₁^{−6} = z₁ of ORDER 7, support-invisible since ξ₂⁷ = 1),
     k ∈ {1,2,3}, non-monomial deg-1 tops over K₂ = F_{2^21}:
     **24/24 walked m = 2 rows GREEN on ledger + δ-law + phir (own
     code); all 24 are separators (Σ ≠ σ′ live and BOTH bare-θ
     variants fail); all 24 δ non-involutions.** The ξ-law now has
     witnesses at twist orders 2, 4, 5, and 7.
  2. **Direct algebraic verification of the (EC-q) collapse** — the
     λ-identity census of §B: 46/46 supported interior slots over 32
     towers, λ_j == ξ_q^{g−j} elementwise, engine `thm_c` tied to the
     c-formula at every interior junction.
  3. **The (SC-q) wrap spot-test** of §B (4/4: closes exactly where
     (EC-q) holds, fails exactly where it fails).

## Remarks (non-findings)

1. ξ₁ is used implicitly as 1 (the (SC-1) triviality and the q = 2
   λ-collapse); §1 defines ξ_q only for q ≥ 2. Harmless (Σ₁ = id).
2. The r1 header's "runner + artifacts byte-frozen at seal 8064ae3"
   names one commit for artifacts that landed at 59c1ff2; both
   verified frozen at their own landing commits.
3. THEOREM SL-1's opening quantifier ("every on-line level-q object")
   reads scope from the §1 standing setting (shared-below junction);
   for q ≥ 3 the (VD-q) clause genuinely needs the perimeter (its
   (SC-(q−1)) input fails off it — my k ≡ 3 towers witness this at
   the level-3 wrap). The r1 ladder paragraph states the perimeter
   scope explicitly, so the note is internally consistent; flagged
   only because a future extraction of (VD-q) without the setting
   would be wrong.

## Disposition

Arc: seal 8064ae3 → verdict 59c1ff2 → PE1 0C+1G+2m (9b0117d) → r1
(6b24942) → **PE2 (this report): CLEAN on the note text — 0C + 0G + 0m;
1 MINOR off-note finding (the 35e6545 GRTW2 correction-annex
transposition, Finding 1)**. The r1 transcription of the
eigen-coefficient law is faithful, independently re-derivable, and
non-circular; its machine phenomenology (byte-equal ⟺-side, mismatch
contrapositive, wrap closure) is reproduced and EXTENDED (k = 5/7
towers, order-7 genre, gap depth 3). Repairs owed: (i) one-line GRTW2
annex #2 label fix (SL-GAP 680 / SL-PHIR 1,414) — orchestrator action
on the ACCEPTED-FROZEN GRTW2 surface, not a SIGMALAW note edit;
(ii) nothing on the note itself. If the counter is scoped to the note
text (the object under acceptance, byte-frozen through this pass), this
is the FIRST CLEAN PASS — counter 1/2, PE3 = the accepting attempt;
the off-note finding's effect on the counter is the orchestrator's
call. The (Σ-LAW box) closure, THEOREM SL-1 with the (VD)+(EC)+(SC)
ladder, SL-C1's δ = ρ^{1−Σ}, and OPEN-2a-Σ's unconditional firing stand
verified on every route this pass could construct.

— passPE2 verifier, 2026-08-08.
