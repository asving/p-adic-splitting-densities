# O2a — engine↔GMN dictionary — Phase-B attempt REV 2 (Fable, 2026-07-31)

Repair of the V10 hostile verification (`V10_o2a.jsonl`, verdict UNSOUND;
9 critical / 3 gap findings) of the rev-1 attempt (`O2a_phaseB_attempt.md`) /
brief (`O2a_phaseB_verifybrief.md`). V10 CONFIRMED: the carrier W-laws'
internal compatibility, the order-1 core calculations (deg G, v₂(φ₁) = h₁,
W3↔Def 3.10, both lattice witnesses, the charge arithmetic), and — given
continuing nodes, OL-1, and Cons_f — the type-tree induction, degree
recursion, saturation argument, and per-order index charge, "complete from
the stated GMN facts". All of that is carried byte-stable. The three
orchestrator-charged criticals are (1) = V10-G2/C7 (§3 below), (2) = V10-C8
(§3), (3) = V10-C4/C9 (§2/§4). This rev repairs ALL twelve findings — no
silent drops (§0). The repaired self-contained brief is
`O2a_phaseB_verifybrief_rev2.md`. New falsifier F5 EXECUTED FIRST, covering
exactly the V10-G1 corner: `O2a_rev2_check.gp` — 871 forced
exact-φ₁-divisibility samples, 0 findings on all four checks (§5).

## 0. V10 findings → dispositions (no silent drops)

| V10 finding | class | disposition |
|---|---|---|
| C1: no domains for s_i, u_i — 𝔈 and its equality not fully defined | CRITICAL | **FIXED** brief §2 (C1): s_i, u_i ∈ ℤ_{≥0} declared; binding semantics moved to Cons_f's positional clause (initial point of the read side in the order-i GMN integer frame; v_i ≥ 0 on O[x]∖0 makes this consistent) |
| C2: Lift image not "(L5)-shaped by construction"; Θ(𝐇) need not lie in 𝔗 before OL-1 | CRITICAL | **FIXED** brief §2 (C2): codomain redesigned as FORMAL chain data 𝔗 (purely combinatorial membership); the GMN interpretation ι is a separate map, defined at level 0 by (D4) (proved) and at levels ≥ 1 exactly by OL-1; the (L5) claim split into SHAPE (by construction) vs ADMISSIBILITY ((D4)+OL-1, claimed only there) |
| C3: terminal last node in 𝔈-equality but discarded by Θ; contradicts recovery under Cons_f | CRITICAL | **FIXED** brief §2 Lemma R: injectivity RESTRICTED to 𝔈°_f (all nodes continuing); terminal non-recoverability is now a DISPLAYED NON-CLAIM with an explicit two-witness counterexample; the terminal seam's needs (t-i) consistency clause + (t-ii) codomain extension are displayed and assigned to O-3; consumer audit shows the restriction costs no clause (everything exported is a function of 𝐇°) |
| C4: Theorem 1 ill-formed at 𝐇 = (ρ₀) and at terminal ν₁ (e₁, …, G undefined) | CRITICAL | **FIXED** brief §3: Theorem 1 restated as a THREE-CASE split — (i) (ρ₀), (ii) (ρ₀; ν₁ terminal), (iii) (ρ₀; ν₁ continuing) — with per-case claims (D0°)/(D2°)/(D4)/(Ch°) vs the full (D0)–(D4)+charge; no symbol is quantified outside its case |
| C5: (D0) injectivity silently assumes ν₁ continuing; false for terminal records | CRITICAL | **FIXED** with C3: Lemma R + case (ii)'s explicit non-recovery clause |
| C6: "(D0) Θ total on 𝔈" asserts codomain membership unavailable before OL-1 | CRITICAL | **FIXED** with C2: Θ : 𝔈 → 𝔗 is a pure re-indexing of discrete data — totality and truncation-compatibility are now genuinely unconditional |
| G1: "principal part on [0, ω]" fails when an initial φ₁-adic coefficient vanishes | GAP | **FIXED** brief §1 (L3+) + §3 (D3): the j₀ := ord_{φ₁}(f) convention (finite part on [j₀, a]; slope-−∞ side of length j₀; j₀ ≤ 1 for separable f, displayed one-line proof; the −∞ side carries the exact factor φ₁, Hensel leaf (1, f₀); the degenerate j₀ = a = 1 no-finite-side case stated); all (c1)/(c2)/Def-3.10 clauses quantify over finite slopes; the charge gains only the nonnegative E_∞·H_fin term. **Falsifier F5 executed: 0 findings** |
| G2: OL-2's coordinate-clearing map and "recorded translation" undefined | GAP | **FIXED** brief §4: the fractional-lattice/"recorded translation" presentation DELETED; the F.0 interface displayed (ℤ-valued side valuation); OL-2 strengthened to exact claims (a) u_{i+1} = v_{i+1} (with the attackable constant-test u(π) = E_i), (b) window polygon = N_{i+1}(f) as subsets of ℝ² — identity frame, NO translation, engine-internal offsets inverted before emission AS PART OF THE CLAIM (HK52's stretch counterexample cited as the reason this is inside the lemma), (c) side dictionary, (d) positional transport of (s, u) |
| C7: higher-order injectivity consumes a stronger positional identification than OL-2 states; terminal nodes break it at every order | CRITICAL | **FIXED** by re-architecture: Cons_f's positional clause is now INTRINSIC at all orders (brief §2 (C4): (s_i, u_i) = initial point of S_i in the order-i integer frame — no engine frame in the definition), so injectivity (Lemma R) consumes NO part of OL-2; the exact positional recovery is the displayed uniqueness-of-slope-side step of Lemma R; OL-2(d) now carries the engine-side positional burden, consumed only by Theorem 2(D); the terminal half is C3's restriction |
| G3: OL-3's "digit data"/"anchor unit"/normalization undefined — not attackable | GAP | **FIXED** brief §4: the stage-residual interface displayed from MOVES F.0–F.2 (digit algebra 𝒟 = ⊕F·u_ρ with carry cocycle, dig map, support-anchored R^st(f)(z) = Σ dig(B_j)z^{(j−j₀)/e}, anchor-unit division to R^nrm ∈ F_{i+1}[z], tower identification); OL-3 restated as R^nrm = c·R_{λ_{i+1}}(f), c ∈ F_{i+1}^×, with the up-to-scalar sharpness argued maximal (GMN's own ∼) and both-sides-nonzero-constant-term displayed |
| C8: Theorem 2(D) has an undeclared emission-discipline dependence; scope remark (3) hid it | CRITICAL | **FIXED** brief §4/§5: **OL-4 (emission discipline) DECLARED** — emitted histories are well-formed elements of 𝔈 (domains; W1–W5 incl. only-last-terminal, interior μ ≥ 2, the W2 inc law; tower dressing; a₀ = ord_{ψ̂₀}(f̄)); rev-1 scope remark (3) DELETED, replaced by the consumer-audit remark (3′); Theorem 2(D) restated to consume OL-1+OL-2+OL-3+OL-4 and rewritten as an explicit induction |
| C9: Theorem 2 allows k' = 0 but uses μ_{k'} and "the last read" | CRITICAL | **FIXED** brief §5: saturation clause guarded by k' ≥ 1 (displayed); (B)'s levelwise clauses marked vacuous at k' = 0; (C)'s k' = 0 branch displayed (dCert = 0 ≤ ind(f) by Def-4.11 nonnegativity, NO (L9) cite at r = 0); (A)'s k' = 0 meaning displayed |

## 1. What changed structurally (the two-line summary of the re-architecture)

(1) The codomain is now FORMAL (𝔗 = chain data; equality literal), with the
GMN interpretation ι quarantined behind (D4)/OL-1 — Θ is total, truncation-
compatible, and cheap, and every conditional GMN assertion is flagged at its
order. (2) The positional data (s_i, u_i) are pinned INTRINSICALLY by Cons_f
(initial point in the order-i integer frame), so recovery/injectivity
(Lemma R, new) is proved from Cons_f + side-per-slope uniqueness alone,
restricted to all-continuing histories 𝔈°_f; ALL engine-frame content now
sits in the strengthened OL-2a-2/OL-2a-3 plus the new OL-2a-4, consumed
exclusively by Theorem 2(D). Naming: the brief's OL-1/2/3/4 = this project's
OL-2a-1/2/3/4.

## 2. The k'-corners (V10-C4/C9) — what the theorems now say

Theorem 1 is a three-case statement (brief §3): the k' = 0 cases carry
(D0°) totality + Lemma-R recovery of 𝐇° = (ρ₀) + the explicit terminal
non-recovery, (D2°) t^{(0)} ∈ t₀(f), (D4), and (Ch°) dCert = 0 ≤ ind₁ ≤ ind
(nonnegativity + (L9) at r = 1); the order-1 symbols appear only in case
(iii). Theorem 2's saturation is asserted only at k' ≥ 1; the k' = 0
degenerations of (A)/(B)/(C) are displayed in the statement, and (C)'s
k' = 0 proof branch avoids (L9) entirely. W3 forces a₀ ≥ 2 whenever ANY node
follows (terminal included) — kept as a carrier law; whether a concrete
engine emits a terminal marker on a Hensel-decided track is OL-2a-4-side
conformance, not carrier business.

## 3. The open-lemma suite rev 2 (V10-G2/G3/C7/C8)

* **OL-2a-1** (lift admissibility + (16)-normalization): UNCHANGED from rev 1
  (V10 raised no finding against its statement); now additionally the
  definedness gate of ι at levels ≥ 1.
* **OL-2a-2** (frame crossing + positional transport): STRENGTHENED — exact
  claims (a)–(d) over the displayed F.0 interface; the frame map is the
  IDENTITY (u_{i+1} = v_{i+1}; window polygon = N_{i+1}(f) as subsets of ℝ²);
  "up to the recorded translation" is gone; engine-internal offset inversion
  is inside the claim (HK52-informed); (d) states the positional transport of
  (s, u) verbatim against (c1)'s intrinsic clause. Consumed by Theorem 2(D)
  only — the injectivity consumption V10 objected to no longer exists.
* **OL-2a-3** (residual identification): restated over the displayed
  F.0–F.2 residual interface (digit algebra, dig, support anchor, anchor-unit
  division, tower identification); claim R^nrm = c·R_{λ_{i+1}}(f),
  c ∈ F_{i+1}^×; independently attackable now. Still the shared-lemma with
  O-9's twisted-residue leg.
* **OL-2a-4** (emission discipline): NEW, DECLARED — the stage flow emits
  W1–W5-lawful, domain-correct, tower-dressed histories with
  a₀ = ord_{ψ̂₀}(f̄) and only-last-terminal. Consumed by Theorem 2(D) only.
  This is the content rev 1's scope remark (3) wrongly externalized; the
  remark is deleted. Intended proof route recorded ((τ-irr) halting, inc
  bookkeeping) — O-3-adjacent, but the DECLARATION lives here because the
  CONSUMPTION lives here.

## 4. Theorem 2 rev 2 — deltas only

(A) injectivity clause re-pointed at Lemma R (restricted, terminal-aware);
type-tree induction byte-stable. (B) byte-stable, saturation under the k' ≥ 1
guard. (C) byte-stable plus the displayed k' = 0 branch. (D) rewritten as the
explicit induction: OL-4 ⇒ well-formed + (c0); (D3) ⇒ level-1 (c1)+(c2)
(positional clause included in the first-read format now); OL-2(c)/(d) ⇒
level-(i+1) (c1); OL-3 ⇒ level-(i+1) (c2); OL-1 ⇒ next level defined. The
conditional theorems (A)–(C) consume only Cons_f + OL-1, exactly as V10
confirmed them.

## 5. Falsifier F5 (executed FIRST, before the document repairs)

`lean/notes/openmath/O2a_rev2_check.gp` (PARI/GP, seed 20260801): 871 samples
f = φ₁·g at p ∈ {2,3,5}, n ∈ {3..7}, constructed with ord_{φ₁}(f) = 1 and
ord_{ψ₀}(f̄) = a ≥ 2 — exactly the vanishing-initial-digit corner that
rev 1's F1 sweep SKIPPED (its code returned early on b₀ = 0, which V10-G1
correctly flagged as unhandled in (D3) too). Checks: (i) predicted (e,f)
multiset — the −∞ side booked as the Hensel leaf (1, f₀) + finite-side
Cor-1.20 leaves — vs `idealprimedec` ground truth on the 827 decided samples:
**0 mismatches**; (ii) degree checksum: **0 failures**; (iii) ind₁ ≤ ind_p
with the E_∞·H_fin term INCLUDED (sharper — the term only raises ind₁):
**0 violations**; (iv) #certified sides ≤ ind₁: **0 violations**. Hand corner
x² + 3x at p = 3 (j₀ = 1: leaves (1,1)+(1,1), ind₁ = ind_p = 1): pass.

## 6. Byte-stability record (what V10 confirmed, carried unchanged)

Kept verbatim in the rev-2 brief: (L1)–(L9) (only (L3+) appended, flagged);
(D4); the (D1)/(D2)/(charge) proofs; OL-1; Theorem 2's (A)-induction,
(B)-proof, (C)-proof bodies (modulo the flagged guards/branches); scope
remarks (1)/(2)/(4); falsifiers F1–F4. Changed, with flags at each site:
(C1) domains, (C2)/(C3) codomain/ι/Θ, (C4) positional clause + terminal
sentence, Lemma R (new), Theorem 1's statement (three cases) and (D0)/(D3),
the §4 interface + OL-2/OL-3 statements + OL-4, Theorem 2's statement guards
and (D), remark (3) → (3′), F5.

## 7. Honesty ledger (rev 2)

**Proved here (order ≤ 1, Theorem 1):** all clauses per case — including the
k' = 0 cases and the j₀ corner — at the declared carrier, from the pinned
citations only; injectivity exactly on all-continuing histories (Lemma R),
with terminal non-recovery displayed as a non-claim.

**Proved here (all orders, Theorem 2):** landing, placement, restricted
injectivity, invariant matching, saturation (k' ≥ 1), charging, k' = 0
degenerations — GIVEN Cons_f and OL-2a-1; the engine seam (D) GIVEN
OL-2a-1/2/3/4.

**Open (the exact residue of O-2a):** FOUR lemmas now — OL-2a-1 (lift
admissibility), OL-2a-2 (frame crossing + positional transport), OL-2a-3
(residual identification), OL-2a-4 (emission discipline). Rev 1's claim that
engine W-law conformance was "O-3-side, not this leaf" is RETRACTED as an
undeclared dependence (V10-C8): it is this leaf's OL-2a-4. The terminal seam
((t-i)/(t-ii)) is a DESIGN obligation assigned to O-3, not an open lemma
here — nothing in this note consumes it.

**Literature consumption:** unchanged from rev 1 — (†) = Thm 4.18(1) +
Def 4.15/4.11 nonnegativity, keyed to F_rep, plus Thm 1.15/1.19/Cor 1.20,
Thm 2.11/Def 2.12, Cor 3.8/Def 3.9/3.10 — all LITERATURE-CONDITIONAL pending
printed-TAMS confirmation; PLUS (L3+)'s slope-−∞ convention (Def 4.12's
E_∞·H_fin term), newly consumed and newly falsifier-covered (F5).

**Not attempted (unchanged):** O-2b, O-3 realization, BNS/LIT-5.

## VERDICT

O-2a rev 2: **all 12 V10 findings repaired (9 critical, 3 gap; dispositions
§0, no rebuttals needed — every finding was accepted and fixed); carrier
re-architected (formal codomain + intrinsic positional clause + Lemma R);
Theorem 1 total on its domain; Theorem 2 reduced to FOUR exactly-stated open
lemmas with the confirmed core induction byte-stable; new falsifier F5
0-findings.** Pending: hostile re-verification of
`O2a_phaseB_verifybrief_rev2.md`.
