# (SURV-DISJ) DOUBLE-KILL CONSTRUCTION — defeat systems for the three unproved strata (g₀ = 3 resurrected; the glued stratum; the first (SD-YJ) towers), sealed before realization

Object: the claim (SURV-DISJ) of SURV_PROOF_2026-08-08.md S7 —

    on live rows (TRACK, (H1)–(H3), c_{m−1} ≥ k) the netted BOTTOM
    stratum survives netting OR the CASCADE slot survives at the
    cascade line

— attacked by DELIBERATE CONSTRUCTION outside its proved loci
(g₀ = 1 ∧ d₀ = 1 ∧ (STK): SD-THM-A cascade leg; g₀ = 2 ∧ (K2-REG):
K2-THM-A bottom leg).  This is the first unit under the standing
do-not-sweep/CONSTRUCT directive (ledger 1d40751): per target we derive
the defeat system, display it, seal falsifiable predictions, and only
then realize and run.  A kill is a COUNTEREXAMPLE (major finding); an
infeasibility derivation is a lemma FOR the claim; every outcome is
data on a machine-dark stratum.

**VERDICT: see S6 (filled from artifacts at the second commit; PENDING
at the seal commit).**

Date: 2026-08-08 campaign (wallclock 2026-08-04).  Unit: the
(SURV-DISJ) DOUBLE-KILL CONSTRUCTION composer.

## S0. Authority, consumption, machine leg, disclosures

Consumption (read-only, dagger discipline; grades ride through):
[RMG] RMENGINE (ACCEPTED — S2.2 child inventory, L-NORM, S2.1 cell/line
kit, corr_table display); WMULTDCX† (W-D2(iv) seed t-inventory — attempt
grade 0/2 CLEAN, the binding cap); SURVDISJ_PROOF† (SD-L1/L2 ledger +
deficit, SD-L6/L7, (★), the (SD-YJ) box — 1/2 CLEAN); SURVK2_PROOF†
(K2-L1..L7 window calculus, the S7 candidate arithmetic — 0/0, PE1
GAPS-ONLY); SURVK2_passPE1_report (the class-pin discipline: check
ψ_j(0) ≠ 0 + irreducibility before every realization).  Everything
measured here is INSTANCE grade; the only new proved content is the
finite inventory arithmetic displayed in S2/S3 and the S1 engine
finding, each verifiable by inspection.

**Machine leg**: `verification/openmath/survdisj_construct.py`
(committed WITH this note at the seal commit = commit 1; run AFTER the
seal; verdict + artifacts = commit 2).  Engines consumed byte-untouched,
md5-pinned inside the runner (grb_order2_check dab62713…,
rmengine_pe_reimpl 103c1a9c…, empty_derive_checks 8fed9240…,
wmultdcx_stress 15315cca…, wmultdcx_derive_checks bea1a43d…,
survk2_derive_checks d8493ab9…, survdisj_derive_checks 3eaf69c0…).
Seventeen verdict families (CON-*) + a FINDINGS channel (measured
events, never violations); families and predictions listed at S5.

**Design-probe disclosure.**  Four pre-seal design probes (throwaway,
outside the repo) observed: the capability wall + hang stage (S1), the
patched towers' construction feasibility + certificate violation counts
(all 0), availability sets A per candidate tower, live-row counts, cell
counts, and wall-clock costs.  NO netting, survival, window-realization
or kill verdict was computed or observed pre-seal (the DCX3
design-disclosure convention).  The S5 predictions are sealed against
exactly the quantities the probes did not touch.

**The pick-extension disclosure.**  The runner monkeypatches TWO
functions of grb_order2_check at load time (files byte-untouched):
`fp_irreducible` → deg ≤ 2 delegates verbatim, deg 3 = no-root test
(exact for cubics); `pick_irreducible` → g ≤ 2 delegates verbatim
(agreement census CON-AGREE over {F2,F3,F5,F4,F9} × g ∈ {1,2} ×
idx ∈ {0,1}), g = 3 enumerates [b, a₁, a₂, 1] in the committed
`_field_elems` order with b ≠ 0 and idx % len wraparound — the
committed convention one degree up.  One tower (C3OMX) uses a declared
PICK_OVERRIDE (S2.4) whose irreducibility and ψ₀(0) ≠ 0 are re-verified
at pick time.  The class pin (ITERLAWN S0.1: ψ_j monic irreducible,
ψ_j(0) ≠ 0, gcd(e,h) = 1) is satisfied by every constructed tower BY
CONSTRUCTION; no tower steps outside the [ILN] class.

## S1. THE ENGINE FINDING (T1 gate): the g₀ ≥ 3 "cost wall" is a CAPABILITY wall

Displayed finding **K2-ENG**, machine bracket CON-WALL:

* `grb_order2_check.fp_irreducible` (line 410–415): "deg <= 2 test …
  `raise ValueError("only deg <= 2 supported")`" — no irreducibility
  test above degree 2 exists anywhere in the level-0 chain.
* `grb_order2_check.pick_irreducible` (line 428–445): for g ≥ 2 the
  candidate loop builds `cand = [b, a, F["one"]]` — DEGREE 2 ONLY,
  for every requested g.  At g = 3 it silently returns a degree-2
  polynomial: probe A1 — `pick_irreducible(F2, 3)` = y² + y + 1.
* Consequence, reproduced under a 20 s alarm: `PE.Eng` at spec
  ("K2G3AF", 3, Fpt, 2, 1, [(2,1,3), …]) constructs a tower whose ψ₀
  has degree 2 while g₀ = 3, and the chain then HANGS inside `PE.prep`
  — no violation ever fires.  This is byte-for-byte the shape of the
  SURVK2-instrument record ("> 240 s engine prep each", ten towers,
  `ENGINE UNSUPPORTED (TimeoutError('K2 tower budget'))`).

**Reading.**  The ten K2_ROSTER g₀ ∈ {3,4} towers could never have been
constructed by the committed chain: the disclosed "measured engine cost
wall" (SURVK2_PROOF S0/S8, instrument amendment bracket) is factually a
capability wall — g₀ ≥ 3 was machine-dark not because trees are
expensive but because no g₀ ≥ 3 tower EXISTS to the committed engine.
(The harness already carries the needed general pick one module up:
`strata3_probe.pick_irr3`, g ≤ 3, used only for interior ψ₂.)  With the
S0 extension installed, ALL probed g₀ = 3 towers (including the two
stalled K2 specs re-run verbatim) construct in < 1 s and pass every
engine certificate with 0 violations — sealed as prediction P1.  The
cost-wall sentences in SURVK2_PROOF S0/S7(d)/S8 and the SURVDISJ S6 box
should be re-annotated once this unit's artifacts land.

## S2. T1 — the g₀ = 3 double-kill system

Setting: g₀ = 3, P₀ = 3e₀, level-0 masses g₀ − k for k ∈ A :=
{k : ψ₀_k ≠ 0} (ψ₀ = y³ + ψ₀₂y² + ψ₀₁y + ψ₀₀, ψ₀₀ ≠ 0 by the class
pin, so 0 ∈ A always; C_k consumes g₀ − k units, promotion 3; events
fire at u ≥ 3; window budget n ≤ 2g₀ − 1 = 5 by K2-L2†).

**(D1) The F2 availability forcing.**  Over K₀ = F₂ there are exactly
two irreducible cubics: y³ + y + 1 (A = {0,1}) and y³ + y² + 1
(A = {0,2}).  [The other six monic cubics have a root: y³+1, y³+y²+y+1
have root 1; y³, y³+y², y³+y, y³+y²+y have root 0.]  So at d₀ = 1,
p = 2, the availability corner |A| = 2 is FORCED — full availability
A = {0,1,2} at char 2 needs d₀ ≥ 2 (K₀ = F₄).

**(D2) The char-2 netting law.**  In residue characteristic 2 the
netted group sum Σ sgn·res = Σ res is SIGN-BLIND; a group dies iff its
residue multiset sums to 0 in K_m (SD-L6†).  In particular any TWO
cells with EQUAL residue annihilate — same sign or opposite — so every
count-(±2) door of the K2-RES S7(d) box is an AUTOMATIC kill at char 2
provided the two members share a residue class.

**(D3) The general drain inventories at g₀ = 3** (Y-free windows;
runner: `legal_drains_gen`; display normalized as [events] →
(units, p, f-units), sign = (−1)^{#corrections}):

A = {0,2}, masses {1 = C₂, 3 = C₀}:

    n = 3:  [C₂] (1,0,2)−   [C₀] (3,0,0)−   [p] (0→ (3u),1,0)+
    n = 4:  [C₂C₂] (2,0,2)+  [C₂C₀] (4,0,0)+  [C₂p] (4,1,0)−
            [C₀] (3,0,1)−    [p] (3,1,1)+
    n = 5:  [C₂C₂C₂] (3,0,2)−   [C₀] (3,0,2)−      ← THE (−2) DOOR
            [C₂C₂C₀] (5,0,0)−   [C₂C₂p] (5,1,0)+
            [C₂C₀] (4,0,1)+     [C₂p] (4,1,1)−
            [p] (3,1,2)+

  The (units,p,f) = (3,0,2) class at n = 5 is the UNIQUE multi-member
  class: {C₀} and {C₂³}, BOTH sign −, count −2 — the S7(d) door,
  derived.  Kill identity: res ψ̄₀ρ vs ψ̄₂³ρ — equal iff ψ̄₀ = ψ̄₂³.
  Over F₂: ψ̄₀ = ψ̄₂ = 1, AUTOMATIC.  Over F₄: x³ = 1 for every
  x ≠ 0 (F₄* has order 3), so the identity reads ψ̄₀ = 1 — holds for
  both default F₄ picks (probe: idx 0 and 1 both have ψ₀₀ = 1).  So on
  every A = {0,2} char-2 tower of this battery the door, WHEREVER
  REALIZED, kills its class outright (sealed as P4).

A = {0,1}, masses {2 = C₁, 3 = C₀}:

    n = 3: [C₁] (2,0,1)−  [C₀]−  [p]+        n = 4: [C₁] (2,0,2)−
           [C₀] (3,0,1)−  [p]+
    n = 5: [C₁C₁] (4,0,1)+  [C₁C₀] (5,0,0)+  [C₁p] (5,1,0)−
           [C₀] (3,0,2)−    [p] (3,1,2)+

  EVERY (units,p,f) class is a singleton at every n ≤ 5: the in-window
  exchange door is CLOSED at A = {0,1} — these towers are controls
  (their bottom kills must ride cross-seed toggles or interior books).

A = {0,1,2} (full; d₀ = 2 char 2 via the C3OMX override, or F₃):

    n = 4, class (2,0,2):  [C₂C₂]+  vs  [C₁]−   — kill iff ψ̄₂² = ψ̄₁
    n = 5, class (3,0,2):  [C₀]−, [C₂³]−, [C₂C₁]+, [C₁C₂]+
           — {C₂,C₁} legal in BOTH orders (the S7(d) order-
           multiplicity door): same book, same residue ψ̄₂ψ̄₁ρ, same
           sign: an IDENTITY-FREE +2 sub-class — automatic kill at
           char 2, no residue equation at all.  Integer-level class
           net: −1 −1 +1 +1 = 0.
    n = 5, class (4,0,1):  [C₂C₂C₁]− vs [C₁C₁]+ — kill iff ψ̄₂² = ψ̄₁.

**(D4) Cross-seed structure.**  Seeds t ∈ {0,1,2} (j₀(D_t) = s₁(u₁) +
t·e₀, W-D2(iv)†), ν = t − M invariant (K2-L6†).  Toggle pairings at
quantum δ: (t, K)↔(t+δ, K ∪ {mass-δ corrections}).  A = {0,2}: δ = 1
via C₂ (sign-flip pair; kill iff ψ̄₂·x_{t+1} = x_t — the Q-A0 identity
one index up) and δ = 2 via C₂C₂ (SAME-sign pair, count ±2 — auto-dead
at char 2 iff x_t = ψ̄₂²x_{t+2}, over F₂ iff x_t = x_{t+2} in K_m =
F₈).  The x_t are engine-determined, NOT tunable: the x-dependent legs
of the system can only be solved by realization, and the battery
measures them.

**(D5) THE DOUBLE-KILL SYSTEM (T1).**  A live row defeats (SURV-DISJ)
iff simultaneously:
  (B) every bottom-line (slot, β_min) group's residue multiset sums to
      0 in K_m — sufficient derived shape: every bottom group is a
      union of realized auto-dead door classes (D3) and residue-equal
      toggle pairs (D4);
  (C) the cascade leg fails: no principal correction-free cell exists
      (θ₀ = 0 towers — the F₂ cubic towers have this, probe census),
      or B_ĵ (the netted sum over ALL cells at the cascade slot) is
      zero or lands at w₀ > ŵ (killed at the cascade line).
Whether pool arithmetic realizes (B) ∧ (C) on one row is exactly the
open question the K2-RES box flags ("whether pool arithmetic realizes
an n = 5 window AT β_min is open") — the battery answers it on the S2.4
roster; no existence prediction is sealed either way (P5).

**(S2.4) T1 roster** (all char-2 unless marked; full live-row
enumeration, no caps): C3W2F/C3W2F2/C2W2F/C3W2Z = A{0,2} F₂-cubic
towers (m = 3, 3, 2, 3; the Zp entry is mixed characteristic);
C3T0F/C3DPF = A{0,1} controls; C3K2AF/C3E3F = the two stalled
K2-instrument specs verbatim ([(2,1,3),(2,1,1),(3,2,1),(2,1,1)] and
[(3,1,3),(2,1,1),(2,1,1),(2,1,1)]); C3OM3F/C2OMF = d₀ = 2 defaults
(A = {0,2} over F₄); C3F3Z = Zp p = 3 with FULL A = {0,1,2} (char-3
control: the +2 order-pair must SURVIVE there — teeth for the char-2
mechanism); C3OMX = the override tower, ψ₀ = y³ + y² + y + z over F₄
(z = the F₄ generator; all coefficients nonzero, A = {0,1,2}: BOTH
doors open at char 2, the order door identity-free).

## S3. T2 — the glued-stratum amplification system

Substrate: the SDW4G2F duplicate-book fiber (PE1 4.3; the only one in
332 traced rows): slot (4,0,0,0), fiber (dump(4,), pc = (0,0,1,2)),
two cells with IDENTICAL (t, K, I, pc, sign) distinguished only by
cross-window correction placement — windows [C₀@w₁, C₁@w₂] vs
[C₁@w₁, C₀@w₂].

**(D6) The duplicate condition, derived** (g₀ = 2, masses C₀ = 2,
C₁ = 1, fire at u ≥ 2): both orders legal across a two-window chain
with no interleaved promotion iff the first window's budget n₁ = 2 and
the second arrival adds exactly 2 units:
  variant A: [C₀@w₁] (2→0), arrival 2, [C₁@w₂] (2→1);
  variant B: [C₁@w₁] (2→1), arrival 2, [C₀@w₂] (3→1);
equal totals (mass 3, p = 0), equal final parked unit 1, one
correction each of {C₀, C₁} — identical books, same sign, SAME residue
(same digit product).  Requires BOTH digits (A = {0,1}, automatic for
g₀ = 2 over F₂: y² + y + 1 is the unique quadratic) and a dump or seed
arrival of exactly 2 units onto a parked-2 state.

**(D7) The amplification system.**  At char 2 a duplicate pair nets 0
outright (D2).  The witness group (5 cells) survived as net −1 = the
lone {C₁,C₁,C₁}-rider chain.  DEFEAT shape: a glued row where every
bottom group's total per-class count is EVEN — i.e. the duplicate
mechanism realized with the odd riders blocked (budget-starved: no
n = 3 window in the rider's chain) or themselves paired — plus (C) of
D5.  The battery enumerates ALL live rows (the committed selection
traced only 14 of SDW4G2F's 49) on: SDW4G2F verbatim, CDW3G2F (the
m = 3 truncation [(3,1,2),(2,1,1),(2,1,1),(2,1,1)] — new, in-class),
CDW4G2F2 (h₁ = 3 variant).  Duplicate detection: fiber key + (t, K,
sign) multiplicity ≥ 2 (CON-DUP: members share residue); glued census;
per-row (B) ∧ (C) evaluation.

## S4. T3 — the first (SD-YJ) towers (g₀ = 1 ∧ d₀ = 2)

The (SD-YJ) box (SURVDISJ_PROOF S6): at g₀ = 1, d₀ ≥ 2 any cascade-slot
companion C ∉ {Ĉ, X-mate} carries ≥ 1 Φ₀Y-edge and solves

    Σ_c defc_c = Y₂(C) ∈ {0,1},   each defc pinned by SD-L1†:
    Y₂ = 0: every correction defc = 0 — e_i = 1 ∧ Y-child ∧ FULL
            principal dump;
    Y₂ = 1: exactly one deficit-1 correction, rest defc = 0.

Class-pin check (the PE1 lesson, performed BEFORE realization): g₀ = 1
∧ d₀ = 2 is INSIDE the class — d₀ is the base residue degree (Φ₀ =
lift of an irreducible quadratic), ψ₀ is a linear read (g₀ = 1,
ψ₀(0) ≠ 0 automatic for y − c, c ≠ 0), gcd pins untouched.  No
committed roster ever carried such a tower (SURV_PROOF F-C); the box
is machine-dark.  Construction: NINE towers (S0 runner roster YJ*),
m ∈ {2,3,4}, kinds Fpt p ∈ {2,3} and Zp p = 2, INCLUDING flat-e₁
shapes [(2,1,1),(1,1,1),…] — e_i = 1 interior levels are exactly where
the Y₂ = 0 companion shape (defc = 0 ⟺ e_i = 1 ∧ Y ∧ full dump) can
exist at all — plus e₀ = 3 (YJ3DPF) and e₃ = 1 (YJT1F) variants.

The battery measures, per row: Φ₀Y-edge counts (first g₀ = 1
Y-instances ever), every cascade-slot companion with its (★) balance
Σ defc = Y₂ (CON-STAR — first d₀ = 2 exercise), the SD-L1 bound
(CON-DEF) and the defc = 0 shape analysis (CON-YJ0), cascade survival,
bottom survival, and the DK predicate.  Either outcome converts the
box to data: companions absent/harmless ⟹ first instance evidence FOR
extending SD-THM-A to d₀ ≥ 2; a materialized Φ₀Y-fed companion that
kills the cascade while the bottom dies ⟹ counterexample.

## S5. THE SEALED PREDICTION SHEET (falsifiable; sealed at commit 1, before any sealed-mode run)

Verdict families predicted ZERO violations across the entire battery:

* **P1 (the wall + the resurrection).**  CON-WALL: the committed pick
  returns degree 2 at (F₂, g = 3) and fp_irreducible raises on cubics.
  CON-AGREE: the patched pick equals the committed pick on every g ≤ 2
  case.  CON-ENG/CON-XWALK/CON-CONS: all extended towers pass every
  engine certificate; the recording walk matches ED.walk terminal-by-
  terminal; stage sums equal E1IH/Q1 — the g₀ = 3 regime is SOUND under
  the extension, killing the cost-wall narrative.
* **P2 (window calculus at g₀ = 3).**  CON-WIN: every window budget
  n ≤ 5; replay exact.  CON-INV: every realized Y-free drain lies in
  the D3 inventories.
* **P3 (factorization).**  CON-FACT: K2-L4 cellwise on junk-free cells
  — first exercise at g₀ = 3 and at g₀ = 1 ∧ d₀ = 2.  CON-CRIT: the
  SD-L6 polynomial/residue kill criteria agree on every group.
* **P4 (the doors kill).**  CON-EXCH: every realized (−2)-door partner
  pair (D3, A = {0,2}) carries equal residues (⟹ nets 0 at char 2).
  CON-DUP: every duplicate-book pair carries equal residues.
* **P7 (the (SD-YJ) algebra).**  CON-STAR: Σ defc = Y₂ on every
  cascade-slot cell at g₀ = 1 ∧ (STK).  CON-DEF: the SD-L1 bound holds
  on every g₀ = 1 correction (now including d₀ = 2).  CON-YJ0: every
  defc = 0 correction has the exact (SD-YJ) shape.

Measured questions with NO sealed prediction (the constructions'
targets — any answer is a finding):

* **P5 (T1).**  Whether any g₀ = 3 row realizes the (−2) door / order
  door AT β_min, and whether any row satisfies (B) ∧ (C) = DOUBLE
  KILL.  A DK row is a (SURV-DISJ) counterexample candidate, to be
  hand-verified before any claim.
* **P6 (T2).**  Whether duplicate-book fibers recur at the D6
  condition on the full row set, and whether any glued row reaches the
  D7 even-parity defeat.
* **P8 (T3).**  Whether Φ₀Y-edges / Φ₀Y-fed cascade companions
  materialize at g₀ = 1 ∧ d₀ = 2, and whether the cascade ever dies
  there.  (The p = 3 tower doubles as the char-blind control.)

Teeth: the C3F3Z control must show the full-A order-pair SURVIVING at
p = 3 (else the char-2 reading of D2 is wrong); the A = {0,1} controls
must show NO in-window exchange class.

## S6. VERDICT (from artifacts; appended at commit 2)

**PENDING AT SEAL.**

## Fences

F-A. Everything measured is INSTANCE grade; consumption caps ride (the
     binding cap = the W arc, 0/2 CLEAN).  The proved content of this
     note = the S1 engine finding (code-level, inspectable), the D1/D3/
     D6 finite inventories (finite checks, displayed), and D2 (one-line
     field arithmetic).  No lemma of the SURV corpus is upgraded here.
F-B. The pick extension is a disclosed construction device, scoped to
     g = 3 picks + one named override; committed engines byte-untouched
     (CON-PIN); every extended tower re-verified by the ENGINE'S OWN
     certificates (CON-ENG), not by this unit's assertions.
F-C. g₀ = 4 is NOT probed (needs a degree-4 irreducibility test; out of
     scope).  Interior g ≥ 2 untouched program-wide.
F-D. The DK predicate is the claim's verbatim reading (bottom stratum
     at β_min; cascade slot at the cascade line via w₀(B_ĵ) = ŵ); rows
     with the cascade cell ABSENT (θ₀ = 0) are labeled DK-ABSENT and
     argued separately if they occur — the claim's cascade leg is
     vacuously dead there, which a hostile reader may contest; both
     readings reported.
F-E. Design probes disclosed at S0; sealed quantities untouched
     pre-seal.  Two-commit discipline: commit 1 = this note (S6
     PENDING) + runner; commit 2 = S6 verdict + output + results json.
