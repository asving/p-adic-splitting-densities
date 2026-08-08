# CODEX LEG 1 (wave-21 queue item (1)) — THE (W-MULT-DCX-m) SECOND-ROUND CLAUSE (SRC-m): TIER-0 DELIVERED AND ORCHESTRATOR-VERIFIED — 2026-08-08 campaign

## S0. Charter and provenance

Unit: the first Codex leg of the wave-21 closure program's post-reset queue
(ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md`, "CODEX WINDOW RESET" entry,
queue item (1)): a PROVER-FIRST leg on the (W-MULT-DCX-m) family — Q2's
grade cap, the [ILN]† S4.7 carry-over ("a proof of (RM-m) with a
second-round clause would close both II-legs and DCX at once"), standing as
the displayed conditional COND-B ([RMG] S7.2) since the RM-GEN acceptance.

- Brief: `/tmp/wmultdcx_brief.txt`, 194,171 chars — self-contained pastes
  A–G @ 3c2ac60 ([ILN] S0–S5 verbatim incl. the (RM-m) box, S4.4–S4.7;
  [RMG] S0/S5–S8 incl. THEOREM RM-GEN + L-CANON + L-VNZ + LAW-DCX-(m+1);
  WMULTDCX in full; E/S/SD statement heads; the [RMG] acceptance block).
  Committed copy: `wmultdcx_brief_2026-08-08.txt` (this directory).
- Launch 1: session 019fdfc4-9333-7f53-9b51-d7a1d8d4115e, model
  gpt-5.6-sol, reasoning effort NONE (config accident, caught at launch) —
  produced NO final message; superseded, untrusted, log archived in /tmp.
- Launch 2 (run of record): session 019fdfc8-4362-7cb3-8846-e15f4ecbdffe,
  model gpt-5.6-sol, reasoning effort HIGH, launched 05:11:11 UTC, exited
  ~05:17 UTC (≈6 min), 86,607 tokens, log
  `/tmp/codex_wmultdcx_hi_1786165871.log` (225,699 bytes; streamed and
  reprinted final messages byte-identical). Raw final message committed as
  `CODEX_WMULTDCX_2026-08-08_raw.md` (this directory).
- Decorrelation discipline: the orchestrator derived a verification key
  (weights, margins, termination route, collision inventory, the export
  check) BEFORE reading any Codex output
  (`/tmp/codex_wmultdcx_scaffold.md`, 05:14 UTC, pre-verdict). The
  adjudication below checks Codex's steps against that key AND against the
  pasted accepted statements, display by display.

## S1. VERDICT (orchestrator adjudication, not Codex's self-grade)

**TIER-0 — CONFIRMED.** (SRC-m) is proved, all four clauses (a)–(d), on
T-scope(m), and STRICTLY MORE than the chartered prize:
**LAW-DCX-(m+1) is NOT consumed** — the TIER-0 charter allowed it as an
explicit hypothesis wherever residue-survival content was needed, and none
is needed. Every re-entrant second-round term lands STRICTLY ABOVE the
read line (margin ≥ 2h_{n−1} > 0), and the flat e_{n−1} = 1 cascade
terminates by strict polynomial-degree descent. Family form:

    (7.1)   T-scope(m)  ⟹  (W-MULT-DCX-m)          [proved, this leg]
    (7.2)   LAW-DCX-(m+1) ⟹ (W-MULT-DCX-m) on T-scope(m)   [a fortiori]

**GRADE (honest): Codex-derived, orchestrator-verified, ATTEMPT GRADE,
0 hostile passes — NOT accepted.** The W arc's own Codex-VERIFIER leg is a
SEPARATE queue item and is NOT satisfied by this prover leg. Verification
performed: every numbered display (1.1)–(7.2) re-derived by hand by the
orchestrator against the pasted [ILN]†/[RMG]† statements (S4 below records
the checks and the two places where Codex's route improves on the
pre-derived key). Zero critical errors found; zero justification gaps left
open; two consumption-wording compressions noted at S4(v), both harmless.

## S2. The statement proved

(SRC-m), as posed in the brief (assembled from [ILN]† S4.6/S4.7; top rung
n, engine level n−1, family index m = n−1, DCX_n = DCX_{m+1}): Setting =
[ILN]† S4.6 Cases II-2/II-3 ON DCX_n — g_{n−1} = 1 tower, E₁ᴵᴴ ≠ 0, engine
calls E₀ᴵᴴĈ = R⁰ + Q⁰Φ and E₁ᴵᴴĈ = R¹ + Q¹Φ (Φ := Φ_{n−1}, Ĉ := Ĉ_{n−1}),
Q¹ ≠ 0 landing at Φ-slot k+2 = e_{n−1} (II-2, k := T_n − e_{n−1}) or at
slot 1 ≥ e_{n−1} = 1 (II-3); fire Φ^{e_{n−1}} = Φ_n − Ĉ on the overflow
(and induced rounds). TO PROVE: (a) w_n(E₀ⁿᵉʷ) = B_n with the read at B_n
unchanged, = z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1}); (b) the −Q¹ joining the
slot-(T_{n+1}+1) digit keeps that slot's line ≥ Γ″ + h_n or contributes
read 0 at Γ″; (c) the e_{n−1} = 1 cascade terminates with total
contribution obeying (a); (d) val(P) = z̄^δ·val(φ_γ)·val(φ_{γ′}) and the
(P-DS) exports of S4.6 hold ON DCX_n — i.e. (W-MULT-DCX-m).

## S3. The verified derivation (full transcription; per-display marks)

Transcribed from the Codex final message in corpus notation; each display
carries the orchestrator's mark: [VER] = re-derived and checked against
the named pasted source. Labels PROVED-HERE / CONSUMED are Codex's, all
audited. Numbering is Codex's own ((1.1)–(7.2), SRC-L1–SRC-L13).

### §1 Notation and consumed inputs

Put m = n−1 and abbreviate Φ := Φ_{n−1}, Ĉ := Ĉ_{n−1}, e := e_{n−1};
a := w_{n−1}(Φ) = e_{n−2}γ_{n−1}; G := γ_n = ea + h_{n−1}; b := B_{n−1},
B := B_n = eb + T_nG.  [VER: a = e_{n−2}γ_{n−1} needs g_{n−2} = 1, forced
by E₁ᴵᴴ ≠ 0 ⟹ CII_{n−1} ⟹ g_{n−2} = 1 — the (P-DS)/CII clause, [ILN] S4.3;
the same consumption the corpus itself makes at the S4.4 weights paragraph.
G = γ_n = e_{n−1}e_{n−2}g_{n−2}γ_{n−1} + h_{n−1} = ea + h_{n−1} at
g_{n−2} = 1 — the S0.1 recursion. B_n = e_{n−1}B_{n−1} + T_nγ_n is the
S4.6 line identity.]

Engine inputs (IH (P-DS) at rung n−1): w_{n−1}(E₀ᴵᴴ) = b,
R_{n−1,b}(E₀ᴵᴴ) = v⁰ ≠ 0, λ₁ := w_{n−1}(E₁ᴵᴴ) ≥ b − a.  [VER: verbatim the
(P-DS) clauses; v⁰ ≠ 0 as a product of units, and independently forced by
L-VNZ.]

Canonical engine divisions E_iᴵᴴĈ = Rⁱ + QⁱΦ (i = 0,1). By RM-GEN:

    (1.1)  w_{n−1}(R⁰) ≥ b + G,      w_{n−1}(Q⁰) ≥ b + G − a
    (1.2)  w_{n−1}(R¹) ≥ λ₁ + G ≥ b + G − a
    (1.3)  w_{n−1}(Q¹) ≥ λ₁ + G − a ≥ b + G − 2a
    (1.4)  R_{n−1,b+G}(R⁰) = z_{n−1}^{ε′}·v⁰·τ_{n−1},
           τ_{n−1} = ε_{n−1}(G)^{−1}c_{n−1}
    (1.5)  w_{n−1}(R⁰) = b + G  (attained: every factor in (1.4) ≠ 0)

[VER: (1.1)–(1.4) are the four [RMG] box clauses (C-W_R)/(C-W_Q)/(C-READ)
verbatim at λ = b resp. λ = λ₁, with w_{n−1}Φ = a; deg Rⁱ, deg Qⁱ < deg Φ
per the box + L-CANON. (1.5): a nonzero read at ordinate b+G forces the
weight exactly (all digits of a higher-weight polynomial sit strictly
above the b+G line, read 0) — sound. All RM-GEN applications pinned on
T-scope(n−1); g_{n−1} = 1 holds in the II-cases, which is RM-GEN's g_m = 1
hypothesis at the called level m = n−1.]

Labels: (1.1)–(1.5) CONSUMED — [RMG], ACCEPTED, together with L-VNZ; the
E_iᴵᴴ data CONSUMED — [ILN] (P-DS).

### §2 SRC-L1 — line of a coefficient term [PROVED-HERE]

If F occurs at Φ-slot j inside a level-n digit, its level-n line is

    (2.1)  L_n(F, j) := e·w_{n−1}(F) + jG,

and if deg F < deg Φ then, alone as a level-n polynomial,

    (2.2)  w_n(F) = e·w_{n−1}(F)

(single slot-0 digit).  [VER: direct from the weight definition
w_n(f) = min_j (e_{n−1}w_{n−1}(f_j) + jγ_n) — displayed inside [RMG]'s
L-VNZ proof as "L-CELL(i) / the S0.2 mirror recursion".]

### §3 Case II-2 (e ≥ 2; on DCX_n: k + 2 = e, Q¹ ≠ 0)

    (3.1)  k = e − 2,  T_n = 2e − 2,  e ≥ 2;   (3.2)  B = eb + (2e−2)G.

[VER: k := T_n − e and k+2 = e ⟺ T_n = 2e−2; matches the S4.7 outer bound
(both s_n-values = e−1). Pre-substitution slot-T_{n+1} coefficient, from
the [ILN] S4.6 II-2 display verbatim:]

    (3.3)  −R⁰Φ^k − (Q⁰+R¹)Φ^{k+1} − Q¹Φ^e.

**SRC-L2 (the one-round principal term has the required read)
[PROVED-HERE].**

    (3.4)  L_n(R⁰,k) = e(b+G) + (e−2)G = eb + (2e−2)G = B     [VER: exact]
    (3.5)  L_n(Q⁰,k+1) ≥ e(b+G−a) + (e−1)G = B + (G−ea) = B + h_{n−1}
    (3.6)  L_n(R¹,k+1) ≥ B + h_{n−1}                          [VER: both]

So in F_pr := −R⁰Φ^k − (Q⁰+R¹)Φ^{k+1} (3.7) only −R⁰Φ^k sits on the line
B. Since δ_n^pl = 1: s_n(B) = T_n − e = k (3.8) [VER: the S4.6 L1-grid
display verbatim]; among digit slots 0..e−1 only k is on the grid. Hence

    (3.9)   R_{n,B}(F_pr) = ε_{n−1}(b+G)·(−z_{n−1}^{ε′}v⁰τ_{n−1})
    (3.10)  ε_{n−1}(b)ε_{n−1}(G) = z_{n−1}^{ε′}ε_{n−1}(b+G)   [EXP-KIT(b)]
    (3.11)  R_{n,B}(F_pr) = −v⁰ε_{n−1}(b)c_{n−1} = z_n·v⁰·ε_{n−1}(b)
                          = z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1})

[VER: slot weight at slot k on line B is (B − kG)/e = b + G ✓; (3.10) is
EPS-MULT with carry ⌊(s_{n−1}(b)+s_{n−1}(G))/e_{n−2}⌋ = ε′ — the SAME
floor as (C-READ)'s ε′, so the carry cancels exactly; τ_{n−1} contributes
ε_{n−1}(G)^{−1}c_{n−1}; z_n = −c_{n−1} (WELL-DEF-(n)(ii)); δ_n^pl = 1.
This is byte-for-byte the corpus's own II-1 "ε′-carry/canonical-lift
CANCELLATION", now applied at the DCX corner. EQ12-ADD and EXP-KIT(b)
CONSUMED [IL]/[ILN]; the line arithmetic PROVED-HERE — all re-derived.]

**SRC-L3 (the overflowing Q¹-term is already strictly above B)
[PROVED-HERE].**

    (3.12)  L_n(Q¹,e) ≥ e(b+G−2a) + eG = B + 2G − 2ea = B + 2h_{n−1}.

[VER: exact; = key computation (3)-adjacent. The overflow is a DEGREE
problem, not a line problem.]

**SRC-L4 (the second round closes after one further engine division)
[PROVED-HERE + CONSUMED].** Substitute Φ^e = Φ_n − Ĉ (WELL-DEF-(n)(ii)):

    (3.13)  −Q¹Φ^e = −Q¹Φ_n + Q¹Ĉ.

If Q¹ ≠ 0, one more engine call: Q¹Ĉ = R² + Q²Φ (3.14) (else R² = Q² = 0).
With q₁ := w_{n−1}(Q¹), RM-GEN gives

    (3.15)  w_{n−1}(R²) ≥ q₁ + G ≥ b + 2G − 2a
    (3.16)  w_{n−1}(Q²) ≥ q₁ + G − a ≥ b + 2G − 3a
    (3.17)  L_n(R²,0) ≥ e(b+2G−2a) = B + 2h_{n−1}
    (3.18)  L_n(Q²,1) ≥ e(b+2G−3a) + G = B + 3h_{n−1}

[VER: all four exact — (3.17)/(3.18) are the pre-derived key computations
(1) and (2) verbatim.] Because e ≥ 2,

    (3.19)  deg(R² + Q²Φ) < 2·deg Φ ≤ e·deg Φ = deg Φ_n,

so R² + Q²Φ is a valid Φ_n-digit and NO further substitution fires. [VER:
deg R², deg Q² < deg Φ from the RM-GEN box/L-CANON (which needs (Ĉ1)
deg Ĉ < deg Φ — a WELL-DEF-(n)(ii) clause); deg Φ_n = e·g_{n−1}·deg Φ =
e·deg Φ by the S4.2 degree telescope at g_{n−1} = 1. Cleaner than the
pre-derived key's slot argument; verified.] The final slot-T_{n+1} digit is

    (3.20)  E₀ⁿᵉʷ = F_pr + R² + Q²Φ,
    (3.21)  w_n(R² + Q²Φ) > B          [min of (3.17),(3.18)]
    (3.22)  w_n(E₀ⁿᵉʷ) = B             [READ-ADD-(n) + (3.11) ≠ 0]
    (3.23)  R_{n,B}(E₀ⁿᵉʷ) = z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1}).

**Clause (a) holds in II-2 — no residue cancellation, no LAW-DCX.** [VER:
READ-ADD-(m) is generic in m and applies at level n to the SUM (3.20),
which also disposes of the slot collisions (k = 0 at e = 2: R² shares slot
k; slot 1 = k+1 grid-collision at e = 3): the colliding parts sit in the
strictly-above summand, killed additively — the pre-derived key's
collision inventory (6), handled uniformly.]

**SRC-L5 (the new top-slot contribution satisfies the E₁ bound)
[PROVED-HERE].** The −Q¹Φ_n of (3.13) joins slot T_{n+1}+1. deg Q¹ < deg Φ
gives w_n(Q¹) = e·w_{n−1}(Q¹) ≥ e(b+G−2a) (3.24); the (P-DS) requirement
is B − e_{n−1}γ_n = B − eG (= B − w_n(Φ_n), (3.25), at g_{n−1} = 1); and

    (3.26)  e(b+G−2a) − (B−eG) = 2G − 2ea = 2h_{n−1} > 0,

so adding −Q¹ to the pre-existing E₁-digit (whose bound is the consumed
S4.6 display) preserves

    (3.27)  w_n(E₁ⁿᵉʷ) ≥ B − eG.

[VER: (3.26) exact = the pre-derived key computation (3). NOTE the margin
2h_{n−1} is STRUCTURAL: it survives even when Q¹'s weight floor is
attained (the W-D5/286-of-286 tightness stratum) — checked by hand at
λ₁ = b − a, q₁ = λ₁ + G − a exactly. This is why no DEV-at-depth
residue-survival input is needed; see S4(iv).]

### §4 Case II-3 (e = 1): the flat cascade

    (4.1)  e = 1, T_n = 0, B = b, G = a + h_{n−1};
    (4.2)  E₀,pre = E₀ᴵᴴ − R¹ − Q¹Φ,  E₁,pre = E₁ᴵᴴ   [S4.6 II-3 verbatim]
    (4.3)  w_{n−1}(R¹) ≥ b − a + G = B + h_{n−1} > B
    (4.4)  w_n(E₀ᴵᴴ − R¹) = B
    (4.5)  R_{n,B}(E₀ᴵᴴ − R¹) = ε_{n−1}(B)·v⁰ = z_n^0·v⁰·ε_{n−1}(B_{n−1})

[VER: at e = 1, B_n = B_{n−1} numerically; s_n(B) = T_n = 0; single slot;
matches the corpus II-3 C₀ display verbatim.]

**SRC-L6 (strict degree descent terminates the flat cascade)
[PROVED-HERE].** Recursively, while Q^r ≠ 0: Q^rĈ = R^{r+1} + Q^{r+1}Φ
(4.6), canonical division by monic Φ. With d := deg Φ: deg Ĉ < d ((Ĉ1))
and deg Q^r < d, so if Q^{r+1} ≠ 0,

    (4.7)  deg Q^{r+1} = deg(Q^rĈ) − d = deg Q^r + deg Ĉ − d < deg Q^r

(O a domain). Hence ∃ N ≥ 1 with Q^{N+1} = 0 (4.8): **clause (c)'s
termination.** [VER: sound — deg(Q^rĈ) = deg Q^r + deg Ĉ over a domain;
if deg(Q^rĈ) < d the canonical quotient is 0, else deg Q^{r+1} =
deg(Q^rĈ) − d exactly since deg R^{r+1} < d. STRICTLY STRONGER than the
pre-derived key's route (5) (π-adic convergence of an infinite cascade):
the cascade is FINITE. The load-bearing input is (Ĉ1), a proved
WELL-DEF-(n)(ii) clause.]

**SRC-L7 (exact finite form) [PROVED-HERE].** At e = 1, Φ = Φ_n − Ĉ, and
induction on the rounds gives

    (4.9)   −Q¹Φ = (Σ_{r=1}^{N} (−1)^r Q^r)·Φ_n + Σ_{r=1}^{N} (−1)^{r+1} R^{r+1}
    (4.10)  E₀ⁿᵉʷ = E₀ᴵᴴ − R¹ + Σ_{r=1}^{N} (−1)^{r+1} R^{r+1}
    (4.11)  E₁ⁿᵉʷ = E₁ᴵᴴ + Σ_{r=1}^{N} (−1)^r Q^r,

both of degree < deg Φ_n = deg Φ (4.12, e = g_{n−1} = 1). [VER: the
alternating identity re-derived by hand through r = 3; the stage-j
residual is (−1)^{j+1}Q^{j+1}Φ, vanishing at j = N; digit uniqueness makes
(4.10)/(4.11) THE development.]

**SRC-L8 (every re-entrant flat-cascade remainder is strictly above B)
[PROVED-HERE].** q_r := w_{n−1}(Q^r):

    (4.13)  q₁ ≥ B − a + h_{n−1}
    (4.14)  q_{r+1} ≥ q_r + G − a = q_r + h_{n−1}     [RM-GEN on (4.6)]
    (4.15)  q_r ≥ B − a + r·h_{n−1}
    (4.16)  w_{n−1}(R^{r+1}) ≥ q_r + G ≥ B + (r+1)h_{n−1}
    (4.17)  w_n(R^{r+1}) = w_{n−1}(R^{r+1}) > B        [e = 1, deg < d]

Finite sum ⟹ cascade part has w_n > B; with (4.4) and READ-ADD:

    (4.18)  w_n(E₀ⁿᵉʷ) = B
    (4.19)  R_{n,B}(E₀ⁿᵉʷ) = z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1}),  δ_n^pl = 0.

**Clauses (a) + (c) hold in II-3.** [VER: all displays exact; the weights
climb h_{n−1} per round — the key's route (5) margin, now finite.]

**SRC-L9 (the flat-cascade top coefficient preserves its bound)
[PROVED-HERE].** Required bound B − eG = B − G = B − a − h_{n−1} (4.21);
every cascade quotient has w_n(Q^r) = q_r ≥ (B−G) + 2h_{n−1} > B − G
(4.22); E₁ᴵᴴ has w_n = λ₁ ≥ b − a = (B−G) + h_{n−1}; so

    (4.24)  w_n(E₁ⁿᵉʷ) ≥ B − G = B − eG.

[VER: exact; consistent with the corpus's PE-N1 supplement ("with h_{n−1}
to spare").]

### §5 SRC-L10 — the slot-(T_{n+1}+1) digit is harmless [PROVED-HERE]

In both cases w_n(E₁ⁿᵉʷ) ≥ B − eG = B − w_n(Φ_n) (5.1). At level n+1,
Γ″ = e_nB + T_{n+1}γ_{n+1} (5.2), and the slot-(T_{n+1}+1) line is

    (5.3)  ≥ e_n(B − eG) + (T_{n+1}+1)γ_{n+1} = Γ″ + γ_{n+1} − e_n·eG
         = Γ″ + h_n,

using γ_{n+1} = e_n·w_n(Φ_n) + h_n = e_n·eG + h_n (5.4). If e_n ≥ 2 the
slot T_{n+1}+1 is OFF the level-(n+1) grid (spacing e_n); if e_n = 1 it is
on-grid but ≥ h_n > 0 strictly above Γ″ — READ-ADD kills the read.
**Clause (b) holds.** [VER: exact; verbatim the mechanism of the corpus's
II-1 top-level display.]

### §6 Completion — SRC-L11 (top read and multiplicative value), SRC-L12 ((P-DS) exports)

    (6.1)  P = E₀ⁿᵉʷΦ_n^{T_{n+1}} + E₁ⁿᵉʷΦ_n^{T_{n+1}+1},
           deg E_iⁿᵉʷ < deg Φ_n (6.2)
    (6.3)  w_{n+1}(P) = Γ″;  (6.4)  s_{n+1}(Γ″) = T_{n+1} − δe_n  [EQ12-ADD]
    (6.5)  val(P) = z̄^δ·ε_n(B)·R_{n,B}(E₀ⁿᵉʷ)
                  = z̄^δ·ε_n(B)·z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1})
    (6.6)  val(P) = z̄^δ·∏_{j=1}^{n} z_j^{δ_j^pl}·∏_{j=1}^{n} ε_j(B_j)
           [v⁰ = the IH certified read, substituted]
    (6.7)  val(P) = z̄^δ·val(φ_γ)·val(φ_{γ′})
           [CONSUMED: EPS-MULT per level (EXP-KIT(b)) + L6-(n) — the same
            conversion the corpus makes at Case I/II-1]

**Clause (d)'s multiplicative law holds.** [VER: (6.5)–(6.6) algebra
re-checked; (6.7) is the accepted S4.5 step verbatim. E₀ⁿᵉʷ sits at grid
slot δ with slot weight B_n, on-line; the other support slot is disposed
by SRC-L10 — so the level-(n+1) read is a SINGLE nonzero coefficient at
slot δ, and w(P) = Γ″ = γ+γ′: (P-WM) in full.]

(P-DS) exports ON DCX_n, all verified [SRC-L12]: support ⊆
{T_{n+1}, T_{n+1}+1} (6.8); deg E_iⁿᵉʷ < deg Φ_n (6.9); w_n(E₀ⁿᵉʷ) = B_n
(6.10); certified read R_{n,B_n}(E₀ⁿᵉʷ) = z_n^{δ_n^pl}·v⁰·ε_{n−1}(B_{n−1})
(6.11); w_n(E₁ⁿᵉʷ) ≥ B_n − e_{n−1}γ_n (6.12); E₁ⁿᵉʷ ≠ 0 only within
II-2/II-3 ⊆ CII_n (the containment, which is all that is consumed
downstream — the PE3-N1 precision note); E₁ⁿᵉʷ = 0 by cancellation
allowed.

### §7 SRC-L13 — family-level conclusion

Simultaneous induction by rung: rung one has no DCX locus (DCX-(1) = ∅);
given the FULL (P-WM)/(P-DS) package at the truncated rung, Cases I/II-1
and the off-corner parts of II-2/II-3 are the consumed [ILN] S4.5–S4.6
argument, and ON DCX_n SRC-L2–L12 supply the missing clause, consuming
RM-GEN only at engine level n−1. The package therefore propagates ACROSS
DCX whenever every called engine level satisfies its T-scope; in family
notation m = n−1:

    (7.1)  T-scope(m) ⟹ (W-MULT-DCX-m).

LAW-DCX-(m+1) is not used; its only role would be to characterize WHEN
Q¹ ≠ 0, and the argument works for either value. [VER: the simultaneous
induction is sound — with the DCX corners closed at every level, the S4.4
inner-pair-off-DCX-(n−1) proviso becomes vacuous and the rung-(n−1)
package is available for ALL pairs; T-scope(m) ⟹ T-scope(m′) for m′ ≤ m
(monotone), so the single pin T-scope(m) covers every called level.]

Codex dependency list (audited, accurate): [RMG] ACCEPTED (four clauses +
degree bounds + L-VNZ, on T-scope); [ILN] ACCEPTED (tower identities,
WELL-DEF incl. (Ĉ1)–(Ĉ3), degree telescope, READ-ADD, EQ12/EXP-KIT/L6,
CASE-SPLIT, the (P-DS) package); [IL]/[IL3] through the pasted packages.
NOT consumed: LAW-DCX-(m+1); W-D0–W-D7/PID†; E-THM/S-THM/SD-THM-A;
instance evidence.

## S4. Orchestrator verification record

(i) **Pre-derived key vs the delivered route.** The scaffold key
(committed in /tmp at 05:14 UTC, before any Codex output was read)
predicted TIER-0 with LAW-DCX not needed, and computed independently: the
R²-slot-0 margin 2h_{n−1} (= (3.17)), the Q²-slot-1 margin 3h_{n−1}
(= (3.18)), the −Q¹ export margin 2h_{n−1} (= (3.26)), the one-extra-round
II-2 closure, the collision inventory (k = 0, k = 1, e = 2 — all killed by
READ-ADD), and the exports. Codex's derivation agrees with every one of
these numbers. Two route improvements over the key, both verified: (3.19)
closes the II-2 round by DEGREE (< 2·deg Φ ≤ deg Φ_n) rather than by slot
position; SRC-L6 terminates the flat cascade FINITELY by strict degree
descent (deg Q^{r+1} = deg Q^r + deg Ĉ − d < deg Q^r via (Ĉ1)) where the
key had only π-adic convergence of a possibly-infinite cascade.

(ii) **Source checks.** Every CONSUMED item was located verbatim in the
pastes and checked at its use site: the (RM-m)/RM-GEN four clauses +
L-CANON + L-VNZ ([RMG] S0.2/S0.3/S5.2 + the acceptance block); (Ĉ1)–(Ĉ3)
and Φ_{m+1} = Φ_m^{e_m} + Ĉ_m with z_{m+1} = −c_m, τ_m = ε_m(γ_{m+1})^{−1}c_m
([ILN] S4.1 WELL-DEF-(n)(ii)); READ-ADD-(m) generic; EQ12-ADD; EXP-KIT(b)
with carry = ε′'s floor; the S4.3 (P-DS)/CII clauses incl. w_r(E₁) ≥
B_r − e_{r−1}γ_r and E₁ ≠ 0 ⟹ CII_r ⟹ g_{r−1} = 1; the S4.4 case split +
weights paragraph; the S4.6 II-2/II-3 one-round developments (3.3)/(4.2);
the S4.7 DCX_m definition (second-round overflow, Q ≠ 0) and outer bound
(T_n = 2e−2 in II-2); s_n(B_n) = T_n − δ_n^pl·e_{n−1}; the S4.5/II-1 top
value extraction. No consumed display was found misquoted or overreached.

(iii) **Arithmetic.** All 40+ numbered displays re-derived by hand;
(3.4)/(3.5)/(3.6)/(3.12)/(3.17)/(3.18)/(3.26)/(4.13)–(4.17)/(4.22)/(5.3)
each reduce to G − ea = h_{n−1} and the line identity — all exact, no
inequality is used beyond its stated direction.

(iv) **Why the corpus's pricing overshot (the S9 "DEV-at-depth" box).**
The priced hard core was a depth-≥1 read clause on the line (residue
survival on DCX, where W-D5's Q¹-weight floor is attained — the sharpness
that defines the locus). The resolution: the TIGHT object is Q¹, but Q¹
never needs a read — it moves whole to the T_{n+1}+1 slot with structural
margin 2h_{n−1} (computed at exact tightness in S3 §3 SRC-L5), and its
re-entrant image Q¹Ĉ gains a FRESH engine round (+γ_n, −a ⟹ net +h_{n−1}
per round). All second-round mass is strictly above every read line.
LAW-DCX/PID†/(SURV-(m+1))/(EMPTY-(m+1)) remain what they always were —
the sharp characterization of the LOCUS (independent interest: emptiness
corollaries, instance prediction) — but they are OFF the (W-MULT-DCX-m)
critical path.

(v) **Minor notes (no grade impact).** (a) SRC-L9 says "the consumed
(P-DS) bound w_n(E₁ᴵᴴ) ≥ B − G"; the consumed bound is w_{n−1}(E₁ᴵᴴ) ≥
b − a, which at e = 1 gives w_n = λ₁ ≥ b − a = (B−G) + h_{n−1} — stronger
than quoted; compression, not error. (b) The dependency list cites "L6"
inside (6.6)'s substitution; the substitution itself is the IH (P-DS)
certified-read display, L6 entering only at (6.7) — attribution
compression, the corpus's own S4.5 wording does the same.

## S5. Honest conditionality (what (7.1) rests on)

- **T-scope(m)** at every called engine level (absorbed into the single
  pin by monotonicity): d₀ = 1 ∨ (e₀ ≥ 2 ∧ e_i ≥ 2 for 1 ≤ i ≤ m−1). OFF
  T-scope the engine's four clauses are open ([RMG]'s fenced flat
  corners) and this leg says nothing.
- **The [ILN]† acceptance scope rides through**: the harness tower class,
  standard-lift, canonical lifts only ((ITER-LAW-LIFT) propagates), and
  the S7 per-rung ledger — in particular rung-2 consumptions ride
  [IL3]†'s attempt grade, exactly as they do for (ITER-LAW-n) itself.
  This leg ADDS no new class pins.
- **Grade**: attempt grade, 0 hostile passes, NOT accepted. The pending
  W-arc Codex-verifier leg (queue item (3) family) should now take THIS
  derivation as its target text alongside the WMULTDCX note.
- The g_{n−1} = 1 and g_{n−2} = 1 hypotheses are internal to the II-cases
  (CASE-SPLIT + CII), not extra pins.

## S6. Consequences + proposed annex text (DRAFT ONLY — applied at acceptance per the incorporation convention)

1. **COND-B upgrade ([RMG] S7.2 / S8 row 13; ledger-block style, note not
   edited).** Draft: "SRC RESOLVED (2026-08-08, Codex leg 1,
   orchestrator-verified, attempt grade): the second-round clause (SRC-m)
   is PROVED on T-scope(m) WITHOUT LAW-DCX-(m+1) — every re-entrant term
   strictly above the line (margin ≥ 2h_{m}), flat cascade finite by
   degree descent. COND-B's IF-clause is dischargeable: T-scope(m) ⟹
   (W-MULT-DCX-m). LAW-DCX-(m+1) stays a sealed conjecture, now OFF the
   W-MULT critical path (locus characterization only)."
2. **[ILN]† S4.7/S7 upgrade (same convention).** Draft: "On T-scope(m),
   the OPEN family (W-MULT-DCX-m) is CLOSED at attempt grade
   (CODEX_WMULTDCX_2026-08-08.md): the S4.6 Cases II-2/II-3 extend ON
   DCX_n by the second-round development, (P-WM)/(P-DS) exports intact.
   Jointly with [RMG]/COR-A: (ITER-LAW-n) holds on T-class(n) WITHOUT the
   DCX-(n) exclusion, modulo the S7 non-(RM) residuals." (T-class(n) =
   ∧_m T-scope(m) over called levels = d₀ = 1 ∨ (e₀ ≥ 2 ∧ e_i ≥ 2,
   i ≤ n−2).)
3. **Downstream**: Q2's grade cap moves — the W-arc's remaining hard core
   ((SURV-(m+1))/(EMPTY-(m+1))/LAW-DCX liveness) is re-scoped to the
   locus program; GRTJC's (DMULT) conditionality row can cite (7.1) at
   attempt grade after the hostile arc.
4. **Owed next**: hostile passes on THIS text (PE + the Codex verifier
   leg on the raw derivation); fold into PROJECT_STATE at the next ROOT.

## S7. Artifacts

- `CODEX_WMULTDCX_2026-08-08_raw.md` — the Codex final message, verbatim.
- `wmultdcx_brief_2026-08-08.txt` — the launched brief (pastes A–G).
- `/tmp/codex_wmultdcx_hi_1786165871.log` — full run log (brief echo +
  message twice, diff-identical); `/tmp/codex_wmultdcx_1786165629.log` —
  launch-1 (effort-none, no output); `/tmp/codex_wmultdcx_scaffold.md` —
  the pre-verdict orchestrator key (quoted in S4(i)).
- Instance evidence standing (never proof): 132/132 at m = 2; 16
  sharp-DCX_2 pairs per rung-4 instance law-exact; 0/10,484 W-arc
  law-keyed stress; 286/286 minimal-depth (the tightness stratum that
  makes SRC-L5's structural margin the load-bearing observation).
