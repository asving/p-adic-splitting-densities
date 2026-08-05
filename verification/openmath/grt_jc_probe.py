#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grt_jc_probe.py -- GRT J-C INSTRUMENT: the carry-algebra junction probe
(W-6..W-9), Phase 0 of docs/in-progress/GRTJC_BRIEF_2026-08-05.md.

MEASURE, DO NOT COMPOSE.  Nothing here is a proof step; no .lean is touched;
no gate fires; BLOCKED-ON-CARRIER-TIE stands.  Two-commit seal: commit 1 =
this runner + the note's preregistration BEFORE the battery; commit 2 = the
verdict written FROM the artifacts.

============================ WHAT IS BEING MEASURED ==========================
(J-C)(ii) (blueprint S2.3): for every level m with E_{m+1} := e_0...e_m > 1,
the fibred carrier (+_{gamma in Z/E} K_{m+1} u_gamma, u_g u_g' =
c_{m+1}(g,g') u_{g+g'}) built from GRT-1's canonical D(T)/c_T is isomorphic,
via u_gamma |-> [phi_gamma]_TC through TC-1 (localize) / TC-2 (gauge p |-> 1)
/ TC-3 (residue quotient by psi), to the K_{m+1}-span A(T) of the anchor
classes in the degree-0 component of the ACTUAL graded ring gr(w_{m+1}) --
with A(T)'s multiplication gr's OWN, never c_T (THE TAUTOLOGY FENCE, OB-5).

INDEXING (the truncation identity, machine-checked as P0-TRUNC).  The
level-(m+1) analysis of a tower is the FULL top-level analysis of the tower
truncated to reads 0..m.  So a probe ROW is a truncated tower T with
NR := m+1 reads, and:
    E        := e_0 * ... * e_{NR-1}          (the brief's E_{m+1})
    K        := T.K[NR]                       (the brief's K_{m+1})
    w        := T.wlev(NR, .)                 (the brief's w_{m+1})
    zbar     := T.z[NR] = the top residual letter (= z_{m+1})
    phi_gamma:= T.tanch(gamma, NR-1) = pi^{u_1} Phi_0^{s_1} ... Phi_{NR-1}^{s_NR}
    Phi_top  := T._build_lift(T.n) = Phi_{NR} = the classifier's NEXT key
Truncation is only legitimate if Phi_0..Phi_{NR-1} do not depend on reads
above NR-1: P0-TRUNC checks this byte-for-byte across all truncations.

=================== THE GR-SIDE MULTIPLICATION (tautology fence) =============
HOW INDEPENDENCE IS ACHIEVED -- state this verbatim in the note.

The gr-side structure constant c_gr(gamma, gamma') is defined as the UNIQUE
solution of a weight inequality in O[x], and its DECISION PROCEDURE calls
exactly four primitives:
    (1) PolyO.mul / PolyO.sub / PolyO.divmod_monic -- polynomial arithmetic
        in O[x] (schoolbook; no residues, no reads);
    (2) Tower.wlev(NR, .) -- the MacLane weight w_{m+1}, computed by iterated
        Phi-development (pure polynomial division + min);
    (3) Tower.realize(NR, c, N) -- the graded SCALAR LIFT: a pure
        construction (iterated eq-(12) splits, eps z-powers, Phi/pi-power
        products).  It calls no residual read and no cocycle.
    (4) Phi_top = Phi_{NR}, the classifier's own next key polynomial (TC-3).
`Tower.constants` (the [ILN] closed form zbar^delta prod_j z_j^{D_j} = c_T)
and `Tower.read` (the harness val) are NEVER called inside the determination
or the certification.  They enter ONLY as the quantities COMPARED against
(P2-ISO, P2-VAL, P5-OB6).

  * On rows with |K| <= EXH_CAP the constant is found by EXHAUSTIVE search
    over K -- no witness whatsoever, so the gr-side constant is determined
    with ZERO input from the harness side, and uniqueness is PROVED on those
    rows (count of certifying c must be exactly 1).
  * Above the cap a witness is proposed by the read (a witness is not an
    assumption) and then CERTIFIED by the fence-clean procedure, with
    uniqueness sampled against a designated wrong-c set.
  * MT3 (the tautology tooth) demonstrates the certifier's discriminating
    power: the SAME planted corruption (one anchor rescaled by a nontrivial
    scalar class) is CAUGHT by the fence-clean certifier and MISSED by a
    c_T-defined "check" (which is 0/0 by construction, printed as the
    contrast).

THE TWO CERTIFIERS (both reported; the difference is a measurement, not a
bug -- it locates TC-3's load).

  RAW (pre-TC-3, pure gr(w_{m+1})):
      w( phi_a phi_b X_N  -  Lam_N(c) phi_{a+b} )  >  a+b+N
  TC3 (post-TC-3, the transported ring; the quotient by the psi-ideal
  operationalized by division by the classifier's key Phi_{NR}):
      exists k in [0,KMAX]:
      w( (pi^k (phi_a phi_b X_N - Lam_N(c) phi_{a+b})) mod Phi_{NR} )
          >  k*E + a+b+N
  where X_N := Lam_N(1), Lam_N(c) := realize(NR, c, N), N a multiple of E
  with N >= wPhi[NR] (so s_NR(N) = 0: multiplication by X_N is carry-free).
  SOUNDNESS of TC3: the tested remainder R obeys pi^k D = Q Phi_NR + R, so
  w(R) > k E + target implies in(pi^k D) lies in the graded ideal generated
  by in(Phi_NR) -- i.e. D dies in the TC-3 quotient.  ONE-SIDEDNESS
  (disclosed): only the CANONICAL quotient Q is tried, so a TC3 failure is
  not a proof of non-membership; the pi^k ladder widens the search.
  BUILD-PHASE SMOKE (pre-seal, disclosed below) found k = 0 everywhere it
  ran; the k-distribution is reported as a measurement (it quantifies how
  much of TC-1's localization the identification consumes).

============================= PREREGISTERED LEGS =============================
(violation counts; a family whose observed count differs from its sealed
prediction is RED.  LAW-KEYED verdicts.  Deterministic; exact arithmetic.)

EXT-GATE  engine_ext standing rule (the brief's MANDATORY in-unit clause):
          import engine_ext, install(), check_pins(), agreement_gate() re-run;
          counts reported.                                     PREDICTED 0.

P0-TRUNC  the truncation identity: for every roster row and every k in
          [2, NR], the tower on reads[:k] has Phi_0..Phi_{k-1} byte-identical
          to the row's own.                                    PREDICTED 0.
P0-ANCH   anchor sanity: w(phi_gamma) = gamma for every gamma in the
          representative systems; deg phi_gamma < deg Phi_NR.  PREDICTED 0.
P0-OB2    OB-2 / COR-4 exactly: phi_{gamma+E} == pi * phi_gamma BYTE-for-byte
          (hence [phi_{gamma+E}]_TC = [phi_gamma]_TC after TC-2 gauges pi
          away).                                               PREDICTED 0.
P0-LIFT   the scalar lift's defining properties: w(Lam_N(c)) = N and
          read(NR, N, Lam_N(c)) = c for EVERY c in K.           PREDICTED 0.
P0-SCAL   the gr-side scalar-action laws, computed by polynomial arithmetic +
          w ONLY (this is the machine support for OB-1's scalar layer):
            additivity      w(Lam_N(c) + Lam_N(c') - Lam_N(c+c')) > N
                            [fails iff the digit lift is non-additive: this
                             is measured, and any failure is reported as the
                             ADD-genre, not scored RED -- see below]
            multiplicativity  TC3-cert of Lam_N(c) Lam_N(c') against
                            Lam_N(c c') X_N at weight 2N.
          SEALED: multiplicativity PREDICTED 0 violations; additivity is
          MEASURED-ONLY (census, never RED) because the O-digit lift is not
          a ring map and a positive count would be a fact about the lift,
          not about gr.
P2-OFF    offset-independence of the STRUCTURE CONSTANTS (the well-posed
          OB-1 offset clause): c_gr recomputed with the scalar home at
          N + E equals c_gr at N.  PREDICTED 0.
          DISCLOSED (build-phase, measured): the naive CLASS identity
          [pi*Lam_N(c)] == [Lam_{N+E}(c)] is FALSE -- two weight-(N+E) lifts
          with the same read need not be the same class, since the level-NR
          read is not injective on a graded piece (that non-injectivity IS
          TC-3's psi-kernel).  So the offset clause is stated on the constants,
          which is what the carrier iso needs.
P0-PSI    the J-B germ letter identity, re-verified per stage:
          psi_{m,0} embedded in K_{m+1} equals -zbar (= -z_{m+1}).
          PREDICTED 0 violations (JB-CM, 28 rows, independently re-run here).

P1-RAW    the PRE-TC-3 certifier on the pair grid: count of pairs with NO
          certifying c.  SEALED IDENTITY (the sharp form, fixed at seal time
          from the build-phase smoke -- disclosed below):
            {pairs with no RAW solution}  ==  {pairs with delta >= g_m}
          where delta = the [ILN] top carry and g_m = g_{NR-1} = deg psi_m.
          RATIONALE (why g_m and not 1): the scalar lift Lam_N realizes
          c = sum_{i<g_m} c_i zbar^i by placing c_i at grid slot i, so a slot
          shift by delta < g_m IS already a scalar; a shift by delta >= g_m
          needs the psi-relation, i.e. TC-3.  PREDICTED 0 set-mismatches (the
          count itself is measured, and is nonzero on the g_m = 1 stages).
          [If RAW succeeded at delta >= g_m the outer zbar^delta factor would
          be a coordinate artifact -- it is not.]
P1-TC3    the POST-TC-3 certifier on the pair grid: every scored pair has a
          certifying c, and it is UNIQUE.                       PREDICTED 0
          (violations = pairs with 0 solutions, plus pairs with >= 2 on the
          exhaustive rows).
P2-ISO    THE CARRIER ISO, on the nose, per (gamma, gamma') pair:
          c_gr == c_T = zbar^delta prod_{j=1}^{m} z_j^{D_j}, on the scored
          stratum (D_j all integral AND the pair off DCX -- [ILN]'s own
          accepted scope; both fences censused).                PREDICTED 0.
P2-REP    representative-independence (GRT-1c descent on the GR side): c_gr
          recomputed with the MINIMAL in-window representative of each class
          (ITL.window_reps) equals c_gr at the uniform base G0.  PREDICTED 0.
P2-VAL    baseline control (accepted ITER-LAW, re-confirmed on this roster):
          c_val := read(phi_a phi_b)/read(phi_{a+b}) equals c_T on the same
          scored stratum.                                       PREDICTED 0.
P3-FACT   the INNER normalization factor, MEASURED: inner := prod_{j=1}^{m}
          z_j^{D_j}, outer := zbar^delta; census of stages/pairs with
          inner != 1 (the load-bearing count) and the observed inner value
          multiset per stage.  Scored clause: c_gr == outer * inner.
          PREDICTED 0 violations of the scored clause.
P3-READ   the three RIVAL readings of the normalization, scored as TEETH
          (each MUST fail somewhere -- a reading that never fails is not
          distinguishable from H-A and that would itself be the finding):
            H-B  c_gr == outer alone (inner dropped)
            H-C  c_gr == (-zbar)^delta * inner (germ-signed outer)
            H-D  c_gr == outer * (-zbar)^{sum_j D_j}  (inner letters
                 replaced by the GERM letter -- the brief's literal
                 working hypothesis "the inner factor at general m is
                 -z_{m+1}")
          PREDICTED: each of H-B/H-C/H-D shows >= 1 failure on the roster
          (counts reported per stage); H-D failing is the adjudication of
          the germ hypothesis AS AN INNER-FACTOR claim.
P3-GERM   THE GERM, measured in the carrier (new; JB-CREAD's c_m = psi_{m,0}
          = -z_{m+1} lives at the level-m read -- here we ask what the
          correction digit does to the CARRIER's anchor classes).  Eligible
          stages: g_m = 1 (so Chat_m := Phi_{NR} - Phi_{NR-1}^{e_m} is THE
          canonical correction digit).  Measured:
            (a) val(Chat_m) := read(NR, e_m*gamma_{m+1}, Chat_m)  vs  -zbar.
                SEALED PREDICTION: EQUAL (0 violations) -- the germ letter is
                the correction digit's own anchor value.
            (b) kappa := the TC3-certified scalar with
                [Chat_m X_N] = [Lam_N(kappa) phi_{e_m gamma_{m+1}}]
                (pi-shifted into W as needed).  MEASURED; the sealed
                prediction is kappa * val(phi_{e_m gamma_{m+1}}) == -zbar,
                i.e. THE MEASURED FACTOR IS -z_{m+1} DIVIDED BY THE ANCHOR'S
                OWN VALUE NORMALIZATION.  Both the raw kappa and the product
                are reported so the composer sees the exact factor.
            (c) transport consistency: c_germ(r) := the TC3-certified
                constant of [Chat_m phi_{gamma_r}] against
                phi_{gamma_r + e_m gamma_{m+1}} equals kappa *
                c_T(e_m gamma_{m+1}, gamma_r) on the scored stratum.
                PREDICTED 0.
P4-DEG    OB-4 leg 1 (the fibred independence content): gamma |-> w(phi_gamma)
          mod E is a BIJECTION Z/E -> Z/E on the representative system, and
          every anchor class is nonzero (w exact).              PREDICTED 0.
          [Displayed honestly in the note: in the fibred presentation OB-4's
          independence reduces to this degree separation; the Delta-rank
          refinement (freeness over K_m[y] before TC-3) is NOT measured by
          this instrument -- an explicitly unmeasured leg.]
P4-SPAN   OB-4 leg 2 (the rank-ONE / spanning content, the part that can
          actually drop).  TWO families:
          SPAN-M (SCORED -- the well-posed rank-one probe): for each class r,
            perturb the anchor's OWN exponent vector at one level
            (s_{j+1} -> s_{j+1} + e_j, compensated in the pi-power so the
            weight is unchanged); the resulting MONOMIAL is a genuine element
            of gr_{gamma_r + N} that is not the anchor.  Does a TC3-certifying
            scalar exist?  A class that DIES in the TC-3 quotient (only c = 0
            certifies) is counted separately as zero-class, not as a failure.
            PREDICTED 0 failures; every failure tabulated as a GENRE row.
          SPAN-S (MEASURED-ONLY census, never RED): weight-matched SUMS
            A + B with A := X_N phi_{gamma_r} and B := pi^t phi_a phi_b
            (gamma_a + gamma_b + tE = gamma_r + N).  The build-phase smoke
            found 2 non-certifying, non-zero-class samples here (C2A r=2
            sample (1,1); C3A r=6 sample (1,5)); because B carries no X_N
            factor its class relates to the anchor only through a
            DIFFERENT scalar offset, so a failure is not evidence about
            OB-4 -- it is disclosed as a census with the exact rows printed,
            and is the reason SPAN-S is not scored.
P5-OB6    OB-6's shadow: harness-val == TC-read, per pair: c_gr == c_val.
          PREDICTED 0 on the scored stratum.  (This is NOT implied by
          P2-ISO+P2-VAL on the DCX/non-integral strata, which are exactly
          where the two can part; those strata are censused separately.)

TEETH (mutation controls; all four must fire -- a silent tooth is a RED):
MT1  WRONG LETTER: the inner factor's letters replaced by the top letter
     (c_bad := zbar^{delta + sum_j D_j}).  MUST FAIL TC3-certification on
     every designated pair (designated = pairs where c_bad != c_T).
     PREDICTED: >= 1 failure per stage that has such a pair; 0 pairs where
     c_bad != c_T yet certifies.
MT2  CYCLIC PRESENTATION AT A COMPOSITE STAGE (the cyclic fence, LAW): the
     (CYC) adjudication -- image(c_gr) subset {1, zeta'} AND a relabeling
     sigma with sigma_r + sigma_s = sigma_{r+s} + E*carry -- run on the
     MEASURED c_gr table (a fresh transcription of the strata-probe B3-adj
     algorithm).  SEALED, designation fixed STRUCTURALLY before the run
     (CYC_DESIGNATED = the g_m = 2 rows C2I / C3I / C4I, where
     K_{m+1} = K_m[zbar] is a genuine degree-2 residual extension so zbar is
     NOT a power of the inner letters): AT LEAST ONE designated row must come
     back NOT-CYCLIC (the tooth fires).  Every row's verdict is RECORDED;
     CYCLIC verdicts on twist-blind rows (|K| = 2, or zbar in <z_1> because
     g_m = 1 collapses K_{m+1} = K_m) and on the e_j = 1 flat controls are the
     D-REAL last-read-layer geography and are NOT RED.  A CYCLIC verdict on a
     designated g_m = 2 row would be a notable finding, reported.
     The relabeling search is skipped (verdict UNDECIDED, recorded) at E > 8.
MT3  TAUTOLOGY TOOTH: rescale ONE anchor (index r* = 1) by a nontrivial
     scalar class kappa_c (the first of zbar, z_1, X-generator that is != 1)
     and re-certify the pairs touching r* = 1.  PREDICTED: the fence-clean
     certifier reports constants that DISAGREE with c_T on >= 1 pair per
     designated stage, while the c_T-defined "check" reports 0 violations by
     construction (both numbers printed).  Stages with no kappa_c != 1
     (|K| = 2) are skipped and disclosed.
MT4  GARBLED SCALAR LIFT: Lam'(c) := Lam_N(c * z_1) (wrong letter inside the
     lift).  PREDICTED: the TRUE constant fails certification on >= 1 pair
     per stage with z_1 != 1.

===================================== ROSTER ================================
28 rows = (constructed tower, level m) with NR = m+1 reads, spanning
m in {1,2,3} (10 / 10 / 8 rows), p in {2,3,5}, d0 in {1,2,3}, mixed (e_j)
with E_{m+1} > 1 on every scored row, wild legs e_j = p, g_j = 2 branching
rows (a genuine degree-2 residual extension: zbar not in <z_1>, the
strata-probe row-N discriminator design), e_j = 1 flat rows ([RMG]'s fenced
corner genre and the D-REAL cyclic controls), the strata NOT-CYCLIC roster's
genres (its rows C/D/E/H/J/K/L/M/N shapes), and the three committed ITERLAWN
4-read instances I4A/I4B/I4C verbatim.  Base rings Z_p and F_p[[t]].

PAIR GRID: all E^2 ordered pairs when E <= 6; otherwise a deterministic
designed subset (diagonal, low pairs, and the carry boundary r+s in
{E-1, E, E+1}) capped at PAIRCAP = 24 pairs.  No randomness anywhere.

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest; part of this seal).  Three
reduced probes ran during construction:
 (i) primitive smoke on 1 row (C2A shape): realize at m = NR works with
     check=False, w and read of the lift are exact for all c in K, anchors
     have w(phi_gamma) = gamma, and the exhaustive certifier returns a
     UNIQUE c equal to c_T = c_val on a delta = 0 pair;
 (ii) 4-row RAW smoke (C2A/C2D/C3A/C4B shapes, 16 pairs each): RAW returns
     ZERO certifying c on exactly the delta = 1 pairs (4/16, 5-6/20, 4/20)
     and a unique correct c elsewhere -- this is what fixed P1-RAW's sealed
     prediction to NONZERO-with-set-identity rather than 0;
 (iii) 4-row TC3 smoke (C2A/C2D/C2I/C3A shapes): TC3 certification 0
     failures, 0 non-unique, k-distribution {0: all}, and c_gr == c_T on
     every pair including the delta = 1 pairs;
 (iv) a 3-row full-battery smoke of THIS runner (C2A/C2I/C3A) which produced
     three pre-seal corrections, all disclosed and applied BEFORE the seal:
     (a) P1-RAW's set identity sharpened from {delta >= 1} to {delta >= g_m}
         (C2I has g_m = 2 and RAW succeeded on its delta = 1 pairs -- the
         scalar lift already covers slot shifts below g_m);
     (b) c = 0 admitted as a certifying scalar in the SPAN legs (a class may
         die in the TC-3 quotient; excluding 0 mis-scored such rows);
     (c) SPAN redesigned into the scored monomial family SPAN-M plus the
         unscored SPAN-S census (see P4-SPAN).
     That smoke also showed, on those three rows: 0 violations in every other
     family, MT3 firing on 21/21 pairs, MT1/MT4 0 misses, H-B failing on 10
     of 56 scored pairs and H-D on 4, and the germ table reading
     val(Chat) = -zbar with kappa = 1 on both eligible rows.
The sealed predictions above are the BRIEF's identities, not sanitized to
the smoke: P1-TC3/P2-ISO/P2-VAL/P5-OB6 are sealed at 0, P1-RAW is sealed as
a SET IDENTITY (its count is measured), P3-GERM's (a)/(b) are sealed as
displayed equalities, and every tooth is sealed as MUST-FIRE.

Outputs: grt_jc_probe_output.txt (stdout, tee'd by the caller) and
grt_jc_probe_results.json.  Note: lean/notes/openmath/GRTJC_PROBE_2026-08-08.md.
"""
import sys, os, json, time, itertools

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
from iterlawn_pe_reimpl import fpow
import engine_ext as EE

EXH_CAP = 512      # exhaustive-c ceiling (|K| <= EXH_CAP -> no witness at all)
PAIRCAP = 24       # designed pair subset cap when E > 6
KMAX = 4           # pi-clearing ladder depth for the TC3 certifier

VIOL = []
COUNTS = {}
RESULTS = {'rows': {}, 'families': {}, 'genres': [], 'germ': {}, 'cyc': {}}


def note(fam, n=1):
    COUNTS[fam] = COUNTS.get(fam, 0) + n


def viol(fam, tag, detail):
    VIOL.append((fam, tag, str(detail)))


# ================================ ROSTER =====================================
# fields: id, ring, p, d0, Phi0, reads, psi  (NR = len(reads), m = NR-1)
ROSTER = [
 # ---- m = 1 (NR = 2) ----
 dict(id='C2A', ring='Zp', p=2, d0=2, Phi0=[1,1,1], reads=[(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]]),                     # wild p=2, K=F4
 dict(id='C2B', ring='Zp', p=2, d0=1, Phi0=[0,1], reads=[(2,1,2),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1]]),                         # g0=2 -> F4
 dict(id='C2C', ring='Zp', p=3, d0=1, Phi0=[0,1], reads=[(3,1,1),(2,1,1)],
      psi=[[1,1],[1,1]]),                                   # wild p=3, blind
 dict(id='C2D', ring='Zp', p=3, d0=2, Phi0=[1,0,1], reads=[(2,1,1),(3,2,1)],
      psi=[[('X',1),1],[('z',1,1),1]]),                     # wild read1, F9
 dict(id='C2E', ring='Fpt', p=2, d0=2, Phi0=[1,1,1], reads=[(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]]),                     # eq-char
 dict(id='C2F', ring='Zp', p=5, d0=1, Phi0=[0,1], reads=[(5,1,1),(2,1,1)],
      psi=[[1,1],[1,1]]),                                   # p=5 wild
 dict(id='C2G', ring='Zp', p=5, d0=2, Phi0=[2,0,1], reads=[(2,1,1),(3,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]]),                     # F25 (EXT-WALL3 safe)
 dict(id='C2H', ring='Zp', p=2, d0=3, Phi0=[1,1,0,1], reads=[(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1]]),                     # d0=3, F8
 dict(id='C2I', ring='Zp', p=2, d0=1, Phi0=[0,1], reads=[(2,1,1),(2,1,2)],
      psi=[[1,1],('TRY',[[1,1,1],[1,0,1],[('z',1,1),1,1]])]),   # g1=2
 dict(id='C2J', ring='Zp', p=3, d0=1, Phi0=[0,1], reads=[(1,1,1),(3,1,1)],
      psi=[[1,1],[1,1]]),                                   # e0=1 flat control
 # ---- m = 2 (NR = 3) ----
 dict(id='C3A', ring='Zp', p=2, d0=2, Phi0=[1,1,1],
      reads=[(2,1,1),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]]),        # E=8 wild F4
 dict(id='C3B', ring='Zp', p=3, d0=1, Phi0=[0,1],
      reads=[(3,1,1),(2,1,1),(2,1,1)], psi=[[1,1],[1,1],[1,1]]),
 dict(id='C3C', ring='Zp', p=3, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(3,2,1),(2,1,1)], psi=[[1,1],[1,1],[1,1]]),  # wild middle
 dict(id='C3D', ring='Fpt', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,2),(2,1,1),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1],[('z',1,1),1]]),
 dict(id='C3E', ring='Zp', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,2),(1,1,1),(2,3,1)],
      psi=[[1,1,1],[('z',1,1),1],[('z',1,1),1]]),            # flat middle
 dict(id='C3F', ring='Zp', p=3, d0=2, Phi0=[1,0,1],
      reads=[(2,1,1),(2,1,1),(3,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]]),        # F9, wild top
 dict(id='C3G', ring='Zp', p=5, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(5,1,1),(2,1,1)], psi=[[1,1],[1,1],[1,1]]),  # p=5 wild mid
 dict(id='C3H', ring='Zp', p=2, d0=3, Phi0=[1,1,0,1],
      reads=[(2,1,1),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1]]),        # d0=3 deep
 dict(id='C3I', ring='Zp', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(2,1,2),(2,1,1)],
      psi=[[1,1],('TRY',[[1,1,1],[1,0,1],[('z',1,1),1,1]]),[('z',2,1),1]]),
 dict(id='C3J', ring='Fpt', p=3, d0=1, Phi0=[0,1],
      reads=[(3,1,1),(2,1,1),(2,1,1)], psi=[[1,1],[1,1],[1,1]]),
 # ---- m = 3 (NR = 4) ----
 dict(id='C4A', ring='Zp', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(2,1,1),(2,1,1),(2,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,1]]),
 dict(id='C4B', ring='Zp', p=2, d0=2, Phi0=[1,1,1],
      reads=[(2,1,1),(2,1,1),(2,1,1),(2,1,1)],
      psi=[[('X',1),1],[('z',1,1),1],[('z',2,1),1],[('z',3,1),1]]),
 dict(id='C4C', ring='Zp', p=3, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(3,1,1),(2,1,1),(2,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,1]]),
 dict(id='C4G', ring='Fpt', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,2),(2,1,1),(2,1,1),(2,1,1)],
      psi=[[1,1,1],[('z',1,1),1],[('z',1,1),1],[('z',1,1),1]]),
 dict(id='C4H', ring='Zp', p=5, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(1,1,1),(5,1,1),(1,1,1)],
      psi=[[1,1],[1,1],[1,1],[1,1]]),                        # p=5 + flat legs
 dict(id='C4I', ring='Zp', p=2, d0=1, Phi0=[0,1],
      reads=[(2,1,1),(2,1,1),(2,1,1),(2,1,2)],
      psi=[[1,1],[1,1],[1,1],
           ('TRY',[[1,1,1],[1,0,1],[('z',1,1),1,1]])]),       # g_m = 2 at m = 3
] + [dict(s) for s in ITL.INSTANCES[:3]]                      # I4A / I4B / I4C

# structural designations, fixed at seal time (see the docstring)
# MT2's designation, fixed structurally at seal time: the rows whose TOP read
# has g_m = 2, i.e. K_{m+1} = K_m[zbar] is a genuine degree-2 residual extension
# so zbar is NOT a power of the inner letters (the strata-probe row-N
# discriminator design).  These are the rows where a cyclic single-zeta
# presentation is structurally most exposed.
CYC_DESIGNATED = ['C2I', 'C3I', 'C4I']


# ============================== stage builder ================================
class Stage:
    """One probe row: a truncated tower analyzed at its top level NR = m+1."""

    def __init__(self, spec):
        self.spec = spec
        self.tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        self.T = ITL.build_tower(spec)
        T = self.T
        self.P = T.P
        self.NR = T.NR
        self.m = T.NR - 1
        self.K = T.K[T.NR]
        self.zbar = T.z[T.NR]
        E = 1
        for e in T.e:
            E *= e
        self.E = E
        self.elems = [c for c in self.K.elems()]
        self.nK = len(self.elems)
        self.PhiTop = T._build_lift(T.n)                  # Phi_{NR}
        self.wPhiTop = T.wlev(T.NR, self.PhiTop)
        self.egg = T.e[T.NR - 1] * T.g[T.NR - 1] * T.gam[T.NR]
        # N: a multiple of E, >= wPhi[NR], on which realize succeeds
        N = E * ((T.wPhi[T.NR] + E - 1) // E)
        self.N = None
        for _ in range(12):
            try:
                X = T.realize(T.NR, self.K.one(), N, check=False)
                if T.wlev(T.NR, X) == N and T.read(T.NR, N, X) == self.K.one():
                    self.N = N
                    self.X = X
                    break
            except Exception:
                pass
            N += E
        assert self.N is not None, 'no usable N for %s' % self.tag
        # scalar lifts
        self.lam = {}
        for c in self.elems:
            self.lam[c] = None if self.K.is_zero(c) else \
                T.realize(T.NR, c, self.N, check=False)
        # uniform representative system: G0 + r, r in [0,E)
        G0 = 0
        while not all(T.inW(G0 + r) for r in range(E)):
            G0 += E
        self.G0 = G0
        self.gam_of = {r: G0 + r for r in range(E)}
        self.ph = {r: T.tanch(G0 + r, T.NR - 1) for r in range(E)}
        self.pi1 = (T.R.pi_pow(1),)

    # ------------------------ certifiers (fence-clean) -----------------------
    def anchor(self, gamma):
        return self.T.tanch(gamma, self.T.NR - 1)

    def raw_cert(self, LHS, base, target, c):
        D = self.P.sub(LHS, self.P.mul(self.lam[c], base))
        w = self.T.wlev(self.NR, D)
        return (w is None) or (w > target)

    def tc3_cert_k(self, LHS, base, target, c):
        """return the minimal pi-clearing depth k that certifies, else None."""
        D = self.P.sub(LHS, self.P.mul(self.lam[c], base))
        for k in range(KMAX + 1):
            _, Rem = self.P.divmod_monic(D, self.PhiTop)
            w = self.T.wlev(self.NR, Rem)
            if (w is None) or (w > target + k * self.E):
                return k
            D = self.P.mul(D, self.pi1)
        return None

    def zero_cert(self, LHS, target, mode='tc3'):
        """does the class DIE (c = 0 certifies)?  Lam_N(0) = 0."""
        if mode == 'raw':
            w = self.T.wlev(self.NR, LHS)
            return (w is None) or (w > target)
        D = LHS
        for k in range(KMAX + 1):
            _, Rem = self.P.divmod_monic(D, self.PhiTop)
            w = self.T.wlev(self.NR, Rem)
            if (w is None) or (w > target + k * self.E):
                return True
            D = self.P.mul(D, self.pi1)
        return False

    def solve(self, LHS, base, target, mode='tc3', lam=None):
        """Determine the structure constant.
        Exhaustive (no witness) when |K| <= EXH_CAP; else read-witness +
        certification + sampled uniqueness.  Returns
        (sols, route, kmin) with sols a list of certifying c."""
        save = None
        if lam is not None:
            save, self.lam = self.lam, lam
        try:
            cert = self.raw_cert if mode == 'raw' else \
                (lambda L, b, t, c: self.tc3_cert_k(L, b, t, c) is not None)
            if self.nK <= EXH_CAP:
                sols = [c for c in self.elems
                        if not self.K.is_zero(c) and cert(LHS, base, target, c)]
                kmin = None
                if sols and mode == 'tc3':
                    kmin = self.tc3_cert_k(LHS, base, target, sols[0])
                return sols, 'exhaustive', kmin
            # witness route
            rl = self.T.read(self.NR, target, LHS)
            rb = self.T.read(self.NR, target,
                             self.P.mul(self.lam[self.K.one()], base))
            if self.K.is_zero(rb):
                return [], 'witness-degenerate', None
            cw = self.K.mul(rl, self.K.inv(rb))
            if self.K.is_zero(cw) or not cert(LHS, base, target, cw):
                return [], 'witness-fail', None
            kmin = self.tc3_cert_k(LHS, base, target, cw) if mode == 'tc3' else None
            # sampled uniqueness: designated wrong-c set
            bad = []
            for alt in self.wrongset(cw):
                if cert(LHS, base, target, alt):
                    bad.append(alt)
            return ([cw] + bad), 'witness', kmin
        finally:
            if save is not None:
                self.lam = save

    def wrongset(self, c):
        K = self.K
        out = []
        for z in [self.zbar] + [self.T.embed(self.T.z[j], j, self.NR)
                                for j in range(1, self.NR)]:
            if not K.is_zero(z) and z != K.one():
                out.append(K.mul(c, z))
        out.append(K.one())
        return [x for x in out if x != c and not K.is_zero(x)][:4]

    # ------------------------- compared quantities ---------------------------
    def cT(self, ga, gb):
        T = self.T
        cst = T.constants(ga, gb)
        if not cst['dint_ok']:
            return None, cst
        v = fpow(self.K, self.zbar, cst['delta'])
        for j in range(1, self.NR):
            v = self.K.mul(v, T.embed(fpow(T.K[j], T.z[j], cst['D'][j]),
                                      j, self.NR))
        return v, cst

    def inner_outer(self, cst):
        T = self.T
        outer = fpow(self.K, self.zbar, cst['delta'])
        inner = self.K.one()
        for j in range(1, self.NR):
            inner = self.K.mul(inner, T.embed(
                fpow(T.K[j], T.z[j], cst['D'][j] or 0), j, self.NR))
        return inner, outer

    def cval(self, ga, gb, A, B, base):
        T = self.K
        num = self.T.read(self.NR, ga + gb, self.P.mul(A, B))
        den = self.T.read(self.NR, ga + gb, base)
        if T.is_zero(den):
            return None
        return T.mul(num, T.inv(den))

    def val(self, gamma, f=None):
        f = self.anchor(gamma) if f is None else f
        return self.T.read(self.NR, self.T.wlev(self.NR, f), f)


def krepr(S, v):
    """name a K-element as zbar^a z_1^{b1} ... or 'raw:'."""
    K = S.K
    if K.is_zero(v):
        return '0'
    if v == K.one():
        return '1'
    gens = [('zb', S.zbar)] + [('z%d' % j, S.T.embed(S.T.z[j], j, S.NR))
                              for j in range(1, S.NR)]
    for (n1, g1) in gens:
        x = g1
        for a in range(1, 2 * S.nK + 2):
            if x == v:
                return '%s^%d' % (n1, a)
            x = K.mul(x, g1)
    for (n1, g1) in gens:
        for (n2, g2) in gens:
            x = g1
            for a in range(1, 8):
                y = x
                for b in range(1, 8):
                    y = K.mul(y, g2)
                    if y == v:
                        return '%s^%d*%s^%d' % (n1, a, n2, b)
                x = K.mul(x, g1)
    return 'raw:%s' % (v,)


def pair_grid(E):
    if E <= 6:
        return [(r, s) for r in range(E) for s in range(E)]
    out = []
    for r in range(min(E, 3)):
        for s in range(min(E, 3)):
            out.append((r, s))
    for r in range(E):
        for s in range(E):
            if r + s in (E - 1, E, E + 1) and (r, s) not in out:
                out.append((r, s))
    for r in range(E):
        if (r, r) not in out:
            out.append((r, r))
    return out[:PAIRCAP]


# ============================== the row battery ===============================
def run_row(S):
    T, P, K, NR, E, N = S.T, S.P, S.K, S.NR, S.E, S.N
    rec = {'tag': S.tag, 'id': S.spec['id'], 'm': S.m, 'NR': NR, 'E': E,
           'p': S.spec['p'], 'd0': S.spec['d0'], 'ring': S.spec['ring'],
           'reads': S.spec['reads'], 'nK': S.nK, 'N': N, 'G0': S.G0,
           'wPhiTop': S.wPhiTop, 'egg': S.egg, 'gam': T.gam[1:],
           'zbar': krepr(S, S.zbar), 'exhaustive': S.nK <= EXH_CAP}

    # ---------------- P0-TRUNC : truncation identity -------------------------
    for k in range(2, NR + 1):
        sub = dict(S.spec)
        sub['reads'] = S.spec['reads'][:k]
        sub['psi'] = S.spec['psi'][:k]
        sub['id'] = S.spec['id'] + '/t%d' % k
        try:
            Tk = ITL.build_tower(sub)
        except Exception as ex:
            note('P0-TRUNC')
            viol('P0-TRUNC', S.tag, 'truncation k=%d failed to build: %r' % (k, ex))
            continue
        for j in range(0, k):
            note('P0-TRUNC')
            if Tk.Phi[j] != T.Phi[j]:
                viol('P0-TRUNC', S.tag, 'Phi[%d] differs at truncation k=%d' % (j, k))

    # ---------------- P0-ANCH / P0-OB2 --------------------------------------
    for r in range(E):
        g = S.gam_of[r]
        note('P0-ANCH')
        if T.wlev(NR, S.ph[r]) != g:
            viol('P0-ANCH', S.tag, 'w(phi_%d) != %d' % (g, g))
        note('P0-OB2')
        if S.anchor(g + E) != P.mul(S.pi1, S.ph[r]):
            viol('P0-OB2', S.tag, 'phi_{%d+E} != pi*phi_%d' % (g, g))

    # ---------------- P0-LIFT / P0-SCAL -------------------------------------
    for c in S.elems:
        if K.is_zero(c):
            continue
        note('P0-LIFT')
        L = S.lam[c]
        if T.wlev(NR, L) != N or T.read(NR, N, L) != c:
            viol('P0-LIFT', S.tag, 'lift law fails at c=%s' % krepr(S, c))
    nz = [c for c in S.elems if not K.is_zero(c)]
    scal_pairs = [(nz[i], nz[j]) for i in range(min(len(nz), 4))
                  for j in range(min(len(nz), 4))]
    add_genre = 0
    for (c1, c2) in scal_pairs:
        s = K.add(c1, c2)
        if not K.is_zero(s):
            D = P.sub(P.add(S.lam[c1], S.lam[c2]), S.lam[s])
            w = T.wlev(NR, D)
            note('P0-SCAL-ADD-census')
            if not ((w is None) or (w > N)):
                add_genre += 1
        pr = K.mul(c1, c2)
        if not K.is_zero(pr):
            LHS = P.mul(S.lam[c1], S.lam[c2])
            note('P0-SCAL')
            if T.wlev(NR, LHS) != 2 * N:
                viol('P0-SCAL', S.tag, 'w(Lam*Lam) != 2N at (%s,%s)'
                     % (krepr(S, c1), krepr(S, c2)))
            elif S.tc3_cert_k(LHS, S.lam[pr], 2 * N, K.one()) is None:
                viol('P0-SCAL', S.tag, 'scalar multiplicativity fails at (%s,%s)'
                     % (krepr(S, c1), krepr(S, c2)))
    rec['scal_add_genre'] = add_genre
    # NOTE (measured, displayed in the note, NOT scored): the class identity
    # [pi*Lam_N(c)] == [Lam_{N+E}(c)] is FALSE in general -- two weight-(N+E)
    # lifts with the same read need not be the same class, because the level-NR
    # read is not injective on a graded piece (the psi-kernel of TC-3).  The
    # well-posed offset clause is therefore stated on the STRUCTURE CONSTANTS
    # (family P2-OFF below), which is what the carrier iso actually needs.

    # ---------------- P0-PSI : the germ letter ------------------------------
    note('P0-PSI')
    psi0 = T.embed(T.psi[NR - 1][0], NR - 1, NR)
    negz = K.neg(S.zbar)
    rec['psi0'] = krepr(S, psi0)
    rec['neg_zbar'] = krepr(S, negz)
    if T.g[NR - 1] == 1 and psi0 != negz:
        viol('P0-PSI', S.tag, 'psi_{m,0} = %s != -zbar = %s'
             % (krepr(S, psi0), krepr(S, negz)))

    # ---------------- P1 / P2 / P3 / P5 : the pair grid ---------------------
    grid = pair_grid(E)
    tab = {}
    raw_nosol = set()
    delta_pos = set()
    kdist = {}
    cnt = dict(scored=0, dcx=0, nonint=0, raw_nosol=0, tc3_nosol=0,
               nonuniq=0, iso_bad=0, val_bad=0, ob6_bad=0, inner_ne1=0,
               HB_fail=0, HC_fail=0, HD_fail=0, MT1_fail=0, MT1_pairs=0,
               MT4_fail=0, MT4_pairs=0)
    innerset = {}
    for (r, s) in grid:
        ga, gb = S.gam_of[r], S.gam_of[s]
        base = S.anchor(ga + gb)
        LHS = P.mul(P.mul(S.ph[r], S.ph[s]), S.X)
        tgt = ga + gb + N
        note('P1-TC3')
        if T.wlev(NR, LHS) != tgt or T.wlev(NR, base) != ga + gb:
            viol('P1-TC3', S.tag, 'weight setup wrong at (%d,%d)' % (r, s))
            continue
        cTv, cst = S.cT(ga, gb)
        d = ITL.pair_data(T, ga, gb)
        dcx = d['dcx_pair']
        if dcx:
            cnt['dcx'] += 1
        if cTv is None:
            cnt['nonint'] += 1
        delta = cst['delta']
        if delta >= T.g[NR - 1]:
            delta_pos.add((r, s))
        # RAW leg
        rsols, _, _ = S.solve(LHS, base, tgt, mode='raw')
        note('P1-RAW')
        if not rsols:
            raw_nosol.add((r, s))
            cnt['raw_nosol'] += 1
        # TC3 leg
        sols, route, kmin = S.solve(LHS, base, tgt, mode='tc3')
        if not sols:
            cnt['tc3_nosol'] += 1
            viol('P1-TC3', S.tag, 'no TC3-certifying c at (%d,%d) delta=%d'
                 % (r, s, delta))
            continue
        if len(sols) > 1:
            cnt['nonuniq'] += 1
            viol('P1-TC3', S.tag, '%d certifying c at (%d,%d) [route %s]'
                 % (len(sols), r, s, route))
        cg = sols[0]
        kdist[kmin] = kdist.get(kmin, 0) + 1
        tab[(r, s)] = cg
        cv = S.cval(ga, gb, S.ph[r], S.ph[s], base)
        scored = (cTv is not None) and (not dcx)
        if scored:
            cnt['scored'] += 1
            note('P2-ISO')
            if cg != cTv:
                cnt['iso_bad'] += 1
                viol('P2-ISO', S.tag, 'c_gr=%s != c_T=%s at (%d,%d) delta=%d D=%s'
                     % (krepr(S, cg), krepr(S, cTv), r, s, delta, cst['D'][1:]))
            note('P2-VAL')
            if cv != cTv:
                cnt['val_bad'] += 1
                viol('P2-VAL', S.tag, 'c_val=%s != c_T=%s at (%d,%d)'
                     % (krepr(S, cv), krepr(S, cTv), r, s))
            note('P5-OB6')
            if cv != cg:
                cnt['ob6_bad'] += 1
                viol('P5-OB6', S.tag, 'c_gr=%s != c_val=%s at (%d,%d)'
                     % (krepr(S, cg), krepr(S, cv), r, s))
            inner, outer = S.inner_outer(cst)
            if inner != K.one():
                cnt['inner_ne1'] += 1
                innerset[krepr(S, inner)] = innerset.get(krepr(S, inner), 0) + 1
            note('P3-FACT')
            if cg != K.mul(outer, inner):
                viol('P3-FACT', S.tag, 'c_gr != outer*inner at (%d,%d)' % (r, s))
            # rival readings (teeth): count FAILURES of each reading
            negzb = K.neg(S.zbar)
            HB = outer
            HC = K.mul(fpow(K, negzb, delta), inner)
            sumD = sum((cst['D'][j] or 0) for j in range(1, NR))
            HD = K.mul(outer, fpow(K, negzb, sumD))
            if cg != HB:
                cnt['HB_fail'] += 1
            if cg != HC:
                cnt['HC_fail'] += 1
            if cg != HD:
                cnt['HD_fail'] += 1
            # MT1 tooth: wrong letter (inner letters -> top letter)
            cbad = fpow(K, S.zbar, delta + sumD)
            if cbad != cTv:
                cnt['MT1_pairs'] += 1
                note('MT1')
                if S.tc3_cert_k(LHS, base, tgt, cbad) is not None:
                    cnt['MT1_fail'] += 1
                    viol('MT1', S.tag, 'wrong-letter c CERTIFIES at (%d,%d)' % (r, s))
            # MT4 tooth: garbled scalar lift Lam'(c) = Lam(c*z_1)
            z1 = T.embed(T.z[1], 1, NR)
            if z1 != K.one():
                lam2 = {}
                for c in S.elems:
                    lam2[c] = None if K.is_zero(c) else S.lam[K.mul(c, z1)] \
                        if not K.is_zero(K.mul(c, z1)) else None
                cnt['MT4_pairs'] += 1
                note('MT4')
                save, S.lam = S.lam, lam2
                try:
                    ok = (lam2.get(cg) is not None and
                          S.tc3_cert_k(LHS, base, tgt, cg) is not None)
                finally:
                    S.lam = save
                if ok:
                    cnt['MT4_fail'] += 1
                    viol('MT4', S.tag, 'garbled lift still certifies at (%d,%d)'
                         % (r, s))
    rec['pairs'] = len(grid)
    rec['counts'] = cnt
    rec['kdist'] = {str(k): v for k, v in kdist.items()}
    rec['inner_values'] = innerset
    # P1-RAW sealed SET IDENTITY: no-RAW-solution set == {delta >= g_m} set
    note('P1-RAW-SET')
    if raw_nosol != delta_pos:
        viol('P1-RAW-SET', S.tag,
             'raw-nosol set %s != {delta>=g_m} set %s'
             % (sorted(raw_nosol), sorted(delta_pos)))
    rec['raw_nosol'] = len(raw_nosol)
    rec['delta_pos'] = len(delta_pos)
    rec['g_m'] = T.g[NR - 1]

    # ---------------- P2-OFF : offset-independence of c_gr -------------------
    off_ck = 0
    try:
        Np = N + E
        Xp = T.realize(NR, K.one(), Np, check=False)
        lamp = {c: (None if K.is_zero(c) else T.realize(NR, c, Np, check=False))
                for c in S.elems}
        ok_setup = (T.wlev(NR, Xp) == Np and T.read(NR, Np, Xp) == K.one())
    except Exception:
        ok_setup = False
    if ok_setup:
        for (r, s) in grid[:4]:
            if (r, s) not in tab:
                continue
            ga, gb = S.gam_of[r], S.gam_of[s]
            base = S.anchor(ga + gb)
            LHS = P.mul(P.mul(S.ph[r], S.ph[s]), Xp)
            tgt = ga + gb + Np
            if T.wlev(NR, LHS) != tgt:
                continue
            sols, _, _ = S.solve(LHS, base, tgt, mode='tc3', lam=lamp)
            off_ck += 1
            note('P2-OFF')
            if not sols or sols[0] != tab[(r, s)]:
                viol('P2-OFF', S.tag,
                     'c_gr offset-dependent at (%d,%d): N+E gives %s, N gives %s'
                     % (r, s, krepr(S, sols[0]) if sols else 'NONE',
                        krepr(S, tab[(r, s)])))
    rec['off_checked'] = off_ck

    # ---------------- P2-REP : representative independence ------------------
    reps = ITL.window_reps(S.T)
    rep_of = {g % E: g for g in reps}
    checked = 0
    for (r, s) in grid[:6]:
        if r not in rep_of or s not in rep_of:
            continue
        ga2, gb2 = rep_of[r], rep_of[s]
        if not (T.inW(ga2) and T.inW(gb2) and T.inW(ga2 + gb2)):
            continue
        A, B = S.anchor(ga2), S.anchor(gb2)
        base2 = S.anchor(ga2 + gb2)
        LHS2 = P.mul(P.mul(A, B), S.X)
        tgt2 = ga2 + gb2 + N
        if T.wlev(NR, LHS2) != tgt2:
            continue
        sols2, _, _ = S.solve(LHS2, base2, tgt2, mode='tc3')
        checked += 1
        note('P2-REP')
        if (r, s) in tab and (not sols2 or sols2[0] != tab[(r, s)]):
            viol('P2-REP', S.tag,
                 'c_gr representative-dependent at (%d,%d): %s vs %s'
                 % (r, s, krepr(S, sols2[0]) if sols2 else 'NONE',
                    krepr(S, tab[(r, s)])))
    rec['rep_checked'] = checked

    # ---------------- P3-GERM ----------------------------------------------
    germ = {'eligible': bool(T.g[NR - 1] == 1)}
    if germ['eligible']:
        tau = K.zero()
        Km = T.K[NR - 1]
        tauM = Km.mul(Km.inv(T.eps(NR - 1, T.gam[NR])), T.psi[NR - 1][0])
        Chat = T.realize(NR - 1, tauM, T.gam[NR])
        wC = T.wlev(NR, Chat)
        wCwant = T.e[NR - 1] * T.gam[NR]
        germ['wChat'] = wC
        germ['wChat_expected'] = wCwant
        note('P3-GERM')
        if wC != wCwant:
            viol('P3-GERM', S.tag, 'w(Chat) = %s != e_m*gam = %d' % (wC, wCwant))
        else:
            valC = T.read(NR, wC, Chat)
            germ['valChat'] = krepr(S, valC)
            germ['neg_zbar'] = krepr(S, K.neg(S.zbar))
            note('P3-GERM')
            if valC != K.neg(S.zbar):
                viol('P3-GERM', S.tag, 'val(Chat) = %s != -zbar = %s'
                     % (krepr(S, valC), krepr(S, K.neg(S.zbar))))
            # (b) kappa: [Chat X_N] = [Lam(kappa) phi_{wC + tE}]
            t = 0
            while not T.inW(wC + t * E):
                t += 1
            gC = wC + t * E
            LHS = P.mul(P.mul(Chat, S.X), P.pow(S.pi1, t))
            baseC = S.anchor(gC)
            tgt = gC + N
            germ['t_shift'] = t
            if T.wlev(NR, LHS) == tgt and T.wlev(NR, baseC) == gC:
                sols, route, kk = S.solve(LHS, baseC, tgt, mode='tc3')
                if sols:
                    kap = sols[0]
                    valA = S.val(gC)
                    germ['kappa'] = krepr(S, kap)
                    germ['val_anchor'] = krepr(S, valA)
                    germ['kappa_times_val'] = krepr(S, K.mul(kap, valA))
                    germ['route'] = route
                    germ['nsol'] = len(sols)
                    note('P3-GERM')
                    if K.mul(kap, valA) != K.neg(S.zbar):
                        viol('P3-GERM', S.tag,
                             'kappa*val(anchor) = %s != -zbar = %s'
                             % (krepr(S, K.mul(kap, valA)),
                                krepr(S, K.neg(S.zbar))))
                    # (c) transport consistency on a few r
                    bad = 0; ok = 0
                    for r in range(min(E, 4)):
                        gr = S.gam_of[r]
                        if not T.inW(gr + gC - t * E + t * E):
                            continue
                        gsum = gr + gC
                        if not T.inW(gsum):
                            continue
                        L2 = P.mul(P.mul(P.mul(Chat, S.ph[r]), S.X),
                                   P.pow(S.pi1, t))
                        b2 = S.anchor(gsum)
                        t2 = gsum + N
                        if T.wlev(NR, L2) != t2:
                            continue
                        s2, _, _ = S.solve(L2, b2, t2, mode='tc3')
                        cTv2, cst2 = S.cT(gC, gr)
                        d2 = ITL.pair_data(T, gC, gr)
                        if cTv2 is None or d2['dcx_pair'] or not s2:
                            continue
                        note('P3-GERM')
                        ok += 1
                        if s2[0] != K.mul(kap, cTv2):
                            bad += 1
                            viol('P3-GERM', S.tag,
                                 'germ transport fails at r=%d: %s != kappa*c_T=%s'
                                 % (r, krepr(S, s2[0]),
                                    krepr(S, K.mul(kap, cTv2))))
                    germ['transport_scored'] = ok
                    germ['transport_bad'] = bad
                else:
                    note('P3-GERM')
                    viol('P3-GERM', S.tag, 'no kappa certifies for Chat')
            else:
                germ['skipped'] = 'weight setup'
    rec['germ'] = germ

    # ---------------- P4-DEG / P4-SPAN --------------------------------------
    degs = sorted((S.gam_of[r] % E) for r in range(E))
    note('P4-DEG')
    if degs != list(range(E)):
        viol('P4-DEG', S.tag, 'degree map mod E not a bijection: %s' % degs)
    # SPAN-M: monomial-perturbation family (the well-posed rank-one probe).
    # W_j := w_NR(Phi_j); the anchor of weight W is pi^{u_1} prod Phi_j^{s_{j+1}}
    # and W = u_1 E + sum_j s_{j+1} W_j.  Perturb one exponent by e_j and
    # compensate in the pi-power; the resulting monomial is a genuine element of
    # gr_W that is NOT the anchor.
    Wj = [T.wlev(NR, T.Phi[j]) for j in range(NR)]
    rec['Wj'] = Wj
    spanM = dict(ok=0, zero=0, fail=0, skip=0)
    spanS = dict(ok=0, zero=0, fail=0, skip=0)
    for r in range(E):
        gr = S.gam_of[r]
        W = gr + N
        sp = T.split(W)
        for j in range(NR):
            a = list(sp['s'][1:NR + 1])
            a[j] += T.e[j]
            extra = T.e[j] * Wj[j]
            if extra % E != 0:
                spanM['skip'] += 1
                continue
            u = sp['u'][1] - extra // E
            if u < 0:
                spanM['skip'] += 1
                continue
            B = (T.R.pi_pow(u),)
            for i in range(NR):
                B = P.mul(B, P.pow(T.Phi[i], a[i]))
            if T.wlev(NR, B) != W:
                spanM['skip'] += 1
                continue
            sols, _, _ = S.solve(B, S.ph[r], W, mode='tc3')
            note('P4-SPAN')
            if sols:
                spanM['ok'] += 1
            elif S.zero_cert(B, W):
                spanM['zero'] += 1
            else:
                spanM['fail'] += 1
                RESULTS['genres'].append(
                    dict(kind='SPAN-M-FAIL', tower=S.tag, m=S.m, r=r,
                         perturbed_level=j))
                viol('P4-SPAN', S.tag,
                     'SPAN-M: no scalar for the Phi_%d-perturbed monomial at r=%d'
                     % (j, r))
    # SPAN-S: weight-matched SUMS A + B (measured census; zero-class rows
    # separated -- a class that dies in the TC-3 quotient is certified by c = 0)
    for r in range(E):
        gr = S.gam_of[r]
        A = P.mul(S.X, S.ph[r])
        for (a, b) in [(r, 0), (1, (r - 1) % E), (2, (r - 2) % E)]:
            ga, gb = S.gam_of[a], S.gam_of[b]
            num = gr + N - ga - gb
            if num < 0 or num % E != 0:
                spanS['skip'] += 1
                continue
            t = num // E
            B = P.mul(P.mul(S.ph[a], S.ph[b]), P.pow(S.pi1, t))
            f = P.add(A, B)
            if T.wlev(NR, f) != gr + N:
                spanS['skip'] += 1
                continue
            sols, _, _ = S.solve(f, S.ph[r], gr + N, mode='tc3')
            note('P4-SPANS-census')
            if sols:
                spanS['ok'] += 1
            elif S.zero_cert(f, gr + N):
                spanS['zero'] += 1
            else:
                spanS['fail'] += 1
                RESULTS['genres'].append(
                    dict(kind='SPAN-S-CENSUS', tower=S.tag, m=S.m, r=r,
                         sample='(%d,%d)' % (a, b)))
    rec['spanM'] = spanM
    rec['spanS'] = spanS
    rec['span'] = dict(ok=spanM['ok'], fail=spanM['fail'],
                       skip=spanM['skip'] + spanM['zero'])

    # ---------------- MT2 : the cyclic fence -------------------------------
    verdict, is_cyc, vals = cyc_adjudicate(S, tab)
    rec['cyc'] = dict(verdict=verdict, cyclic=is_cyc, values=vals)
    RESULTS['cyc'][S.tag] = rec['cyc']

    # ---------------- MT3 : the tautology tooth ----------------------------
    kap = None
    for cand in [S.zbar] + [T.embed(T.z[j], j, NR) for j in range(1, NR)]:
        if not K.is_zero(cand) and cand != K.one():
            kap = cand
            break
    mt3 = {'kappa': None if kap is None else krepr(S, kap)}
    if kap is None or E < 2:
        mt3['skipped'] = 'no nontrivial scalar class (|K| = %d)' % S.nK
    else:
        # corrupt anchor index 1: phi'_1 := Lam_N(kappa) * phi_1 / X_N
        # (realized by putting the extra Lam on the LHS and keeping weights)
        caught = 0; pairs_ct = 0
        for (r, s) in grid:
            if 1 not in (r, s):
                continue
            ga, gb = S.gam_of[r], S.gam_of[s]
            base = S.anchor(ga + gb)
            mult = 1 if r != s else 2
            LHS = P.mul(P.mul(S.ph[r], S.ph[s]), S.X)
            for _ in range(mult):
                LHS = P.mul(LHS, S.lam[kap])
            tgt = ga + gb + N + mult * N
            # compare against Lam(c)*phi_{a+b}*X_N^{mult}
            baseX = base
            for _ in range(mult):
                baseX = P.mul(baseX, S.X)
            if T.wlev(NR, LHS) != tgt or T.wlev(NR, baseX) != ga + gb + mult * N:
                continue
            cTv, cst = S.cT(ga, gb)
            d = ITL.pair_data(T, ga, gb)
            if cTv is None or d['dcx_pair']:
                continue
            pairs_ct += 1
            sols, _, _ = S.solve(LHS, baseX, tgt, mode='tc3')
            note('MT3')
            if (not sols) or sols[0] != cTv:
                caught += 1
        mt3['pairs'] = pairs_ct
        mt3['caught'] = caught
        mt3['cT_defined_violations'] = 0     # by construction: c_T == c_T
        note('MT3')
        if pairs_ct > 0 and caught == 0:
            viol('MT3', S.tag, 'tautology tooth did NOT fire (%d pairs)' % pairs_ct)
    rec['mt3'] = mt3
    return rec


def cyc_adjudicate(S, tab):
    """(CYC): image(c) subset {1, zeta'} + a relabeling sigma with
    sigma_r + sigma_s = sigma_{r+s} + E*carry.  Fresh transcription of the
    strata-probe B3-adj algorithm, re-keyed to the MEASURED c_gr table."""
    K, E = S.K, S.E
    vals = {}
    for (r, s), c in tab.items():
        if c != K.one():
            vals[krepr(S, c)] = c
    if not vals:
        return 'CYCLIC (c == 1 identically, zeta = 1)', True, []
    if len(vals) > 1:
        return ('NOT-CYCLIC (>= 2 distinct non-1 values: %s)'
                % ', '.join(sorted(vals))), False, sorted(vals)
    zname, zeta = next(iter(vals.items()))
    kappa = {(r, s): (1 if tab[(r, s)] == zeta else 0) for (r, s) in tab}
    if E > 8:
        return ('UNDECIDED (E = %d > 8: relabeling search skipped; single '
                'value %s)' % (E, zname)), None, [zname]
    for perm in itertools.permutations(range(1, E)):
        sig = (0,) + perm
        if all(sig[r] + sig[s] == sig[(r + s) % E] + E * kappa[(r, s)]
               for (r, s) in tab):
            return ('CYCLIC zeta = %s, sigma = %s' % (zname, sig)), True, [zname]
    return ('NOT-CYCLIC (single value %s but carry pattern not realizable '
            'by any relabeling)' % zname), False, [zname]


# ================================== main =====================================
def main(smoke=False):
    t0 = time.time()
    print('grt_jc_probe.py -- GRT J-C carry-algebra instrument%s'
          % (' [SMOKE]' if smoke else ''))
    # EXT-GATE (standing rule, MANDATORY per the brief)
    v0 = len(EE.VIOL)
    EE.install()
    EE.check_pins()
    gate_new = EE.agreement_gate(full=False)
    note('EXT-GATE')
    if gate_new or len(EE.VIOL) > v0:
        viol('EXT-GATE', 'engine_ext', '%d new violations' % (len(EE.VIOL) - v0))
    print('  [%6.1fs] EXT-GATE done (new: %d)'
          % (time.time() - t0, len(EE.VIOL) - v0))

    roster = ROSTER if not smoke else \
        [s for s in ROSTER if s['id'] in ('C2A', 'C2I', 'C3A')]
    for spec in roster:
        tA = time.time()
        try:
            S = Stage(spec)
        except Exception as ex:
            note('BUILD')
            viol('BUILD', spec['id'], 'stage build failed: %r' % ex)
            print('  [%6.1fs] %-18s BUILD FAILED: %r'
                  % (time.time() - t0, spec['id'], ex))
            continue
        rec = run_row(S)
        RESULTS['rows'][S.tag] = rec
        c = rec['counts']
        print('  [%6.1fs] %-18s m=%d E=%-3d |K|=%-4d pairs=%-3d scored=%-3d '
              'raw-nosol=%-3d(delta+=%-3d) iso=%d val=%d ob6=%d inner!=1:%-3d '
              'span %d/%d cyc=%s (%.1fs)'
              % (time.time() - t0, rec['id'], rec['m'], rec['E'], rec['nK'],
                 rec['pairs'], c['scored'], c['raw_nosol'], rec['delta_pos'],
                 c['iso_bad'], c['val_bad'], c['ob6_bad'], c['inner_ne1'],
                 rec['span']['ok'], rec['span']['ok'] + rec['span']['fail'],
                 'Y' if rec['cyc']['cyclic'] else
                 ('?' if rec['cyc']['cyclic'] is None else 'N'),
                 time.time() - tA))

    # ---------------------------- aggregate -------------------------------
    fam = {}
    for (f, tag, det) in VIOL:
        fam[f] = fam.get(f, 0) + 1
    RESULTS['families'] = {'counts': COUNTS, 'violations': fam}
    RESULTS['violations'] = [list(v) for v in VIOL]

    print()
    print('=' * 78)
    print('FAMILY TABLE (samples / violations; sealed prediction in the docstring)')
    order = ['EXT-GATE', 'P0-TRUNC', 'P0-ANCH', 'P0-OB2', 'P0-LIFT', 'P0-SCAL',
             'P0-PSI', 'P1-RAW', 'P1-RAW-SET', 'P1-TC3',
             'P2-ISO', 'P2-OFF', 'P2-REP', 'P2-VAL', 'P3-FACT', 'P3-GERM', 'P4-DEG',
             'P4-SPAN', 'P5-OB6', 'MT1', 'MT2', 'MT3', 'MT4', 'BUILD']
    for f in order:
        if f in COUNTS or f in fam:
            print('  %-12s samples %6d   violations %4d'
                  % (f, COUNTS.get(f, 0), fam.get(f, 0)))
    tot = dict(scored=0, raw_nosol=0, delta_pos=0, inner_ne1=0,
               HB_fail=0, HC_fail=0, HD_fail=0, MT1_pairs=0, MT1_fail=0,
               MT4_pairs=0, MT4_fail=0, dcx=0, nonint=0, pairs=0,
               span_ok=0, span_fail=0, span_skip=0, mt3_pairs=0, mt3_caught=0)
    for rec in RESULTS['rows'].values():
        c = rec['counts']
        for k in ('scored', 'inner_ne1', 'HB_fail', 'HC_fail', 'HD_fail',
                  'MT1_pairs', 'MT1_fail', 'MT4_pairs', 'MT4_fail', 'dcx',
                  'nonint'):
            tot[k] += c[k]
        tot['raw_nosol'] += rec['raw_nosol']
        tot['delta_pos'] += rec['delta_pos']
        tot['pairs'] += rec['pairs']
        tot['span_ok'] += rec['spanM']['ok']
        tot['span_fail'] += rec['spanM']['fail']
        tot['span_skip'] += rec['spanM']['skip']
        tot['spanM_zero'] = tot.get('spanM_zero', 0) + rec['spanM']['zero']
        for k2 in ('ok', 'zero', 'fail', 'skip'):
            tot['spanS_' + k2] = tot.get('spanS_' + k2, 0) + rec['spanS'][k2]
        tot['mt3_pairs'] += rec['mt3'].get('pairs', 0)
        tot['mt3_caught'] += rec['mt3'].get('caught', 0)
    RESULTS['totals'] = tot
    print()
    print('TOTALS: rows %d  pairs %d  scored %d  (DCX-censused %d, '
          'non-integral-D %d)' % (len(RESULTS['rows']), tot['pairs'],
                                  tot['scored'], tot['dcx'], tot['nonint']))
    print('P1-RAW: no-solution pairs %d  == delta>=1 pairs %d  (set identity '
          'violations %d)' % (tot['raw_nosol'], tot['delta_pos'],
                              fam.get('P1-RAW-SET', 0)))
    print('P3 inner factor != 1 on %d scored pairs; rival-reading failures: '
          'H-B %d, H-C %d, H-D %d (of %d scored)'
          % (tot['inner_ne1'], tot['HB_fail'], tot['HC_fail'], tot['HD_fail'],
             tot['scored']))
    print('P4-SPAN-M (monomial rank-one probe): %d certified / %d zero-class / '
          '%d FAILED / %d skipped'
          % (tot['span_ok'], tot.get('spanM_zero', 0), tot['span_fail'],
             tot['span_skip']))
    print('P4-SPAN-S (sum census, measured-only): %d certified / %d zero-class '
          '/ %d neither / %d skipped'
          % (tot.get('spanS_ok', 0), tot.get('spanS_zero', 0),
             tot.get('spanS_fail', 0), tot.get('spanS_skip', 0)))
    print('TEETH: MT1 %d/%d designated pairs missed; MT3 %d/%d pairs caught; '
          'MT4 %d/%d missed'
          % (tot['MT1_fail'], tot['MT1_pairs'], tot['mt3_caught'],
             tot['mt3_pairs'], tot['MT4_fail'], tot['MT4_pairs']))
    des = {rec['id']: rec['cyc'] for rec in RESULTS['rows'].values()
           if rec['id'] in CYC_DESIGNATED}
    note('MT2')
    if des and not any(v['cyclic'] is False for v in des.values()):
        viol('MT2', 'designated', 'no designated g_m=2 row is NOT-CYCLIC: %s'
             % {k: v['verdict'] for k, v in des.items()})
    RESULTS['cyc_designated'] = {k: v['verdict'] for k, v in des.items()}
    cycN = sum(1 for v in RESULTS['cyc'].values() if v['cyclic'] is False)
    cycY = sum(1 for v in RESULTS['cyc'].values() if v['cyclic'] is True)
    cycU = sum(1 for v in RESULTS['cyc'].values() if v['cyclic'] is None)
    print('MT2 CYCLIC FENCE: NOT-CYCLIC %d / CYCLIC %d / UNDECIDED %d rows'
          % (cycN, cycY, cycU))
    print()
    print('GERM TABLE (per eligible stage: val(Chat) vs -zbar; kappa; '
          'kappa*val(anchor) vs -zbar)')
    for tag, rec in RESULTS['rows'].items():
        g = rec['germ']
        if not g.get('eligible'):
            print('  %-24s INELIGIBLE (g_m = %d)'
                  % (rec['id'], rec['reads'][-1][2]))
            continue
        print('  %-24s val(Chat)=%-10s -zbar=%-10s kappa=%-12s '
              'kappa*val=%-10s transport %s/%s'
              % (rec['id'], g.get('valChat'), g.get('neg_zbar'),
                 g.get('kappa'), g.get('kappa_times_val'),
                 g.get('transport_bad'), g.get('transport_scored')))
    print()
    print('CYCLIC ADJUDICATION (per row)')
    for tag, v in RESULTS['cyc'].items():
        print('  %-28s %s' % (tag, v['verdict']))
    if VIOL:
        print()
        print('VIOLATIONS (first 60):')
        for (f, tag, det) in VIOL[:60]:
            print('  [%s] %s: %s' % (f, tag, det))
    print()
    print('elapsed %.1fs;  total violations %d' % (time.time() - t0, len(VIOL)))
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_jc_probe_results.json')
    with open(out, 'w') as fh:
        json.dump(RESULTS, fh, indent=1, sort_keys=True, default=str)
    print('wrote %s' % out)
    return len(VIOL)


if __name__ == '__main__':
    sys.exit(0 if main(smoke=('--smoke' in sys.argv)) >= 0 else 1)
