# C.1.5 derivation unit — 2026-07-26

Goal: settle §C's one-move → joint-history product kernel.
Route A: prove C.1.5 (displaced-carry codimension) with initialized induction.
Route B: restructure C.2 to consume per-step conditional counting in child frames
  (D.11 + species region-disjointness + triangular solvability on the solved locus).
Route C: honest open-problem statement.

## S1. Spec (verifier objections from pass 7/8)
## S2. Reading notes: C.0.5 / C.1 / C.1.5 / C.2, D.3(e) / D.8 / D.11, C10B apparatus
## S3. Route decision + informal argument
## S4. The statement and proof
## S5. Instance checks (S6.1, S6.2 reruns + new collision instance)
## S6. Deliverable: exact replacement text
## S7. Loose ends fixed: (HV) naming; absolute v_p-scale declaration

---
*(S1+S2 appended.)*

### S1. The spec (pass-7/8 objections, verbatim scope)

C.1.5's rev-7 proof was rejected because: (1) no INITIALIZED induction — the
package ((INV-a)/(FLOOR)/(INV-c)) is consumed at step i but never established
at the root i = 0; (2) STEP 2's "the level-γ' support is exactly the
stride-admissible positions of its block" imports an exact-support/true-address
assertion STRONGER than D.3(e), D.8, (‡), or PIN-WELLDEF supplies — D.3(e)(ii)
gives only: each digit equation is unitriangular with SOME leading coordinate,
carries reference ≺-earlier coordinates; it does not locate the support of the
level-γ' unit part at exactly the (‡)-positions after iterated developments;
(3) the rim bullet retains a gap; (4) (HV) must be a predicate on node data
alone (name the transported vertex value as a component of ν_i's fixed
pattern); (5) C.1.5's level formulas (stair, off) not reconciled with
C.1.0(c)'s (h − off)/str conversion — declare ONE absolute v_p-scale.

### S2. What each accepted tool actually gives (no more, no less)

(T1) D.3(e)(ii): every stratum/landing locus is cut by UNITRIANGULAR digit
  equations — each pins one digit coordinate as an F-polynomial in strictly
  ≺-earlier coordinates. Counting consequence: k such equations with distinct
  leading coordinates ⟹ mass factor (alphabet)^{−k}.
(T2) D.8 + D.10: per move, stratum ↔ landing cylinder, a digit-level
  unitriangular bijection; (BOX)+(VERTEX)+(TRANSPORT) is the landing content.
(T3) D.11: ONE-move measure exactness: #stratum = p^{nN}·vol(cylinder),
  vol = nominal product over the cylinder's digit equations.
(T4) PIN-WELLDEF (C10B S2.3): a digit-cylinder LOCUS determines its pin set
  and volume — presentation-independent. Two systems, same locus ⟹ same
  |pins|, same vol.
(T5) C.0.5: move maps and their inverses are ≺-unitriangular; pullback of a
  digit system is a digit system with the SAME pins.
(T6) C.1(i)+(ii) (accepted crossing analysis): on the prefix locus T_i,
  E(ν_{i+1}) = E_inh ⊔ E_fresh with E_inh implied; E_fresh's clauses are the
  (α)-strips/digits, (β)-strips, (γ)-strips left of j×, hinge content — all
  with weights STRICTLY above ν_i's old line at their slots, at factor-interior
  indices (rim excluded by C.1's rim bullet).
KEY GAP the rejected proof tried to jump: (T1)'s unitriangularity is per
EQUATION IN ITS OWN FRAME'S coordinates; after substituting T_i's solved form,
the claim "the re-solved equation's lead is a free coordinate at a
predictable-enough address" needs the exact support location — which no tool
supplies. ROUTE B AVOIDS THIS: count without ever re-solving fresh equations
against T_i coordinate-by-coordinate — use (T4) volume well-definedness plus a
one-move exactness (T3) applied IN THE CHILD FRAME, conditioned on the prefix.

---
*(S3 appended.)*

### S3. Route decision: B — per-step conditional counting; the graded mechanism

DECISION: ROUTE B. The rejected C.1.5 tried to re-solve each fresh digit
equation against T_i's solved form and name its true lead — which requires
locating the equation's unit support exactly (the (‡)-address arithmetic),
strictly more than D.3(e) supplies. Route B never names a lead. Its engine:

(KEY OBSERVATION 1 — valuation clauses are literal.) w is DEFINED through
the K1 chain as the iterated slot-minimum, all the way down to Z_p-digits.
Hence in the CURRENT frame's tower coordinates (the iterated development's
digit coordinates, D.3(e)(ii)), a clause "w(B_j) >= beta" is a set of
LITERAL coordinate zeros y_(b,l) = 0 on a per-index initial segment
(downset) — no carries, no addresses. All (BOX) content, all strip zeros,
all staircase floors are of this species.

(KEY OBSERVATION 2 — fresh value digits are graded content.) A fresh value
clause pins the FIRST residual digit of a slot coefficient B at its exact
valuation gamma' (the strip zeros below gamma' are part of the same or the
prior clauses). On the locus where w(B) >= gamma', that digit is
R_{gamma'}(in(B)) — a function of the initial form ALONE, i.e. of the
weight-gamma' LEVEL SET of B's tower coordinates. By D.3(e)(i) the piece
map R_delta is additive, F_Q-linear, INJECTIVE, with explicit image (the
additive span of slot images). No carry ever enters a FRESH value digit:
carries live only in D.8's (TRANSPORT) recursion — inherited/rim content.
[This dissolves the collision problem: S6.2's displaced address was an
artifact of presenting the graded condition as a base digit equation; the
count needs only the piece map's injectivity, never the presentation.]

(KEY OBSERVATION 3 — same-frame step.) Let Sigma_i := Psi_i(S(prefix_i)) be
the state cylinder — the prefix locus presented in frame-(i+1) coordinates.
Then Sigma_i = Theta_i(Sigma_{i-1}) ∩ Λ(ν_i) (D.8/D.10 one-move
two-sidedness), and node ν_{i+1}'s stratum is ALSO a frame-(i+1) system:
both loci live in ONE frame. The counting step is
    mass(Sigma_i ∩ stratum(ν_{i+1})) = mass(Sigma_i) · vol_nom(E_fresh(ν_{i+1})),
and Theorem C's product follows by the mass recursion (moves preserve mass:
global digit-level bijections). Pin-set statements in C.2(a) become
corollaries via PIN-WELLDEF (the locus owns its pin count).

(THE INVARIANT.) The induction carries, instead of (FLOOR)/addresses:
 (ZC-a) VALUATION CORE: Sigma_i's locus = {f : VAL_i ∧ DIG_i} where VAL_i
   is a conjunction of frame-free valuation staircase conditions whose
   current-frame realization is a literal zero downset, per index, with top
   F_i = the pointwise-max staircase of the history's lines over their
   clause regions (C10B (INV-a), machine-checked);
 (ZC-b) RIM SUPPORT: DIG_i is a finite set of graded digit equations (piece
   conditions + D.8-transport carries) ALL of whose variables lie at rim
   indices (>= mu_i·D_{i+1}); count = the number of history value digits;
 (ZC-c) the accepted rim domination (INV-c): later nodes never contradict
   and never re-pin the rim content.
Base case i = 0: the root read. VAL_0 = the initial cluster conditions
(literal zeros) + the root side's staircase; DIG_0 = the root pattern
digits + root transports, rim-supported by D.8 applied at the root (D.4's
ROOT case). Fully explicit — the induction is INITIALIZED.

(THE STEP, informally.) Intersect Sigma_i with stratum(ν_{i+1}):
 - E_inh: implied on Sigma_i (C.1(i)'s accepted crossing analysis).
 - Fresh strip zeros: literal free coordinates strictly above F_i at
   factor-interior indices (region disjoint from the downset by (ZC-a) and
   from DIG_i by (ZC-b)): each cuts mass by exactly p^{-1}.
 - Fresh value digits: on the joint zero locus, condition = (injective
   piece map)(free level set) = (pattern value in the image); the level
   sets are disjoint from everything constrained (above the floor;
   interior; pairwise disjoint across digits by slot/level); each cuts
   mass by exactly (alphabet)^{-1}, alphabet := |image| = |piece| —
   D.11's own per-digit convention (same pieces, same map).
 - (HV)/adjacent hinge: the pattern-lead clause degenerates to the DATA
   identity vtx(ν_i) = (pattern lead) — pins nothing; named in S7.
 - Move by Theta_{i+1} (mass-preserving) and re-present: D.8's landing
   gives the new literal core and the new rim digits; (N1) + rim
   domination keep the old DIG at rim indices: (ZC) persists at i+1.

---
*(S4a appended: scale declaration, the invariant, the statement, base case.)*

### S4a. Lemma C.1.5' — statement and initialization

SCALE DECLARATION (pass-7 item 5, fixed). All heights are ABSOLUTE
v_p-scale rationals. The tower coordinate c = (b, l) (base index b,
integer level l >= 0: the l-th p-adic digit of the b-th iterated
coefficient of the CURRENT frame's tower) has v_p-height
  ht(c) := l + off(b),  off(b) := Sum_r innerslot_r(b)·kappa_r,
  kappa_r := h_r/(e_r·STR_r)  (v_p-scale; C10B S6's recursion).
C.1.0(c)'s conversion l = (h - off_stage)/str is THE SAME map with
off_stage(b) = STR·off(b) and str = STR (the accumulated stretch):
stage-scale h relates to v_p by division by STR. All comparisons below are
v_p-scale at fixed labels; strictness transfers both ways (C.1.0(c)).

DOWNSET NOTATION. For a staircase F (a map b -> Q ∪ {-inf} on an index
set), Z(F) := the system { y_(b,l) = 0 : ht((b,l)) <= F(b) } — literal
zeros, one per coordinate of the region. A valuation clause
"w(B_j) >= beta" equals Z(F) on B_j's block with F = beta - (slot
contributions) unfolded through the K1 chain: DEFINITIONAL (w is the
iterated slot-minimum; a min is >= beta iff every branch is >= beta; at
the leaves v_p(x) >= k iff digits 0..k-1 vanish — literal).

**Definition (state cylinder).** Sigma_i := Psi_i(S(prefix_i)) in
frame-(i+1) tower coordinates; Sigma_{-1} := the full box. Recursion
(D.8/D.10 two-sidedness, one move at a time):
  (R)  Sigma_i = Theta_i(Sigma_{i-1} ∩ stratum_i(ν_i)),
where stratum_i(ν_i) is ν_i's descend stratum in frame-i coordinates.

**Invariant (ZC).** After node ν_i (i >= 0), in frame-(i+1) coordinates:
 (ZC-a) Sigma_i = locus( Z(F_i) ∪ DIG_i ), where F_i := the pointwise max,
   over m <= i, of node m's line staircase restricted to its clause region
   (transported to the current index axis; frame-free content: each
   summand is a valuation statement about f);
 (ZC-b) DIG_i is a finite set of graded digit equations, each condition of
   the form R_delta(level set of one rim block) = (explicit F-polynomial
   in strictly ≺-earlier RIM level sets and history data) — every variable
   at base indices >= mu_i·D_{i+1}; |DIG_i| = the number of value digits
   the history has emitted (vertex + transport + surviving older rim);
 (ZC-c) mass(Sigma_i) = p^{nN} · Prod_{m<=i} vol_nom(E_fresh(ν_m)) for
   every N >= 1 + max constrained level.

**Lemma C.1.5' (per-step conditional exactness).** Let the prefix through
ν_i satisfy (ZC) and be realizable (C.0: (NA), (HV) as named in S7). Let
ν_{i+1} be any read of the frame-(i+1) window with fresh-clause nominal
digit count m* (the D.11/C.1(ii) inventory: strips + value digits). Then
 (1) mass(Sigma_i ∩ stratum(ν_{i+1})) = mass(Sigma_i)·vol_nom(E_fresh(ν_{i+1})),
     vol_nom := the product of the m* per-digit alphabet factors;
 (2) (ZC) holds for Sigma_{i+1} = Theta_{i+1}(Sigma_i ∩ stratum(ν_{i+1}))
     in frame-(i+2) coordinates.
No claim about pin addresses is made; pin-count corollaries follow from
PIN-WELLDEF applied to the loci.

INITIALIZATION (i = 0, the root — pass-7 item 1 fixed). Frame 0: key x,
tower coordinates = the base digits themselves (off = 0, STR = 1).
E(ν_0) = (initial cluster conditions) ∪ (root side pattern):
 - the cluster conditions are literal zeros (non-lead coefficients ≡ 0 mod
   p: the level-0 digits of indices 0..n-1 vanish) — Z(F) form;
 - the root side's span clauses: per-slot valuation bounds (literal zeros
   below the root line) + pattern digits (level sets ON the root line:
   frame-0 pieces are 1-dimensional — base digit coordinates — the piece
   map is the identity on F_p-digits; image = alphabet, trivially);
 - Theta_0 = the root Φ̂-development; D.8 (D.4's ROOT case) gives
   Sigma_0 = Λ(ν_0) = (BOX)+(VERTEX)+(TRANSPORT): (BOX) = Z(F_0) with
   F_0 = the root staircase on the factor interior; (VERTEX)+(TRANSPORT)
   = DIG_0, supported on blocks >= mu_0·D_1 (their defining level sets are
   the old-line level sets of rim blocks; the D.8 carries reference only
   parent slot residuals R(B_j), j >= mu_0 — rim level sets): (ZC-a,b) hold.
   (ZC-c): D.11 at the root move, verbatim (one move, nominal product).

---
*(S4b appended: the step, part 1 — counting on the same frame.)*

### S4b. Proof of C.1.5'(1): the conditional count

All in frame-(i+1) coordinates. Write W := Sigma_i = locus(Z(F_i) ∪ DIG_i).
Solve W's system in ≺-order (unitriangular: zeros are literal; DIG's
equations reference ≺-earlier variables only — D.3(e)(ii)/D.8): W is the
graph of the solved functions over its FREE coordinates; counting on W =
counting free-coordinate assignments.

STEP 1 (inherited clauses cost nothing). stratum(ν_{i+1})'s clause set
splits per C.1 into E_inh ⊔ E_fresh (canonical, by pin membership) with
E_inh IMPLIED on W — this is C.1(i)'s accepted crossing analysis
verbatim ((α) below-old zeros ⊆ Z(F_i); (γ) at and beyond j× weaker than
Z(F_i); adjacent endpoint = (VERTEX)'s own content in DIG_i). So
W ∩ stratum(ν_{i+1}) = W ∩ locus(E_fresh realizations).

STEP 2 (fresh strip zeros: literal, free, disjoint). Every fresh strip
clause is a valuation bound at a factor-interior slot j with
new(j) > old(j) (C.1(ii): (α) interior strips, (β) strips, (γ) strips
left of j×, the non-adjacent endpoint prefix). By the DOWNSET NOTATION
its realization is literal zeros on the region
  S_j := { (b,l) : b ∈ blk(j), F_i(b) < ht(b,l) <= stair_new(b) },
(the part <= F_i is E_inh, already discarded in STEP 1). Each coordinate
of S_j: (i) is NOT in Z(F_i)'s region (strictly above F_i); (ii) is not a
variable of DIG_i (interior index < mu_i·D_{i+1} by C.1's rim bullet;
DIG_i is rim-supported, (ZC-b)); (iii) the S_j are pairwise disjoint
(distinct blocks for distinct j; within a block, disjoint level ranges).
Hence all strip coordinates are FREE coordinates of W, pairwise distinct:
imposing them cuts mass by exactly p^{-|S|}, |S| = the total strip count —
the nominal factor of the zero digits. Let W' := W ∩ locus(strips).

STEP 3 (fresh value digits: graded fiber count). A fresh value clause at
slot j pins the first residual digit of B_j at its exact valuation
gamma' = new(j) (on-lattice slots of the new side; the non-adjacent
endpoint value): ON W' we have w(B_j) >= gamma' (floor zeros ∪ strip
zeros = all levels with ht <= gamma' minus the level set itself... 
precisely: all coordinates of B_j's block with ht < gamma' are zero-pinned
by Z(F_i) ∪ strips — the strip tops reach stair_new = gamma' at b exactly
below the level set), so the digit IS R_{gamma'}(in_{gamma'}(B_j)), a
function of the weight-gamma' level set
  L_j := { (b,l) : b ∈ blk(j), ht(b,l) = gamma' , l ∈ Z>=0 }
alone (KEY OBSERVATION 2; no carries — carries are (TRANSPORT) content,
which is E_inh/DIG, not fresh). The realization is
  (E_j):  R_j(y_{L_j}) = v_j,
R_j := the piece map of D.3(e)(i) — ADDITIVE, injective, image = the
additive span of the admissible slot images; v_j := the pattern value,
an element OF THAT IMAGE (the emission alphabet of the digit is the
image — D.11's own convention: the same piece, the same map, per move).
Count: the coordinates L_j are free on W' ((i) ht = gamma' > F_i(b);
(ii) interior, so disjoint from DIG_i; (iii) disjoint from strips — strips
stop strictly below gamma' at each index; disjoint from L_k, k ≠ j — 
different blocks, or same block different levels never happens: one fresh
value digit per slot per node). Injectivity: the fiber of R_j over v_j
within the level-set assignments has EXACTLY ONE point; the level set has
|piece| = |image| = (alphabet of the digit) assignments. Conditioned on
every other free coordinate (the equation involves no other variable),
(E_j) cuts mass by exactly (alphabet)^{-1}. The (E_j) are variable-
disjoint across j, so jointly they cut the product.

STEP 4 (the adjacent hinge pins nothing). At an adjacent endpoint the
pattern-lead clause's level set is the OLD vertex level set — entirely
inside DIG_i's (VERTEX) equation. Substituting the solved form, the
clause reads vtx(ν_i) = (pattern lead of ν_{i+1}) — an identity of
HISTORY DATA (both sides explicit functions of node data, S7): by
realizability ((HV)) it holds, and the clause is E_inh (no factor). If it
fails, both sides are constants and the intersection is EMPTY — the
history is excluded by C.0's quantifier. Likewise (NA)'s arithmetic at
slot mu_i ((γ)'s crossing endpoint) constrains data, not f. 

CONCLUSION (1): mass(W ∩ stratum) = mass(W)·p^{-|S|}·Prod_j (alphabet_j)^{-1}
= mass(Sigma_i)·vol_nom(E_fresh(ν_{i+1})). No lead was ever named. ∎(1)

---
*(S4c appended: the step, part 2 — persistence; one amendment to (ZC-b).)*

### S4c. Proof of C.1.5'(2): persistence of (ZC); the (ZC-b') amendment

AMENDMENT (found while proving persistence; the deliverable S6 uses this
form). (ZC-b)'s "every variable at rim indices" is too strong under
Theta-pushes: a pushed equation acquires unitriangular corrections
referencing ≺-earlier coordinates, which include lower levels at interior
indices. What S4b consumed, and what persists, is:
 (ZC-b') LEADS AT RIM: DIG_i is a unitriangular system whose equations
   solve, in ≺-order, for their LEADING variables (per-equation: the
   coordinates of one rim-block level set), all at base indices
   >= mu_i·D_{i+1}; non-lead arguments are unrestricted (≺-earlier).
S4b's counting is unaffected: it needs only that (a) the interior
coordinates strictly above the floor are never LEADS of Z(F_i) ∪ DIG_i —
so they are free coordinates of the solved graph — and (b) constraining a
free coordinate (strip zero) or a free level set (fresh digit) cuts mass
exactly, which holds on any solved graph regardless of where those
coordinates appear as arguments of other equations' right sides. ht-scale
remark consumed there: the floor at index b in ht-terms is
max_m old_m(slot_m(b)) — constant across each block — so gamma' > old(j)
puts the ENTIRE level set L_j strictly above the floor (the absolute
v_p-scale declaration is what makes this per-index-uniform).

PROOF OF (2). Sigma_{i+1} = Theta_{i+1}(Sigma_i ∩ stratum(ν_{i+1})); mass
is preserved (global digit-level bijection), so (ZC-c) at i+1 follows
from (1). For (ZC-a,b'):
STEP A (same-frame implication, then split). In frame i+1, the joint
system is Z(F_i) ∪ DIG_i ∪ (fresh strips) ∪ (fresh values). Split by the
NEXT factor interior I' := [0, mu_{i+1}·D_{i+2}):
 - On I': I' ⊆ [0, w'·D_{i+1}) (width inequality (W)), so I''s slots are
   span/(β) slots of ν_{i+1}, where new >= old_i >= (older floors, by the
   C10B (INV-a) induction: the current line dominates the floor on the
   current interior — machine-checked invariant). Hence the old zeros on
   I' are IMPLIED by ν_{i+1}'s own valuation clauses (same frame, same
   slot coefficients, lower thresholds: downset containment) — drop them.
 - Off I': the surviving old content — old zeros in excess of the new
   staircase (the (γ) region at/beyond j×, base indices >= j×·D_{i+1} >
   w'·D_{i+1} >= mu_{i+1}D_{i+2}) and DIG_i (leads at >= mu_i·D_{i+1} >=
   mu_{i+1}D_{i+2} by (N1)) — sits with all its LEADS at future-rim
   indices.
STEP B (move and re-present). Apply Theta_{i+1}:
 - ν_{i+1}'s own content maps, by D.8/D.10 two-sidedness (one move,
   exact), onto Λ(ν_{i+1}) = (BOX)+(VERTEX)+(TRANSPORT) in frame-(i+2)
   coordinates: (BOX) is the literal zero downset Z(new staircase) on I'
   (DOWNSET NOTATION in frame i+2 — definitional through K1(Φ̂_{i+1}/w));
   (VERTEX)+(TRANSPORT) are piece-map equations with leads = the level
   sets of blocks >= mu_{i+1}D_{i+2} and constant right sides (D.8's
   carries are functions of the pinned pattern — history data).
 - The surviving old content pushes to Theta-translates: unitriangular
   equations with THE SAME leads (C.0.5: corrections are ≺-earlier;
   re-solving for the same leading level set stays unitriangular) — all
   leads at future-rim indices.
So Sigma_{i+1} = locus( Z(F_{i+1})|_{I'} ∪ DIG_{i+1} ) with F_{i+1} =
ν_{i+1}'s staircase on I' (= the pointwise max, by STEP A's domination)
and DIG_{i+1} := (VERTEX)+(TRANSPORT) ∪ (pushed survivors): leads at rim.
(ZC-a) + (ZC-b') hold at i+1. ∎(2)

WHAT WAS CONSUMED, per claim: C.1(i) crossing analysis (accepted); C10B
(INV-a)/(N1)/rim-domination (machine-checked; rim-domination enters only
via C.1's rim bullet: fresh clauses live on the factor interior); D.8/
D.10 two-sidedness + carry structure (accepted); D.3(e)(i) per-piece
additivity/injectivity/image (accepted); D.3(e)(ii) literal tower
coordinates (accepted); K1 chain = downset definitionality (accepted);
C.0.5 unitriangularity (accepted); PIN-WELLDEF only for the pin-count
corollaries, never for the mass. NO address arithmetic anywhere: the
(‡)-offsets appear only inside the piece maps' internal structure, which
the count never opens.

---
*(S5 appended. Script /tmp/c15_check.py, output /tmp/c15_check.txt.)*

### S5. Instance checks — all pass

S5.1 S6.1 RERUN (p=2, n=5, chain (1,1,2)mu=2 -> (2,5,1) adj -> (1,11) adj),
now as a SAMPLING CENSUS of C.1.5'(1) itself (the derivation's c10b check
was label arithmetic only; this one measures the conditional MASSES):
node-0 stratum imposed exactly (literal digits, pattern psi^2 = (1,0,1,0,1));
300,000 members; Phi1 = x^2+2x+4; Phi2 = Phi1^2 + t0 with the (S6b) lift
t0 found by search = p^4·x (unique among the p^2−1 candidates).
 - SANITY (D.8 exactness): (BOX)/(VERTEX)+dig'(B2)=1 hold on ALL 300k: 0
   violations. [(HV) exercised: the vertex digit is FORCED = vtx(nu_0)=1.]
 - P(node-1 | node-0) = 0.25009 vs predicted vol_nom = p^{-2} = 1/4
   (one F_4-digit: 2 base pins): z = +0.11.
 - CARRY-CANCELLATION FALSIFIER: the frame-2 ht-5 digit of B0' must vanish
   IDENTICALLY on node-1 members (D.8 transport absorbs node-1's value
   pins): 0 failures of 75,027.
 - P(node-2 | node-1) = 0.25102 vs 1/4: z = +0.64. Joint 0.062777 vs 1/16.
 - LEVEL SETS by ht-arithmetic (current-frame kappas: kappa_1 = 5/2 after
   the (2,5) read): node-1 digit at G=5: {(0,5),(1,4)}; node-2 digit at
   G=11/2: {(2,3),(3,2)}, indices 0,1 stride-inadmissible — EXACTLY the
   machine-checked fresh labels of the c10b note, now DERIVED as level
   sets, no leading-coordinate choice anywhere.

S5.2 NEW COLLISION INSTANCE (p=3, F_9, designed): same chain shape over
p=3: psi = z^2+1, pattern psi^2 = (1,0,2,0,1); nodes (2,5,1) then (1,11);
D_0 = zbar so that c-tilde = -zbar/1 and signs are exercised. COLLISION BY
DESIGN: the node-2 digit's naive (stale-weight) address is node-1's pin
pair {(0,5),(1,4)}, value-pinned with (1,4) |-> 1 NONZERO — while the true
level set {(2,3),(3,2)} (ht-arithmetic) is disjoint from every pin, floor
ht 5 < 11/2. Census (300,000):
 - sanity violations 0; the (S6b) lift again unique = p^4·x;
 - P(node-1 | node-0) = 0.11048 vs 1/9 (one F_9-digit = 2 base pins,
   3^{-2}): z = −1.09;
 - cancellation falsifier: 0 of 33,145 (the p=3 sign structure confirmed);
 - P(node-2 | node-1) = 0.11290 vs 1/9: z = +1.04; joint 0.012473 vs 1/81.
 Also exercised: a 1-dimensional piece (the vertex digit at integer ht has
 image F_3 inside F_9 — the per-piece alphabet convention of S4b STEP 3).

S5.3 S6.2 RERUN (static ht-arithmetic; n=9, root (1,1,2) mu=4, node 1 =
(3,7,1) at s0'=1, node-2 tail): my statements reproduce every recorded
verdict:
 - (β)-strip pins at slot 0 = {(0,9),(1,8)} (floor 8,7; top new(0)=28/3);
 - node-1 pattern digit = {(2,7),(3,6)} (frame-1 inner offsets);
 - frame-2 zero core tops at 28/3 = w(f) ((BOX) strict), whose ht-28/3
   level set is THE SAME LABELS (2,7),(3,6): node-1's base-side VALUE pins
   reappear frame-2-side as ZEROS — the transported value cancels against
   the lift (MOVE-INV preserves pin sets, not zero/value character). This
   is (ZC-a)'s content in its subtlest corner, confirmed;
 - the REJECTED h2=28 read: its level set at G=28/3 = {(2,7),(3,6)} lies
   entirely inside the zero core — the hull point at slot 0 is strictly
   above 28/3, the read has empty stratum: my framework EXCLUDES it as a
   non-hull read (matches the c10b checker's rejection + diagnosis);
 - the corrected h2=22 read: level set at G=29/3 = {(4,5),(5,4)}, free,
   floor top l=4 at idx 4 — the recorded fresh labels, nominal count 2.

MORAL. In correct current-frame ht-arithmetic the "displaced-carry
collision" NEVER occurs: fresh level sets are automatically strictly above
the floor (that is S4b STEP 2/3). The rev-7 "collision" was stale-weight
label arithmetic (frame-1 kappas applied to frame-2 demands); the S6.2
"rejection" was a non-hull read. Both dissolve, and the conditional masses
are exactly nominal at 4 sealed-style census points.

---
*(S6 appended — the deliverable.)*

### S6. Exact replacement text

REPLACES: the whole of §C's "C.1.5 The displaced-carry codimension lemma"
(MOVES_2026-07-24.md, rev 7) and the PROOF of C.2 (statement of C.2
unchanged except as flagged). Every hypothesis is a predicate on node
data; no address claim survives anywhere.

------------------------------------------------------------------
### C.1.5 The per-step conditional exactness lemma (supersedes the
displaced-carry codimension lemma; rev 8)

**Scale.** All heights are absolute v_p-scale rationals. The current
frame's tower coordinate (b, l) has height ht(b,l) := l + off(b),
off(b) := Σ_r innerslot_r(b)·κ_r over the coordinate's INNER tower levels,
κ_r := h_r/(e_r·STR_r) with the CURRENT stage weights (a key's κ changes
at its augmentation). C.1.0(c)'s conversion is this same map in stage
scale (off_stage = STR·off, division by STR); strictness transfers.

**Downsets are literal.** Since w is defined through the K1 chain as an
iterated slot-minimum, a valuation clause "w(B) ≥ β" is, in the frame's
own tower coordinates, the literal zero system {y_(b,l) = 0 :
ht(b,l) < β, b ∈ blk(B)} (plus ht = β when β is demanded strictly). No
carries occur in valuation content.

**State cylinder.** Σ_i := Ψ_i(S(prefix_i)), the prefix locus in
frame-(i+1) coordinates; Σ_i = Θ_i(Σ_{i−1} ∩ stratum(ν_i)) (D.8/D.10).

**Invariant (ZC), carried along the history.**
 (ZC-a) Σ_i = locus(Z_i ∪ DIG_i), Z_i := the literal zero downset with
   per-index top F_i := the pointwise max of the history's line
   staircases over their clause regions (in ht-terms, constant per block:
   F_i(b) = max_m old_m(slot_m(b)));
 (ZC-b) DIG_i is unitriangular with each equation solving for the level
   set of one rim block (base indices ≥ μ_i·D_{i+1}) — LEADS AT RIM;
   non-lead arguments unrestricted;
 (ZC-c) mass(Σ_i) = p^{nN}·∏_{m≤i} vol_nom(E_fresh(ν_m)) for every
   N ≥ 1 + the largest constrained level.
Initialization: at i = 0, (ZC) is D.8 at the root read (D.4 ROOT case):
Z_0 = cluster zeros + (BOX), DIG_0 = (VERTEX)+(TRANSPORT) (leads = rim
level sets, right sides = history constants), (ZC-c) = D.11, one move.

**Lemma.** Let the prefix through ν_i satisfy (ZC) and be realizable
(C.0's (NA) and (HV), the latter as defined in C.0 via vtx(ν_i)). Let
ν_{i+1} be a read of the frame-(i+1) window with fresh nominal digit
count m* (C.1(ii)'s inventory). Then
 (1) mass(Σ_i ∩ stratum(ν_{i+1})) = mass(Σ_i)·vol_nom(E_fresh(ν_{i+1}));
 (2) (ZC) holds for Σ_{i+1}.
*Proof.* (1): Solve Σ_i's system in ≺-order (graph over free
coordinates). E_inh is implied (C.1(i)). Fresh STRIP clauses are literal
zeros at coordinates with ht strictly above F_i at factor-interior
indices: not in Z_i, not leads of DIG_i ((ZC-b): rim), pairwise distinct —
each cuts exactly p^{−1} on the graph. Fresh VALUE clauses pin the first
residual digit of a slot coefficient B at its exact valuation γ' =
new(slot): on the joint zero locus the digit is R_{γ'}(in_{γ'}(B)) — a
function of the weight-γ' level set alone (graded content; carries are
(TRANSPORT) = inherited); by D.3(e)(i) the piece map is additive and
injective with image = the digit's alphabet, so the equation cuts exactly
(alphabet)^{−1}; level sets sit strictly above F_i (γ' > old, in
ht-terms uniform across the block), are interior, and are pairwise
disjoint (one per slot): the factors multiply. The adjacent hinge's lead
clause degenerates to the data identity (HV) — pins nothing (or empties
the stratum: excluded by realizability). (2): mass by (1) + bijectivity;
split by the next interior I' = [0, μ_{i+1}D_{i+2}) ⊆ [0, w'D_{i+1}):
on I' the old zeros are implied by ν_{i+1}'s clauses (new ≥ old there;
same frame, same coefficients, downset containment); off I' the
survivors — old zeros beyond the crossing slot (indices ≥ j×D_{i+1} >
w'D_{i+1}) and DIG_i (leads ≥ μ_iD_{i+1}) — have all leads at future-rim
indices, and Θ_{i+1}-pushforward preserves leads (C.0.5). ν_{i+1}'s own
content re-presents as Λ(ν_{i+1}) (D.8/D.10 two-sidedness): (BOX) = the
new literal core on I', (VERTEX)+(TRANSPORT) = new rim equations with
history-constant right sides. ∎
*(What C.2 consumes: (ZC-c)'s mass recursion. Pin-set language: by
PIN-WELLDEF the locus Σ_i has a well-defined pin count, = |Π_i| :=
Σ_{m≤i} m*(ν_m); no pin ADDRESS is defined or needed.)*
------------------------------------------------------------------

------------------------------------------------------------------
REPLACEMENT for C.2's *Proof* (statement of Theorem C unchanged, except:
in (a), "T(H, Z) is a digit system with pins = Π_k ⊔ pins(Z)" is read
via PIN-WELLDEF as a statement about the LOCUS's pin count; Π_k :=
Σ m*(ν_m) with the C.1 freshness selection, and Z-admissibility means
pins(Z) at coordinates free on Σ_k — equivalently pins(Z) ∩ pins(Σ_k) = ∅,
well-typed by PIN-WELLDEF):

*Proof.* Induction along the prefix with the state cylinder Σ_i and the
invariant (ZC) of C.1.5, initialized at the root (C.1.5's base = D.8 +
D.11 at ν_0). Step: C.1.5(1) multiplies the mass by exactly
vol_nom(E_fresh(ν_{i+1})); C.1.5(2) re-establishes (ZC); the move maps
are global digit-level bijections (Fact A/B), so S(prefix_{i+1}) has the
same mass as Σ_{i+1}. After ν_k, append Z: its pins are free coordinates
of Σ_k's solved graph (admissibility), so Z cuts exactly vol(Z). This
gives (b): #{f mod p^N ∈ S(H, Z)} = p^{nN}·∏_{i=0}^{k}
vol(E_fresh(ν_i))·vol(Z) for every N ≥ N(H, Z). For (a): S(H, Z) is the
solution set of T(H, Z) (C.1(i): the inherited clauses are implied
stepwise, so intersecting with each stratum adds exactly the fresh
realizations); its pin count is Σ m* + |pins(Z)| (PIN-WELLDEF + the mass
count: a digit-cylinder locus of mass p^{nN}·p^{−K} has exactly K pins);
Ψ_H maps it bijectively onto the pushforward system's locus with the
same pins (C.0.5 applied stepwise to the inverses, as before). ∎
------------------------------------------------------------------

ADJUSTMENTS ELSEWHERE IN §C (all small, listed exhaustively):
1. C.1(ii)'s final sentence (the "NO claim... stride-displaced FREE
   address" caveat) is replaced by: "No base ADDRESS of a digit
   equation is ever claimed or used: C.1.5 counts fresh value digits by
   the injectivity of the piece map on the weight-γ' level set (which
   lies strictly above the cumulative floor), and C.2 consumes only
   masses and freshness."
2. The (FLOOR)/(INV) package paragraph heading C.1.5 (rev 7) is deleted
   with the lemma it served; C.1's proof bullets keep citing the
   derivation's (INV-a)/rim-domination, now via (ZC-a)/(ZC-b).
3. C.3's VOLUME STRUCTURE sentence gains: "per-digit alphabets are the
   piece-map images of D.3(e)(i) (= residue-field copies at fresh side
   digits; possibly proper subfields at 1-dimensional pieces, e.g.
   integer-height vertex digits), identical to D.11's convention."

### S7. The two bundled fixes (exact text, for C.0)

(HV) REPLACEMENT in C.0 (REALIZABLE histories): define, as a component
of node ν_i's data, its ANCHORED RESIDUAL POLYNOMIAL R_anch(ν_i) :=
Σ_j d_j·z^{p_j(γ_i)−a_i} ∈ F_i[z] (d_j = the FIXED side-pattern digits,
p_j = D.3(c)'s stride positions, a_i = the anchor) — pattern data only —
and its TRANSPORTED VERTEX VALUE
  vtx(ν_i) := z̄^{−μ_i·m̂_i}·z̄^{a_i}·((R_anch(ν_i)/ψ_i^{μ_i}) mod ψ_i)
              ∈ F_{i+1}ˣ.
  (HV) at an ADJACENT read ν_{i+1}: (pattern lead of ν_{i+1}) = vtx(ν_i).
Both sides are explicit functions of node data: (HV) is a predicate on
the history alone. [Why well-defined: the descend stratum fixes the FULL
side-digit tuple (d_j), which determines R_anch(ν_i) completely; D.8's
split R_anch = (ψ-normalized pattern)·h̃ is a factorization OF this fixed
polynomial, so (R_anch/ψ^μ) mod ψ — hence vtx — is pattern data, not
f-data. Exercised live in S5.1/S5.2: vtx(ν_0) = 1 forced the vertex
digit on all 600k census members, 0 violations.]

SCALE DECLARATION for §C's preamble (reconciling C.1.5 with C.1.0(c)):
insert after C.1.0(c): "All of §C's height comparisons are in absolute
v_p-scale; a base coordinate (b, l) has height l + off(b) with off(b)
the inner-tower offset at CURRENT stage weights (κ_r = h_r/(e_r·STR_r));
C.1.0(c)'s (h − off)/str is this map in stage scale. A key's κ is
updated at its augmentation — stale-κ arithmetic is the source of the
rev-7 'displaced address' artifact (derivation note S5)."

---
### S8. Status and honest perimeter

ROUTE TAKEN: B. C.1.5 (displaced-carry codimension) is SUPERSEDED, not
proved: its address claims are unnecessary and its collision phenomenon
is a stale-scale artifact (S5). The replacement C.1.5' consumes only:
D.3(e)(i) per-piece additivity/injectivity/image, D.3(e)(ii) literal
tower coordinates, the K1 chain (downset definitionality), D.8/D.10
two-sidedness + carry structure, D.11 (root base case), C.1(i)/(ii)
crossing inventory, (W)/(N1), C.0.5, PIN-WELLDEF — all accepted.
NEW load-bearing claims INTRODUCED here (for the verifier's attention):
 (i) "valuation clause = literal zero downset in the frame's own tower
     coordinates" (S4a DOWNSET NOTATION) — definitional via K1, but the
     K1-chain-to-leaves unfolding should be line-checked;
 (ii) "a fresh value digit is graded content: on the joint zero locus it
     is R_{γ'}(in_{γ'}(B)), level-set-supported, carry-free" (S4b STEP 3);
 (iii) the (ZC-b') leads-at-rim persistence under Θ-pushforward (S4c);
 (iv) the same-frame implication direction old ⇐ new on the next interior
     (S4c STEP A) — dual to C.1(i), same crossing input.
Instance evidence: 4 census points (2 per prime) at exactly nominal
conditional masses; 2 falsifier families at exact zero; every recorded
c10b label verdict re-derived by ht-arithmetic. NOT covered by instances:
recentering steps inside the chain (S4's proof covers them via D.10 =
g = 1, but no census here; Case-L's sealed 3-move gate with a
recentering remains the standing empirical cover), depth > 3, s0' > 0
census (S6.2 rerun is arithmetic-only; the Case-L census covers the
β-strip masses). Re-enters the §C pass loop as rev 8.
