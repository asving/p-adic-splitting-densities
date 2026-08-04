# GRTJB — J-B, THE TREE JUNCTION: the expansion identity, the polygon identity through the displayed shear, the division-step correspondence (the [RMG] tree = the classifier's own division arithmetic, with LED-Λ's line face as the polygon bookkeeping), and the (C-READ) transport with the ε-carry collapse

**Unit:** J-B COMPOSER (weld dependency order: W-2 and J-A composed and
consumable at attempt grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md`
§S2.2 (J-B) and §S3.1 rows W-3/W-5). **Genre: PROOF NOTE at attempt grade
(acceptance counter 0/2; no gate fires; no acceptance arc opened), with
sealed-runner machine brackets** (`verification/openmath/grt_jb_checks.py`,
two-commit seal).

**Grade cap (read first).** JB-DEV (§2) is PROVED at attempt grade — its
byte clause exactly on the W-2 byte-equality perimeter, its representative
clause on W-2 clause 1's perimeter, its residual layer at J-A's grades
(unconditional at read level 2, per-digit proviso above — JA-BOX-2
inherited). JB-VTX (§3) is PROVED at attempt grade at every level, stated
at the harness key as the W2-C1 admissible representative; the shear is
DISPLAYED (the GD-2/T-F convention pin made explicit — the unsheared
identification is FALSE and is this note's teeth family). JB-TREE (§4) is
PROVED at attempt grade on [RMG]'s own scope (T-scope(m) termination fence,
g_m = 1 rows for the Ĉ_m instance), consuming [RMG] as ACCEPTED and LED-Λ
at ATTEMPT grade (its λ_E face is cited as the polygon bookkeeping — the
grade rides). JB-CREAD (§5) is PROVED on the (VD-m) perimeter (unconditional
at m ≤ 2; per-digit proviso / (R-coll) at m ≥ 3) intersected with the
non-degenerate read stratum v ≠ 0 (the v = 0 branch displayed at the
theorem), with the ε-collapse lemma JB-EPS unconditional. ONE BLUEPRINT DISPLAY IS CORRECTED (JB-BOX-1):
J-B(iii)'s "shifts the classifier's residual read by τ_m with the level-m
EPS-carry z_m^{ε′}" — in the print's own twisted coordinates the carry
CANCELS (the shift constant is c_m = ψ_{m,0}, = −z_{m+1} one level up);
the carry-bearing form is the HARNESS-frame statement ([RMG] (C-READ)
itself). Nothing here fires any gate, touches any accepted text, makes any
gr/carrier (J-C) claim, or advances any density (J-D) statement.

**Literature and consumption discipline.** Classifier side = the GMN print
`docs/references/HigherNewton.tex`, consumed as literature through the
SEALED probe transcription `grt_weld_probe.GmnLeg` (no new print
transcription in this unit; the runner's fresh legs are its own division/
hull/integer recomputations). Print anchors used here beyond J-A's list:
the order-r polygon definition N_r(f) from the φ_r-adic development with
ordinates u_i := v_r(a_i φ_r^i) = v_r(a_i) + i·v_r(φ_r) (tex ~1370–1376,
"We define the Newton polygon N_r(f) … Note that we consider the v_r-value
of the whole monomial"); the principal part N_r^−(f) = negative-slope sides
(tex 1377); Lemma `shape` items 1–2 (min_i u_i = v_r(f), ℓ(N_r^−) = ω_r;
tex ~1395–1414); Definition `t(i)` (tex 1431), `rescoeff` (tex 1447),
`defresidual` (tex 1497); Proposition `propertiesv` item 3 (tex 1028).
Consumed notes: **[RMG]** = `RMENGINE_2026-08-08.md` ACCEPTED (S0.2 the
(RM-m) box verbatim incl. (C-READ)/(C-EPS); S2.1 cells/lines/L-CELL/L-NORM;
S2.2 (ID-(i+1)) + the E1-priority tree + L-EXACT + L-CANON; S3.2 L-LINE;
S4 T-TERM on T-scope(m)); **[ILN]†** S0.1/S0.2 (accepted; class pin,
canonical lifts, REALIZE/WELL-DEF incl. the g_m = 1 form
Φ_{m+1} = Φ_m^{e_m} + Ĉ_m); **W-2** = `GRTW2_PROOF_2026-08-08.md` at
ATTEMPT grade (clause 1 admissibility W2-C1/C1a; clause 2 byte law §3.4(3)
+ (C-coll) split; clause 3 transport W2-C3; W2-L0/L2/L3); **J-A** =
`GRTJA_PROOF_2026-08-08.md` at ATTEMPT grade, arc 0/1 clean (JA-PIN,
JA-VAL, JA-EPS, JA-GRID, JA-RES/(VD-m)/JA-VDIND with JA-BOX-1..5);
**LED-Λ** = `LEDGERLAMBDA_2026-08-08.md` at ATTEMPT grade (the S1 quantum
table's λ_E column, LED-Λ(A1)/(B), L-MONO's edge signs). Every consumption
is at the source's own grade; nothing is upgraded here.

**Machine bracket:** `grt_jb_checks.py` — both sides of every §2–§5
equality on the weld-probe roster (16 towers) + the 5 concrete QO shapes +
the 4 fresh d₀ ≥ 2 shapes (engine_ext standing rule honored in-unit),
LAW-KEYED with teeth; transported-chamber re-instantiation on every tower
with a nontrivial W-2 transport ledger. Verdict in §7 (commit 2).

---

## §1. Setting, indexing, and the two frames (fixed once)

Harness and P-index dictionary VERBATIM from J-A §1 (itself from W-2
§1.1–1.2): [ILN]† S0.1 class pin; GMN level i = harness read i−1; GMN keys
φ_i = harness Φ_{i−1}; v_i = w_{i−1} (THEOREM JA-VAL, consumed); GMN
order-q residual R_q pairs with the harness level-q read R_q v; pins
(P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the probe. **Shared-key
perimeter at level q**: Φ_j^har = φ_{j+1}^cls byte-for-byte for all j ≤ q.
Read data A_m := ℓ_{m−1}g_{m−1}γ_m, W_m := w_mΦ_m as in W-2/J-A.

**The two frames.** Fix a level q (0 ≤ q ≤ n) and nonzero f ∈ O[x] with
Φ_q-development f = Σ_i A_i·Φ_q^i (iterated division by the monic Φ_q).

    PRINT FRAME    U(f) := { (i, u_i) : A_i ≠ 0 },
                   u_i := v_{q+1}(A_i·Φ_q^i) = v_{q+1}(A_i) + i·v_{q+1}(φ_{q+1})
                   — the print's own N_{q+1}-ordinates (tex ~1370).

    SHEARED FRAME  H(f) := { (i, e_q·w_q(A_i) + i·γ_{q+1}) : A_i ≠ 0 }
                   — the harness eq-(12) ordinates (the S0.2 weight
                   recursion's arguments; the GD-2 frame normalization).

    THE SHEAR      Σ_q : (i, u) ↦ (i, e_q·u + h_q·i).

The names are load-bearing: GD-2's T-F machine check (41,720 instances)
verified the polygon tie in the SHEARED frame and measured 7,472 violations
of the unsheared identification — every polygon statement below displays
which frame it lives in, and the shear itself is a theorem clause (§3(a)),
never a silent convention.

---

## §2. THEOREM JB-DEV (the expansion identity = blueprint J-B(i) first half; W-3)

**THEOREM JB-DEV.** Level q ≥ 0, f ∈ O[x] nonzero, notation §1.

**(i) [same division].** Φ_q^har is monic of degree m_{q+1}^GMN, and the
print's φ_{q+1}-adic development of f AT THE REPRESENTATIVE
φ_{q+1} := Φ_q^har is the harness Φ_q-development digit-for-digit: both
are THE canonical division chain by the same monic polynomial (uniqueness
of division with remainder). Under W-2 clause 1, Φ_q^har is a GMN Def-2.12
admissible representative on W-2's perimeter (of the ξ-conjugate class at
the pinned (P-ell) convention; of the type itself when the character is
support-trivial; STRICT at every level of the transported chamber, W2-C3)
— so the left side is a legitimate print development, not a harness-only
object.

**(ii) [byte clause].** If the junction chain is byte-equal through q (the
W-2 §3.4(3) byte law from read data; TH-BASE gives it always at q = 1),
then φ_{q+1}^cls = Φ_q^har byte-for-byte and (i) is the classifier's OWN
expansion at its own construct key. On the weld roster the byte-equal set
is the probe's F1 verdict pattern (12 GREEN / 18 RED of 30 walked
junctions, reproduced by W-2's CK-BYTE from read data alone — consumed).

**(iii) [coefficient correspondence, three layers].** For the common
digit list (A_i):

    (VAL)  w_q(A_i) = v_{q+1}(A_i) for every i           [JA-VAL, consumed]
    (GRID) the on-line attained abscissas lie on the print's T-side grid
           s + j·e_q, and the plain carry = the side-lattice crossing
           indicator                                  [JA-GRID/W2-L0, consumed]
    (RES)  at read level m := q+1 ≥ 2 the print residual coefficients obey
           the per-slot character-gauge law c_i = z_{m−1}^{−i·A_{m−1}}·C_i
           against the harness packed digits C_i — unconditional at m = 2,
           per-digit proviso at m ≥ 3            [JA-RES, consumed with
                                                  JA-BOX-1/BOX-2 verbatim]

**(iv) [cross-key fence, displayed not claimed].** For a DIFFERENT strict
representative φ′ of the same type, blanket digit equality and blanket
operator equality are FALSE (J-A §4(i): v_{r+1}(φ − φ′) = e_r·v_r(φ) —
the standard MacLane representative-dependence); the lawful transport
across representatives is W-2 clause 2's covariance (slot-ratio characters)
and clause 3's chamber re-instantiation, never a byte identity. This is
the JuncForge parity-wall lesson honored: J-B is stated against the
semantic development objects at a NAMED representative; no SideReads/
TreeModel transcription is consumed.

*Proof.* (i) Uniqueness of quotient and remainder in division by a monic
polynomial over any commutative ring: the print's development (tex
`phiradic` genre) and the harness development are the same recursion; the
representative legitimacy is W-2 clause 1 consumption. (ii) W-2 §3.4(3)
byte law + TH-BASE, consumed. (iii) consumption as displayed. (iv) cited.
∎ Grade: PROVED at attempt grade with the displayed consumptions; no
clause here upgrades W-2/J-A. [Machine: JB-DEV — the development recomputed
by this runner's OWN schoolbook division (fresh leg, decorrelated from the
shared PolyO.dev used by both engines) and compared against both engines'
digit lists at every shared level; JB-KEYEQ — byte-equality census tied to
the W-2 read-data byte law; teeth MJB-DEV.]

---

## §3. THEOREM JB-VTX (the polygon identity = blueprint J-B(i) second half; W-3)

**LEMMA JB-AFF (two lines, displayed).** Let Σ : (i, u) ↦ (i, a·u + b·i + c)
with a > 0, b, c ∈ ℚ. Then Σ maps lower convex hulls to lower convex hulls
and vertices to vertices, bijectively, preserving abscissas. *Proof.* Σ is
affine and abscissa-preserving, so it maps segments to segments and
preserves "lies strictly below the chord": a·u + b·i + c < a·u′ + b·i + c
⟺ u < u′ at equal i, since a > 0. Hulls, faces, and strict-vertex
conditions are defined by these two relations. ∎

**THEOREM JB-VTX.** Level q with read (e_q, h_q) defined (0 ≤ q ≤ n),
f ∈ O[x] nonzero, frames as §1, all statements at the representative
φ_{q+1} := Φ_q^har (legitimate by W-2 clause 1 on its perimeter; on
byte-equal chains this is the classifier's own key, JB-DEV(ii)).

**(a) [the shear is exact, pointwise].** H(f) = Σ_q(U(f)) with
Σ_q(i, u) = (i, e_q·u + h_q·i): indeed e_q·u_i + h_q·i =
e_q·v_{q+1}(A_i) + i·(e_q·v_{q+1}(φ_{q+1}) + h_q) = e_q·w_q(A_i) + i·γ_{q+1}
by JA-VAL and the weight recursion γ_{q+1} = e_q·w_qΦ_q + h_q (JA-PIN
clause 7). Moreover e_q·u_i + h_q·i = v_{q+2}(A_i·Φ_q^i) (propertiesv
item 3 at a single digit): THE SHEARED FRAME IS THE PRINT'S OWN NEXT-LEVEL
BOOKKEEPING — the harness ordinates are the v_{q+2}-values of the
monomials, the print ordinates their v_{q+1}-values.

**(b) [vertex-for-vertex].** By (a) and JB-AFF, the harness development
polygon (lower hull of H(f)) equals Σ_q(N_{q+1}(f)) vertex-for-vertex,
same abscissas; equivalently N_{q+1}(f) = Σ_q^{−1}(harness polygon). This
is GD-2's displayed clause with the shear EXPLICIT. The unsheared
identification (hull of {(i, w_q(A_i))} against N_{q+1}(f)) is FALSE in
general — the T-F 7,472-violation genre; teeth family MJB-VTX.

**(c) [slope/length translation].** A print side of slope σ over abscissas
[i₀, i₁] maps to a sheared side of slope e_q·σ + h_q over the same
[i₀, i₁]; lengths (abscissa runs) are preserved. In particular:
the REALIZED side σ = −h_q/e_q maps to slope 0 — the sheared frame is the
frame in which the read side is HORIZONTAL, at height
min_i(e_q·w_q(A_i) + i·γ_{q+1}) = w_{q+1}(f) — exactly the eq-(12)
presentation of the level-(q+1) read; a side of print slope −h/e in lowest
terms has its lattice data preserved: degree d = (abscissa run)/e is the
same integer in both frames (the print's d(S) = the harness grid count).
The print principal part N^−_{q+1} (σ < 0, tex 1377) corresponds to
sheared slopes < h_q; the weld's type-quantification consumes only the
principal sides (JA-PIN clause 2's Hensel/L1 dispatch, displayed there).

**(d) [min/read ties].** min ordinate of U(f) = v_{q+1}(f) (print Lemma
`shape` item 1, tex ~1395); min ordinate of H(f) = w_{q+1}(f) = v_{q+2}(f)
(the weight recursion + JA-VAL one level up); the attained abscissas on
the realized side are the read grid s(λ) + j·e_q, and the level-(q+1)
read is assembled exactly from the on-line digits at those slots (S0.2
consumed; JA-GRID). So the polygon identity carries the READ data — the
harness read of f and the print's side data (s_{q+1}(f), attained set,
side degree) are the same integers under Σ_q.

**(e) [window clause].** Restricted to the junction window i ≤ e_q·g_q
(the lift comparison window), one-sidedness holds in both frames
simultaneously (Σ_q preserves sides): this is W2-C1a's polygon leg —
v-correct, one-sided, support {0, e_q g_q} ∪ attained grid slots — i.e.
the "window polygon" of the blueprint IS N_{q+1}(Φ_{q+1}^har) restricted
to its single side, vertex-for-vertex under Σ_q.

*Proof.* (a) displayed arithmetic + consumptions; (b) JB-AFF; (c)(d)
displayed arithmetic + the cited print lemmas (Lemma `shape` item 1 is
also re-verified by machine through the second development route — see
runner family JB-SHEAR); (e) W2-C1a consumed. ∎ Grade: PROVED at attempt
grade; unconditional GIVEN the representative legitimacy (W-2 clause 1's
perimeter and conditionality ride; on byte-equal chains no W-2 input is
needed beyond TH-BASE). [Machine: JB-VTX — fresh lower hulls of both
frames, vertex bijection, per-side slope/length translation; JB-SHEAR —
pointwise shear + all four min/read ties, with v_{q+1}(f) computed BOTH
as min u_i and by the vgen recursion through the φ_q-development (two
different developments, one value — Lemma shape item 1 machine-keyed);
teeth MJB-VTX on designated rows.]

---

## §4. THEOREM JB-TREE (the division-step correspondence = blueprint J-B(ii); W-5)

Setting: reduction level m (1 ≤ m ≤ n), [RMG] T-scope(m) (its termination
fence), g_m = 1, Ĉ_m := Φ_{m+1} − Φ_m^{e_m} (WELL-DEF g_m = 1 form,
consumed); f ∈ O[x] nonzero, deg f < deg Φ_m. The [RMG] S2.2 objects
(cells, (ID-(i+1)), the E1-priority tree, L-NORM splits, L-EXACT, L-CANON,
L-LINE) are consumed as ACCEPTED displays.

**THEOREM JB-TREE.** Under the J-A dictionary (and W-2 clause 1 for the
representative reading; clause 3's chamber off the byte perimeter):

**(i) [the tree computes the classifier's division].** The E1-priority
tree on the initial cells of f·Ĉ_m terminates (T-TERM, consumed) with
Σ R-leaves = R and Σ exit cofactors = Q for THE canonical division
f·Ĉ_m = R + Q·Φ_m (L-EXACT + L-CANON, consumed) — and by JB-DEV(i) at
level m this IS the classifier's division step at the admissible
representative (its own key on byte-equal chains): R = the 0-th digit and
Q = the once-divided cofactor of the print's φ_{m+1}-adic development
algorithm applied to f·Ĉ_m. One tree = one classifier division step,
executed inside the expansion arithmetic.

**(ii) [each edge = one classifier division step].** The identity
(ID-(i+1)): Φ_i^{P_i} = Φ_{i+1} − Σ_{k<g_i} C_k^{(i)}·Φ_i^{e_ik} IS the
statement that the φ_{i+1}-adic development of the KEY φ_{i+2} = Φ_{i+1}
has digit list {C_k^{(i)} at abscissa e_i·k (k < g_i), 1 at abscissa P_i}
(uniqueness of division; the C_k^{(i)} are reduced, REALIZE R1). So every
in-tree edge applies the classifier's own key-expansion relation exactly
once: a promotion edge carries one key power up one level (the division
algorithm's carry), a Φ_m-exit emits one quotient summand (a division
step's quotient write), and a correction edge substitutes the key's lower
development digits (the remainder write), L-NORM-split into its L/π-junk/
Φ₀Y-junk children. The tree is the classifier's division arithmetic made
cell-local; the blueprint's "each cell = a set of expansion slots" is
L-CELL: every node is a sum of reduced cells = multiadic expansion slots
(iterated JB-DEV at levels m−1, …, 0).

**(iii) [the polygon bookkeeping = LED-Λ's line face, one citation].**
On reduced cells, line(C) = w_m(C) ([RMG] L-LINE(iv)) = v_{m+1}(C)
(JA-VAL): THE LEDGER'S LINE FUNCTIONAL IS THE CLASSIFIER'S MacLANE
ORDINATE. Hence LED-Λ(A1)/(B) at the face λ_E — one theorem — supplies the
complete per-edge polygon bookkeeping of the division in classifier
coordinates: promotions raise v_{m+1} by exactly the quantum q_{i+1} > 0,
correction-main edges are v_{m+1}-flat, junk edges gain ≥ E_m (π) / ≥ Γ₀
(Y), exits pay w_mΦ_m ([LED-Λ] S1 table, λ_E column; L-MONO = the
division never descends below the polygon — the print's
division-stability genre read through the dictionary). Where earlier
units re-derived these per edge, J-B cites the ledger ONCE; LED-Λ is
consumed at ATTEMPT grade and the tie's grade rides it.

**(iv) [(RM-m) as the transported instance].** On this scope the four
(RM-m) box clauses ([RMG] ACCEPTED) become classifier statements: (C-W_R)/
(C-W_Q) are polygon statements about the classifier's R and Q digits
(their v_{m+1}-values, via JA-VAL), and (C-READ) transports as §5. No
clause of [RMG] is re-proved or touched.

*Proof.* (i) consumption chain as displayed + JB-DEV(i). (ii) dev of
Φ_{i+1} by Φ_i: the right side of (ID-(i+1)) has every C_k^{(i)}Φ_i^{e_ik}
of degree < deg Φ_{i+1} with the C_k reduced (REALIZE R1), so the digit
list reads off; uniqueness of division. (iii) the two displayed equalities
+ LED-Λ citation. (iv) composition. ∎ Grade: PROVED at attempt grade on
the displayed scope. Scope fences: T-scope(m) (the [RMG] d₀ ≥ 2 flat
corners stay fenced — the weld inherits them, blueprint S5's cross-cutting
row); g_m = 1 for the Ĉ_m instance; W-WIN not consumed (window-free legs
only, as in [RMG]). [Machine: JB-TREE — a FRESH from-note tree walker
(this unit's own implementation of S2.1/S2.2 on ITL towers: cells,
E1-priority, L-NORM via divmod, signed reassembly) checked against (1)
exact reassembly f·Ĉ_m = R₀ + QΦ_m, (2) the canonical division by the
harness key AND by the print-side key where byte-equal, (3) R-leaf
reducedness; JB-ID — (ID-(i+1)) as the key's own development, both
engines; JB-LINE — line(C) = wlev = vgen on reduced cells + the per-edge
λ_E quanta recomputed fresh (LED-Λ's table row keyed); teeth MJB-TREE.]

---

## §5. THEOREM JB-CREAD (the (C-READ) transport = blueprint J-B(iii); W-5)

Setting: the (RM-m) box verbatim ([RMG] S0.2, ACCEPTED on its scope):
level m, g_m = 1, Ĉ_m the canonical correction digit
(R_{m,γ_{m+1}}(Ĉ_m) = τ_m = ε_m(γ_{m+1})^{−1}·c_m), f ≠ 0 with
deg f < deg Φ_m, λ := w_m(f), v := R_{m,λ}(f), and the canonical division
f·Ĉ_m = R + Q·Φ_m. Here c_m = ψ_{m,0}, the constant coefficient of the
degree-1 modulus ψ_m(y) = y + ψ_{m,0} (from WELL-DEF's g_m = 1 lift form
and REALIZE R3, consumed) — so in K_{m+1} = K_m[z_{m+1}]/(ψ_m),

    c_m = ψ_{m,0} = −z_{m+1}    (the classifier's NEXT residual letter).

**LEMMA JB-EPS (the ε-cocycle collapse; unconditional, pure read data).**
For every m ≥ 1 and V, V′ ≥ 0 in the level-m weight lattice, with
t_m(β) = (ℓ_{m−1}β − s_m(β))/e_{m−1} the print twist exponent (JA-EPS's
convention) and ε′ := ⌊(s_m(V) + s_m(V′))/e_{m−1}⌋:

    t_m(V + V′) − t_m(V) − t_m(V′) = ε′ ,   hence
    ε_m(V+V′) · ε_m(V)^{−1} · ε_m(V′)^{−1} = z_m^{−ε′} .

*Proof.* The numerator telescopes: ℓ(V+V′) − s(V+V′) − ℓV + s(V) − ℓV′ +
s(V′) = s(V) + s(V′) − s(V+V′) = e_{m−1}·ε′ by the carry clause (JA-GRID(c)
= (C-EPS)); divide by e_{m−1}. The field form is JA-EPS (ε = z^{−t}). ∎
[Machine: JB-EPS, integers + field elements, every roster level.]

**THEOREM JB-CREAD.** Suppose (VD-m) (J-A §3.4's evaluated dictionary)
holds at f and at R — unconditional for m ≤ 2 (VD-1 = W2-L3; m = 2 by
JA-RES), per-digit proviso / (R-coll) at m ≥ 3 (JA-BOX-2) — and suppose
v ≠ 0 (THE NON-DEGENERATE READ STRATUM; the v = 0 branch is displayed
after the proof). Define the print's TWISTED EVALUATED READ
ρ_m(A) := z_m^{τ_m(A)}·R_m^cls(A)(z_m) (R_m^cls the print residual
operator at A's own realized side, τ_m(A) = (s_m(A) − ℓ_{m−1}w_m(A))/e_{m−1}
as in (VD-m)). Then w_m(R) = λ + γ_{m+1} exactly, and

    ρ_m(R)  =  c_m · ρ_m(f)  =  ψ_{m,0} · ρ_m(f) .

**The transport, stated.** [RMG]'s (C-READ) — "multiplying a read digit by
the canonical correction digit shifts the read by τ_m with the level-m
EPS-carry z_m^{ε′}" — transports to the classifier as: THE CLASSIFIER'S
TWISTED RESIDUAL READ SHIFTS BY THE CONSTANT c_m, WITH NO CARRY FACTOR.
The z_m^{ε′} carry of the harness frame is EXACTLY the coordinate change
between the print twist t_m and the harness ε-kit (LEMMA JB-EPS); it
reappears verbatim when the identity is written in ε-coordinates — that
form IS [RMG] (C-READ), consumed not re-proved.

*Proof (displayed in full).* By (VD-m) at f: ρ_m(f) = ε_m(λ)·v. Since
v ≠ 0 and τ_m is a unit, (C-READ) gives R_{m,λ+γ_{m+1}}(R) =
z_m^{ε′}·v·τ_m ≠ 0, so some cell of R sits on-line on-grid at
λ + γ_{m+1} (B-READ), forcing w_m(R) ≤ λ + γ_{m+1}; with (C-W_R)'s ≥
this pins w_m(R) = λ + γ_{m+1} EXACTLY — so (VD-m) at R is an identity
at the (C-READ) target:

    ρ_m(R) = ε_m(λ+γ_{m+1}) · R_{m,λ+γ_{m+1}}(R)
           = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · τ_m            [(C-READ)]
           = ε_m(λ+γ_{m+1}) · z_m^{ε′} · v · ε_m(γ_{m+1})^{−1} · c_m
           = [ε_m(λ+γ_{m+1}) ε_m(λ)^{−1} ε_m(γ_{m+1})^{−1}] · z_m^{ε′}
             · c_m · ε_m(λ)·v
           = z_m^{−ε′} · z_m^{ε′} · c_m · ρ_m(f)            [JB-EPS]
           = c_m · ρ_m(f) .                                  ∎

**The degenerate branch (v = 0), displayed.** There ρ_m(f) = ε_m(λ)·v = 0
by (VD-m) at f, and (C-READ) gives only the TARGET-read vanishing
R_{m,λ+γ_{m+1}}(R) = 0; R's OWN weight can sit strictly above λ + γ_{m+1}
with a nonzero own-side print residual, so the ρ-form identity is NOT
claimed at v = 0 — the transport there is the read-at-target statement
(0 = 0) only. This stratum split is the theorem's own scope, not a gap;
the runner scores v ≠ 0 rows and censuses the v = 0 rows (checking
ρ_m(f) = 0 on them, which does hold).

Grade: PROVED at attempt grade on the (VD-m) perimeter ∩ {v ≠ 0}; the
ingredient grades ride ([RMG] ACCEPTED; J-A/W-2 attempt). [Machine: JB-CREAD — both
sides computed end-to-end (print residuals by the sealed GmnLeg
transcription, harness division/reads by ITL, τ/ε′ by fresh integers) with
the (VD-m) instances at f and R MACHINE-EVALUATED per row: scored where
they hold, boundary census disclosed; JB-CM — c_m = ψ_{m,0} and
embed_{K_{m+1}}(c_m) = −z_{m+1}; teeth MJB-CREAD — the spurious-carry
reading ρ_m(R) = z_m^{ε′}·c_m·ρ_m(f) must FAIL on designated ε′ ≥ 1 rows.]

**Remark (the carry seed; fence).** ρ_m(R) = −z_{m+1}·ρ_m(f) in K_{m+1}:
on twisted residual reads, multiplication by the canonical correction
digit IS multiplication by the negative of the classifier's next residual
letter. This is the semantic germ the J-C carrier block (W-6..W-9) needs —
displayed here as an identity of READ VALUES only; no graded-ring (gr)
object is constructed or claimed, and BLOCKED-ON-CARRIER-TIE stands.

---

## §6. Honest boxes

* **JB-BOX-1 (blueprint correction, review-owed).** Blueprint J-B(iii)
  displays the classifier transport WITH the carry ("shifts the
  CLASSIFIER's residual read by τ_m with the level-m EPS-carry z_m^{ε′}").
  CORRECTED: in the print's twisted coordinates the carry cancels
  (THEOREM JB-CREAD); the shift constant is c_m (not τ_m), and the
  τ_m-with-carry form is the HARNESS-frame statement ([RMG] (C-READ)).
  The blueprint display conflated the two frames; both are displayed
  above with the coordinate change (JB-EPS) between them.
* **JB-BOX-2 (inherited conditionality, quantified).** Every print-residual
  statement rides J-A's boxes verbatim: the (VD-m)/per-digit proviso at
  m ≥ 3 (JA-BOX-2 — (R-coll) sufficient, converse unsealed), the
  unpinned-ℓ orbit (JA-BOX-3: all displays at the pinned (P-ell)
  representative; §4.3-orbit transport per J-A §4(ii)), and W-2's
  (C-coll)/recursion split for the byte law. JB-CREAD's own stratum
  split (v ≠ 0 scored; v = 0 = the read-at-target branch only, ρ-form
  not claimed) is displayed at the theorem. W2-OPEN-1 (the value layer
  on transported lifts) is consumed NOWHERE.
* **JB-BOX-3 (cross-key fence).** No cross-representative operator or
  byte identity is claimed anywhere (JB-DEV(iv)); transport across
  representatives is W-2 clause 2/3 covariance only. The JuncForge
  parity-wall lesson is honored structurally: every §2–§5 statement is
  against the semantic development/polygon/tree/read objects; SideReads/
  TreeModel are consumed nowhere.
* **JB-BOX-4 (tree scope).** JB-TREE inherits [RMG]'s fences verbatim:
  termination on T-scope(m) (d₀ = 1 ∨ non-degenerate below top; the
  d₀ ≥ 2 flat corners stay FENCED and are quantified over nowhere here);
  g_m = 1 for the Ĉ_m instance; W-WIN consumed by nothing. LED-Λ is
  ATTEMPT grade (acceptance counter 0) — the §4(iii) citation's grade
  rides it, and the runner therefore re-verifies the λ_E quanta FRESH
  rather than trusting the ledger (decorrelation, not redundancy).
* **JB-BOX-5 (instance perimeter).** Machine evidence = the §7 roster
  (16 towers, reads ≤ 4 + top, residue fields ≤ F₉ + F₈/F₂₅ via the d₀
  leg; 5 QO shapes; 4 fresh d₀ ≥ 2 shapes); F_p[[t]] rows have no PARI
  leg (JA-BOX-4 inherited); mixed-characteristic print, equal-char rows
  ride construction-identity + machine only.
* **JB-BOX-6 (standing fences).** No gr/carrier claim (J-C untouched;
  BLOCKED-ON-CARRIER-TIE stands); no count/menu/density claim (J-D
  untouched); the P0 application gate stands; acceptance counter 0/2 —
  nothing here may be consumed at proof grade before its hostile arc.

---

## §7. Records (commit 2 — from the sealed artifacts)

### 7.1 Machine bracket — **ALL 18 FAMILIES GREEN, 6,700 samples, 0 violations, every sealed prediction hit exactly** (`grt_jb_checks_output.txt` / `grt_jb_checks_results.json`, elapsed 0.7 s; seal commit 7f6759d)

| family | claim keyed | samples | verdict |
|---|---|---|---|
| EXT-GATE | engine_ext pins + agreement gate re-run (standing rule) | 1 | GREEN |
| JB-DEV | fresh schoolbook dev == both engines + digit weight ties | 893 | GREEN |
| JB-KEYEQ | byte census + TH-BASE (q = 1 byte-equal on all 25 rows) | 25 | GREEN |
| JB-SHEAR | pointwise shear + the four min/read ties (Lemma shape 1 through a second development) | 893 | GREEN |
| JB-VTX | vertex bijection + per-side slope/length law, fresh hulls | 893 | GREEN |
| JB-ID | (ID-(i+1)) exact + key-dev digits + print-key grid/shear-constancy | 34 | GREEN |
| JB-TREE | fresh tree walk == canonical division, harness AND print keys | 79 walks (125 with chambers) | GREEN |
| JB-LINE | λ_E quanta per edge + leaf line == wlev == vgen | 194 | GREEN |
| JB-EPS | ε-cocycle collapse, integers + field | 955 | GREEN |
| JB-CM | c_m = ψ_{m,0} = −z_{m+1} (28 eligible (T, m) rows) | 28 | GREEN |
| JB-CREAD | ρ(R) = c_m·ρ(f) + w_m(R) pin, scored stratum | 79 | GREEN |
| JB-QO / JB-D0 | 5 concrete shapes / 4 fresh d₀ ≥ 2 shapes (engine_ext) | 5 / 4 | GREEN |
| TW-JB | chamber re-instantiation (all 16 towers, nontrivial ledgers) | 2,480 | GREEN |
| MJB-DEV / MJB-VTX / MJB-TREE / MJB-CREAD | teeth (garbled key / unsheared frame / corrupted correction / spurious carry) | 3/3/3/3 rows | GREEN (all caught) |

Censuses (the note's displayed conditionality, quantified): JB-CREAD
**scored 104 (66 roster + 38 chamber), 0 violations; boundary 21 —
ALL on the character-visible/interior-twist towers T3A, T3B, T3C, T3D,
I4B and their transported chambers**, exactly the JA-BOX-2/(VD-m)-proviso
geography (T3B/I4B = the W-2 collapse-boundary pair); **v = 0 stratum:
0 occurrences; R = 0: 0; off-perimeter tree rows: 0**. Byte census
(JB-KEYEQ) reproduces the probe's F1 pattern row-for-row (e.g. I4A/I4B
byte-equal through the top; T3A/T3C/T3D/T3E diverge at q = 2; I4C at
q = 2, 3 — and I4C has NO eligible (g_m = 1 ∧ T-scope) reduction level,
so its tree/cread rows are honestly absent, the §4 scope fence in
action). MJB-CREAD teeth material: 22 scored samples with z_m^{ε′} ≠ 1
across 7 towers — the spurious-carry reading fails on every one, i.e.
the ε-carry collapse is machine-load-bearing, not a notational
convention.

### 7.2 Claims table (grades)

| claim | statement | grade |
|---|---|---|
| JB-DEV | expansion identity: same division; byte clause on the byte law; three-layer coefficient correspondence; cross-key fence | PROVED (attempt grade 0/2), consumptions at their own grades |
| JB-AFF | affine ordinate maps preserve hulls/vertices | PROVED (two lines) |
| JB-VTX | window/development polygon = Σ_q(N_{q+1}(f)) vertex-for-vertex; slope/length translation; min/read ties; window clause | PROVED (attempt grade), at the W2-C1 representative |
| JB-TREE | the [RMG] tree computes the classifier's division; edge = division step; cells = expansion slots; λ_E face = polygon bookkeeping | PROVED (attempt grade) on T-scope(m), g_m = 1; LED-Λ cited at attempt grade |
| JB-EPS | ε-cocycle collapse t(V+V′) − t(V) − t(V′) = ε′ | PROVED, unconditional |
| JB-CREAD | (C-READ) transport: ρ_m(R) = c_m·ρ_m(f), carry-free in print coordinates | PROVED on the (VD-m) perimeter ∩ {v ≠ 0} (uncond. m ≤ 2) |
| JB-BOX-1 | blueprint J-B(iii) carry placement | CORRECTED (frame conflation; both frames displayed) |

### 7.3 Consequence display and dependency line

**What J-B now supplies (at attempt grade, hostile passes owed):** the
blueprint's W-3 in full (expansion + polygon identities, shear explicit);
W-5 in full on [RMG]'s scope ((ii) the tree/division correspondence with
LED-Λ as bookkeeping, (iii) the (C-READ) transport in both frames).
**NOT supplied:** W-1's uncollapsed all-orders dictionary (JA-BOX-2),
W-2's grades (consumed), the J-C block W-6..W-9 (no gr claim;
BLOCKED-ON-CARRIER-TIE stands), J-D counts/menus (W-10..W-12), W2-OPEN-1.
The P0 application gate stands.

CONSUMES: [RMG] (ACCEPTED) · [ILN]† (accepted) · W-2 + J-A + LED-Λ at
attempt grade (conditionality verbatim) · GMN HigherNewton as literature
(header anchors) through the sealed probe transcription · engine_ext
(standing rule). CONSUMED BY (intended): the J-C block units (W-6..W-9 —
the §5 remark is their semantic germ), the W-10/J-D count units, the weld
campaign ledger at J-B. Acceptance counter 0/2.

— J-B COMPOSER unit, campaign date 2026-08-08 (wallclock 2026-08-04).
