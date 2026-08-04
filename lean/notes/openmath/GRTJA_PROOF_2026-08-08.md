# GRTJA — J-A, THE DICTIONARY JUNCTION: type data → tower data, the four operator equalities, and the covariance-corrected residual tie

**Unit:** J-A COMPOSER (weld dependency order: consumes W-2 clause 1 at attempt
grade; per `docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §S2.1/S3.1
rows W-0/W-1/W-4). **Genre: PROOF NOTE at attempt grade (acceptance counter
0/2; no gate fires; no acceptance arc opened), with sealed-runner machine
brackets** (`verification/openmath/grt_ja_checks.py`, two-commit seal).

**Grade cap (read first).** J-A-PIN (§2) is PROVED at attempt grade (its legs
are the print's own definitions plus one one-line argument), with its lift
clause consumed from W-2 clause 1 AT ATTEMPT GRADE and W-2's conditionality
carried verbatim. Of the four operator equalities (§3): (i) w = v and (iii)
ε = the print twist are PROVED unconditionally on the shared-key perimeter;
(iv) the grid/carry tie is PROVED unconditionally; (ii) the residual
dictionary is PROVED at m = 1 (= W2-L3, consumed) and at m = 2
(unconditional per-slot character-gauge law, new here), and at m ≥ 3 is
PROVED under the displayed per-digit collapse proviso — outside it the exact
law is the recursion, W-2 §3.3(c) genre. One blueprint display is CORRECTED:
the J-A(ii) "slot-independent c" form is false at m ≥ 2 (JA-BOX-1). Nothing
here fires any gate, touches any accepted text, makes any gr/carrier (J-C)
claim, or advances any density (J-D) statement.

**Literature consumption (faithfulness discipline).** The classifier side is
the GMN print `docs/references/HigherNewton.tex` ("Newton polygons of higher
order in algebraic number theory"), consumed as literature with tex anchors
per formula, through the SEALED probe transcription `grt_weld_probe.GmnLeg`
(no new print transcription in this unit; the fresh legs of the runner are
integer/geometric recomputations, not new print readings). Anchors used:
sides/slopes in lowest terms (tex 220, 828, 912); order-one and order-r type
data ψ monic irreducible ≠ y, F_r := F_{r−1}[y]/(ψ_{r−1}) (tex 829, 882);
principal polygon = negative-slope sides (tex 449, 1377); residual polynomials
never divisible by y (tex 1149); Proposition `construct` (tex 1166–1258,
hypothesis V ≥ e_{r−1}f_{r−1}v_r(φ_{r−1})); Theorem `phir` + eq `vrphir`
(tex 1257–1283); the representative definition = the project's "Def 2.12"
(tex 1285); Bézout ℓ_r h_r − ℓ′_r e_r = 1 with NO pinned representative
(tex 1291); Proposition `propertiesv` items 3/4 (tex 1028); Definitions
`t(i)`/`rescoeff`/`defresidual` (tex 1431/1447/1497 and the order-one base
tex ~460/534). The FGMN print enters ONLY through the accepted N-1 base case
(§5) — a second, independent print of the same operators.

**Machine bracket:** `grt_ja_checks.py` — both sides of every §2/§3 equality
computed on the weld probe's 16-tower roster + the 5 concrete wild
polynomials (fresh QO extraction) + 4 FRESH d₀ ≥ 2 shapes (d₀ = 3 root keys
and a p = 5 row, certified through `engine_ext` per its standing rule),
LAW-KEYED with teeth. Verdict in §7 (commit 2).

---

## §1. Setting and indexing (fixed once)

Harness: the [ILN]† S0.1 class pin verbatim (DVR O, uniformizer π, reads
(e_j, h_j, g_j) for j = 0..n with e_j, h_j, g_j ≥ 1 and gcd(e_j, h_j) = 1;
normalized Bézout ℓ_j h_j + ℓ′_j e_j = 1 with 0 ≤ ℓ_j < e_j; residue chain
K_{j+1} = K_j[z_{j+1}]/(ψ_j), ψ_j monic irreducible, ψ_j(0) ≠ 0; weights
γ₁ = h₀, γ_{j+1} = e_j·w_jΦ_j + h_j, w_jΦ_j = e_{j−1}g_{j−1}γ_j; the
standard lift Φ₁, the canonical ε-corrected lifts Φ_{m+1}, the units
ε_m(β) = z_m^{ℓ′_{m−1}s − ℓ_{m−1}u} with (s, u) = eq12(β; e_{m−1}, h_{m−1}),
the level-m weights w_m and reads R_m v of S0.2). Classifier: the GMN print
objects, as transcribed in the sealed probe leg.

**The P-index dictionary** (probe pins, restated once; W-2 §1.2): GMN level
i = harness read i−1: (e_i, h_i, f_i)^GMN = (e_{i−1}, h_{i−1}, g_{i−1})^har;
ψ_i^GMN = ψ_{i−1}^har; F_i = K_{i−1}; z_i^GMN = z_i^har; ℓ_i^GMN ≡ ℓ_{i−1}^har
under (P-ell); GMN keys φ_i = harness Φ_{i−1}; GMN valuations v_i = harness
w_{i−1} (THEOREM JA-VAL below is exactly this pin proved); in particular
v_i(φ_i) = w_{i−1}Φ_{i−1} and v_{i+1}(φ_i) = γ_i^har. The GMN order-q
residual operator R_q (φ_q-adic dev) pairs with the harness level-q read
R_q v. Convention pins (P-ell)/(P-lift)/(P-root)/(P-index) as sealed in the
probe docstring. **Shared-key perimeter at level m**: Φ_q^har = φ_{q+1}^cls
byte-for-byte for all q ≤ m−1 (all operators at level m consume only keys
that deep). The read-data quantities of W-2, reused throughout:

    A_m := ℓ_{m−1}·g_{m−1}·γ_m ∈ ℤ_{≥0}   (m ≥ 1; A_m = 0 ⟺ e_{m−1} = 1),
    W_m := w_mΦ_m = e_{m−1}g_{m−1}γ_m     (so A_m = ℓ_{m−1}W_m/e_{m−1}).

---

## §2. THEOREM JA-PIN (= blueprint W-0): the dictionary map and the class-pin membership, clause by clause

**Definition (the dictionary map T).** For a realized principal-read OM type
t of order r on a separable monic f ∈ O[x], O ∈ {ℤ_p, F_p[[t]]} — GMN data
(φ_i, λ_i = −h_i/e_i, ψ_i)_{i≤r}, f_i = deg ψ_i, φ₁ the order-0 key — set

    T(t) := ( Φ₀ := φ₁;  reads (e_j, h_j, g_j) := (e_{j+1}, h_{j+1}, f_{j+1})^GMN,
              j = 0..r−1;  residue chain K_{j+1} := K_j[z_{j+1}]/(ψ_j),
              ψ_j := ψ_{j+1}^GMN;  weights by the harness recursion ).

**THEOREM JA-PIN.** T(t) satisfies every clause of the [ILN]† S0.1 class pin
EXCEPT the lift clause, each clause forced by the print's own hypotheses:

1. **DVR base.** O = ℤ_p is the print's own base (𝒪 the valuation ring of a
   local field); the F_p[[t]] instance is the displayed equal-characteristic
   deferral (JA-BOX-4) — construction-identical, machine-covered, no PARI leg.
2. **e_j ≥ 1, h_j ≥ 1, gcd(e_j, h_j) = 1.** The print DEFINES every side
   slope as λ = −h/e "with h, e positive coprime integers" (tex 220 order
   one; tex 828 type datum; tex 912 order r). Positivity of h is the
   PRINCIPAL restriction: types are built from the principal polygon
   N_r^−(f), the negative-slope sides only (tex 449, 1377). Slope-0 legs
   never enter a type; they are dispatched by Hensel/L1 at order 0 (the
   machine-checked capstone leg), so the weld quantifies over principal
   reads only — displayed, blueprint pin honored.
3. **g_j ≥ 1.** g_j = f_{j+1} = deg ψ_{j+1}; ψ monic irreducible forces
   deg ≥ 1 (tex 829/882).
4. **ψ_j monic irreducible.** Verbatim print hypothesis (tex 829 order one,
   tex 882 order r).
5. **ψ_j(0) ≠ 0.** The print requires ψ ≠ y (tex 829/882; used again at tex
   1149: "the residual polynomials are never divisible by y, and
   ψ_{r−1}(y) ≠ y"). One line: if ψ(0) = 0 then y | ψ, and ψ monic
   irreducible forces ψ = y — excluded. ∎
6. **Residue chain.** F_{r} := F_{r−1}[y]/(ψ_{r−1}(y)) is the print's own
   definition (tex 882); under F_i = K_{i−1} and z_i^GMN = z_i^har this IS
   the pin's chain K_{j+1} = K_j[z_{j+1}]/(ψ_j).
7. **Weights.** The print's v_{i+1}(φ_i) = e_i v_i(φ_i) + h_i and
   v_{i+1}(φ_{i+1}) = e_i f_i v_{i+1}(φ_i) (Prop `propertiesv` tex 1028; eq
   `vrphir` tex 1259) transcribe under P-index to EXACTLY the pin's
   γ_{j+1} = e_j·w_jΦ_j + h_j and w_{j+1}Φ_{j+1} = e_j g_j γ_{j+1}, with
   base v₁(φ₁) = 0, v₂(φ₁) = h₁^GMN = h₀ = γ₁ (the uniformizing
   convention). Integer identity, machine family JA-PIN.
8. **THE LIFT CLAUSE (the sole exception) = W-2, consumed at attempt
   grade.** GRTW2_PROOF_2026-08-08.md supplies it in the corrected
   three-clause form: Φ_{m+1}^har is a strict GMN Def-2.12 representative
   (tex 1285) of the ξ-CONJUGATE type under the pinned (P-ell) convention
   (W2-C1, proved on the §3 perimeter there), and of the TRANSPORTED type
   t^tw strictly at every level (W2-C3, attempt grade, machine 44/44/44).
   Conditionality carried verbatim: the (C-coll)/recursion split, the §4.3
   ℓ-orbit convention fence, and W2-OPEN-1 (value layer) OPEN.

*Proof.* Clauses 1–7 are the cited definitions plus the displayed one-line
arguments; clause 8 is consumption. ∎ Grade: PROVED at attempt grade; the
Bézout normalization 0 ≤ ℓ < e is OURS not the print's (tex 1291 pins
nothing — JA-BOX-3). [Machine: JA-PIN — every clause re-verified by fresh
integer/field computations on every roster + QO + d₀ ≥ 2 level.]

---

## §3. The four operator equalities (= blueprint W-1 (i)–(iii) + W-4 (iv))

Throughout §3 the level-m statements are on the shared-key perimeter (§1);
§4 states what survives off it and across the orbit.

### 3.1 THEOREM JA-VAL (J-A(i): w_m = v_{m+1})

**Statement.** For every m ≥ 0 and every nonzero A ∈ O[x]:
w_m(A) = v_{m+1}(A), where v is the print's MacLane/GMN valuation of the
type prefix (order-one v₁ = min coefficient π-valuation, tex ~460 region;
order-r recursion v_r(A) = min_i (e_{r−1}·v_{r−1}(a_i) + i·v_r(φ_{r−1})),
Prop `propertiesv` item 3, tex 1028, hypothesis: φ_{r−1}-adic development).

*Proof.* Induction on m. Base m = 0: w₀ = min coefficient valuation = v₁ by
definition on both sides. Step: under shared keys the φ_{m+1}-adic dev IS
the Φ_m-dev (same monic key, same canonical division), and the two
recursions are the same integer min — v_{m+2}(A) = min_i(e_m^har·v_{m+1}(a_i)
+ i·v_{m+2}(φ_{m+1})) with v_{m+2}(φ_{m+1}) = γ_{m+1} (JA-PIN clause 7)
versus w_{m+1}(A) = min_i(e_m·w_m(a_i) + i·γ_{m+1}); the inductive
hypothesis identifies the arguments. ∎ Grade: PROVED (attempt grade),
unconditional on the shared-key perimeter. This is the P-index pin
v_i = w_{i−1} PROVED rather than assumed; it is stated in the GD-2 frame
normalization (the sheared eq-(12) presentation of ordinates — the T-F
machine check's convention pin) — the identity lives at the v-level where
no shear ambiguity exists. [Machine: CK-VAL, both engines on the same
samples, every shared level of every roster/QO/d₀ ≥ 2 tower.]

### 3.2 THEOREM JA-EPS (J-A(iii): ε_m = the print's twist unit)

**Statement.** For every m ≥ 1 and every β ∈ ℤ in the level-m weight
lattice: ε_m(β) = z_m^{−t_m(β)}, where t_m(β) := (ℓ_{m−1}β − s(β))/e_{m−1}
is the print's twist exponent (Definition `t(i)`, tex 1431; the same
exponent prescribes Prop `construct`'s children, tex 1213–1218) evaluated
at the point of ordinate-argument β on its own side, s(β) = ℓ_{m−1}β mod
e_{m−1} (integrality by W2-L0). More generally, for u = β + k·W_m (weight
shifts by key multiples): ε_m(β)·z_m^{t_m-at-u} = z_m^{A_m·k} — W2-L2
consumed proved (the Bézout bridge; hypothesis list: gcd(e, h) = 1,
normalized (ℓ, ℓ′), u − β ∈ W_m·ℤ).

*Proof.* The k = 0 case of W2-L2: T + (ℓ′s − ℓu′) = ℓ(u − V)/e = 0 at
u = V = β, i.e. the ε-exponent ℓ′s − ℓu′ = −t_m(β). ∎ Grade: PROVED,
unconditional (pure read-data integers; no key bytes consumed). This is
W-2 §2.4's structural sentence promoted to the J-A ledger: **the harness
ε-kit IS the print's t(i)-twist rewritten in eq12-canonical coordinates.**
[Machine: CK-EPS — committed T.eps vs fresh geometric-scan integers;
k-grid covariance included.]

### 3.3 THEOREM JA-GRID (J-A(iv): eq-(12-int) digits = abscissa/side coordinates, + the carry clause)

**Statement.** Fix a read (e, h), gcd(e, h) = 1, h, e ≥ 1, and V ∈ ℤ_{≥0}.
(a) The print's T-side initial point (Prop `construct` tex 1176: "the
greatest side T contained in L whose end points have nonnegative integer
coordinates", initial point (s, u); same object at tex 1498) is EXACTLY
eq12(V; e, h): s = ℓV mod e = the smallest nonnegative abscissa with
integer ordinate on the line, u = (V − sh)/e. (= W2-L0, consumed proved.)
(b) Consequently the print's slot grid s + je and slot values V_j equal the
harness digit grid and digit weights at every junction slot (W2-L0's
consequence display: the two legs' polygons agree point-for-point).
(c) CARRY CLAUSE (elementary, new display): for V, V′ ≥ 0,

    s(V) + s(V′) − s(V + V′) = e·δ,   δ ∈ {0, 1},   δ = 1 ⟺ s(V) + s(V′) ≥ e,

and δ = 1 exactly when the concatenated grid offsets cross a lattice point
of the coarser (period-e) grid — the plain carry δ^pl of the harness
eq-(12-int) split IS the side-lattice crossing indicator (GD-8's exact-key
seam genre at order 1; the print-side reading of the same integer).

*Proof of (c).* s(V+V′) ≡ ℓ(V+V′) ≡ s(V) + s(V′) (mod e) and all three lie
in [0, e), so the difference is 0 or e; it is e iff s(V) + s(V′) ≥ e. ∎
Grade: PROVED, unconditional. SCOPE: this is the single-level additive
statement only; the multi-level defect/carry chains (S_j, D_j) are [ILN]†'s
content, consumed not re-proved (fence displayed). [Machine: CK-GRID —
geometric brute scan (no ℓ, no eq12) vs eq12 on both (a) and (c).]

### 3.4 THEOREM JA-RES (J-A(ii): the residual dictionary — the per-slot character-gauge law)

Notation: at level m ≥ 2, for nonzero A ∈ O[x] with deg A < deg Φ_m, let
β = w_m(A); dev A by Φ_{m−1} with digits a_i; harness packed coefficients
C_i := ε_{m−1}(β_i)·R_{m−1}v(a_i) at the exact-weight abscissas i (grid
s(β) + j·e_{m−1}, β_i = (β − i·γ_m)/e_{m−1}, so R_m v(A) = Σ_j C_{i_j}z_m^j);
print residual coefficients c_i := z_{m−1}^{t(i)}·R_{m−1}(a_i)(z_{m−1})
(Definition `rescoeff` tex 1447 at order ≥ 2, `defresidual` tex 1497;
t(i) = (s_{m−1}(a_i) − ℓ_{m−2}u_i)/e_{m−2} per Definition `t(i)` tex 1431,
u_i = v_m(a_i·Φ_{m−1}^i); order-one base c_i = red(a_i/π^{u_i}), tex ~460).

**(VD-m), the evaluated dictionary at level m** (the inductive interface):

    z_m^{τ_m(A)} · R_m(A)(z_m) = ε_m(β) · R_m v(A),
    τ_m(A) := (s_m(A) − ℓ_{m−1}β)/e_{m−1},  s_m(A) = initial attained abscissa.

(VD-1) is W2-L3, PROVED (consumed).

**THEOREM JA-RES (per-slot law).** Level m ≥ 2, shared keys below m. IF
(VD-(m−1)) holds at every on-line digit a_i of A (the PER-DIGIT PROVISO),
THEN for every attained abscissa i:

    c_i = z_{m−1}^{−i·A_{m−1}} · C_i .

The print's order-m residual coefficient equals the harness packed digit
times the PURE CHARACTER z_{m−1}^{−i·A_{m−1}} in the abscissa. At m = 2 the
proviso is (VD-1) = W2-L3: **the law is UNCONDITIONAL at m = 2.**

*Proof.* By the proviso, R_{m−1}(a_i)(z_{m−1}) = z_{m−1}^{−τ_{m−1}(a_i)}·
ε_{m−1}(β_i)·R_{m−1}v(a_i) = z_{m−1}^{−τ_{m−1}(a_i)}·C_i. So c_i =
z_{m−1}^{t(i) − τ_{m−1}(a_i)}·C_i, and with u_i = β_i + i·W_{m−1} (both
ordinates of the same on-line point, W_{m−1} = w_{m−1}Φ_{m−1} = the print's
v_m(φ_m), JA-PIN clause 7):

    t(i) − τ_{m−1}(a_i) = [s_{m−1}(a_i) − ℓ_{m−2}u_i − s_{m−1}(a_i)
        + ℓ_{m−2}β_i]/e_{m−2} = −ℓ_{m−2}·i·W_{m−1}/e_{m−2} = −i·A_{m−1}. ∎

**COROLLARY JA-VDIND (the induction step and its exact boundary).** Under
the per-slot law, (VD-m) holds for A IF the slot character is trivial
ABSOLUTELY on A's attained abscissas: z_{m−1}^{i·A_{m−1}} = 1 for every
attained i (sufficient: A_{m−1} = 0, i.e. e_{m−2} = 1; or
ord(z_{m−1}) | A_{m−1} and the abscissa condition; NOT sufficient:
single-slot support alone — the constant z^{−s₀A} survives). Conversely,
when the absolute character is nontrivial on the attained set, the two
sides of (VD-m) differ by z_{m−1}^{−s₀A}·(the ϑ-twisted packed sum vs the
packed sum), which is generically nonzero — the converse is NOT sealed
(cancellations and the zero-read escape R_m v(A) = 0 are possible).
*Proof of the forward direction.* Summing the per-slot law along the grid,
with s₀ = s(β) + ν·e_{m−1}: R_m(A)(z_m) = Σ_att z^{−iA_{m−1}}·C_i·
z_m^{(i−s₀)/e_{m−1}} = z_m^{−ν}·Σ_att C_i z_m^{(i−s)/e_{m−1}} under the
absolute triviality, = z_m^{−ν}·R_m v(A); and τ_m(A) − ν = the
ε_m(β)-exponent (W2-L2 at k = 0, as in W2-L3's proof). ∎ [The FULL general
form, off the collapse: R_m(A)(y) = z^{−s₀A_{m−1}}·Q_A(ϑ_m·y),
ϑ_m := z_{m−1}^{−e_{m−1}A_{m−1}}, Q_A(y)·y^ν = the packed polynomial — the
same-polynomial instance of W-2 §3.2's conjugation; the dictionary at
levels ≥ 3 is a CONJUGATION, scalar only on the collapse perimeter.]

**Definition (R-coll, the residual collapse perimeter at level m).** Every
level-q instance of the proviso, 2 ≤ q ≤ m−1, collapses: at every recursion
node the slot character is trivial on that node's attained abscissas (the
JA-VDIND condition). On (R-coll): the per-slot law and (VD-m) hold at all
levels up to m by induction with base (VD-1). Off it: the exact law is the
per-slot law fed by the recursion (HR-REC genre), not a scalar form —
JA-BOX-2.

**COROLLARY JA-MIN (the MIN CORE transfer, GD-3 genre at orders ≥ 2).** On
the per-slot law's perimeter, the gauge is a unit per slot: c_i = 0 ⟺
C_i = 0, supports and degrees agree slot-for-slot, and ord_ψ data of the
print residual is computable from the harness read (and conversely). The
GD-3 MIN CORE at orders ≥ 2 is therefore a theorem WHERE THE DICTIONARY
REACHES, with the same conditionality — not unconditional (JA-BOX-2).

Grades: JA-RES PROVED at m = 2 (attempt grade); PROVED-under-proviso at
m ≥ 3, unconditional on (R-coll); JA-VDIND PROVED; JA-MIN rides JA-RES.
[Machine: CK-RES1 (m = 1, W2-L3 both sides), CK-RES (per-slot, proviso
machine-evaluated per digit; scored where the proviso holds, boundary rows
recorded with counts), CK-VDM (JA-VDIND forward direction), CK-BPREF (the
JA-BOX-1 refutation census: the slot-independent form must FAIL on
designated character-visible rows).]

---

## §4. Covariance: how each equality transports (the (ξ, w) orbit and the transported chamber)

**The orbit action** (W-2 §4.3, consumed as convention analysis; machine
family ORB-RES gives it a machine leg it did not have): shifting the print's
free Bézout representative ℓ_{m−2} ↦ ℓ_{m−2} + κ·e_{m−2} (tex 1291 pins
none) changes Def-`t(i)` by t(i) ↦ t(i) − κ·u_i and hence rescales the
order-m residual on a side with initial attained point (s₀, u₀) by

    (ORB-RES)   R^{(ℓ+κe)}(A)(y) = z_{m−1}^{−κ·u₀} · R^{(ℓ)}(A)( z_{m−1}^{κ·h} · y ),

h = the level-m grid height (u drops by h per grid slot). Against this
action, clause by clause:

* **(i) w = v: ℓ-ORBIT-INVARIANT, with the MacLane representative caveat
  across chambers.** v never consumes ℓ (Prop `propertiesv`'s recursion is
  ℓ-free); JA-VAL is orbit-blind. ACROSS the W-2 clause-3 transported
  chamber, blanket operator equality on the OTHER chain's keys is FALSE:
  two strict representatives φ, φ′ of the same type with different strict
  units satisfy v_{r+1}(φ − φ′) = e_r·v_r(φ) < v_{r+1}(φ), so the two
  augmented valuations already disagree AT the key class (A = φ genre) —
  the standard MacLane representative-dependence, surfaced here rather
  than hidden. The honest transport of (i) is (a) the CHAIN level: key
  polygons and weights agree (W2-C3(i), machine 44/44 in the W-2 runner),
  and (b) RE-INSTANTIATION (last bullet): inside the transported chamber
  J-A holds verbatim with the chamber's own keys on both sides.
  [Machine: TW-INST.]
* **(ii) the residual dictionary: SHAPE-COVARIANT.** Under the κ-shift the
  per-slot law keeps its unit-times-character form with transported data:
  c_i ↦ z^{−κu_i}c_i and u_i = β_i + i·W_{m−1}, β_{i_j} = β₀ − j·γ_m along
  the grid, so in grid coordinates the law transports to
  c_j = (w·z^{−κβ₀−κs₀W̃})·(ξ·z^{κ(γ_m − e_{m−1}W_{m−1})})^j·C_j-shape —
  i.e. the ORBIT of laws {c_j = w·ξ^j·C_j} is stable, with the DISPLAYED
  (character = z^{−iA_{m−1}}, unit = 1) values valid at the pinned (P-ell)
  representative only. This is the same orbit as W-2 §3.4's (ξ, w)
  non-uniqueness — J-A adds no new pinning (JA-BOX-3). [Machine: ORB-RES —
  the displayed rescaling law verified by running the sealed print
  transcription with a shifted ℓ at one level, fixed keys.]
* **(iii) ε = twist: PINNED-CONVENTION STATEMENT.** Under the κ-shift
  t_m(β) ↦ t_m(β) + κβ, so the identity transports to
  ε_m(β)·z_m^{t^{(κ)}(β)} = z_m^{κ·β}. The harness ε is canonical (its own
  normalized Bézout); the print twist is orbit-valued. [Machine: ORB-EPS.]
* **(iv) grid: INVARIANT.** s = ℓV mod e and u = (V − sh)/e depend on ℓ
  only mod e — eq12 and the carry clause are orbit-blind (and ℓ-free by the
  geometric characterization). [Machine: CK-GRID's geometric leg IS the
  invariance witness.]
* **The lift tie rides W-2 clause 2 verbatim:** R(Φ_{m+1}^har) =
  w_{m+1}·ψ_m(ξ_{m+1}·y) with the §3.4 (ξ, w) closed form — JA-RES is the
  standalone per-slot mechanism behind that tie ("the same HR-REC mechanics
  read backwards", W2-C1's proof), now displayed as a theorem about
  ARBITRARY on-line A, not only the lifts.
* **Transported chamber (the transport of J-A is RE-INSTANTIATION, not
  cross-key operator equality):** the transported ledger is itself a
  class-pin instance (W2-C3's induction), so §2/§3 apply VERBATIM inside
  it — harness tower REBUILT on the transported ψ-ledger against the
  chamber's print chain, same theorems, new instance. The cross-chamber
  letter identification z_old = ξ·z_new is W-2 §5.1 step 2, consumed.
  [Machine: TW-INST — the full CK battery re-run on the transported
  instance (SpecTower on the transported ledger + its own GmnLeg), every
  roster tower with a nontrivial transport ledger.]

---

## §5. Base cases consumed (accepted partials, with their exact grades)

* **N-1 (order 2) = the GRB order-2 numeric harness** (`grb_order2_check.py`;
  record `GRB_ORDER2_2026-08-05.md` REV 11/14): **EXECUTED and GREEN
  (2026-08-08) at family-ledger scope** — harness operators = FGMN print
  operators (Def 3.15/3.16/3.18, eq (12)) at order 2, with the ǫ
  extraction-artifact CORRECTED reading ǫ_i(α) = z_i^{ℓ′_i s(α) − ℓ_i u(α)}
  pinned three independent ways (FGMN's own ǫ₀ ≡ 1 remark; Lemma 4.3's
  Bézout algebra, 0/23,111; the external PARI kill-shot P12). Consumed as:
  the ACCEPTED order-2 instance of JA-VAL/JA-EPS and the operator half of
  JA-RES — against a SECOND print (FGMN), decorrelated from this unit's
  GMN/HigherNewton literature leg. Its honest deferral rides: the
  garbled-prime genre at e₀ ≥ 2 was N-1's teeth, reused here (MJ-EPS).
  N-1 does NOT cover: the carrier identification (C15 separation), orders
  ≥ 3, the lift construction (that is W-2).
* **GD-5 (order 1) = base-read conformance, NEARLY CLOSED by composition**
  (`docs/MATH_COMPLETION_TREE_2026-08-01.md` §D2.2 row GD-5): O-2a OL-5
  (b′)+(c′) = O-1thr's PROVED (V1)/(V2)-at-order-1 layer (VAL1 + KEY1 +
  DIV1 + ROOT-M + WGEO) composed with O-2a's PROVED (D3); residue = the S-1
  transcription audit + the degree-g > 1 root-key KEY1 generalization.
  Consumed as: the order-1 floor of JA-VAL/JA-GRID and (with W2-L3) of
  JA-RES. Riding machine partials, cited not re-run: GD-2's T-F check
  (41,720 instances, 0 violations sheared / 7,472 violations unsheared —
  the convention pin this note's §3.1 sentence honors) and GD-8's order-1
  exact-key harness (871 forced samples, 0 findings) for the §3.3 carry
  clause's order-1 layer.
* **W-2 clause 1/2/3** (`GRTW2_PROOF_2026-08-08.md`): consumed AT ATTEMPT
  GRADE (0/2 hostile passes) with its full conditionality ledger — the §2
  clause-8 citation, W2-L0/L2/L3 in §3, and the §4 transport. Nothing here
  upgrades W-2's grades.

## §6. Honest boxes

* **JA-BOX-1 (blueprint correction, review-owed).** Blueprint J-A(ii)
  displays "R_{m,λ} = c·R_λ^GMN with c ∈ F^× slot-independent". FALSE as
  stated at m ≥ 2 whenever the character z_{m−1}^{−i·A_{m−1}} is nontrivial
  on the read support (A_{m−1} > 0 rows abound: any e_{m−2} ≥ 2 with
  ℓ_{m−2} ≥ 1 and ord(z_{m−1}) ∤ e_{m−1}A_{m−1}). The CORRECTED display is
  JA-RES (unit-per-slot CHARACTER gauge). The slot-independent form is
  exactly the JA-VDIND collapse case. [Machine: CK-BPREF census — refuting
  samples counted on designated rows; prediction ≥ 1 per designated row.]
* **JA-BOX-2 (the collapse perimeter, inherited genre W2-BOX-1).** At
  m ≥ 3 the scalar/evaluated forms hold only on (R-coll); the exact law off
  it is the per-slot law fed by the recursion. A two-parameter scalar
  formula on ALL levels would need the monomial-collapse exponents tracked
  explicitly — same residue as W-2 clause 2's. W-1's FULL "operator
  dictionary at all orders" therefore remains OPEN beyond the displayed
  forms; J-A does not claim it.
* **JA-BOX-3 (the unpinned-ℓ convention, inherited from the probe/W-2
  §4.3, review-owed).** Every §3 equality involving print twists/residuals
  is stated at the pinned (P-ell) representative; the print pins no ℓ (tex
  1291). §4 displays the exact orbit action; whether Def-2.12-genre
  statements are read strictly-at-pinned-ℓ or up-to-orbit is genuinely
  underdetermined by the print. Nothing downstream may consume a pinned
  reading silently.
* **JA-BOX-4 (equal characteristic).** The print is mixed-characteristic;
  the F_p[[t]] rows ride construction-identity + the machine leg only (no
  PARI entry point) — displayed deferral, inherited from the probe.
* **JA-BOX-5 (scope fences).** "Realized principal-read" only (slope-0 →
  Hensel/L1 at order 0; JA-PIN clause 2). Single-level carry clause only
  (§3.3 fence). No gr/carrier claim (J-C untouched; BLOCKED-ON-CARRIER-TIE
  stands), no count/menu claim (J-D untouched), no advance on W2-OPEN-1,
  and the P0 application gate stands.

## §7. Records — SEAL PENDING

**Two-commit seal, commit 1:** this note (§§1–6 composed, predictions =
the displayed laws + the runner docstring's family table) and
`verification/openmath/grt_ja_checks.py` are committed BEFORE the sealed
full-roster battery. The §7 machine table, claims/grades table, and
dependency line are appended in commit 2 FROM THE ARTIFACTS
(`grt_ja_checks_output.txt`, `grt_ja_checks_results.json`). Build-phase
smoke disclosed in the runner docstring (reduced roster, ALL GREEN, 4,409
samples; two runner-local repairs + the CK-BPREF designation triple
confirmed there, sealed as T2A/T3A/T3E).

— J-A COMPOSER unit, campaign date 2026-08-08.
