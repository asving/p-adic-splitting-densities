# SIGMALAW — THE Σ-LAW PROVED: the per-coordinate ledger identity at every level, with the map and sign pinned (the ξ-composite, not the bare interior twist)

**Unit:** Σ-LAW (the one displayed lemma of the (Σ-LAW box),
`OPEN2ATTACK_2026-08-08.md` §6; the level-m generalization of GRTW2's LEMMA
W2-L3). **Genre: PROOF NOTE at attempt grade (acceptance counter 0/2;
arc: composed → PE1 NOT CLEAN 0C+1G+2m @ 9b0117d
(`SIGMALAW_passPE1_report.md`: every theorem statement survives, incl. on
an adversarial regime the sealed battery never samples; the GAP = the
(SC-q) REMARK's wrap display, whose TRUE input — the eigen-coefficient
law — the verifier derived on-perimeter) → r1 THIS REPAIR (F1
substantive transcription of the PE1 derivation + F2/F3 in place,
note-only, [r1] tags; runner + artifacts byte-frozen at seal 8064ae3);
counter 0/2; PE2 next; disclosure-grade honesty).** Neither
`GRTW2_PROOF_2026-08-08.md` (ACCEPTED-FROZEN) nor
`OPEN2ATTACK_2026-08-08.md` is edited by this unit; the closing fold is
delivered as PROPOSED ANNEX TEXT (§8).

**Machine bracket:** `verification/openmath/sigmalaw_checks.py` (this unit;
outputs `sigmalaw_output.txt`, `sigmalaw_results.json`). Engine =
committed `iterlawn_pe_reimpl` verbatim; `TowerX`/`gap_scan` imported from
the committed `open2attack_checks` verbatim; classifier = the sealed
probe's `GmnLeg` verbatim; `actual_ratios` from the sealed `grt_w2_checks`
verbatim. Fresh code: the ξ-composite map `Sigma`, the u_j closed form,
the separator families, teeth.

**VERDICT UP FRONT.** The Σ-LAW is **PROVED at attempt grade** — in the
sharper per-coordinate form Prnt_j(A) = u_j·Σ_m(R_m v(A)) with an EXPLICIT
slot constant u_j and an EXPLICIT coordinate map Σ_m — for EVERY on-line
level-m slot object at every shared-below junction at every m ≥ 1, gap
rows included with no correction term. Two corrections to the boxed
statement, both derived and both machine-witnessed by constructed
non-involution separators:

1. **The map is not the bare interior twist.** The boxed σ′ (the runner's
   `sigma_twist`: z_q ↦ θ_q z_q, θ_q = z_{q−1}^{A_{q−1}e_{q−1}}) is the
   WRONG map: the true map Σ_m twists each letter by the **§3.4 FORMULA
   character** ξ_q = χ_{q−1}^{γ_q}·z_{q−1}^{−e_{q−1}A_{q−1}} — i.e.
   θ_q^{−1} at q = 2, and θ_q^{−1}·(the χ-chain correction χ_{q−1}^{γ_q})
   at q ≥ 3. On every involution geography (ALL δ ≠ 1 rows of the sealed
   468-row battery) Σ_m and σ′^{±1} coincide — which is exactly why the
   sealed unit measured 0 violations yet could not fix the sign.
2. **The sign is fixed**: δ_j = ρ_j / Σ_m(ρ_j) — the coboundary
   ρ^{1−Σ}. Both boxed variants ρ^{1∓σ′} (bare-θ map, either sign) are
   **FALSE in general**: refuted on constructed witnesses at m = 2 (map
   inverse visible at an order-4 invisible twist) and at m = 3 (the
   χ-chain correction visible), where the ξ-law holds and both bare-θ
   variants fail (§5; machine SL-SEP2/SL-SEP3).

Consequence (§4): **THEOREM OPEN-2a-Σ fires unconditionally** on the
Σ-LAW leg — at every shared-below junction at every m, strict ⟹
byte-equal, hence recorded ξ = 1 ⟹ byte-equal under every selection rule
— consuming OA-L1–L4 at their recorded grades (attempt). The (Σ-LAW box)
CLOSES at attempt grade; the m ≥ 2 forward direction of (OPEN-2a) is no
longer boxed on the Σ-LAW.

---

## §1. Setting and objects (OPEN2ATTACK §1 notation, code-pinned)

Junction at level m+1 (GMN r = m+2), keys byte-shared below; slot field
K_m, modulus ψ = ψ_m, g = g_m, e_m; slots k_j = j·e_m, weights
β_j = (g−j)γ_{m+1}, supp = {j < g : ψ_{m,j} ≠ 0}. Harness slot digits
C_j = realize_m(ε_m(β_j)^{−1}ψ_{m,j}, β_j); print slot digits P_j
(Prop-`construct` children). Reads (e_q, h_q, g_q), Bézout (ℓ_q, ℓ′_q)
under (P-ell), γ/wΦ recursions as in GRTW2 §1.

**The print slot evaluator** (Def-`t(i)` + Def-`rescoeff`, exactly the
sealed `GmnLeg.rres` semantics): for the order-(r−1) residual of a key X,
the slot-j coefficient is

    Prnt_j(A) = z_m^{t_j(A)} · R_m(A)(z_m),
    t_j(A)    = (s_m(A) − ℓ_{m−1}·u_j)/e_{m−1},

A = the dev digit of X at abscissa k_j (a level-m object, on-line at
weight β_j), u_j = β_j + k_j·w_mΦ_m its polygon ordinate, s_m(A) the
ATTAINED initial abscissa of A's own level-m polygon, and R_m(A)(z_m) the
order-m print residual of A packed at the letter z_m FROM THE ATTAINED
START (rres recursion). The harness read is R_m v(A) (level-m read,
ε-corrected packing from the eq12 GRID start). The gauge objects ρ_j,
R_j = Prnt_j(C_j), δ_j = R_j·ρ_j/(c·ψ_{m,j}) as in OPEN2ATTACK §1.

**The two normalized evaluators.** For an on-line level-q object A at
weight β, with (s, u) = eq12(β; e_{q−1}, h_{q−1}) and s₀ = s_q(A) = s +
ν₀e_{q−1} the attained start (ν₀ ≥ 0 = the GAP of the top node):

    H_q(A) := R_q v(A)                      (harness read),
    P_q(A) := z_q^{τ_q(A)} · R_q(A)(z_q),   τ_q(A) := (s₀ − ℓ_{q−1}β)/e_{q−1}.

τ_q is W2-L3's τ₁ verbatim at level q. Then t_j(A) = τ_m(A) − k_j·A_m
(Bézout: ℓ_{m−1}(u_j − β_j)/e_{m−1} = k_j·ℓ_{m−1}g_{m−1}γ_m = k_jA_m
[r1, PE1 F3: the sealed parenthetical read k_j·ℓ_{m−1}g_mγ_{m+1} — an
index slip; u_j − β_j = k_j·w_mΦ_m = k_j·e_{m−1}g_{m−1}γ_m; the final
k_jA_m and every downstream use are correct and machine-keyed]
with A_m = ℓ_{m−1}g_{m−1}γ_m read off u_j − β_j = k_j·w_mΦ_m and
ℓ_{m−1}w_mΦ_m/e_{m−1} = A_m), so **Prnt_j = z_m^{−k_jA_m}·P_m** on slot-j
digits, and the whole problem is the dictionary P_m vs H_m.

**The ledger characters (all §3.4 objects, used as DEFINITIONS):**

    A_q  = ℓ_{q−1}g_{q−1}γ_q ;   χ₁ = 1 ,
    χ_q  = χ_{q−1}^{ℓ′_{q−1} − ℓ_{q−1}·w_{q−1}Φ_{q−1}} · z_{q−1}^{A_{q−1}ℓ_{q−1}}   (q ≥ 2),
    ξ_q  = χ_{q−1}^{γ_q} · z_{q−1}^{−e_{q−1}A_{q−1}}                                 (q ≥ 2).

**(Σ-DEF) the ξ-composite twist** Σ_q : K_q → K_q, K₀-linear, coordinate
bijection fixing 1: Σ₁ = id (and Σ₀ = id); for q ≥ 2, writing x = Σ_ν
y_ν z_q^ν (y_ν ∈ K_{q−1}, ν < g_{q−1}, the faithful basis),

    Σ_q( Σ_ν y_ν z_q^ν ) := Σ_ν Σ_{q−1}(y_ν) · ξ_q^ν · z_q^ν .

At q = 2: ξ₂ = z₁^{−e₁A₁} = θ₂^{−1} — the INVERSE of the runner's
`sigma_twist` letter; at q ≥ 3 the χ-correction χ_{q−1}^{γ_q} enters.

**(U-REC) the weight gauge:** U₁(β) ≡ 1;

    U_q(β) = z_{q−1}^{−s(β)·A_{q−1}} · χ_{q−1}^{−w₀(β)}   (q ≥ 2),
    s(β) = ℓ_{q−1}β mod e_{q−1},  w₀(β) = (β − s(β)γ_q)/e_{q−1}.

---

## §2. The two recursions and the gap cancellation (LEMMA SL-L1)

**LEMMA SL-L1.** For every on-line level-q object A at weight β (q ≥ 1),
with digits A_ν (the Φ_{q−1}-dev digits at abscissa a_ν = s + νe_{q−1}
that are on-line at exact weight w_ν = (β − a_νγ_q)/e_{q−1}; arbitrary
support, gaps allowed):

    (H-REC)  H_q(A) = Σ_ν ε_{q−1}(w_ν) · H_{q−1}(A_ν) · z_q^ν ,
    (P-REC)  P_q(A) = ε_q(β) · Σ_ν z_{q−1}^{−a_ν·A_{q−1}} · P_{q−1}(A_ν) · z_q^ν ,

with P₀ = H₀ (res at exact weight) and, in (P-REC) at q = 1, the twist
factor absent (order-one rescoeff has no twist): P₁(A) = ε₁(β)·H₁(A) —
LEMMA W2-L3 verbatim. **The gap terms ν₀ do not appear in either
recursion**: they cancel identically inside P_q at every node.

*Proof.* (H-REC) is the read recursion (GRTW2 (HR-REC) mechanics; the
engine's `read`/`read_coeffs` definition): grid-indexed from s, only
exact-weight digits contribute, packing faithful since ν < g_{q−1}.

(P-REC): unfold `rres`. The order-q print polygon of A minimizes
e_{q−1}·(v_q(digit) + a·v_q(φ_q)) + a·h_{q−1} = e_{q−1}w_{q−1}(digit) +
aγ_q over nonzero digits (P-index ties v_q = w_{q−1}, v_q(φ_q) =
w_{q−1}Φ_{q−1}, γ_q = e_{q−1}w_{q−1}Φ_{q−1} + h_{q−1}) — the SAME
functional as the harness weight, so the attained set = the exact-weight
digit set, and attained abscissas satisfy a ≡ ℓ_{q−1}β ≡ s (mod
e_{q−1}). The slot-(ν−ν₀) rres coefficient of A is
z_{q−1}^{t(a_ν)}·R_{q−1}(A_ν)(z_{q−1}) with t(a_ν) = (s_{q−1}(A_ν) −
ℓ_{q−2}·(w_ν + a_ν·w_{q−1}Φ_{q−1}))/e_{q−2} = τ_{q−1}(A_ν) − a_ν·A_{q−1}
(Bézout as in §1, ℓ_{q−2}w_{q−1}Φ_{q−1}/e_{q−2} = A_{q−1}), i.e. the
coefficient is z_{q−1}^{−a_νA_{q−1}}·P_{q−1}(A_ν). Packing from the
attained start and multiplying by z_q^{τ_q(A)}:

    P_q(A) = z_q^{(s−ℓβ)/e} · z_q^{ν₀} · Σ_ν z_{q−1}^{−a_νA_{q−1}} P_{q−1}(A_ν) z_q^{ν−ν₀},

and z_q^{ν₀}·z_q^{ν−ν₀} = z_q^ν while (s − ℓβ)/e = ℓ′s − ℓu = the
ε_q(β)-exponent (ℓh + ℓ′e = 1 — W2-L2's 𝔰 = s, k = 0 case). ν₀ is gone. ∎

*Why this answers §6's "gap-term" obstruction:* the τ-normalization is
pinned to the SAME attained start the rres packing uses, so each
builder's gap ledger cancels within its OWN evaluator, node by node. No
coincidence of the two builders' gap ledgers is needed, and none is
claimed — the sealed unit's guess ("the two builders' gap ledgers
coincide") was the wrong mechanism; they need not coincide.

---

## §3. THEOREM SL-1 (the ledger identity, every level)

**THEOREM SL-1.** For every on-line level-q object A at weight β, q ≥ 1:

    (VD-q)      P_q(A) = ε_q(β) · U_q(β) · Σ_q( H_q(A) ) .

Consequently, at a shared-below junction at level m+1, for every
supported slot j and EVERY on-line level-m object A at weight β_j (in
particular both builders' slot digits C_j, P_j):

    (Σ-LEDGER)  Prnt_j(A) = u_j · Σ_m( R_m v(A) ),
    u_j = z_m^{−k_j·A_m} · ε_m(β_j) · U_m(β_j)     — slot-constant.

*Proof of (VD-q), induction on q.* q = 1: W2-L3 (U₁ = 1, Σ₁ = id). Step
q−1 → q (q ≥ 2): substitute (VD-(q−1)) into (P-REC) per digit:

    P_q(A) = ε_q(β) Σ_ν z_{q−1}^{−(s+νe)A'} · ε'(w_ν) U'(w_ν) Σ_{q−1}(H_{q−1}(A_ν)) · z_q^ν

(shorthand e = e_{q−1}, A' = A_{q−1}, ε' = ε_{q−1}, U' = U_{q−1}).
Meanwhile ε_q(β)U_q(β)Σ_q(H_q(A)) expands over (H-REC) coordinates as
ε_q(β)U_q(β)·Σ_ν Σ_{q−1}(ε'(w_ν))·Σ_{q−1}(H_{q−1}(A_ν))·ξ_q^ν z_q^ν. The
coordinates ν < g_{q−1} are faithful, so equality per ν is required and
sufficient; dividing, (VD-q) holds iff for every populated ν

    U_q(β) · ξ_q^ν · Σ_{q−1}(ε'(w_ν)) = z_{q−1}^{−sA'} · z_{q−1}^{−νeA'} · ε'(w_ν) · U'(w_ν),

i.e., defining the GAUGE RATIO  Λ_{q−1}(w) := ε_{q−1}(w)·U_{q−1}(w) /
Σ_{q−1}(ε_{q−1}(w)):

    (MATCH)   U_q(β) = z_{q−1}^{−sA'} · [ z_{q−1}^{−eA'} ξ_q^{−1} ]^ν · Λ_{q−1}(w_ν) .

**LEMMA SL-L2 (the gauge-ratio law).** Λ_q(w) = χ_q^{−w} for every q ≥ 1
and every weight w in the level-q grid. *Proof, induction riding the main
one.* q = 1: Λ₁ = ε₁U₁/Σ₁(ε₁) = 1 = χ₁^{−w}. Step: with U_q as in
(U-REC) and ε_q(w) = z_q^{E(w)}, E(w) = (s(w) − ℓ_{q−1}w)/e_{q−1}, and
Σ_q(z_q^k) = ξ_q^k z_q^k (z_q-powers with k < g_{q−1}; for general k the
map is multiplicative on the relation ψ_{q−1}... — see the REMARK below):

    Λ_q(w) = U_q(w) · ξ_q^{−E(w)}
           = z_{q−1}^{−s(w)A_{q−1}} χ_{q−1}^{−w₀(w)} · [χ_{q−1}^{γ_q} z_{q−1}^{−e_{q−1}A_{q−1}}]^{−E(w)} .

z-part exponent: −s(w)A_{q−1} + A_{q−1}(s(w) − ℓ_{q−1}w) = −A_{q−1}ℓ_{q−1}w.
χ-part exponent: −(w − s(w)γ_q)/e_{q−1} − γ_q(s(w) − ℓ_{q−1}w)/e_{q−1}
= w(ℓ_{q−1}γ_q − 1)/e_{q−1} = w(ℓ_{q−1}w_{q−1}Φ_{q−1} − ℓ′_{q−1})
(using γ_q = e_{q−1}w_{q−1}Φ_{q−1} + h_{q−1} and ℓh − 1 = −ℓ′e). Hence
Λ_q(w) = [χ_{q−1}^{ℓ′_{q−1} − ℓ_{q−1}w_{q−1}Φ_{q−1}}·z_{q−1}^{A_{q−1}ℓ_{q−1}}]^{−w}
= χ_q^{−w} — **the §3.4 χ-recursion verbatim**. ∎

Given SL-L2 at q−1, (MATCH) reads U_q(β) = z_{q−1}^{−sA'}·
[z_{q−1}^{−eA'}ξ_q^{−1}]^ν·χ_{q−1}^{−w₀+νγ_q} with w_ν = w₀ − νγ_q; the
ν-dependent part is [z_{q−1}^{−eA'}·ξ_q^{−1}·χ_{q−1}^{γ_q}]^ν = 1
**precisely by the §3.4 ξ-definition** ξ_q = χ_{q−1}^{γ_q}z_{q−1}^{−e_{q−1}A_{q−1}},
and the rest is (U-REC). ∎ (VD-q), (Σ-LEDGER) as displayed (§1 tie
Prnt_j = z_m^{−k_jA_m}P_m). ∎

*REMARK (Σ on z-powers).* In SL-L2, Σ_q(ε_q(w)) with ε_q(w) = z_q^{E},
E ∈ ℤ arbitrary: Σ_q as defined acts on the coordinate FORM; for it to
satisfy Σ_q(z_q^E) = ξ_q^E z_q^E one needs ξ_q^{g_{q−1}}·(compatibility
with the relation z_q^{g_{q−1}} = −Σ_j ψ_{q−1,j}z_q^j). The proof does
NOT need Σ_q multiplicative: SL-L2 is used only where ε'(w_ν) multiplies
the coordinate y_ν INSIDE the ν-th slot, i.e. only the K_{q−1}-scalar
action Σ_{q−1}(ε'·y) with ε' ∈ K_{q−1} — and there the identity
Σ_{q−1}(ε'(w)y) = [ε'(w)·Λ'-corrected] requires the same statement one
level down, resolved by the induction: formally, SL-L2's content is the
scalar identity Σ_{q−1}(ε_{q−1}(w)·y) = ε_{q−1}(w)Λ_{q−1}(w)^{−1}·
U_{q−1}(w)... — to keep the chain honest the induction is run with the
COMBINED statement [r1, PE1 F1: THREE clauses now — the
eigen-coefficient law (EC-q), displayed below, joins the sealed two as
the wrap-closing clause]: (VD-q) AND (EC-q) AND the scalar covariance

    (SC-q)   Σ_q( ε_q(w) · y ) = ε_q(w)·ξ_q^{E(w)} · Σ_q(y)   for all y ∈ K_q, w,

which holds because ε_q(w) = z_q^{E(w)} with E(w) = ℓ′s − ℓu and
multiplication by z_q^{E} maps the coordinate basis z_q^ν by shifting
ν-support through the relation; (SC-q) as stated is the assertion that
this shift commutes with Σ_q up to ξ_q^{E}. For 0 ≤ E and ν with
E + ν < g_{q−1} it is definitional; the wrap terms (E + ν ≥ g_{q−1})
consume preservation of the relation z_q^{g_{q−1}} = −Σ_{i<g_{q−1}}
ψ_{q−1,i}z_q^i: the wrapped slot comparison is, per supported i,

    Σ_{q−1}(y·ψ_{q−1,i})·ξ_q^{i} = Σ_{q−1}(y)·ψ_{q−1,i}·ξ_q^{g_{q−1}}   for ARBITRARY y ∈ K_{q−1},

equivalently (take y = 1; Σ_{q−1} fixes 1) the **EIGEN-COEFFICIENT LAW**

    (EC-q)   Σ_{q−1}(ψ_{q−1,j}) = ξ_q^{g_{q−1}−j} · ψ_{q−1,j}    (j ∈ supp ψ_{q−1})

plus Σ_{q−1}-multiplicativity against ψ_{q−1,j} (Σ_{q−1} ∈ Aut(K_{q−1}),
supplied one level down by the same ladder). (EC-q) is exactly the
condition that the (Σ-DEF) twist preserve the relation ideal
(ψ_{q−1} ↦ ξ_q^{g_{q−1}}·ψ_{q−1}), making Σ_q a ring AUTOMORPHISM of
K_q — whence the shift commutes with Σ_q up to ξ_q^{E} for ALL E, and
(SC-q) closes.

[r1, PE1 F1 (justification gap; the two §7 self-flagged points, one
root cause) — SUBSTANTIVE REPLACEMENT: the sealed REMARK displayed the
wrap input as "ξ_q^{g_{q−1}−i} = 1 on supp(ψ_{q−1})", identified with
the byte-share law of GRTW2 §3.4 rk. 3 "at level q−1" as supplied by
the shared-below premise. That display is (EC-q)'s Σ_{q−1} = id
SPECIAL CASE only, and PE1 proved it FALSE on part of the shared-below
perimeter: 7 constructed doubly-twisted towers (instrument note, end
of §5) are shared-below with ξ₃^{g₂−j} = z₁^{±2} ≠ 1 on the supported
slot — the asserted implication "shared-below ⟹ ξ_q-invisibility at
every interior level" is REFUTED, and rk. 3's proved display is the
m = 1 form only. The theorem SURVIVES there: the ledger identity, the
δ-law, and (EC-q) itself hold on all 7 rows, with a NON-trivial
eigenvalue. At Σ_{q−1} = id, (EC-q) collapses to the old display
(λ_j = 1 ⟺ θ^{g−j} = 1 at m = 1 — rk. 3 recovered). The derivation
below is PE1's, transcribed in full per the repair charge; r1
re-verified the k = 1 tower's arithmetic and the λ_j collapse by
hand.]

**(EC-q) is DERIVABLE on the shared-below perimeter** — no new premise.
At the interior junction at level q (slot field K_{q−1}, modulus
ψ_{q−1}, weights β_j = (g_{q−1}−j)γ_q, slots k_j = j·e_{q−1}), which
the shared-below premise makes byte-equal (2 ≤ q ≤ m), chain the
level-(q−1) induction clauses with the junction's evaluator theorems:
byte-equal ⟹ ρ_j = 1 (OA-L4), so both builders' slot digits carry the
read R_{q−1}v = ε_{q−1}(β_j)^{−1}·ψ_{q−1,j} (REALIZE R3); then

    c·ψ_{q−1,j} = Prnt_j(P_j)                                      [Thm-`phir`]
                = u_j · Σ_{q−1}( ε_{q−1}(β_j)^{−1}·ψ_{q−1,j} )     [(Σ-LEDGER) at q−1, from (VD-(q−1)); ρ_j = 1]
                = u_j · ε_{q−1}(β_j)^{−1}·ξ_{q−1}^{−E(β_j)} · Σ_{q−1}(ψ_{q−1,j})   [(SC-(q−1))],

and with u_j's closed form (§3): Σ_{q−1}(ψ_{q−1,j}) = λ_j·ψ_{q−1,j},
λ_j = c·z_{q−1}^{k_jA_{q−1}}·U_{q−1}(β_j)^{−1}·ξ_{q−1}^{E(β_j)}. SL-L2
at q−1 gives U_{q−1}(β_j)^{−1}·ξ_{q−1}^{E(β_j)} = χ_{q−1}^{β_j}, and
Thm-`phir`'s constant is c = z_{q−1}^{−A_{q−1}e_{q−1}g_{q−1}} (GRTW2:
c = c₁^{e_{q−1}g_{q−1}}, c₁ = z_{q−1}^{−A_{q−1}}), so

    λ_j = z_{q−1}^{−A_{q−1}e_{q−1}g_{q−1}} · z_{q−1}^{j·e_{q−1}A_{q−1}} · χ_{q−1}^{(g_{q−1}−j)γ_q}
        = [ χ_{q−1}^{γ_q} · z_{q−1}^{−e_{q−1}A_{q−1}} ]^{g_{q−1}−j}  =  ξ_q^{g_{q−1}−j}

— identically, by ξ_q's §3.4 definition, with NO invisibility
assumption. The ladder is well-founded: (VD-1)/(SC-1) are trivial
(Σ₁ = id); for q ≥ 2, (EC-q) is discharged by the display above from
(VD-(q−1)) + (SC-(q−1)) + SL-L2 at q−1 + Thm-`phir` + the byte-equal
interior junction at level q; (EC-q) closes (SC-q)'s wrap terms and
makes Σ_q ∈ Aut(K_q); (SC-q) feeds (VD-q). Every interior level
2 ≤ q ≤ m is byte-equal on the shared-below perimeter — which is the
Σ-LAW's stated scope. [Machine: the checker tests
(VD-q)/(Σ-LEDGER)/(SC) jointly by testing the final identities on
elements; SL-VDM. (EC-q) itself is machine-keyed by PE1 on the
doubly-twisted regime — 7/7 with a non-trivial eigenvalue — and its
eigen-MISMATCH control (k = 3, i = 1) builds but FAILS m = 2
byte-equality 1/1, exactly as the derivation predicts; instrument
note, end of §5.]

**Grade & consumption.** Attempt grade (0/2). Consumes: the engine
definitions (REALIZE R1–R3, read/eq12/ε — S0.1/S0.2 accepted), the print
evaluator definitions (Def-`t(i)`, Def-`rescoeff`, order-one base — the
sealed transcription), the P-index dictionary (GRTW2 §1.2), W2-L0 grid
mechanics, W2-L2 Bézout identity (both directions of the exponent
bookkeeping), W2-L3 as the base case, the §3.4 χ/ξ RECURSIONS as
definitions (no §3.4 theorem-content consumed — the recursion falls OUT
of the induction here), and, for (EC-q) at each interior level, the
shared-below premise's byte-equal interior junctions consumed through
OA-L4 (byte-equal ⟹ ρ = 1) + Thm-`phir` with its constant [r1, PE1 F1:
the sealed list cited "the shared-below byte-share law" here — the
Σ_{q−1} = id reading of the input; the true consumption is interior
byte-EQUALITY itself, per the (EC-q) derivation above]. No new
literature consumption.

---

## §4. Consequences: the δ-law and OPEN-2a-Σ unconditional

**COROLLARY SL-C1 (the Σ-LAW, map and sign pinned).** At every
shared-below junction at level m+1, every j ∈ supp:

    δ_j = ρ_j / Σ_m(ρ_j) .

*Proof.* δ_j = [Prnt_j(C_j)/R_mv(C_j)]/[Prnt_j(P_j)/R_mv(P_j)] (OA-L2's
invariant reading, consuming Thm-`phir` = OA-PHIR for the denominator);
by (Σ-LEDGER) both bracketed gauges are u_j·Σ_m(x)/x at x = the
respective reads, so δ_j = ρ_j·Σ_m(x/y) = ρ_j·Σ_m(ρ_j^{−1}·...)
— with x = R_mv(C_j), y = R_mv(P_j) = ρ_j·x: δ_j = (y/x)·Σ_m(x)/Σ_m(y).
Σ_m(x)/Σ_m(y): x and y = ρ_jx are the two reads
and the quotient identity δ_j = ρ_j/Σ_m(ρ_j) is
asserted as the ELEMENT identity that follows when Σ_m(y)/Σ_m(x) =
Σ_m(ρ_j) — this holds because **Σ_m ∈ Aut(K_m)**: the eigen-coefficient
law (EC-q) of §3's REMARK preserves the relation ideal at every
interior level 2 ≤ q ≤ m (ψ_{q−1} ↦ ξ_q^{g_{q−1}}·ψ_{q−1}), so the
composite Σ_m is a ring automorphism and Σ_m(y) = Σ_m(ρ_j)·Σ_m(x)
outright [r1, PE1 F1: re-pointed at the derived law. The sealed hedge —
"(SC)-type covariance when x is an ε-monomial-times-class
(x = ε_m(β_j)^{−1}ψ_{m,j}, REALIZE R3), by the same wrap-invariance as
§3's REMARK" — was INSUFFICIENT as stated: the step needs
Σ_m(ρ·x) = Σ_m(ρ)Σ_m(x) with ρ an ARBITRARY unit, i.e. the automorphism
property, i.e. ideal preservation = exactly (EC); OA-M1 never met this
because σ′ is coefficientwise-trivial below, while the composite Σ_m at
m ≥ 3 is not]; the machine keys the element
identity directly on every walked row (SL-DELTA). ∎ (attempt grade; the
multiplicativity step now rides (EC-q), discharged on-perimeter in §3's
REMARK).

**COROLLARY SL-C2 (THEOREM OPEN-2a-Σ, now unconditional on its Σ-leg).**
At every shared-below junction at level m+1, m ≥ 1: strict ⟹ byte-equal;
hence recorded ξ = 1 ⟹ byte-equal, under EVERY selection rule. *Proof.*
Strict ⟹ δ_j = ρ_j on supp (OA-L3) ⟹ Σ_m(ρ_j) = 1 = Σ_m(1) (SL-C1) ⟹
ρ_j = 1 (Σ_m is a K₀-linear coordinate BIJECTION fixing 1 — nonzero
characters coordinatewise; no automorphism property needed, OA-M1 not
consumed) ⟹ byte-equal (OA-L4). ∎ Grades consumed: OA-L1/L2/L3/L4 at
attempt grade (OPEN2ATTACK §1), SL-1/SL-C1 at attempt grade.

**Remark (perimeter collapse).** On (C-coll) every ξ_q = 1, Σ_m = id,
δ ≡ 1: recovers OA-GAUGE and the W2-ID1/(C-coll) collapse of OPEN2ATTACK
§1's remark. At m = 1, Σ₁ = id and δ ≡ 1 — W2-L3's scalar form.

---

## §5. The sign/map question RESOLVED (constructed separators)

All observed δ on the sealed battery were involutions, so the two boxed
variants ρ^{1∓σ′} could not be separated there (OPEN2ATTACK §4.3). The
resolution is by CONSTRUCTION (the constructed-counterexamples
discipline: derive where the candidate laws differ, then build it):

* **SEP-A (m = 2; the map is the inverse).** Chamber ℤ₃,
  (2,1,2)+(e₁,h₁,4): K₁ = F₉ with z₁ PRIMITIVE (ψ₀ = y²+y+2, ord 8);
  A₁ = 2, so ξ₂ = z₁^{−2e₁} has ORDER 4 yet is SUPPORT-INVISIBLE on
  ψ₁ = y⁴ + z₁^k (supp {0,4} ≡ 0 mod 4) — the m = 1 junction is
  byte-equal and the m = 2 junction is shared-below with a NON-involution
  twist. Monomial top moduli keep ρ in even z₂-parity (the W2-L2 parity
  collapse: texp + ε-exponent ≡ 0 mod ord — whence no separation on any
  monomial genre); NON-MONOMIAL top moduli (ψ₂ coefficient 1 + z₂ etc.)
  put both parities into the read and separate the maps. Measured
  (smoke, disclosed; sealed family SL-SEP2): on every such row δ is NOT
  an involution, δ_j = ρ_j/Σ₂(ρ_j) HOLDS, and BOTH bare-θ variants
  δ = ρ^{1∓σ′} FAIL.
* **SEP-B (m = 3; the χ-chain correction is real).** Chamber ℤ₃,
  (2,1,1)+(2,1,2)+(2,1,2) with ψ₂ = y² + (nonsquare of F₉): χ₂ =
  z₁^{A₁ℓ₁} = −1 and γ₃ odd, so ξ₃ = χ₂^{γ₃}z₂^{−e₂A₂} = −z₂^{−e₂A₂}
  while the bare θ₃^{±1} = z₂^{±e₂A₂} MISSES the −1: at
  (e₂,h₂) = (2,1), z₂^{e₂A₂} = 1, so the runner's composite σ′₃ is the
  identity on the letter while the true Σ₃ twists z₃ by −1. Non-monomial
  ψ₃ (1 + z₃ etc.) exposes it. Measured (smoke, disclosed; sealed family
  SL-SEP3): δ ≠ 1 rows where the ξ-law HOLDS and both bare-θ variants
  FAIL.

So the honest restatement of the boxed law is: **δ_j = ρ_j/Σ_m(ρ_j),
Σ_m the ξ-formula composite** — "variant A with σ′ replaced by the
ξ-twist"; equivalently, at m = 2, variant A with the runner's map
INVERTED. The involution degeneracy of the sealed battery is now
explained rather than boxed: on every one of its δ ≠ 1 rows the acting
characters were ±1, where Σ_m = σ′ = σ′^{−1}.

**[r1] INSTRUMENT NOTE (PE1 F1): the doubly-twisted counter-regime —
the 7 towers the sealed battery never samples.** PE1's verifier
constructed the regime where the sealed REMARK's wrap display fails
while every theorem survives (verifier's own code,
`/tmp/slverify/fresh_check.py`, not committed; figures quoted from
`SIGMALAW_passPE1_report.md`): chamber ℤ₃, reads (2,1,2)+(3,1,4),
ψ₀ = y²+y+2 (z₁ primitive, ord 8), ψ₁ = y⁴+z₁^k (k odd) — A₁ = 2,
ξ₂ = z₁^{−6} = z₁² of ORDER 4, support-invisible on supp ψ₁ = {0,4}
(m = 1 junction byte-equal); third read (1,1,2), ψ₂ = y² + c·z₂
(c ∈ K₁*) — the coefficient is NOT Σ₂-fixed (Σ₂(cz₂) = ξ₂·cz₂ =
z₁²·cz₂), and ξ₃ = χ₂^{γ₃}z₂^{−e₂A₂} = z₁^{6−5k mod 8} has
ξ₃^{g₂−0} = ξ₃² = z₁^{±2} ≠ 1 on the supported slot; deg-1
non-monomial top (1,1,1)/ψ₃ = y+(1+z₃) walks the m = 3 junction.
Machine (PE1): 8 towers built, 7 shared-below (byte-equal m = 2); on
all 7 walked m = 3 rows the ledger identity AND the δ-law hold (0
violations), each row is a separator (both bare-θ variants fail),
(EC-q) holds with a NON-trivial eigenvalue, and the sealed REMARK's
input ξ₃^{g₂−j} = 1 is FALSE; the eigen-MISMATCH control (k = 3,
i = 1) builds but fails m = 2 byte-equality, 1/1 as predicted. r1
re-verified the k = 1 tower by hand: z₁⁴ = 2 = −1 (ord 8); γ₁ = 1,
ℓ₀ = 1 ⟹ A₁ = 2; w₁Φ₁ = 4, γ₂ = 13, w₂Φ₂ = 156, A₂ = 52, γ₃ = 157
odd; χ₂ = z₁^{A₁ℓ₁} = z₁²; z₂⁴ = −z₁^k = z₁^{k+4} ⟹ z₂^{−52} =
z₁^{3k+4 mod 8}, so ξ₃ = z₁^{3k+6} = z₁^{6−5k mod 8} ✓; at k = 1:
ξ₃ = z₁, ξ₃² = z₁² = ξ₂ — (EC) holds, non-trivially eigen; at k = 3:
ξ₃² = z₁⁶ ≠ ξ₂ = z₁² — the control's mismatch ✓. **Zero-sampling
disclosure for the SEALED battery:** PE1's census of all 145 walked
m = 3 rows: (ξ₂-trivial, g₂, ψ₂-Σ₂-fixed) = {(True, 2, True): 123;
(False, 1, False): 22 — the B3D genre, whose g₂ = 1 relation is
degenerate (Σ₃ = Σ₂, no wrap)}. NO sealed row has ξ₂ ≠ 1 with g₂ ≥ 2:
the regime where the sealed display fails is exactly the regime the
sealed instrument never samples — PE1's 7 rows are its first
instances, and the law is green there too. The sealed runner +
artifacts stay byte-frozen (seal 8064ae3); this note records the
coverage hole honestly rather than patching the battery.

---

## §6. Machine bracket (preregistration; two-commit seal)

Battery (deterministic; engine/classifier/helpers verbatim from the
committed artifacts; fresh code = Sigma/u_j/families): (i) the FULL
OPEN2ATTACK battery reproduced (`OA.gen_battery()`: roster 16 towers +
B1/B1F/B4/B2/B3A/B3B/B3D), (ii) SEP-A family (F₉/ord-4 genre above,
capped deterministic sweep), (iii) SEP-B family (χ-correction genre,
capped deterministic sweep).

| family | claim | prereg |
|---|---|---|
| SL-VDM | (Σ-LEDGER) with the CLOSED-FORM u_j, both legs (C_j and P_j), every walked shared-below junction, every m ∈ {1,2,3} | 0 |
| SL-DELTA | δ_j = ρ_j/Σ_m(ρ_j), every walked junction, every m | 0 |
| SL-GAP | SL-VDM/SL-DELTA restricted to gap rows (gap_scan > 0 on either digit) | 0 violations; > 100 gap slots expected |
| SL-PHIR | Prnt_j(P_j) = c·ψ_{m,j} (Thm-phir reproduction; δ's factorization leg) | 0 |
| SL-SEP2 | census: m = 2 rows where Σ₂(ρ) ≠ σ′(ρ) and both bare-θ variants fail while SL-DELTA holds | ≥ 8 rows (smoke: 8) |
| SL-SEP3 | census: m = 3 rows likewise (χ-correction live) | ≥ 6 rows (smoke: 6) |
| SL-INVREC | reconciliation census: on OA-battery rows, # where Σ_m(ρ) = `sigma_twist`(ρ) (explains the sealed 0-violation record) | = all OA δ≠1 rows |
| TEETH-US | u_j garbled (U_m dropped) on 2 designated towers | caught on both |
| TEETH-SB | Σ garbled (bare-θ forward composite — the boxed candidate) on 2 designated separator towers | caught on both |
| TEETH-PR | print leg garbled (`mut_droptwist`) on T2C + T3C | caught on both (via SL-PHIR) |

**Smoke disclosure (pre-seal, honest).** Four throwaway scripts
(`/tmp/sl_smoke.py`, `/tmp/sl_hunt{,2,3,4}.py`, disclosed here, not
sealed) were run BEFORE composing this note: (a) the ledger identity +
δ-law verified on I4A/I4B/I4C + sampled B1/B2/B3B/B3D rows (66 ledger
checks incl. 24 gap-involved, 33 δ checks, 0 violations); (b) the
separator hunts that FOUND SEP-A (8 rows) and SEP-B (6 rows) after two
failed genres (monomial moduli: the parity-collapse lemma of §5 was
learned from the first hunt's 512 non-separating rows); (c) teeth
visibility (U ≠ 1, Σ ≠ σ′ on designated rows) verified in the same
smokes. The sealed runner's own `--smoke` mode re-runs a subset. Nothing
else tuned; the full sealed battery is UNRUN at commit 1.

## §6R. RESULTS (commit 2; from the committed artifacts)

**Sealed battery (`sigmalaw_checks.py`, run once post-seal, exit 0,
18.5 s, 6,970 samples): 539 towers built (389 OA-battery + 96 SEPA + 54
SEPB, 0 rejects), 1,217 junction rows = 1,211 walked (539 m=1 + 527 m=2
+ 145 m=3) + 6 SKIP (the roster's above-twist rows). ALL preregistered
families GREEN; all six teeth rows CAUGHT.** Family table (pred/obs/
samples): SL-VDM 0/0 (2,854 — both legs, every walked slot, every m) ·
SL-DELTA 0/0 (1,427) · SL-GAP 0/0 (688 gap-slot samples; 340 gap slots
across 317 gap rows — every one conforming with NO correction term) ·
SL-PHIR 0/0 (1,427) · TEETH-US caught 2/2 · TEETH-SB caught 2/2 ·
TEETH-PR caught 2/2. Separator censuses: **SL-SEP2 = 96 rows (predicted
≥ 8)** — every SEPA junction row separated: δ non-involution, the ξ-law
holds, BOTH bare-θ variants fail; **SL-SEP3 = 27 rows (predicted ≥ 6)**
— the χ-chain correction witnessed at m = 3 likewise. Reconciliation:
SL-INVREC = 221 δ ≠ 1 slot-samples with Σ_m(ρ) = `sigma_twist`(ρ), of
which 218 on the OA-battery geography — the sealed unit's ENTIRE δ ≠ 1
record sits where the two maps coincide, confirming §5's explanation of
its 0-violation-with-undetermined-sign verdict.

[r1, PE1 F2 (bookkeeping; counts kept above as machine-quoted): the
printed family COUNTS include teeth-run leakage — `run_tooth` restores
`VIOL` and pops `ROWS` but never restores `COUNTS`, so the six mutation
runs leak `note()` samples into the family tallies. PE1 measured the
leak exactly (teeth re-run in isolation): SL-VDM +26, SL-DELTA +13,
SL-PHIR +13, SL-GAP +8, SL-INVREC +3; cross-check Σ|supp| over all
1,211 walked rows of the committed JSON = 1,414 (OA 1,060 + SEP 354),
and 1,427 − 1,414 = 13, 2,854 − 2×1,414 = 26, 688 − 2×340 = 8 — exact.
The GENUINE battery figures are SL-VDM 2,828 (both legs, every walked
slot, every m) · SL-DELTA 1,414 · SL-PHIR 1,414 · SL-GAP 680; and
SL-INVREC = 218 EXACTLY — the 3 non-OA samples inside the printed 221
are not battery rows but TEETH-PR mutation artifacts (garbled-print δ
on T2C/T3C under `mut_print`), so the genuine census is 218 = exactly
the OA δ ≠ 1 record, which makes the reconciliation claim STRONGER,
not weaker. No verdict is affected: teeth violations are correctly
diverted; 0-violation families are 0 on the genuine samples a
fortiori; the 340-gap-slot and 96/27 separator censuses come from
`ROWS`, which IS cleaned, and are exact. Runner + artifacts stay
byte-frozen (seal 8064ae3); figures per `SIGMALAW_passPE1_report.md`
Finding 2.]

---

## §7. What is and is not advanced

* **Closed at attempt grade:** the (Σ-LAW box) of OPEN2ATTACK §6 — with
  the boxed statement CORRECTED as in §5 (ξ-map, minus sign). THEOREM
  OPEN-2a-Σ now fires with no Σ-hypothesis: (OPEN-2a)'s forward
  direction at m ≥ 2 (strict form AND recorded form) is PROVED at
  attempt grade, riding OA-L1–L4 + SL-1. The (DEFEAT) system is
  infeasible outright on the shared-below perimeter.
* **Unchanged:** the converse (recorded ξ ≠ 1 ⟹ byte-RED) — UNPROVED at
  every m, PE3/EXT counter-instances stand; W2-OPEN-2's chain-level
  claims (a)/(b) ABOVE a fired twist r₀ (off the shared-below perimeter)
  — untouched, still riding TW-ADM instance evidence; drainage,
  exhaustiveness, and every other Phase-B box.
* **Grades:** this note is attempt grade 0/2 — ~~it has had NO hostile
  pass; SL-1's REMARK step ((SC-q) wrap-invariance) and SL-C1's
  multiplicativity step are the two places a hostile pass should press
  first (both ride the same shared-below byte-share input, and both are
  machine-keyed on every walked row)~~ **[r1] arc: PE1 (report
  `SIGMALAW_passPE1_report.md`, ledger 9b0117d/a00cf97) pressed exactly
  the two self-flagged places and found their ONE root cause — the wrap
  input as displayed was FALSE on the doubly-twisted part of the
  perimeter; the true input is the eigen-coefficient law (EC-q), which
  PE1 derived on-perimeter and r1 transcribed into §3's REMARK and
  SL-C1's proof (no statement changed); every theorem statement
  survived, incl. on the 7-tower regime the sealed battery never
  samples (§5 instrument note); machine leg re-run bit-identical
  ex-timing, exit 0; counter 0/2, PE2 next**. No Lean artifact.

---

## §8. Proposed annex text (orchestrator action; GRTW2 §5.2/OPEN2ATTACK §6 fold)

> **[ANNEX 2026-08-08, orchestrator, Σ-LAW PROVED — the SIGMALAW unit
> (`SIGMALAW_PROOF_2026-08-08.md`, sealed battery `sigmalaw_checks.py`;
> seal commit 8064ae3, verdict commit = the §6R fold).]** The (Σ-LAW box) displayed at
> OPEN2ATTACK §6 is CLOSED at attempt grade, with two corrections to the
> boxed display: the covariance map is the **ξ-formula composite** (the
> §3.4 characters ξ_q = χ_{q−1}^{γ_q}z_{q−1}^{−e_{q−1}A_{q−1}}, χ-chain
> included — NOT the bare interior twist z_{q−1}^{A_{q−1}e_{q−1}}), and
> the sign is fixed: δ_j = ρ_j/Σ_m(ρ_j). Proof: the per-coordinate
> ledger identity Prnt_j(A) = u_j·Σ_m(R_m v(A)) with EXPLICIT
> slot-constant u_j = z_m^{−k_jA_m}ε_m(β_j)U_m(β_j), by double recursion
> (the gap terms cancel per node inside each builder's own evaluator —
> the attained-start τ-normalization is W2-L3's mechanism at every
> level, so gap rows carry NO correction term; and the gauge-ratio
> recursion Λ_q(w) = χ_q^{−w} REDERIVES the §3.4 χ/ξ recursion from the
> evaluator side). Machine: 1,211 walked junction rows (539 towers:
> the full OPEN2ATTACK battery reproduced + 150 constructed separator
> towers), SL-VDM 2,854 / SL-DELTA 1,427 / SL-GAP 688 samples (340 gap
> slots), 0 violations, exit 0, 3 teeth caught 2/2 each; the sign/map
> corrections are witnessed by 96 constructed non-involution separator
> rows at m = 2 and 27 at m = 3 where the ξ-law holds and BOTH boxed
> variants fail — the sealed battery's involution degeneracy is thereby
> explained (its entire δ ≠ 1 record sits where the maps coincide,
> 218/218 slot-samples). Consequence:
> THEOREM OPEN-2a-Σ fires unconditionally on its Σ-leg — at every
> shared-below junction at every m, strict ⟹ byte-equal and recorded
> ξ = 1 ⟹ byte-equal under every selection rule, at attempt grade given
> OA-L1–L4 — so **(OPEN-2a)'s forward direction at m ≥ 2 is PROVED at
> attempt grade** and the simultaneous-defeat system is infeasible on
> the whole shared-below perimeter. The converse's UNPROVED status and
> W2-OPEN-2's above-r₀ chain claims are unchanged.

[r1, PE1 F2 — annex caveat: the annex's 2,854/1,427/688 and 218/218
figures are the machine-printed counts; per §6R's [r1] block the
genuine battery decomposition is 2,828/1,414/680 with SL-INVREC = 218
exactly (the printed 221 carries 3 TEETH-PR artifacts). The annex as
applied to GRTW2 at a9f45ab carries the printed figures; mirroring this
caveat there is an orchestrator action (GRTW2 is ACCEPTED-FROZEN, not
edited by this repair), owed alongside the PE2 fold. Also owed to the
PE2 reader: the annex's "(SC-q) wrap" mechanics now run through the
eigen-coefficient law (EC-q) per §3's [r1] REMARK — the annex text
above is the SEALED wording, kept verbatim as applied.]

---

— Σ-LAW unit, campaign date 2026-08-08; commit 1 (seal) = runner + this
note with §6R PENDING; commit 2 (verdict from committed artifacts) fills
§6R and the annex blanks.

---

## ★ ACCEPTANCE RECORD (orchestrator, 2026-08-08) ★

**THIS NOTE IS ACCEPTED at 2/2** — PE2 (6e57e03, CLEAN on the note
text; independent (EC-q) re-derivation with the 3-clause ladder proved
well-founded; 16 own doubly-twisted towers incl. the k≡3 (mod 4)
contrapositive; order-7 fresh route) and PE3 (165ca12, CLEAN; SL-L2
re-derived line-by-line + machine-keyed BY NAME for the first time;
the all-three-u_j-factors junction constructed; own census walk
1,211 rows leak-free; mutant audit 13/13 caught; fresh route = 𝔽₂₇
chamber with ord-13 invisible twist, 0 violations). Full arc: composed
→ seal 8064ae3 / verdict 59c1ff2 → PE1 (0C+1G+2m, 9b0117d — the GAP
was the wrap display; the verifier DERIVED the true (EC-q) law) → r1
(6b24942, the derivation transcribed) → PE2 CLEAN-on-note → PE3
CLEAN. Three passes, one substantive repair.

**FREEZE-CONVENTION STAMP**: the accepted text is the post-r1 body,
md5 a50d3d5f, byte-frozen since 6b24942; dated appends only hereafter.

**WHAT IS ACCEPTED**: THEOREM SL-1 (the Σ-LAW: Prnt_j(A) =
u_j·Σ_m(R_m v(A)) with closed-form slot constant, every on-line
level-m object at every shared-below junction, every m ≥ 1, via the
(VD-q)+(EC-q)+(SC-q) ladder — Σ_m the ξ-formula composite twist, both
bare-θ variants refuted by construction) + THEOREM OPEN-2a-Σ's firing
(the (OPEN-2a) forward direction at every m ≥ 2, given OA-L1–L4) +
COROLLARIES, at the displayed boxes; the converse's UNPROVED status
unchanged.
