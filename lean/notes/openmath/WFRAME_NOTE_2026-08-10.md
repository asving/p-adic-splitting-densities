# THE w-FRAME NOTE — the cross-frame unit w and the twisted residual ψ^{(w)}, once
## RCT unit T5-w-frame-note (FABLE arm) — 2026-08-10 — grade 0/2, hostile arc follows

**Charge (blueprint T5, as amended by Plan revision R.2 S-4 re-scope).**
One citable home for the cross-frame unit w and the w-twisted realized
residual ψ^{(w)}, in the w-inclusive canonical frame, absorbing the
rider scatter: GENTOW2's (B-law)/B″ statement of w, GENTOW5's ψ^{(w)}
re-scope, the w ≠ 1 measurement records at 7 primes, and the
[GENTOW5-W(i)] fence. This note DEFINES and CONSOLIDATES; it proves no
new mathematics. Every law displayed in §2 is PROVED in the accepted
corpus and carries its source statement's S-0 ledger label (or, for
material with no ledger row, a (commit, line-range) span pin per the
R.1(a) span-pin rule). Per R.2 S-4 rules: "light" is withdrawn — §5
carries the frame-equivalence leg for each transferred fact; the
measured w ≠ 1 instances stay UNCONDITIONAL records; no absorbed
statement gains a w-hypothesis anywhere in this note (§6 audit).
This note also lands the owed "w ≠ 1 as-of note" (blueprint append
#16): §4 is that record's single home.

**Standing conditionality, named up front.** The single-w form is
unconditionally proved at level i = 2 only (the landed GENTOW2 r3
B-law). At i = 1 the SHAPE is proved with the tie u1 = w₁ OPEN
(GENTOW5 S11.3); at i ≥ 3 the form is OPEN behind the named lemma
[GENTOW5-W(i)] (GENTOW5 S11.2). §5 fences both. The T1 gauge-cocycle
frame (unit S-1) is NOT consumed here — S-1 is in flight on its own
RCT arm and unaccepted at this writing; this note is self-contained
on the accepted corpus.

**Sections.** §1 definitions · §2 the basic laws (proved, sourced) ·
§3 the level ladder (what holds at which i) · §4 the measurement
record (enumerative) · §5 open items, fenced · §6 consumption
(three-leg checks per R.1) · §7 machine leg (sealed instrument) ·
§8 as-of ledger.

---

## §1. DEFINITIONS (the w-inclusive canonical frame)

Ambient setting (the accepted towerrat frame, fixed for this note):
K/ℚ_p a p-adic base, a type chain µ₀ < µ₁ < ... < µ_i with key
polynomials Φ₁, ..., Φ_i, stage data (e_j, f_j, u_j), residue letters
z_j ∈ K_j (K_j the level-j residue field), n̂_j(m) the level-j ladder
monomial at dv_j-height m, π_{j+1} the Def 3.12 level-(j+1)
uniformizer (µ_{j+1}(π_{j+1}) = 1/e(µ_j), Lemma 3.13(1)), and
R_{j+1,β}(·) the FGMN canonical-homogeneous-frame residual read at
grade β. All symbols as in GENTOW2_PROOF (@ 33f86204) and
GENTOW5_PROOF (@ b0e5c648); nothing is re-founded here.

**DEF W-1 (the cross-frame unit w — GENTOW2's object, verbatim at
i = 2; GENTOW5's level-i quote).** At level i with next-stage data
(e_{i+1}, f_{i+1}, u_{i+1}):

    w_i := R_{i+1, κ̄_i}(n̂_i(u_{i+1})) ∈ K_i^×,
    κ̄_i := u_{i+1}/e(µ_i)   (the top slot's grade).

At i = 2 this is GENTOW2's w := R_{3,κ̄}(n̂₂(u₃)), κ̄ := u₃/e(µ₂)
(LEMMA GENTOW2-B″'s display, ledger row GENTOW2 #4). w_i is a single
SLOT-INDEPENDENT unit: one value per (tower, level, u_{i+1}), not one
per recipe slot. Unit-hood is Cor 4.4(1) (single-point polygon,
degree < m_{i+1} — inside B′'s proof, ledger row GENTOW2 #3). The
definition builds in NOTHING about w's value: w = 1 is a possible
value of this definition, decided only by measurement or derivation
(§4, §5).

**DEF W-2 (the w-twisted residual ψ^{(w)}).** For ψ ∈ K_i[y] monic of
degree f with ψ(0) ≠ 0, and a unit w ∈ K_i^×:

    ψ^{(w)} := w^{f} · ψ(y/w).

Equivalently, coefficientwise: if ψ = y^f − Σ_{t<f} a_t y^t then
ψ^{(w)} = y^f − Σ_{t<f} a_t w^{f−t} y^t. The map ψ ↦ ψ^{(w)} is the
grade-covariant substitution y ↦ wy followed by the monic
renormalization; it preserves monicity, degree, irreducibility,
factor degrees, and the nonzero constant term (ψ^{(w)}(0) =
w^f ψ(0) ≠ 0) — LAW W-A below. GENTOW5's display
ψ_{i+1}^{(w_i)} := w_i^{f_{i+1}} ψ_{i+1}(y/w_i) is this definition
at ψ = ψ_{i+1}, w = w_i (span pin: GENTOW5_PROOF @ b0e5c648,
L780–796).

**DEF W-3 (the n̂-cocycle ϑ — the slot-varying twin, for contrast).**
For slot t < f_{i+1} (level-i recipe geometry):

    ϑ_i(t) := res((n̂_i(u_{i+1}(f_{i+1}−t)) / n̂_i(u_{i+1})^{f_{i+1}−t})(x₀)) ∈ K_i^×,

GENTOW2's ϑ(t) at i = 2 (inside ledger row GENTOW2 #2's display).
ϑ_i is grade-determined, x₀-free, LETTER-VALUED (a z-letter monomial
by the γ-calculus, §2 LAW W-E), and ϑ_i(f_{i+1}−1) = 1. The
division of labor this note fixes as vocabulary: ϑ is the
SLOT-VARYING letter cocycle (measurable from verdict-level data);
w is the SINGLE slot-independent cross-frame unit (verdict-blind,
measurable only in the canonical frame — §4).

**DEF W-4 (the w-inclusive canonical frame — the reading
convention).** A statement is "in the w-inclusive canonical frame"
when its residual displays are read at the FGMN canonical
homogeneous frame WITHOUT quotienting by the unit w_i — i.e. realized
residuals are displayed as ψ^{(w_i)}, never silently identified with
ψ. The opposite convention ("on the nose", u ≡ 1, the old B-2) is
REFUTED at letter-live grades (PE4, machine; §4 row R-5). Every law
in §2 is stated in this frame.

---

## §2. THE BASIC LAWS (each PROVED in the accepted corpus; source labeled)

Every law below is a QUOTE-WITH-RECAP of an accepted statement: the
proof lives in the source note; the recap shows only the one-line
algebra a reader needs to use the law. Source labels are S-0 ledger
rows (note, label, md5-8) or R.1(a) span pins. Nothing here extends
any source statement's quantifier.

**LAW W-A (admissibility transport).** For ψ ∈ K_i[y] monic
irreducible of degree f with ψ(0) ≠ 0 and any unit w ∈ K_i^×, the
twist ψ^{(w)} = w^f ψ(y/w) is monic irreducible of degree f with
ψ^{(w)}(0) = w^f ψ(0) ≠ 0; more generally y ↦ wy is a K_i-algebra
automorphism of K_i[y] (composed with the monic renormalization), so
ψ ↦ ψ^{(w)} preserves the entire irreducible-factor pattern (factor
degrees and multiplicities). Hence ψ^{(w)} is
GENTOW2-A-ADMISSIBLE at each value of w.
*Source:* the parenthetical proof inside LEMMA GENTOW2-B [r3
RESTATED] (S-0 row GENTOW2 #2, md5-8 `8a00bf44`, L303–340 @
33f86204: "the substitution y ↦ wy preserves monicity after the
renormalization displayed, irreducibility, degree, and the nonzero
constant"); quoted level-generally by GENTOW5-B(a) with the PE5
verification sentence "ψ₃^{(w)} is verifiably admissible for every
w in K₂^×" (span pin: GENTOW5_PROOF @ b0e5c648 L780–796;
GENTOW2_passPE5_report @ 75923bc).

**LAW W-B (the cocycle factorization — the u ↔ ϑ,w adjudication,
i = 2).** In GENTOW2-B's recipe geometry (slots t < f₃, slot grades
β_t = u₃(f₃−t)/e(µ₂)), B′'s per-grade unit family factors as

    (6)   u(β_t) = ϑ(t) · w^{f₃−t},     w := R_{3,κ̄}(n̂₂(u₃)),

with ϑ = DEF W-3's cocycle and w DEF W-1's single slot-independent
unit. *Source:* LEMMA GENTOW2-B″ (S-0 row GENTOW2 #4, md5-8
`d4c8b885`, L729–738 @ 33f86204); the unit family u(β) itself is
LEMMA GENTOW2-B′ (row #3, `bae471b0`, L518–538). Proof: B″'s
(i)–(iv) (Cor 4.7(2) peeling, Def 1.8 expansion minimum, the j ≥ 1
y-degree kill, the j = 0 digit-1 read) — GENTOW2 S5.2, re-walked
clean at PE5/PE6.

**LAW W-C (the B-law and the ψ^{(w)} realization, i = 2).** The
recipe key Φ₃ = Φ₂^{e₃f₃} − Σ_{t<f₃} k̂_t Φ₂^{e₃t} with digit string
(c_t) realizes

    R_ν(Φ₃) = y^{f₃} − Σ_{t<f₃} ϑ(t) w^{f₃−t} c_t y^t,

and the MULTIPLICATIVE-CONVENTION prescription c_t := ϑ(t)^{−1}a_t
against a target ψ₃ = y^{f₃} − Σ a_t y^t (monic irreducible,
ψ₃(0) ≠ 0) realizes R_ν(Φ₃) = w^{f₃}ψ₃(y/w) = ψ₃^{(w)} — DEF W-2's
twist at DEF W-1's w. The unadjusted per-height prescription
(c_t = a_t) realizes ψ₃ itself iff u(β_t) = 1 at each used slot
(REFUTED letter-live; §4 row R-5). *Source:* LEMMA GENTOW2-B [r3
RESTATED] (row GENTOW2 #2, `8a00bf44`); one-line algebra:
u(β_t)c_t = ϑ(t)w^{f₃−t}·ϑ(t)^{−1}a_t = a_t w^{f₃−t}, and
y^{f₃} − Σ a_t w^{f₃−t} y^t = w^{f₃}ψ₃(y/w).

**LAW W-D (consumer invisibility — w never reaches a verdict).**
THEOREM GENTOW2-A consumes only its hypothesis (ii) with an
admissible residual — never a digit string, never the untwisted ψ —
and by LAW W-A the twist preserves factor patterns; so every
GENTOW2-A output clause (σ, exact values, degrees, prime-split
verdicts, repo-side residue classes) is w-BLIND: unchanged under
w ↦ (any unit). Consequently verdict-level machine data can measure
ϑ but structurally cannot measure w (why §4's record required the
canonical frame). *Source:* THEOREM GENTOW2-A (row GENTOW2 #1,
`5d1ae5f0`, L187–219) + the B″ consequence sentence ("with P's
irreducible-factor pattern for every value of w", inside row #4) +
GENTOW2's S4 consumption note as quoted by PE6 §C; GENTOW5's
per-consumer walk (span pin L816–819 @ b0e5c648: "σ, values,
degrees, irreducibility, and the REPO-side residue classes are
w-blind — checked per consumer in the [GT5-r2] walk").

**LAW W-E (letter values and forced trivialities of ϑ).** At i = 2:
ϑ(t) is x₀-free and letter-valued — a z₁^j z₂^k monomial with
grade-determined exponents (the γ-calculus: the defining ratio is a
value-0 Laurent monomial in π, x, Φ′, and value-0 monomials form
exactly ⟨γ₁, γ₂⟩ with res(γ₁(x₀)) = z₁, res(γ₂(x₀)) = z₂); hence
ϑ(t) = 1 at any slot whose letter monomial is trivial (in
particular wherever z₁ = z₂ = 1, the letter-dead geography); and
ϑ(f₃−1) = 1 always (the defining ratio is trivial at the top slot).
At f₃ = 1 the single slot is the top slot, so no cocycle is live.
*Source:* the γ-calculus paragraph of GENTOW2 S5.2 (proof preamble
of row GENTOW2 #4; span pin GENTOW2_PROOF @ 33f86204 L715–727).
NOTE the asymmetry, which is this note's central caution: LAW W-E
is proved for ϑ. The analogous letter-valuedness of the w-AVATAR
(the measured object of §4) rides an interpretation leg with one
DESCRIPTIVE-status row (§4 preamble); no law of this section
computes w.

---

## §3. THE LEVEL LADDER (what holds at which i — the net position
## after GENTOW5 S11.2 + S11.3)

* **i = 2 — UNCONDITIONAL.** LAW W-B/W-C verbatim (the landed
  GENTOW2 r3 B-law; ledger rows GENTOW2 #2/#3/#4). This is the ONE
  level at which the single-w form is proved.
* **i = 1 — SHAPE PROVED, TIE OPEN.** The proved form (GENTOW5
  S11.3's dated re-scope, span pin @ b0e5c648 L1955–1957):

      R_{ν₁}(Φ₂) = ψ₂^{(u1)},  u1 ∈ K₁^× a FIXED
      z₁-letter-power unit (the letter formula's species);
      the tie u1 = w₁ = R_{2,κ̄₁}(n̂₁(u₂)) is OPEN.

  The species comes from GENTOW2-A(c)'s letter-formula content
  (z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}); the derivation never evaluates the
  residue R_{2,κ̄₁}(n̂₁(u₂)), so it cannot identify u1 with the
  pinned w₁ (different units give different residual polynomials).
* **i ≥ 3 — OPEN BEHIND [GENTOW5-W(i)].** Proved by GENTOW5's own
  sections: per-grade FIXEDNESS of u_i(β) (the τ_i-cocycle letter
  computation), x₀-freeness and g-freeness, and the reciprocity
  ϑ_i(t) = ϑ̄_{i,f_{i+1}−t}^{−1} (S2.1's monomial quotient, inverse
  read). NOT proved: the single-w geometric form

      [GENTOW5-W(i)]   u_i(β_t) = ϑ_i(t) · w_i^{f_{i+1}−t},
                       w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1})),

  which per-grade fixedness underdetermines (fixed families exist
  that fit no single w) — GENTOW2-B″'s computation run at level i,
  reproduced nowhere. §5 fences it with its exact conditional
  scope. *Source:* GENTOW5 S11.2 (span pin @ b0e5c648 L1888–1933).

---

## §4. THE MEASUREMENT RECORD (enumerative; no universal claims)

**What "measured" means here.** The measured object is the w-AVATAR
res((n̂₂(u₃)/π₃^{u₃})(ξ)) at a specific prime of a committed frame
(π₃ the Def 3.12 uniformizer). The interpretation leg avatar =
R_{3,κ̄}(n̂₂(u₃)) = w rides Thm 4.2/eq (16) (GENTOW2 S6.1 row 23,
DESCRIPTIVE status) + Lemma 3.13(1) (row 20, consumed) +
GENTOW2-A(d)'s exact values through a C-m1-style bridge — disclosed
in the measuring runner's docstring and carried here unchanged.
Instruments: gentow2_pe6_fresh.py (seal ade1727; run-1 68/1 RED kept
as committed, the miss a disclosed verifier-instrument literal;
run-2 GREEN 68/0 @ dfbc938) and gentow5_pe3_fresh.py (run-1 RED 48/2
kept, one gp-stdin print defect; run-2 GREEN 48/0). Towers: LP1
(Φ′ = x²−2; e₁ = 2, f₁ = 2, z₁ live with z₁²+z₁+1 = 0; e₂ = 2,
f₂ = 1, z₂ = 1; u₂ = 9, V₂ = 4, e(µ₂) = 4) and GB (Φ′ = x²−2;
e₁ = 2, f₁ = 1, z₁ = 1; e₂ = 2, f₂ = 2, z₂ live; u₂ = 5, V₂ = 2,
e(µ₂) = 4).

**The rows (7 measured primes across 5 keys on 2 towers):**

| row | frame (tower; e₃,f₃,u₃) | primes | w-avatar | companion facts |
|---|---|---|---|---|
| R-1 | LD1 (LP1; 1,2,19) | 1 | z₁ ≠ 1 | ϑ(0) = z₁; u(β₀) measured = 1 = ϑ(0)·w² — B″(6) closed with 3 independent measurements |
| R-2 | LD3 (LP1; 2,1,37) | 1 | z₁² ≠ 1 | vs R-1: same tower, different u₃ ⟹ different w |
| R-3 | GA1 (GB; 1,2,21) | 2 | z₂² ≠ 1 (each) | ϑ(0) = z₂²; u(β₀) measured = 1 = ϑ(0)·w² |
| R-4 | GA3 (GB; 2,2,41) | 2 | z₂ ≠ 1 (each) | u(β₀) measured = z₂ — the first letter-valued canonical unit on record; vs R-3: u₃-discrimination fired |
| R-6 | GA3\* (GB; 2,2,41; NEW key, target ψ₃ = y²−y−z₂) | 1 | z₂ ≠ 1 | the 7th prime, first carrier-(8,4) geometry; PSIW: ψ₃^{(w)}(Y) = 0 ON THE NOSE at measured w ≠ 1 (GENTOW5-B(a) as re-scoped, verified); NOSE tooth fired: ψ₃(Y) ≠ 0; naive twin (untwisted prescription = the committed GA3 key) splits [16,16] |

Sources: R-1..R-4 = GENTOW2_passPE6_report §E (@ deba21bd,
L245–295); R-6 = GENTOW5_passPE3_report §S4 LEG W (@ 39c36aa2,
L270–292).

**R-5 (the refutation record that forced this frame — PE4,
RED-by-design, kept).** At LD2 (LP1; e₃ = 1, f₃ = 2, u₃ = 19; digit
string (z₁, z₁²)), the PER-HEIGHT prescription for the split target
ψ₃ = y²+z₁y+z₁² = (y+1)(y+z₁²) realized a SINGLE (4,4) prime with
realized residual y²+z₁y+1: sealed fresh route RED 62/9, each of
the 9 misses a B-2-on-the-nose prediction (gentow2_pe4_fresh.py,
seal 23def87, output kept as-is); decode probe GREEN 14/0
(gentow2_pe4_decode.py). This is the machine event that killed the
old B-2 and created DEF W-4's frame.

**Enumerated consequences (this record, no further).** (i) w ≡ 1 is
dead at each of the 7 measured primes. (ii) "w constant per tower"
is dead twice over (R-1 vs R-2; R-3 vs R-4). (iii) The measured
avatars equal the S5.2 γ-calculus hand values at each of the 4
frames (exponent-lattice splits, re-verified by §7's instrument).
(iv) B″(6) is closed w-inclusively at the 3 slots where all three
residues were independently measured (R-1, R-3, R-4). (v) The
record does NOT decide w at unmeasured frames, unmeasured u₃, or
levels i ≠ 2 (GENTOW5's dated-note wording, adopted verbatim).

**Frame-equivalence legs (R.2 S-4: old-frame ⟺ w-inclusive reading
for each transferred fact).**
* *The w ≠ 1 rows (R-1..R-4, R-6).* Old frame = the pass reports'
  sentences ("w-avatar = z₁/z₁²/z₂²/z₂ ... ≠ 1"). w-inclusive frame
  = the same sentences: DEF W-1 is byte-identical to the object the
  passes measured (the same defining display R_{3,κ̄}(n̂₂(u₃))), so
  the transfer is the identity; the one frame-sensitive step
  (avatar ↔ w, row-23 descriptive leg) is INSIDE the source record
  and is carried with its disclosed status, not upgraded here.
* *PSIW at GA3\* (R-6).* GENTOW5-B(a) as re-scoped was BORN in the
  w-inclusive frame (its display is ψ_{i+1}^{(w_i)}); old-frame and
  w-inclusive readings coincide by inspection of the display.
* *The PE4 refutation (R-5).* Old frame: "B-2 on-the-nose is FALSE
  at letter-live grades." w-inclusive frame: LAW W-C's iff — the
  per-height prescription realizes ψ₃ iff u(β_t) = 1 at each used
  slot — makes R-5 the instance u(β₀) = ϑ(0)·w² = z₁·z₁² read
  against the LD2 digits; equivalence via LAW W-B. (The two
  readings agree that the realized residual is y²+z₁y+1; checked
  in §7.)

**The F19 rule (binding on every consumer of this note).** The
measured w ≠ 1 instances are UNCONDITIONAL records. A named
w-hypothesis (e.g. "assume w_i = 1") may condition only statements
whose accepted forms already depend on the dichotomy; and no
consumption check may show an absorbed statement GAINING a
w-hypothesis. In particular nothing in §5's open items
conditionalizes any row of this section.

---

## §5. OPEN ITEMS, FENCED

**OPEN-1 — [GENTOW5-W(i)], the single-w form at i ≥ 3.** Statement
and status exactly as GENTOW5 S11.2 (span pin @ b0e5c648
L1888–1933; displayed in §3). Conditional on it at i ≥ 3: clause
(a)'s realized-residual display ψ_{i+1}^{(w_i)}, the (a)-certificate
legs that consume that form (KP membership via ψ^{(w)}
admissibility, prime, non-equivalence), and (b)'s FGMN-side residual
displays at the same indices. NOT conditional (w-blind): σ, exact
values, degrees, irreducibility transport, repo-side residue
classes and P-membership, (c)'s budgets, (d), (e). The committed
depth-4 witness is w-trivial (K_i = F₂ there), so the machine record
does not discriminate this fence.

**OPEN-2 — the u1 = w₁ tie at i = 1.** The proved i = 1 shape is
ψ₂^{(u1)} with u1 a fixed z₁-letter-power unit (species from the
letter formula); the tie u1 = w₁ = R_{2,κ̄₁}(n̂₁(u₂)) is OPEN
(GENTOW5 S11.3, span pin @ b0e5c648 L1933–1964). The fold's grep
audit found zero consumers needing the tie; it stays a
statement-level open item, not a load-bearing gap.

**OPEN-3 — a derived w-law (closed form, and avatar = w at theorem
strength).** No closed-form letter derivation of w as a function of
(tower, level, u_{i+1}) is claimed anywhere in the accepted corpus;
the 7-prime record measures w at its frames and no further. The
exact missing leg for elevating §4's hand-value agreement to a
THEOREM about w: the interpretation identity avatar =
R_{3,κ̄}(n̂₂(u₃)) rides GENTOW2 S6.1 row 23 at DESCRIPTIVE status —
row 23's two-leg elevation obligation (stated in GENTOW2's rider) is
the gate. Until then, "w's avatar is a letter monomial" is a
measured pattern at 4 frames, not a law; §2 LAW W-E deliberately
covers ϑ only.

**OPEN-4 — w = 1 as a question, correctly housed.** On the measured
record the open w_i = 1 case is NOT the generic one (GENTOW5's dated
note): at the 7 measured primes w ≠ 1. The question "is w = 1
somewhere / at which geographies" remains open exactly where OPEN-3
is open; per the F19 rule it conditionalizes nothing in §4, and per
DEF W-4 no statement of this note reads ψ^{(w)} as ψ pending it.

---

## §6. CONSUMPTION — three-leg checks per R.1

**The absorbed-statement census (10 items).** Rowed (S-0 ledger,
note GENTOW2_PROOF @ 33f86204): A-1 THEOREM GENTOW2-A (row #1,
`5d1ae5f0`, L187–219); A-2 LEMMA GENTOW2-B [r3 RESTATED] (row #2,
`8a00bf44`, L303–340); A-3 LEMMA GENTOW2-B′ (row #3, `bae471b0`,
L518–538); A-4 LEMMA GENTOW2-B″ (row #4, `d4c8b885`, L729–738).
Span-pinned (no ledger row; R.1(a) span-pin rule, byte-frozen
sources): A-5 THEOREM GENTOW5-B(a) as re-scoped, incl. the w_i
display and the w-blind consumer walk (GENTOW5_PROOF @ b0e5c648,
L780–819); A-6 the [GENTOW5-W(i)] fence (same file, S11.2,
L1888–1932); A-7 the (a)@i=1 re-scope with the open u1 = w₁ tie
(S11.3, L1933–1964); A-8 the six-prime w-measurement record
(GENTOW2_passPE6_report @ deba21bd, §E, L245–295); A-9 the GA3\*
seventh-prime + PSIW record (GENTOW5_passPE3_report @ 39c36aa2, §S4
LEG W, L270–292); A-10 the PE4 refutation record as folded into
GENTOW2's honesty box (GENTOW2_PROOF @ 33f86204, B-2 clause,
L384–448). Scope-fixing prose pinned with them: GENTOW2's S5.2
γ-calculus preamble (L715–727), consumed by LAW W-E.

**Leg (a) — STATEMENT.** Each rowed statement is consumed at its
ledger md5 (the four md5-8 values above; `statement_ledger.py
--check` green at this note's final commit — §7). Closed as
displayed: this note prefixes NO binder, hypothesis, or
fixed-witness clause to any absorbed statement — §2's laws quote
the source displays at source generality, and where this note
narrows (LAW W-B/W-C carry "i = 2" in their names) the narrowing is
the SOURCE's own scope, not a new hypothesis. Span-pinned items are
consumed at (commit, line-range) with their quoted sentences
appearing in §2–§5 verbatim or with declared ASCII↔Unicode letter
transliteration only.

**Leg (b) — PROVENANCE.** This note constructs no new lemma and no
new instance: every §2 law is a quote-with-recap whose proof inputs
are the SOURCE note's own enumerated inputs (GENTOW2 S5/S5.1/S5.2's
FGMN quote stack + GENHN-2′ for A-2/A-3/A-4; GENTOW2-A's own stack
for A-1; GENTOW5's [Q1]–[Q10] stack for A-5). No absorbed statement
appears as a proof input to any other absorbed statement THROUGH
THIS NOTE (the recap of LAW W-C's algebra uses only A-2's own
display; §4's rows cite runner artifacts, not §2's laws; §7's
instrument re-derives from frame data, citing no law as input).
Grep-auditable: the note's citation list is exactly
{GENTOW2 #1–#4, the six span pins, the sealed runner artifacts};
no self-citation cycles are constructible from a one-page census.

**Leg (c) — DEFINITION AUDIT (each new definition against the
frozen notion, at source quantifier generality).**
* DEF W-1 vs GENTOW2's w and GENTOW5's w_i: the defining expression
  R_{i+1,κ̄_i}(n̂_i(u_{i+1})) is symbol-identical to both sources
  (GENTOW2 at i = 2; GENTOW5's level-i display). NOTHING is built
  in: not w ≠ 1 (§4 is record, not definition), not
  letter-valuedness (OPEN-3), not any frame restriction. Defining
  w_i at general i commits to no law at general i — §3 keeps the
  law's level ladder.
* DEF W-2 vs GENTOW2's ψ₃^{(w)} and GENTOW5's ψ_{i+1}^{(w_i)}: same
  expression; the coefficientwise form is a one-line expansion
  displayed in §1. Admissibility (irreducibility etc.) is LAW W-A's
  CONCLUSION, not a definitional restriction — ψ^{(w)} is defined
  for every monic ψ with ψ(0) ≠ 0, matching the sources' usage
  sites.
* DEF W-3 vs GENTOW2's ϑ(t): same expression, generalized in INDEX
  NOTATION only (ϑ_i, matching GENTOW5's theta_i which PE6 §C
  checked symbol-by-symbol against GENTOW2's). Letter-valuedness is
  LAW W-E's conclusion at i = 2, not built in.
* DEF W-4 is a reading CONVENTION (no mathematical content): it
  re-binds no absorbed statement in a new ambient frame — §2's laws
  are quoted with their own frames, and DEF W-4 only names the
  frame they already use.

**The F19 audit (no absorbed statement gains a w-hypothesis).**
Checked item-by-item over A-1..A-10: each is consumed at its source
conditionality; no display in this note attaches "assume w = 1",
"assume w ≠ 1", or any w-quantifier to an absorbed statement. The
only w-conditionality anywhere is the SOURCE-carried fence scope of
A-6/A-7 (reproduced in §5 with its own source pins), which the
sources themselves declare.

---

## §7. MACHINE LEG (sealed instrument, two-commit seal)

(instrument seal + verdict, commits 5–6)

---

## §8. AS-OF LEDGER (what this note dates, what it lands, what it
## leaves untouched)

* **Landed here:** the owed "w ≠ 1 as-of note" (blueprint append
  #16) — §4 is its single home; future w measurements append to §4
  as dated rows rather than new riders.
* **Dated (sources stay byte-frozen; this section is the standing
  cross-reference):** GENTOW2's honesty-box sentence "not computed
  anywhere in the corpus" — TRUE AS DATED (pre-PE6), dated by the
  PE6 §E measurement (A-8); GENTOW5's body sentences "w_i = 1 IS
  OPEN" / "the uncomputed cross-frame unit" — dated by GENTOW5's own
  [GT5-r3 DATED 2026-08-10] bracket and by A-8/A-9; on the measured
  record the ψ^{(w)} form is the operative reading (GENTOW5's dated
  note, adopted).
* **Left untouched:** every absorbed statement's bytes (the S-0
  tripwire stays green — §7); the [GENTOW5-W(i)] fence and the
  u1 = w₁ tie (live, §5); the row-23 DESCRIPTIVE status and its
  two-leg elevation obligation (GENTOW2 rider; gate for OPEN-3).
* **Grade line:** this note is grade 0/2 (RCT unit T5, FABLE arm);
  the 2-clean hostile arc follows. It consumes ACCEPTED texts only
  (GENTOW2 2/2 @ PE6; GENTOW5 2/2-annotated with its S11 repairs)
  plus committed, sealed pass-record artifacts cited at their
  seals. Nothing in this note upgrades any source's grade or
  status.
