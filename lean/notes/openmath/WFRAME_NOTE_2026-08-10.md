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

(filled in commit 3)

---

## §5. OPEN ITEMS, FENCED

(filled in commit 3)

---

## §6. CONSUMPTION — three-leg checks per R.1

(filled in commit 4)

---

## §7. MACHINE LEG (sealed instrument, two-commit seal)

(instrument seal + verdict, commits 5–6)

---

## §8. AS-OF LEDGER

(filled in commit 4)
