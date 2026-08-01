/-!
# (HEN-LIFT) faithfulness brief — unit D12R-U1 (HDISCHARGE_H3 §2.2)

*Prover D12R-U1, HDISCHARGE_H3 division. Machine clock 2026-08-01.*
*Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §2.2 (read-only). Consumer: the
ROOT §4 item-5 row ("LITERATURE-CANDIDATE" drop) and the D-12r retirement
adjudication (D12R-U4) — which may not fire until all three parts below are
pinned. This file is a doc unit: the Lean tail is a content-free marker so the
repo gate (`lake env lean` on this file) can run; nothing mathematical is
machine-checked here.*

**Provenance discipline for every "CONFIRMED" below.** The blueprint owes
confirmations "against physical/PDF copies". What this brief actually checked:
the **publisher's own ebook text**, read verbatim through Google Books
search-inside (Neukirch = volume id `hS3qCAAAQBAJ`, Springer Grundlehren 322,
English, 1999; Serre = volume id `3LAJCAAAQBAJ`, Local Fields, GTM 67, English
translation). Snippets are OCR of the printed pages; page numbers are the
printed pagination (Google `page_number` fields; Neukirch's own index snippet
independently gives "Hensel's lemma 129"). OCR glyph repairs are marked
`[..]`; truncation seams are marked `<seam>` and bridged only by independently
corroborated text (Kedlaya, Chan — cited per seam). This is PDF-copy-grade in
substance; whether it meets the row's "physical/PDF" bar is for the VC pass
(D12R-U4) to adjudicate, not this brief.

## 0. The declared statement package (MOVES §T.2)

Verbatim from `lean/notes/MOVES_2026-07-24.md` lines 7254–7261:

> (HEN-LIFT) Let f ∈ ℤ_p[x] be monic, f̄ = ψ·h̄ in F_p[x] with ψ irreducible
> and gcd(ψ, h̄) = 1 (ψ a SIMPLE factor). Then f = g·h in ℤ_p[x], g, h
> monic, ḡ = ψ, and this lift is UNIQUE; g is irreducible (ḡ is) and
> generates an unramified extension: (E, F) = (1, deg ψ). [The
> coprime-factor Hensel lemma over a complete local ring — standard;
> exact source pinned at acceptance, attribution flagged for lookup per
> the cite policy. Valid at ALL primes incl. wild — coprimality, not
> tameness, is the hypothesis.] This discharges (τ-hen)'s read-off.

Per blueprint §2.2 this is a THREE-part package: **(HL-a)** coprime-factor
lifting existence, **(HL-b)** uniqueness of the lift pair, **(HL-c)** the
read-off (g irreducible, unramified, (E, F) = (1, deg ψ)). Each part is
pinned separately below; (HL-c) does NOT follow from (HL-a) alone.

## 1. (HL-a) existence — CONFIRMED

**Pin: Neukirch, *Algebraic Number Theory* (Grundlehren 322, Springer 1999),
Chapter II §4, statement (4.6) "Hensel's Lemma", page 129.**

Running frame of II §4: K a field complete with respect to a nonarchimedean
valuation, o its valuation ring, 𝔭 the maximal ideal, κ = o/𝔭 the residue
field; f ∈ o[x] is *primitive* iff f ≢ 0 mod 𝔭, i.e. |f| = 1. Ebook text,
OCR-repaired (o, 𝔭, overbars restored; raw OCR shows `p` for 𝔭 and drops
diacritics):

> **(4.6) Hensel's Lemma.** If a primitive polynomial f(x) ∈ o[x] admits
> modulo 𝔭 a factorization f(x) ≡ ḡ(x)·h̄(x) mod 𝔭 into relatively prime
> polynomials ḡ, h̄ ∈ κ[x], then f(x) admits a factorization
> f(x) = g(x)·h(x) `<seam>` such that deg(g) = deg(ḡ) and g(x) ≡ ḡ(x) mod 𝔭
> and h(x) ≡ h̄(x) mod 𝔭.

`<seam>` = "into polynomials g, h ∈ o[x]": the two snippets overlap up to this
phrase; bridged by Chan (Princeton ANT notes, Prop 8.4, transcribing this
statement: "f has a factorization f(X) = g(X)h(X) where g, h ∈ R[X]") and by
Kedlaya (Math 204B notes on Hensel's lemma, "following Neukirch II.4.6").
The proof opening was also read (`"Proof: Let d = deg(f), m = deg(ḡ), hence
d − m ≥ deg(h̄). Let g₀, h₀ ∈ o[x] be polynomials with ḡ₀ = ḡ, h̄₀ = h̄ ..."`)
— the Bézout successive-approximation mechanism, as the blueprint expects.

Instance consumed by (HEN-LIFT): K = ℚ_p, o = ℤ_p, 𝔭 = pℤ_p, κ = F_p.
Degrees preserved; hypothesis is coprimality of the reduced factors — exactly
the (HL-a) shape. **Number, page, and statement text confirmed.**

### The monic-normalization step (displayed — the blueprint's named mismatch risk)

(4.6) speaks of primitive f and does not assert monic lifts; (HEN-LIFT)
consumes monic f with MONIC g, h. The standard leading-unit corollary,
displayed:

Let f ∈ ℤ_p[x] be monic of degree d, f̄ = ψ·h̄ with ψ, h̄ coprime and (as in
(HEN-LIFT)'s use) ψ monic of degree m, h̄ monic of degree d − m. Monic ⇒
|f| = 1 ⇒ primitive, so (4.6) applies: f = g·h, deg g = deg ψ = m,
ḡ = ψ, h̄-clause as stated. Since deg g = m and deg h ≤ d − m while
deg(g·h) = d, we get deg h = d − m exactly and lead(g)·lead(h) = 1, so
a := lead(g) ∈ ℤ_p^×. Reducing the degree-m coefficient: ā = lead(ψ) = 1.
Set g′ := a⁻¹·g and h′ := a·h. Then g′, h′ are monic, f = g′·h′, and
ḡ′ = ā⁻¹·ψ = ψ, h̄′ = ā·h̄ = h̄. ∎

## 2. (HL-b) uniqueness — printed clause ABSENT; companion lemma carried here

**Disposition: Neukirch's printed (4.6) asserts existence only.** Confirmed
from the ebook text: the statement runs directly from "... h(x) ≡ h̄(x)
mod 𝔭." into "Proof: ..." with no uniqueness clause. (Kedlaya's Theorem 1
does print "there is a unique lift", but that is his packaging; and bare
uniqueness WITHOUT a monic normalization is false — over ℤ_p take f = x,
ḡ = x, h̄ = 1: both (x, 1) and ((1+p)·x, (1+p)⁻¹) are lifts satisfying all
of (4.6)'s conclusions. The monic normalization is load-bearing.)

Per the blueprint, the uniqueness consumed by VP determinism is therefore a
**companion lemma displayed by this brief** — never a silent strengthening of
the cite:

**Companion Lemma (monic uniqueness).** Let f ∈ ℤ_p[x] be monic and suppose
f = g₁·h₁ = g₂·h₂ with all gᵢ, hᵢ ∈ ℤ_p[x] monic, ḡ₁ = ḡ₂ = ψ,
h̄₁ = h̄₂ = h̄, and gcd(ψ, h̄) = 1 in F_p[x]. Then g₁ = g₂ and h₁ = h₂.

*Proof (displayed).* By induction on k ≥ 1 we show g₁ ≡ g₂ and h₁ ≡ h₂
mod p^k. Base k = 1 is the hypothesis. Step: write g₁ = g₂ + p^k·u,
h₁ = h₂ + p^k·v with u, v ∈ ℤ_p[x]; monicity and equal degrees give
deg u < deg ψ and deg v < deg h̄. Expanding g₁·h₁ = g₂·h₂:
p^k·(u·h₂ + v·g₂) + p^{2k}·u·v = 0, hence u·h₂ + v·g₂ ≡ 0 mod p^k, and in
particular mod p: ū·h̄ + v̄·ψ = 0 in F_p[x]. Thus ψ divides ū·h̄; by
coprimality ψ | ū; since deg ū < deg ψ this forces ū = 0, and then
v̄·ψ = 0 forces v̄ = 0. So g₁ ≡ g₂ and h₁ ≡ h₂ mod p^{k+1}. As
⋂ₖ p^k·ℤ_p = 0, coefficientwise equality follows. ∎

(The induction is the blueprint's specified "two monic coprime-reduction
factorizations agreeing mod p agree mod p^k" argument; completeness of ℤ_p
enters only through the separatedness of the p-adic filtration.)

## 3. (HL-c) read-off — CONFIRMED (primary pin: Serre; Neukirch frame pinned as alternate)

**Primary pin: Serre, *Local Fields* (GTM 67, Springer 1979; translation of
*Corps Locaux*), Chapter I §6 "Example: Simple Extensions" (§6 begins p. 17),
Proposition 15, page 18.** Ebook text:

Setup (p. 17, verbatim modulo OCR): "let A be a local ring with residue field
k. Let n be a positive integer, and let f [be a] monic polynomial of degree
n. Let B_f be the quotient ring of A[X] by the principal ideal (f) generated
by f. It is an A-algebra that is free and of finite type over A, with
{1, X, ..., X^{n−1}} as basis."

> **Proposition 15.** If A is a discrete valuation ring, and if f̄ is
> irreducible, then B_f is a discrete valuation ring with maximal ideal
> m·B_f, and residue field k[X]/(f̄).

Immediately following on p. 18 the text notes the unramified reading (OCR
fragment "... is unramified. Obvious.") and continues "Proposition 15 admits
the following converse: **Proposition 16.** Let A be a discrete valuation
ring, K its field of fractions, and let L be an extension of K of finite
degree n. Let B be the integral closure of A in L. Suppose that B is a
discrete [valuation ring] ..." — confirming the §6 context. The exact printed
wording of the intermediate unramified remark sits behind an OCR seam; the
derivation below therefore consumes ONLY Proposition 15's displayed
conclusions plus the standard definitions.

**Displayed derivation of (HL-c) at A = ℤ_p, k = F_p** (this is the SEPARATE
content the blueprint warns must not be presented as following from (HL-a)):
let g ∈ ℤ_p[x] be monic with ḡ = ψ irreducible in F_p[x]. Proposition 15
gives: B := ℤ_p[X]/(g) is a discrete valuation ring with maximal ideal p·B
and residue field F_p[X]/(ψ).

1. *g irreducible over ℚ_p*: B is a domain, so (g) is prime in ℤ_p[X], so g
   is irreducible there; g monic + Gauss transfers irreducibility to
   ℚ_p[X]. (Direct alternative, no Serre needed: a nontrivial monic
   factorization over ℚ_p descends monic to ℤ_p[x] and reduces to a
   nontrivial factorization of ψ — contradiction.)
2. *B is the ring of integers*: B is finite free over ℤ_p and is a DVR
   (hence integrally closed), so B = O_K for K := ℚ_p[X]/(g) = Frac(B).
3. *(E, F) = (1, deg ψ)*: the maximal ideal of O_K is p·O_K, so E = 1; the
   residue field is F_p[X]/(ψ), so F = deg ψ; E·F = deg g checks. The
   residue extension is separable automatically (finite fields), so K|ℚ_p
   is unramified in the standard sense (Neukirch (7.1)). ∎

**Neukirch frame alternates, numbers pinned from the same ebook:** II §4
**(4.7) Corollary** p. 131 ("for every irreducible polynomial f(x) = a₀ +
a₁x + ⋯ + aₙxⁿ ∈ K[x] such that a₀aₙ ≠ 0, one has |f| = max{|a₀|, |aₙ|}
..."); II §4 **(4.8) Theorem** p. 131 ("Let K be complete with respect to the
valuation | |. Then | | may be extended in a unique way to a valuation of any
given algebraic extension L|K. This extension is given by the formula
|α| = |N_{L|K}(α)|^{1/n} ..."); II §7 **(7.1) Definition** (unramified: λ|κ
separable and [L : K] = [λ : κ]) and **(7.2) Proposition**, pp. 152–153.
NOTE for the ROOT row: the blueprint's candidate label "Neukirch II §4 Prop
4.8" is printed as "**(4.8) Theorem**" — and it supplies the valuation-
extension FRAME only, not the one-statement read-off; the single numbered
statement carrying (HL-c) is **Serre LF I §6 Proposition 15**, which is
within the blueprint's declared alternate list ("or Serre LF I §6").

## 4. Translation risks (per §2.2)

* (r-a) **Characteristic-free**: both pins hypothesize coprimality (4.6) or
  irreducibility of the reduction (Prop 15) — never tameness; valid at all
  primes including wild, as (HEN-LIFT) asserts.
* (r-b) **Residue field F_p exactly**: consumed at K = ℚ_p, o = ℤ_p only,
  matching the GMN rider's scope discipline; separability of the residue
  extension in (HL-c) is automatic there.
* (r-c) The O_δ (δ > 1) unramified-base re-reads ride (UB-X)(a), NOT this
  brief.
* (r-d) **Edition risk**: confirmations are against the ENGLISH texts
  (Grundlehren 322, 1999; GTM 67, 1979). The blueprint's "Corps Locaux I §6"
  French numbering was NOT independently checked (the translation preserves
  the continuous proposition numbering, but this is expectation, not a
  check). OCR seams as marked in §§1–3; no conclusion above depends on
  seam-bridged text.

## 5. Confirmation ledger (`docs/GMN_citations.md`-style)

| part | source | numbered statement | printed page | status |
| --- | --- | --- | --- | --- |
| (HL-a) | Neukirch ANT, II §4 | (4.6) Hensel's Lemma | 129 | CONFIRMED (publisher ebook text; index cross-check "Hensel's lemma 129") |
| (HL-b) | — | printed uniqueness clause ABSENT in (4.6); companion lemma displayed in §2 above | 129 (statement→Proof seam read) | DISPOSED (companion-lemma route) |
| (HL-c) | Serre LF, I §6 | Proposition 15 (+ Prop 16 converse context) | 17–18 | CONFIRMED (publisher ebook text) |
| frame | Neukirch ANT | (4.7) Cor, (4.8) Thm, (7.1) Def, (7.2) Prop | 131, 152–153 | numbers CONFIRMED (context alternates only) |

Residuals: physical-copy re-read is a strictly optional upgrade; French
*Corps Locaux* numbering unchecked (r-d). Whether this brief's provenance
channel meets the row's bar, and the ROOT §4 item-5 "LITERATURE-CANDIDATE"
drop itself, are D12R-U4 / VC-pass decisions.

## 6. The optional Lean upgrade's statement (D12R-U2a; transcribed verbatim from blueprint §2.2, compile-probed there; NOT compiled in this file)

```lean
open Polynomial in
theorem henLift_padic (p : ℕ) [hp : Fact p.Prime] (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (ψ h : Polynomial (ZMod p)) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h)
    (hfact : f.map (PadicInt.toZMod) = ψ * h) :
    ∃ g k : Polynomial ℤ_[p], g.Monic ∧ k.Monic ∧ f = g * k ∧
      g.map PadicInt.toZMod = ψ ∧ k.map PadicInt.toZMod = h
```

Per the blueprint's scope correction this formalizes (HL-a) ONLY; U2b
(uniqueness) and U2c (read-off) are separate E-phase statements, and a landed
U2a upgrades nothing but (HL-a). The literature pins above remain the
operative discharge.
-/

namespace LeanUrat.Scaffold.H3HenLiftBrief

/-- Doc-unit marker for D12R-U1. Carries NO mathematical content — the unit's
content is the module docstring above; this declaration exists only so the
file participates in the `lake env lean` gate. -/
theorem docUnit_landed : True := trivial

end LeanUrat.Scaffold.H3HenLiftBrief
