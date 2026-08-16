/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B29
import Uniformity.ChapB.B34
import Uniformity.ChapB.B42a

/-!
# Uniformity.ChapB.B42 — the theorem of the polygon, as a SIGNED LITERATURE IMPORT

**Chapter B, NODE B.42** [theorem] [cite:GN15 Thm 2.3 + FGMN Thm 6.6]
(`blueprint/CHAP-B_leaf_layer.md` §6, amendment A-F.10), ENV-C. One signed declaration —
**an `axiom`, deliberately.**

*The statement (the side dissection, NS-1).* For a monic `f` over a complete DVR `O` whose
reduction is `φ̄^μ` at an order-1 key `φ`, with `φ ∤ f` (transcribed as `dev φ f 0 ≠ 0`), the
`φ`-Newton polygon's sides dissect `f`: there is a finite set `s` of pairwise-distinct coprime
slopes `(u,ℓ)` and monic factors `F p` with `f = ∏_{p ∈ s} F p`, each `F p` pure at its own
slope, with `φ.natDegree ∣ (F p).natDegree`, `dev φ (F p) 0 ≠ 0`, `0 < (F p).natDegree`; `s` is
*exactly* the set of slopes carrying a two-point side of `f`; and at each `p ∈ s` the residual
polynomials of `f` and of `F p` agree up to a unit of `resField φ`.

## ⚠ THIS FILE ADDS AN AXIOM TO THE REPO'S TRUSTED BASE. Read the whole header.

**Any downstream `#print axioms` of a declaration that consumes this node WILL show
`Uniformity.Density.Leaf.exists_slope_factorization` — and it SHOULD. That visibility is the
design**, not a defect to be worked around: the axiom census (`AxChk`-style `#print axioms`
lines throughout this corpus, and the roll-up gates) is exactly how the project's honesty
invariant reports "this result rests on a literature cite". Nothing in this file may be
`@[simp]`-ed, `unfold`ed, or otherwise hidden; no consumer may re-derive it under a different
name to launder the footprint.

## The signature event

**Owner-signed, 2026-08-16** (Asvin), under Part V **gate (b)** — the per-cite literature-import
gate of `blueprint/CONVENTIONS_2026-08-15.md` Part V, the only two owner sign-offs being (a) the
main Lean statement and (b) each literature-cite import. The record is
`docs/PROJECT_STATE.md` **DATED APPEND #66** (2026-08-16): the exact Lean statement below and
its two sources were displayed to the owner in full immediately before the approval, and the
same append amends `leanfinal/README.md`'s charter line to "no axioms beyond Lean core, **plus
owner-signed gate-(b) literature cites**, each with a faithfulness entry". Gate (b)'s queue
mechanics were fixed at PROJECT_STATE **#61**.

**The signed artifact** is the `leanspec` stub `LeanspecB.exists_slope_factorization`
(`leanspec/Leanspec/ChapB.lean`); the declaration below is byte-identical to it modulo namespace
mechanics, and the stub is now retired to the example-diff form against THIS declaration, so any
future drift between the signed interface and this axiom is a hard Lean error on the `leanspec`
build. The same text is displayed in the faithfulness entry (next paragraph).

**Faithfulness entry:** `blueprint/CHAP-I_capstone_conditionality.md`, DATED ADDENDUM
2026-08-16 ("CHAP-B A-F.10 — GATE-(b) CITE QUEUE ADDITION") — the full clause-by-clause mapping
(import ↔ source), the standing-hypothesis analysis, the disclosed caveats, and the
corroboration list. It is the permanent faithfulness record for this axiom; this header is its
in-code pointer, not a replacement.

## The completeness binder — a landing-time STOP-THE-LINE finding, resolved

`[IsAdicComplete (maximalIdeal O) O]` is written **inline in the axiom's own binder list**, not
inherited from a section `variable`. This is deliberate and it is soundness-critical.

*What happened.* The first draft of this file declared the axiom inside a
`section ENVC / variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]` block,
copying B.48's convention. At the Lean 4.31 pin, section-variable auto-inclusion is **usage
based**: an instance-implicit `variable` is included only if elaborating the statement actually
consults it. It did NOT fire here, and the axiom landed **without** the completeness
hypothesis. The `leanspec` stub — same statement text, same section variables — DID pick the
instance up, because `leanspec/Leanspec/ChapB.lean` imports the whole `Uniformity` root while
this node file imports only B.29/B.34/B.42a, and the larger instance set changes which local
instance the elaboration of `IsLocalRing.residue O` in `hres` consults. **So the elaborated type
of this statement depends on the file's import set.** Bisected at landing:
`f.map (residue O) = (φ.map (residue O)) ^ μ` is the trigger clause.

*Why it is fatal, not cosmetic.* Without completeness the statement is **FALSE**, so the axiom
would have made the whole corpus inconsistent. Witness (repo-side derivation, exhibited at
landing): `O = ℤ₍₅₎` (localization of `ℤ` at `(5)`) — a DVR, not adic-complete, finite residue
field `𝔽₅`; `π = 5`; `φ = X` (an `IsKey`); `f = X² + 5X + 250`, monic, `f̄ = X̄²` so `μ = 2`,
and `dev X f 0 = C 250 ≠ 0`. Heights `(3, 1, 0)` at abscissae `(0, 1, 2)`, so the polygon has
two sides: `(u,ℓ) = (2,1)` has `sideSet = {0,1}` and `(1,1)` has `sideSet = {1,2)`, both of card
`2 > 1`, so clause 5 forces `{(2,1), (1,1)} ⊆ s`. Clauses 3 and 4 then split `f` into at least
two monic factors of positive degree summing to `deg f = 2` — i.e. a root of `f` in `ℤ₍₅₎`,
hence in `ℚ`. But `disc f = 25 − 1000 = −975 < 0`. Contradiction: the axiom minus completeness
proves `False`.

*The rule this file establishes.* A hypothesis that the statement's truth depends on is never
left to section auto-inclusion. It is written in the binder list, where a diff can see it and
a careless edit cannot silently drop it. The `leanspec` retirement `example` is the standing
gate that this binder still matches the signed type.

*Not carried:* `[Finite (ResidueField O)]`. The signed stub's elaborated type does not carry it
and the cited sources do not need it (both [GN15] and [FGMN] are stated over an arbitrary
discrete valued field). Adding it would only weaken the import below what was signed.

## Sources (CO-PRIMARY — two cites, and both are needed)

* **[GN15]** J. Guàrdia, E. Nart, *Genetics of polynomials over local fields*, Contemp. Math.
  **637** (2015) 207–241, **Theorem 2.3**. Setting: "an arbitrary discrete valued field
  `(K,v)`" — COVERS-ALL-O, both characteristics; our complete `O` is the case `K = K_v`.
  Display: `g = g₀ · φ^{ord_φ(g)} · ∏_{(λ,ψ)} g_{λ,ψ}`, with `−λ` running over the slopes of
  `N⁻(g)`, `deg g₀ = deg g − ℓ(N⁻(g))·deg φ` and
  `deg g_{λ,ψ} = e_λ·ord_ψ(R_λ(g))·deg ψ·deg φ`; instantiated at MacLane chain length `r = 0`
  (the Gauss valuation, `φ` an order-1 key). **Numbering A-3-VERIFIED**
  (`docs/CITE_NUMBERING_AUDIT_2026-08-16.md`): volume/pages from the AMS CONM 637 ToC, Crossref
  DOI 10.1090/conm/637/12767, zbMATH Zbl 1396.11143, and the statement confirmed verbatim in
  two copies straddling the referee round (the `upcommons.upc.edu` author PDF and
  **arXiv:1309.4340v2**, the freely checkable witness).
* **[FGMN]** J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane
  valuations*, arXiv:1305.0775 / J. Algebra, **Theorem 6.6** (arXiv-v3 numbering).
  **WHY THIS SECOND CITE IS LOAD-BEARING, not decorative:** [GN15] Thm 2.3 carries the standing
  hypothesis `φ ≁_µ φ_r`, which at `r = 0` reads `φ ≁_{µ₀} x` and therefore **excludes exactly
  the keys `{x + a : a ∈ 𝔪}`** — including `φ = x` itself, i.e. the Eisenstein / totally
  ramified branch, which is this import's most-used instance (and the landed `m = ℓ = 1` case
  B.44). [FGMN] Thm 6.6 is the same theorem in its intrinsic form — identical display,
  identical degree laws — with "**proper** key polynomial" in place of `φ ≁_µ φ_r`, and at
  `r = 0` every key is proper: [FGMN] Def 5.10 states `KP(µ₀)_str = KP(µ₀)` and
  `KP(µ)_str ⊂ KP(µ)_pr ⊂ KP(µ)`, with the independent arithmetic leg `e₀ = m₀ = 1` ([GN15]
  §1.4), so "`deg φ` a multiple of `e₀m₀ = 1`" is automatic. [FGMN]'s setting is the same
  arbitrary discrete valued field, so no scope is lost. **Sign [FGMN] Thm 6.6 for the whole
  `IsKey` range; [GN15] Thm 2.3 is the chain-relative restatement covering `φ ≁_{µ₀} x`. Do
  NOT read [GN15] Thm 2.3 alone as covering `∀ φ, IsKey φ`.**
  **⚠ OPEN BROWSER-CHECK RIDER (non-blocking per PROJECT_STATE #66 (c)):** [FGMN]'s published
  (J. Algebra) numbers drift uniformly by `−1` across §§5–6, so print is **PREDICTED** Thm 6.6 →
  **Thm 6.5** and Def 5.10 → **Def 5.9** — *predicted, NOT verified* (arXiv 1305.0775 has only
  v1–v3, none carrying the published numbering). Confirm against the Elsevier PDF. A rider that
  later fails is a stop-the-line correction event **on this source line**, not on the signed
  statement.
* **Secondary displays (corroborating, NOT the signed cite).** GMN Thm 1.15 (printed TAMS 364
  (2012) 361–416, A-3-verified): `f_φ = F_1 … F_g` with `N_φ(F_i)` one-sided of slope `λ_i` and
  `R_{λ_i}(F_i) ∼ R_{λ_i}(f)` — the per-slope grouping and clauses 3/6 transcribed here, but at
  `K/ℚ_p` scope only, so it does not reach ENV-C's equal-characteristic case. [AGNPRW] Thm 4.4
  and [FGMN] Thm 2.8 (NS-9 residual multiplicativity) are the general-scope legs of clause 6;
  the [AGNPRW] numbers in the repo are arXiv-v1 numbers and have DRIFTED in print (Found.
  Comput. Math. 25 (2025) 631–681: Thm 4.4 → Thm 4.10, Thm 4.6 → Thm 4.15, Cor 2.9 → Cor 2.17).

## Why this is an axiom and not a theorem — the machine-checked route block

The signed PROOF ROUTE of this node is **machine-checked UNREACHABLE**. The committed
obstruction record is `leanfinal/Uniformity/ChapB/B42_ROUTE_BLOCKED.lean.txt` (kept as
`.lean.txt`, outside the build; it compiles at the pin, sorry-free, Lean-core footprint):

1. The route's step 5 applies B.41 to `f` itself, and B.41's frozen signature carries
   `(hpure : IsPure φ f u ℓ)`. But purity forces a ONE-SIDED polygon — that is NODE **B.42a**,
   `card_sideSet_le_one_of_isPure`, landed as a real theorem in `Uniformity/ChapB/B42a.lean`
   (imported here) — so `hpure` is unavailable exactly in the multi-side inductive case. The
   obstruction record's corollary `b42_route_blocked` states this in the node's own inductive
   hypotheses.
2. Independently, step 5's degree arithmetic is unsatisfiable: B.41's `hprod` would force
   `ℓ₁·d₁ = μ`, i.e. the steepest side spans the whole polygon — the case already handled.

The missing mechanism is a **graded Hensel at a VERTEX** (a Weierstrass-type split whose two
factors are pure at DIFFERENT slopes). No corpus proof exists at general keys: the candidate
extraction B.44′ is CLOSED-REFUTED (amendment A-F.7, machine-checked). **Retirement route for
this cite:** prove that vertex split — `B-BOX-1`-tier own design, specified in the obstruction
record's "missing mechanism" display. Landing it turns this `axiom` back into a `theorem` and
removes it from every downstream footprint.

**NOT claimed by the route block:** that the statement is false. It is the classical theorem of
the polygon at order 1 and is expected to be true as signed; no counterexample is offered or
expected.

## Statement provenance: two machine-refutation waves preceded the signature

The signed type is the survivor of A-F.6, A-F.9 and A-F.10, all recorded in
`leanspec/Leanspec/ChapB.lean`'s RE-SIGN LOG:

* **[repaired: A-F.6]** conclusion STRENGTHENED (hypotheses unchanged): clause 1 records
  `0 < p.1`, clause 3 records `φ.natDegree ∣ (F p).natDegree` — what the repaired B.48 needs at
  B.63.
* **[repaired: A-F.9]** `(h0 : dev φ f 0 ≠ 0)` ADDED — the A-F.6 form is machine-REFUTED
  (`B42_REFUTATION.lean.txt`: `f = φ`, `μ = 1` at ANY DVR/key). `h0` is the classical `φ ∤ f`;
  [GN15] Thm 2.3 peels `φ^{ord_φ(g)}` explicitly. Clause 3 further gained
  `dev φ (F p) 0 ≠ 0` and `0 < (F p).natDegree`.
* **[repaired: A-F.10]** clause 6 ADDED — the residual tie `R_λ(F p) ∼ R_λ(f)`, the cited
  theorem's own third clause, which B.63 step 2 consumes and which cannot be re-derived from a
  construction under the cite.

**⚠ CLAUSE 6 IS FLAGGED.** Clauses 1–5 survived both machine-refutation waves and were then
source-verified clause by clause (A-F.9 (II)–(III)). **Clause 6 is the one clause of this
import never refutation-tested** — it was added at A-F.10, after the last wave. It is flagged
FIRST for the gate-(b) fresh-context audit, with the named transcription-shear risk: this
chapter's `resPoly` is the DIGIT read at the side line, not the intrinsic graded normalization,
and the A-F.6 record documents the two known shear modes and why the clause 1 / clause 3
hypotheses exclude them. Treat clause 6 as the least-hardened part of this axiom.

Two further disclosed caveats: the chapter's slopes `(u,ℓ)` are the source's `−λ` in lowest
terms (`e_λ = ℓ`); and the import is stated only for `f̄ = φ̄^μ`, the single-branch case, where
the source's arbitrary monic `g` is strictly more general — no strengthening is smuggled in.

## Corroboration on record

`W12-SHAPE` (0/164 counterexamples over 23 rows, BOTH directions — the completeness half is
exactly clause 5); `HE6-SEP` (4,232 strict-excess certificates); the quartic PARI oracle
harness (`verification/quartic_oracle.py`); the landed `m = ℓ = 1` instance **B.44**, reached
without any of §§3–5's polygon machinery (deriving B.44 from this axiom is the booked
decorrelation check); **B.42a**, whose machine-checked "pure ⟹ one-sided" is the coherence gate
below; and two earlier transcriptions of this very statement that the wave process REFUTED
before import — evidence the audit pipeline has teeth.

DEPENDS (for the statement to elaborate): B.01 (`IsKey`) · B.02 (`dev`) · B.11 (`npHgt`) ·
B.16 (`sideSet`) · B.20 (`sideMin`) · B.25 (`resField`) · B.29 (`resPoly`) · B.34 (`IsPure`).
B.42a is imported for the coherence gate only.

## Status

**AXIOM (owner-signed gate-(b) literature import).** No `sorry`. Footprint by construction:
`propext`, `Classical.choice`, `Quot.sound`, **plus this axiom** in every consumer.
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

/-- **B.42** [theorem] ENV-C — **[cite:GN15 Thm 2.3 + FGMN Thm 6.6], gate (b), owner-signed
2026-08-16 (PROJECT_STATE #66)**: the side dissection of the `φ`-Newton polygon, imported from
the literature as an `axiom`. Its in-repo proof route is machine-checked unreachable
(`B42_ROUTE_BLOCKED.lean.txt`); the faithfulness entry is CHAP-I's 2026-08-16 dated addendum;
clause 6 (the residual tie) is the flagged, never-refutation-tested clause. Every downstream
`#print axioms` will and should display this name.

**`[IsAdicComplete (maximalIdeal O) O]` is written INLINE and is LOAD-BEARING — see the
header's "The completeness binder" section. Do not delete it, do not move it into a section
`variable`.** -/
axiom exists_slope_factorization [IsAdicComplete (maximalIdeal O) O]
    (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O),
      (∀ p ∈ s, 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 * q.2 ≠ q.1 * p.2) ∧
      (∀ p ∈ s, (F p).Monic ∧ IsPure φ (F p) p.1 p.2 ∧
        φ.natDegree ∣ (F p).natDegree ∧
        dev φ (F p) 0 ≠ 0 ∧ 0 < (F p).natDegree) ∧
      f = ∏ p ∈ s, F p ∧
      (∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
        (1 < (sideSet φ f u ℓ).card ↔ (u, ℓ) ∈ s)) ∧
      (∀ p ∈ s, ∀ (hne : (sideSet φ f p.1 p.2).Nonempty)
        (hne' : (sideSet φ (F p) p.1 p.2).Nonempty) (H₀ H₀' : ℕ),
        npHgt φ f (sideMin φ f p.1 p.2 hne) = (H₀ : ℕ∞) →
        npHgt φ (F p) (sideMin φ (F p) p.1 p.2 hne') = (H₀' : ℕ∞) →
        ∃ c : (resField φ)ˣ,
          resPoly π φ f p.1 p.2 hne H₀ =
            Polynomial.C (c : resField φ) * resPoly π φ (F p) p.1 p.2 hne' H₀')

/-! ## Sanity gates

Two `example`s, both sorry-free. They are not blueprint nodes; they exist so that a broken
import is a build error here rather than a surprise at B.63. -/

/-- **GATE 1 — the axiom fires.** Specialize the import and destructure it: `f` really is the
product of the slope factors. If the axiom ever failed to elaborate, or its conclusion's
conjunction structure drifted, this `example` would break. -/
example [IsAdicComplete (maximalIdeal O) O]
    (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O), f = ∏ p ∈ s, F p := by
  obtain ⟨s, F, -, -, -, hprod, -, -⟩ := exists_slope_factorization hπ hφ hf hμ hres h0
  exact ⟨s, F, hprod⟩

/-- **GATE 2 — the B.42a coherence check.** The imported clause 3 says each factor `F p` is
`(p.1, p.2)`-pure; the LANDED theorem B.42a (`card_sideSet_le_one_of_isPure`, Lean-core) then
forces each factor's polygon to be one-sided. So the cite and the machine-checked dictionary
agree: the dissection's output is exactly what the engine's own notion of purity predicts. This
consumes both, and is the shape of every future consumer's footprint. -/
example [IsAdicComplete (maximalIdeal O) O]
    (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hμ : 0 < μ)
    (hres : f.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ μ)
    (h0 : dev φ f 0 ≠ 0) :
    ∃ (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → Polynomial O), f = ∏ p ∈ s, F p ∧
      ∀ p ∈ s, ∀ u ℓ : ℕ, 0 < ℓ → u * p.2 ≠ p.1 * ℓ →
        (sideSet φ (F p) u ℓ).card ≤ 1 := by
  obtain ⟨s, F, hslope, -, hfac, hprod, -, -⟩ :=
    exists_slope_factorization hπ hφ hf hμ hres h0
  refine ⟨s, F, hprod, ?_⟩
  intro p hp u ℓ hℓ hne
  obtain ⟨-, ht, -⟩ := hslope p hp
  obtain ⟨hFm, hFpure, hdvd, -, -⟩ := hfac p hp
  obtain ⟨k, hk⟩ := hdvd
  exact card_sideSet_le_one_of_isPure hφ hFm (μ := k) (by rw [hk, Nat.mul_comm]) ht hFpure hℓ hne

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint

The declaration below is the repo's FIRST owner-signed gate-(b) literature cite. It prints
itself, by design: `#print axioms` on the axiom names the axiom. Every consumer inherits it. -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_slope_factorization
#print axioms Uniformity.Density.Leaf.card_sideSet_le_one_of_isPure
end AxCheck
