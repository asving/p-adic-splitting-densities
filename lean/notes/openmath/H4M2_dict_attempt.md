/-
# H4-M2 — the (a6)/(EQ-1) matching dictionary at this group's slice + (R4) + Lemma 4 — attempt (Fable prover H4-M2, 2026-08-01)

Unit H4-M2 of `lean/blueprints/HDISCHARGE_H4.md` (§M table + §2's (R4) plan).
This file is a LITERATE LEAN MARKDOWN NOTE: the prose lives in doc-comment
blocks and every Lean declaration compiles. Gate command (from `lean/`):
`lake env lean notes/openmath/H4M2_dict_attempt.md` — green, zero sorry.

CHARGE (blueprint §M row, verbatim): "the (a6)/(EQ-1) matching dictionary at
this group's slice + (R4) + Lemma 4 proved | §2's (R4) plan items (i)–(iv);
M14 §7.2/§8.2 constraints hard-coded | consumes: M14 Lemma 4;
Lidl–Niederreiter 3.46 (pinned); (EQ-1) text | MED | gate: hostile pass ×1 +
N-K3's gcd table."

CHARGE detail (blueprint §2 (R4) plan, verbatim): "(R4) is definitional GIVEN
the (a6)/(EQ-1) matching dictionary (the owed REL.1 artifact defining 'the
matched position' and `posLetter δ`). H4-M2 writes the dictionary AT THE SLICE
THIS GROUP NEEDS: (i) TWO objects, kept rigorously apart (Codex fold, finding
5 — the REL.1 rule: the O_δ classifier's OWN tower is RECONSTRUCTED over F_q,
never scalar-extended): (i-a) the re-based classifier's own tower (the
construction — REL.1's object, consumed, not defined here), and (i-b) the
same-keys COMPARISON tower (ℤ_p-tower keys viewed in O_δ[x], residuals read
along F_k ↪ F_k·F_q) — a comparison DEVICE; the dictionary's central display
is WHEN the two coincide at a matched prefix (expected: exactly at
prefix-stable positions — a lemma to prove, not a definition to decree);
(ii) `posLetter δ x` with the M14 §7.2 constraint hard-coded — prefix
stability via a designated off-domain letter — PLUS the equivalence PROVED,
not assumed (Codex fold, finding 12): the letter grammar is injective on the
encoded prefix data (`SpeciesSyntax.shape`/side data — the note's
`letter_det` typing) and the off-domain letter is outside the grammar's
range, so that Lean `Stable` ⟺ (R4) is a displayed lemma; (iii) Lemma 4's
gcd(m, δ) = 1 characterization upgraded from 'test-design tool' to a proved
lemma of the dictionary (inputs (F1) Lidl–Niederreiter 3.46 and (F2)
compositum degrees, pinned literature); (iv) the worked F₉ instance
re-derived as the out-of-domain example."

SOURCES consumed: `M14-eq2-alphabet_attempt.md` (Lemma 4, §7.2, the (R)
package, the F₉/T3 instance data); `M14-eq2-alphabet_brief.md` (the species
and stability text); `MOVES_2026-07-24.md` lines ~9368–9560 ((a6), (EQ-1)
verbatim); `LeanUrat/MovesRBase/Defs.lean` (`SpeciesSyntax`/`AlphabetData`/
`Stable`, imported VERBATIM, never re-transcribed); wave-0
`LeanUrat/Scaffold/HDischarge/H4/Defs.lean`.

POINTER RESOLUTION, flagged honestly: the blueprint charge says "M14
§7.2/§8.2 constraints". The M14 attempt has NO §8.2 — its §1 contains a
dangling internal reference "(§8.2 records why the instance MUST encode this
in `posLetter` …)" whose content is exactly §7.2's constraint plus the F₉
evidence that letter-only stability is insufficient. Both constraints are
hard-coded below (§2); the dangling pointer is reported, not papered over.

REVISION 1 (2026-08-08, pass-1 fold): hostile pass 1
(`H4M2_pass1_2026-08-08.md`, verdict CRITICAL — 5 critical + 3 gap) folded
in full; the finding-by-finding record is §6. Headline cure: the
matched-position definition is now KEY-FREE and the key/valuation
coincidence is the DISPLAYED OPEN lemma DICT-0, consumed everywhere as the
named hypothesis [IN-C].

REVISION 2 (2026-08-08, pass-2 fold): hostile pass 2
(`H4M2_pass2_2026-08-08.md`, verdict CRITICAL — 2 critical + 1 gap + 1
confirmation) folded in full; the finding-by-finding record is §6. Headline
cures: (1) the REVISION-1 "invariant-data" match (numerical prefix ledger:
stage tuples + base degree) was NOT WELL-DEFINED — distinct branches can
share identical ledgers, so the ledger either presupposes the numerical
coincidence (if equality defines the match) or names no unique counterpart
(if it merely labels the base position); RETIRED. The matched position is
now defined by the FACTOR CORRESPONDENCE (§1): matched = routing a common
irreducible factor of the input f itself — classifier-independent data of
f, no ledger coincidence, no key clause; a well-defined RELATION, honestly
one-to-many, with uniqueness at split-free prefixes extracted as DICT-0's
clause (d), open, never decreed. (2) DICT-0/[IN-C] restated at EXACTLY the
strength its consumers use — four clauses (a)–(d), including the next-read
divisibility (c) that the (1) ⇒ (2) leg consumes (its "sees the same
residual ψ_{j₀}" step was previously supplied by NO named input) and the
field range j ≤ k+1 (pass-2 gap); a two-directional consumer audit is
displayed (no gap in either direction: literal transported-key equality is
consumed by nothing and asserted nowhere). Clean counter stays 0/1; one
clean hostile pass owed on THIS revision.

REVISION 3 (2026-08-08, pass-3 fold): hostile pass 3
(`H4M2_pass3_2026-08-08.md`, verdict GAPS-ONLY — 1 gap + 4 confirmations,
including CONFIRMATION of the REVISION-2 factor-correspondence
well-definedness with references now folded into §1) folded in full; the
finding-by-finding record is §6. Headline cure (display-only, NO strength
change — the four-clause DICT-0 already supplies everything consumed): the
REVISION-2 consumer audit MISCLASSIFIED clause (b) — it said the (1) ⇒ (2)
leg "consumes (c) ONLY", but that leg consumes (b) AND (c): clause (c)'s
divisibility comparison is meaningful only under (b)'s residue-field
identification, exactly as the proof leg itself already cited ("under
[IN-C](b)'s identification"). The audit display is corrected at its §1
statement and at its §5/§6 repetitions. Counter stays 0/1; the final clean
pass runs on THIS revision.

VERDICT (summary, at the REVISION-3 honest strengths — identical in
strength to REVISION 2; the REVISION-3 fold is display-only): the four charge items
are delivered as follows. (i) the two objects are defined and kept apart;
the matched position is defined by the FACTOR CORRESPONDENCE (key-free AND
ledger-free: matching through the irreducible factors of f itself, §1), the
key-level coincidence is the DISPLAYED OPEN lemma DICT-0 ([IN-C], four
clauses at exactly consumer strength), and the
coincidence-at-stable-prefixes display DICT-1 is a MATH lemma conditional on
FOUR named inputs ([IN-R1], [IN-U], [IN-C], [IN-F1]) — NOT a Lean theorem:
its Lean face is the hypothesis rows of `GcdSlice`, supplied by instances,
not proved here. (ii) `posLetter` per §7.2 + `Stable ⟺ (R4)` PROVED, in
Lean, from THREE `DictModel` rows — finding 12's two (grammar injectivity
`henc` + off-domain letter `hoff`, both themselves assumed rows here, with
grammar-level derivation lemmas supplied) PLUS the load-bearing base-side
tautology `splitFree_one` (§2) — theorem `DictModel.stable_iff_R4` below,
wired to the corpus `AlphabetData.Stable` verbatim by
`alphabetData_stable_iff_R4` (which additionally assumes `Encodes`).
(iii) Lemma 4: the arithmetic core `lemma4_arith` is UNCONDITIONAL Lean; the
field-theoretic inputs (F1)/(F2) and DICT-1's transport identity are NAMED
HYPOTHESIS ROWS of `GcdSlice` (assumed by every instance, their MATH
arguments in §3/§1 conditional as displayed), and
`GcdSlice.stable_iff_coprime` chains Stable ⟺ gcd(m, δ) = 1 GIVEN those
rows. (iv) the F₉ instance re-derived: math + a compiled split witness over
the concrete F₉ = F₃[i] and the decide-checked gcd table (N-K3 seed); the
dictionary-level realization of the example (instances, branch letters,
alphabet dimensions) stays prose, scoped in §4.

RISK, displayed (per the blueprint): this dictionary is ALSO consumed by the
(UB-X)(b) adjudication (H4-M4) and by Route A of H4-M5 — it is the shared
gate unit of the blueprint. Nothing here discharges (UB-X)(b); the dictionary
only makes it WELL-POSED at this slice.
-/

import Mathlib
import LeanUrat.MovesRBase.Defs
import LeanUrat.Scaffold.HDischarge.H4.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H4.Dict

open MovesRBase Polynomial

/-!
## §1. Item (i) — the two objects, kept rigorously apart

Throughout: p prime, δ ≥ 1, q := p^δ, F_q := the subfield of F̄_p of order
p^δ (the corpus's `Fsub p δ`), O_δ := W(F_q) (the corpus's `O p δ`; ABSOLUTE
base indices per the standing convention). The input is one monic
f ∈ ℤ_p[x] ⊆ O_δ[x]; the matching of inputs is the literal inclusion — that
is the (a6) slice this group needs (nothing about Θ_j-coordinates, frames, or
measure transport — (a1)–(a5) — is defined or consumed here; (a6) is quoted
at its READ-DICTIONARY clause only: "letter-for-letter transport of b_j's
continuation READS to O_δ-classifier reads ((EQ-1)'s dictionary), displayed
per read field").

The base-side data at a ledger position class x: the accepted ℤ_p tower
prefix through stage k — keys Φ_1, …, Φ_k ∈ ℤ_p[x], read indices (e_j, h_j)
with gcd(e_j, h_j) = 1, residue fields F_1 ⊆ … ⊆ F_{k+1} inside F̄_p with
[F_1 : F_p] = d and F_{j+1} = F_j[z]/(ψ_j), ψ_j the stage-j residual,
irreducible over F_j of degree g_j.

### (i-a) The RECONSTRUCTED tower — REL.1's object, consumed, not defined here

The O_δ classifier's OWN run on f: stages built over the base O_δ, keys
chosen in O_δ[x], residue fields RECONSTRUCTED over F_q, residual polynomials
factored over the reconstructed fields and every stage residual irreducible
BY CONSTRUCTION. Per the REL.1 rule (Codex fold, finding 5) this tower is
NEVER the scalar extension of the ℤ_p tower and is NEVER obtained by
substituting a cardinality; its existence and its (S1)–(S6)/D.0 stage package
over O_δ are exactly the (R1)–(R3) slice that unit H4-M1 re-scopes — this
note CONSUMES that object and defines nothing about its internals.

### (i-b) The SAME-KEYS COMPARISON tower — a device, not a classifier

DEFINITION (this note's artifact). The comparison device C^{(δ)} at the
prefix of x: take the ℤ_p-side keys Φ_1, …, Φ_k VERBATIM as elements of
O_δ[x], with the same read indices (e_j, h_j); equip O_δ[x] with the
inductive (MacLane-augmented) valuations w_j^{comp} defined by the same
augmentation data over the Gauss valuation of O_δ (which extends the Gauss
valuation of ℤ_p; O_δ/ℤ_p is unramified, v(p) = 1 on both sides); read the
stage-j residual data along the compositum F_j ↪ F_j·F_q inside F̄_p: the
device's stage-j residue field is DEFINED as F_j^{comp} := F_j·F_q, and the
transported residual is ψ_j itself, read in (F_j·F_q)[z].

STATUS OF THE DEVICE, displayed: C^{(δ)} is a well-defined valuation-theoretic
object (augmentation chains need no irreducibility to be defined), but it is a
CLASSIFIER TOWER only where every transported residual stays irreducible — at
a stage where ψ_j splits over F_j·F_q, the augmentation is not a legal OM
stage (keys must carry irreducible residuals) and the device stops being a
tower of the theory. That is exactly why (i-a) and (i-b) must be kept apart:
the device is a COMPARISON instrument whose agreement with (i-a) is a THEOREM
with a domain, not an identification.

### The matching, at this slice — the FACTOR CORRESPONDENCE (REVISION 2, pass-2 finding 1; key-free AND ledger-free)

Matched position: same input f, same height γ, matched THROUGH THE
IRREDUCIBLE FACTORS OF f ITSELF. Precisely: the irreducible factors of f in
ℤ_p[x] and in O_δ[x] are data of f, computed by no classifier; distinct
ℤ_p[x]-irreducible factors of f remain pairwise coprime in O_δ[x] (they are
coprime over ℚ_p, hence over every extension field), so each
O_δ[x]-irreducible factor G of f divides exactly ONE ℤ_p[x]-irreducible
factor h — say "G lies over h". Each classifier run ROUTES each irreducible
factor over its own base through the positions of its tree (a position's
accepted prefix approximates the factor): the base run routes each h through
base positions — accepted base theory; the reconstructed run ((i-a),
consumed) routes each G through its own positions — a definitional face of
the consumed object (i-a), not of this note. DEFINITION: a reconstructed
position y is MATCHED to the base position x iff some O_δ[x]-irreducible
factor G of f routed through y lies over some ℤ_p[x]-irreducible factor h of
f routed through x. The device C^{(δ)} needs no matching clause of its own:
it is built from x's base prefix, hence canonically attached to x.

WELL-DEFINEDNESS, displayed: the definition consumes only f's two
factorizations (classifier-independent) and each run's own factor-routing.
NO numerical coincidence, NO ledger comparison, and NO key clause enters.
The "lies over" clause is well-defined (CONFIRMED at pass 3, references
folded here): O_δ is a DVR, so O_δ[x] is a UFD and its irreducibles are
prime [Stacks 0BC1] — hence any O_δ[x]-irreducible factor G of f divides
SOME ℤ_p[x]-irreducible factor h; distinct ℤ_p[x]-irreducible factors are
relatively prime over ℚ_p and STAY relatively prime over
K_δ = Frac(O_δ) (relative primality of polynomials is preserved under
field extension [Stacks 09GY]), so G divides exactly ONE.
QUALIFICATION, displayed (pass-3 finding 2): "coprime in O_δ[x]" throughout
means the gcd sense — no common non-unit factor — NOT comaximality of
ideals; the gcd sense is exactly what the uniqueness argument uses.
The match is a RELATION, in general one-to-many — §4's F₉ instance realizes
exactly this shape: both branch positions are matched to the one base
position. Uniqueness of the matched position at a split-free prefix is NOT
definitional; it is DICT-0's clause (d) below, displayed open (the
canonicity content pass 2 found hidden behind "position class"). And NO
audited consumer silently needs a functional branch selection OUTSIDE the
split-free locus (CONFIRMED at pass 3): DICT-0(d) supplies the single
reconstructed position exactly where DICT-1(3), `pdata`, and the (2) ⇒ (3)
leg need it, and off the split-free locus `posLetterD` collapses the branch
ambiguity to `offLetter` — no consumer selects a particular branch there.

RETIREMENTS of record, both readings of both predecessors: (pre-REVISION 1,
pass-1 finding 1) "same prefix keys (via the inclusion ℤ_p[x] ⊆ O_δ[x])"
presupposed the key-level coincidence the dictionary exists to PROVE —
circular, retired at REVISION 1. (REVISION 1, pass-2 finding 1) the
replacement — matching by the numerical prefix ledger (stage tuples
(e_j, h_j, g_j)_{j≤k}, base degree d) read against the device's realized
reads — was NOT WELL-DEFINED: distinct branches of the same input can carry
identical ledgers, so if ledger EQUALITY defines the match it presupposes
the numerical-coincidence half of DICT-1(1), and if the ledger merely NAMES
the base position it fails to determine which reconstructed position is the
counterpart. Retired at REVISION 2; the factor correspondence needs neither
reading. The key/valuation coincidence remains its own displayed lemma:

**DICT-0 (key/valuation coincidence) — DISPLAYED OPEN; restated at
REVISION 2 at EXACTLY the strength its consumers use (pass-2 finding 2).**
At a matched split-free prefix through stage k (k = 0 allowed: the empty
prefix with only the base read pending):

(a) [valuations] every reconstructed position matched to x realizes the
device's inductive valuations: w_j^{recon} = w_j^{comp} on O_δ[x] for
j ≤ k. (The GMN gloss — stagewise Okutsu-equivalence of the reconstructed
keys with the transported ℤ_p-keys — survives only as a GLOSS; no consumer
reads it, see the audit below.)

(b) [embedded fields] the reconstructed residue fields are the composita AS
EMBEDDED subfields of F̄_p: F_j^{(δ)} = F_j·F_q for ALL j ≤ k+1 (range
through k+1, fixed at REVISION 2 — pass-2 finding 3: the terminal field is
load-bearing at the next residual read, exactly clause (c)'s field).

(c) [next-read divisibility] every irreducible stage-(k+1) residual the
reconstructed run realizes at the matched position (one per branch of its
next read; the base residual, of degree d over F_q, is the k = 0 case)
divides — up to a unit multiple, under (b)'s identification — the
transported next residual ψ_{k+1} read over F_{k+1}·F_q.

(d) [uniqueness] exactly one reconstructed position is matched to x at the
split-free prefix.

CONSUMER AUDIT (the pass-2 charge: no strength gap in EITHER direction;
CORRECTED at REVISION 3 — pass-3 finding 1: the REVISION-2 display said the
(1) ⇒ (2) leg "consumes (c) ONLY", misclassifying clause (b); the full
proof-leg replay was re-confirmed at pass 3 modulo exactly this fix).
The (2) ⇒ (3) leg of DICT-1 consumes (a) (feeding [IN-U]), (b) (clause
(3)'s embedded-field identity), and (d) (clause (3)'s single-position
reading — which the model layer's single-valued `pdata` also presupposes),
plus [IN-R1] and [IN-U]; the (3) ⇒ (1) leg consumes no additional DICT-0
clause; the (1) ⇒ (2) leg consumes (b) AND (c), plus [IN-F1], applied at
the first failing stage — clause (c)'s divisibility comparison is
meaningful ONLY under (b)'s residue-field identification (range through
k+1), exactly as the proof leg below has cited since REVISION 2 ("under
[IN-C](b)'s identification"); the audit's "(c) ONLY" wording contradicted
its own proof leg and is retired (its pre-REVISION-2 ancestor asserted the
reconstructed read "sees the same residual ψ_{j₀}" — a step supplied by NO
named input, pass-2 critical 2; (b)+(c) is the exact fragment that leg
uses); the `l4_persist` row is
device-side only and consumes no clause of DICT-0. NO consumer uses literal
equality of the reconstructed keys with the transported ℤ_p-keys, so
DICT-0 does not assert it: the pre-REVISION-1 same-keys clause OVERSHOT
(stronger than any consumer needs, and not expected to hold literally — the
reconstructed classifier chooses its own keys), while REVISION 1's bare
Okutsu-equivalence form UNDERSHOT (weaker than what (1) ⇒ (2) uses). Both
mismatches are closed at this restatement.

STATUS of DICT-0, displayed: OPEN — consumed below as the named hypothesis
[IN-C], all four clauses. It is NOT derivable from the uniqueness material
on file: [IN-U] (essential uniqueness, below) applies only to two chains
ALREADY realizing the same inductive valuation, which is clause (a)'s
content — invoking it here would be circular (adjudication re-affirmed by
pass 2). ROUTE (named, owed): per-factor canonicity of OM data — GMN's
Okutsu-equivalence framework attaches canonical invariants/valuations to
each irreducible factor of f over O_δ; the REVISION-2 factor correspondence
supplies precisely the non-circular identification of the common factor
that pass 2 noted this route ALSO needed (the reconstructed run and the
legal, split-free device chain now approximate the SAME factors G of the
same f BY DEFINITION of "matched", so per-factor canonicity can compare
them); clause (c) additionally needs the residual-polynomial-of-a-factor
divisibility staple of that framework. Discharge runs through H4-M1's
(R1)-slice ([IN-R1]) plus GMN canonicity/divisibility pins (LITUNIT-roster
duties). HONESTY DIRECTION: every downstream consumer of "matched" GAINS
[IN-C] as a displayed hypothesis (§5 item 3) — nothing downstream gets
stronger by this fold, and REVISION 2 only STRENGTHENS the hypothesis
consumers carry (clauses (c)/(d) added).

`posLetter δ x` (§2) reads the letter the device realizes at the matched
position, with the §7.2 off-domain clause. This is the (a6)/(EQ-1)
dictionary AT THE SLICE THIS GROUP NEEDS; the full (a6) artifact (all read
fields, plus the (a1)–(a5) frame data) remains an owed REL.1 artifact and is
NOT claimed here.

### DICT-1 — the coincidence display (the central lemma, MATH-conditional, with named inputs)

**Lemma DICT-1.** At the matched prefix through stage k (matched = the §1
factor correspondence, REVISION 2), the following are equivalent:

(1) [prefix stability = (R4)] every reconstructed position matched to x
realizes the base-side stage tuples (e_j, h_j, g_j) for j ≤ k and the base
degree d, with every re-based residual irreducible of the matched degree;

(2) [split-freeness of the device] the transported base residual (degree d,
read over F_q) and every transported ψ_j (read over F_j·F_q) remain
irreducible;

(3) [ledger coincidence] exactly ONE reconstructed position is matched to
x, and its prefix ledger data equal the device's: same stage tuples,
w_j^{recon} = w_j^{comp} as valuations on O_δ[x], and F_j^{(δ)} = F_j·F_q
for all j ≤ k+1.

NAMED INPUTS (never silently absorbed; FOUR of them — the pre-REVISION-1
"two named inputs" claim was wrong and is retired, pass-1 finding 2):
[IN-R1] the device's stages satisfy the (S1)–(S6)/D.0 package over O_δ where
(2) holds — this is a face of the (R1)-slice, H4-M1's re-scoping charge
(REL.1; open, consumed as a hypothesis); [IN-U] essential uniqueness of
MacLane/OM augmentation chains: two chains realizing the same inductive
valuation on the same base have equal numerical invariants (e_j, h_j, g_j)
and ISOMORPHIC residue towers, stagewise (MacLane 1936, "A construction for
absolute values in polynomial rings", TAMS 40; modern forms: Vaquié 2007;
GMN's Okutsu-equivalence framework — PIN-PRECISION FLAGGED: the exact
printed theorem number is a LITUNIT-roster duty, not asserted here). NOTE,
displayed (finding 2): as quoted, [IN-U] yields abstract isomorphisms of
residue towers only, NOT literal equality of embedded subfields of F̄_p —
and it applies only to chains ALREADY realizing the same valuation. Both
missing pieces — and two more surfaced by pass 2 — live in: [IN-C] = DICT-0
(above; DISPLAYED OPEN; four clauses at exactly consumer strength,
REVISION 2): (a) the matched reconstructed chain realizes the device's
inductive valuations, (b) the embedded residue-field identification
F_j^{(δ)} = F_j·F_q for all j ≤ k+1, (c) next-read divisibility of the
realized residuals into the transported one, (d) uniqueness of the matched
position at split-free prefixes. [IN-F1] = (F1), Lidl–Niederreiter 3.46
(§3, pinned): the gcd factor count, consumed by the (1) ⇒ (2) leg.

*Proof (conditional on the four named inputs; legs re-cited at REVISION 2
to the exact [IN-C] clause each consumes; audit tally corrected at
REVISION 3 — the (1) ⇒ (2) leg's citations below were already right, the
§1 audit's "(c) ONLY" tally was not).* (2) ⇒ (3): under (2) every
augmentation step of the device uses a monic key whose residual is
irreducible over the current residue field, so C^{(δ)} is a LEGAL OM chain
over O_δ (key axioms are valuation-numeric and transport verbatim with the
numerical data; the graded/stage bookkeeping is [IN-R1]). By [IN-C](d)
exactly one reconstructed position is matched to x — clause (3)'s
single-position reading, an input, NOT a consequence of the factor
correspondence. That its chain realizes the SAME inductive valuations as
the device is exactly [IN-C](a) — the pre-REVISION-1 text asserted it from
"same input, same position", which does not imply it (pass-1 finding 2).
Given (a), [IN-U] applies: the two chains have equal stage tuples and
isomorphic residue towers; the EMBEDDED identification F_j^{(δ)} = F_j·F_q
for all j ≤ k+1 is [IN-C](b) (the device's fields are the composita by
construction).

(3) ⇒ (1): the reconstructed residuals are irreducible by construction;
under (3) their degrees are the matched g_j and the stage tuples equal the
transported (= base-side) integers, which is (1) verbatim (the single
matched position of (3) is in particular "every matched position").

(1) ⇒ (2): suppose some transported residual fails; let j₀ be the FIRST
failing stage (base stage included, with residual of degree d over F_q; the
base failure is the k = 0 case below). The sub-prefix through j₀ − 1 is
split-free, so DICT-0 applies to it with k = j₀ − 1; by [IN-C](c) every
irreducible stage-j₀ residual the reconstructed run realizes at the matched
position divides — up to a unit, under [IN-C](b)'s identification, whose
range through (j₀ − 1) + 1 = j₀ is exactly what is consumed here (pass-2
finding 3; so this leg consumes (b) AND (c) — the REVISION-3 audit
correction, pass-3 finding 1) — the transported ψ_{j₀} read over
F_{j₀}·F_q. By [IN-F1] that
read factors into gcd > 1 conjugate irreducible factors of equal degree
g_{j₀}/gcd, so EVERY realized stage-j₀ residual, being an irreducible
divisor, has degree g_{j₀}/gcd < g_{j₀}: every matched position's realized
letter has its g dropped, and the stage tuples do NOT match — contradicting
(1). (The pre-REVISION-2 text asserted here that the reconstructed read
"sees the same residual ψ_{j₀}" — a step supplied by NO named input at
REVISION 1's [IN-C] strength, pass-2 critical 2; clause (c) is the exact
fragment this leg uses.) ∎

The equivalence (1) ⟺ (2) is the "coincide exactly at prefix-stable
positions" display the blueprint demanded as a lemma — delivered as a MATH
lemma CONDITIONAL on the four named inputs, one of which ([IN-C]) is
displayed open. LEAN STATUS, displayed (pass-1 finding 3): DICT-1 is NOT a
Lean theorem — no Lean definition of its three clauses and no Lean proof of
their equivalence exists in this note. Its Lean face at the model layer is
HYPOTHESIS SHAPE only: the (2) ⇒ (3) leg appears as the NAMED row `coincide`
of `GcdSlice` below (pdata level, supplied — never proved — by each
instance), and the (1) ⇐ (2) packaging is what licenses row `l4_persist`
reading stability through the device. Neither direction of the biconditional
is established in Lean; the Lean discharge is fenced at the H4-F6 carriers.
-/

/-!
## §2. Item (ii) — `posLetter` with §7.2 hard-coded, and Stable ⟺ (R4) PROVED

M14 §7.2, verbatim, hard-coded here: "`Stable` must entail prefix stability.
The Theorem's induction consumes stability of every sub-position; with
letter-only stability at x the induction hypothesis is unavailable, and the
note's F₉ instance shows interior splitting genuinely redistributes alphabet
dimensions. The instance should make `posLetter δ x` encode the matched
prefix (e.g. return a designated off-domain letter when any prefix residual
splits), so that the Lean `Stable` ⟺ (R4). An instance with a coarser
`posLetter` is NOT covered by this proof and is expected to admit
countermodels."

The dictionary model below is the DEFINITIONAL layer: `Data` is the encoded
matched-prefix data (the stage-tuple list (e_j, h_j, g_j)_{j≤k}, the base
degree d, and the letter grammar's side/polygon data — i.e. what (EQ-1) says
a letter is defined by), `pdata δ x` is the data the device realizes at the
matched position over O_δ, and `splitFree δ x` is DICT-1's clause (2). These
carry the [M]-semantic content and stay NAMED STRUCTURE ROWS (never axioms).
`splitFree_one` is the base-side tautology (over δ = 1 nothing is
transported; every residual is irreducible by the accepted base theory).

Finding 12's two hypotheses are the rows `henc` (the letter grammar is
injective on encoded prefix data) and `hoff` (the designated off-domain
letter is outside the grammar's range on encoded data). Lemmas
`enc_injective_of_faithful` and `off_not_mem_range_of_reserved` below show
how to DERIVE them from the grammar level (`SpeciesSyntax.shape`/`side`/
`poly` fields), and `letter_unique_of_triple` displays the `letter_det`
typing (the grammar triple determines the letter — no collisions). HONESTY,
displayed (pass-1 finding 5): at THIS note's altitude `henc` and `hoff`
remain ASSUMED rows of `DictModel` — the derivation lemmas are generic
recipes, and no instance discharges them here (an H4-F1/H4-F6 duty).

THREE rows, not two (REVISION 1, pass-1 finding 5): the `Stable ⟺ (R4)`
proof below consumes a THIRD substantive row, `splitFree_one` (via
`posLetterD_one`), and this dependency is logically ESSENTIAL — if both the
δ-prefix and the base prefix were non-split-free, both letters would equal
`offLetter`, so `Stable` would hold while (R4) fails. The pre-REVISION-1
"from exactly finding 12's two hypotheses" claim is retired. Also displayed:
the corpus wiring (`alphabetData_stable_iff_R4`) additionally assumes
`Encodes`, and it connects corpus stability to THIS note's `DictModel.R4` —
whose semantic reach is bounded by the carrier caveat on `DictModel` below.
-/

/-- The (a6)/(EQ-1) matching-dictionary MODEL at this group's slice.
[M]-semantic rows (named, never discharged by fiat): `splitFree` = DICT-1(2)
at the matched prefix of x over O_δ; `pdata` = the prefix data the device
realizes; `splitFree_one` = the base-side tautology. Grammar rows: `henc`,
`hoff` per finding 12 (derivable via `enc_injective_of_faithful` /
`off_not_mem_range_of_reserved`; assumed here, no instance on file).
TRIVIALIZABLE-CARRIER CAVEAT (REVISION 1, pass-1 finding 4): `Data` is an
unconstrained `Type` and `pdata` an unconstrained function — a singleton
`Data` with constant `pdata` satisfies EVERY row (with `henc` trivially
injective and any second letter as `offLetter`), making `coincide` and
(R4)'s data clause vacuous. The names in these docstrings impose NOTHING in
Lean: this structure carries the SHAPE of DICT-1(3) at pdata level only —
none of its stage-tuple/valuation/residue-field content. FACTOR-BLINDNESS
(REVISION 2): `Pos` is likewise an unconstrained `Type` — the Lean carriers
CANNOT see the irreducible factors of f, so the §1 factor-correspondence
matching is invisible at this layer; the math definition needs no Lean
change (factors are f's own data), but positions keyed so that the factor
correspondence is realized (and `pdata` single-valued per DICT-0(d)) join
the instance obligation. The semantic content is an INSTANCE OBLIGATION
(fenced H4-F1/H4-F6): `Data` must be the encoded
stage-tuple/degree/side data with `pdata` the device's realized
read. Recorded as honest-residue item 6 (§5). -/
structure DictModel (Sp : SpeciesSyntax) (Pos : Type) where
  /-- encoded matched-prefix data: stage tuples, base degree, side/polygon data -/
  Data : Type
  /-- the letter the grammar assigns to a prefix datum -/
  enc : Data → Sp.Letter
  /-- finding 12(a): the grammar is injective on encoded prefix data -/
  henc : Function.Injective enc
  /-- §7.2's designated off-domain letter -/
  offLetter : Sp.Letter
  /-- finding 12(b): the off-domain letter is outside the grammar's range -/
  hoff : offLetter ∉ Set.range enc
  /-- [M] DICT-1(2): every transported prefix residual stays irreducible -/
  splitFree : ℕ+ → Pos → Prop
  /-- [M] the prefix data realized at the matched position over O_δ -/
  pdata : ℕ+ → Pos → Data
  /-- [M] base-side tautology: at δ = 1 the prefix is split-free -/
  splitFree_one : ∀ x : Pos, splitFree 1 x

/-- `letter_det` displayed: the grammar triple (shape, side, poly) determines
the letter — the dictionary's letter assignment has no collisions. -/
theorem letter_unique_of_triple {Sp : SpeciesSyntax} {l l' : Sp.Letter}
    (h : (Sp.shape l, Sp.side l, Sp.poly l) = (Sp.shape l', Sp.side l', Sp.poly l')) :
    l = l' :=
  Sp.letter_det h

/-- finding 12(a) DERIVED at the grammar level: if the letters assigned to
prefix data carry the data faithfully into the grammar triple via an
injective interpretation ι, the encoding is injective. -/
theorem enc_injective_of_faithful {Sp : SpeciesSyntax} {Data : Type}
    (enc : Data → Sp.Letter)
    (ι : Data → (ℕ × ℕ × ℕ × ℕ) × Sp.SideData × Sp.PolyConv)
    (hι : Function.Injective ι)
    (hfaith : ∀ d, (Sp.shape (enc d), Sp.side (enc d), Sp.poly (enc d)) = ι d) :
    Function.Injective enc := by
  intro d d' h
  apply hι
  rw [← hfaith d, ← hfaith d', h]

/-- finding 12(b) DERIVED at the grammar level: an off-domain letter whose
grammar triple is reserved (realized by no encoded prefix datum) lies outside
the encoding's range. -/
theorem off_not_mem_range_of_reserved {Sp : SpeciesSyntax} {Data : Type}
    (enc : Data → Sp.Letter)
    (ι : Data → (ℕ × ℕ × ℕ × ℕ) × Sp.SideData × Sp.PolyConv)
    (hfaith : ∀ d, (Sp.shape (enc d), Sp.side (enc d), Sp.poly (enc d)) = ι d)
    (off : Sp.Letter)
    (hres : ∀ d, ι d ≠ (Sp.shape off, Sp.side off, Sp.poly off)) :
    off ∉ Set.range enc := by
  rintro ⟨d, hd⟩
  exact hres d (by rw [← hd]; exact (hfaith d).symm)

attribute [local instance] Classical.propDecidable

/-- §7.2 HARD-CODED: the dictionary's `posLetter` — the encoded matched-prefix
letter when the whole prefix persists, the designated off-domain letter the
moment ANY prefix residual splits. -/
noncomputable def DictModel.posLetterD {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) : Sp.Letter :=
  if M.splitFree δ x then M.enc (M.pdata δ x) else M.offLetter

/-- (R4) at the model, verbatim M14 §2: the matched prefix persists
(split-free) AND realizes the base-side prefix data. -/
def DictModel.R4 {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) : Prop :=
  M.splitFree δ x ∧ M.pdata δ x = M.pdata 1 x

theorem DictModel.posLetterD_one {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (x : Pos) :
    M.posLetterD 1 x = M.enc (M.pdata 1 x) :=
  if_pos (M.splitFree_one x)

/-- **Item (ii), PROVED (finding 12): Lean `Stable` ⟺ (R4)** at the §7.2
`posLetter`. The proof consumes THREE `DictModel` rows (REVISION 1, pass-1
finding 5 — the earlier "exactly two" claim was wrong): `henc` (injectivity
on encoded prefix data) kills collisions in the stable direction, `hoff`
(off-domain letter outside the range) makes a split prefix visibly unstable,
and `splitFree_one` (via `posLetterD_one`) anchors the δ = 1 side — a
LOAD-BEARING dependency: without it both sides could read `offLetter`, and
`Stable` would hold while (R4) fails. -/
theorem DictModel.stable_iff_R4 {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) (δ : ℕ+) (x : Pos) :
    M.posLetterD δ x = M.posLetterD 1 x ↔ M.R4 δ x := by
  rw [M.posLetterD_one]
  unfold DictModel.posLetterD
  by_cases h : M.splitFree δ x
  · rw [if_pos h]
    constructor
    · intro he
      exact ⟨h, M.henc he⟩
    · rintro ⟨-, hd⟩
      rw [hd]
  · rw [if_neg h]
    constructor
    · intro he
      exact absurd ⟨M.pdata 1 x, he.symm⟩ M.hoff
    · rintro ⟨hsf, -⟩
      exact absurd hsf h

/-- DICT-1's (1) ⇒ (2) contrapositive shadow at the model: a split prefix is
never Stable (the ⇒ leg of the coincidence display, model level). -/
theorem DictModel.not_stable_of_not_splitFree {Sp : SpeciesSyntax} {Pos : Type}
    (M : DictModel Sp Pos) {δ : ℕ+} {x : Pos} (h : ¬ M.splitFree δ x) :
    M.posLetterD δ x ≠ M.posLetterD 1 x :=
  fun he => h ((M.stable_iff_R4 δ x).mp he).1

/-- The §7.2-conformance row tying a corpus `AlphabetData` instance to the
dictionary model: its `posLetter` IS the dictionary's. -/
def Encodes (p : ℕ) [Fact p.Prime] {Sp : SpeciesSyntax}
    (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos) : Prop :=
  ∀ (δ : ℕ+) (x : AD.Pos), AD.posLetter δ x = M.posLetterD δ x

/-- **The corpus-verbatim form: `AlphabetData.Stable` ⟺ (R4)** at any
§7.2-conforming instance (the displayed lemma the blueprint demanded; the
corpus `Stable` is imported, never re-transcribed). -/
theorem alphabetData_stable_iff_R4 (p : ℕ) [Fact p.Prime] {Sp : SpeciesSyntax}
    (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos) (hE : Encodes p AD M)
    (δ : ℕ+) (x : AD.Pos) :
    AlphabetData.Stable p AD δ x ↔ M.R4 δ x := by
  unfold AlphabetData.Stable
  rw [hE δ x, hE 1 x]
  exact M.stable_iff_R4 δ x

/-!
## §3. Item (iii) — Lemma 4's gcd(m, δ) = 1 characterization: arithmetic core PROVED, field inputs as named rows

M14 Lemma 4 (verbatim statement): "Same-keys transport setting: the re-based
read is of the same input data with the ℤ_p-tower keys viewed in O_δ[x] (the
natural matching the (a6)/(EQ-1) dictionary is owed to produce), so that
residual polynomials transport verbatim along F_k ↪ F_k·F_q. Let
m := d·g₁···g_k be the accumulated residue degree through x's letter. Then x
is δ-stable iff gcd(m, δ) = 1, and in that case F_j^{(δ)} = F_j·F_q for all
j ≤ k+1."

UPGRADE EXECUTED HERE (charge item (iii); scope corrected at REVISION 1,
pass-1 findings 2/6): M14 recorded Lemma 4 as "CONDITIONAL on the same-keys
transport identity … a REL.1/(a6)-dictionary fact, flagged, not proved".
This note IS that dictionary at the needed slice: §1 DEFINES the comparison
device ((i-b)) with the factor-correspondence matching (REVISION 2 —
key-free AND ledger-free), and STATES the transport identity as DICT-1
((2) ⇒ (3): at split-free prefixes the reconstructed run realizes the
verbatim-transported residuals) — a MATH lemma conditional on
[IN-R1]/[IN-U]/[IN-C], with [IN-C] (DICT-0, the key/valuation coincidence,
four clauses) itself DISPLAYED OPEN. The upgrade is therefore from "flagged, not proved"
to "stated with named inputs and a displayed open core" — NOT to "proved
outright". With the setting so supplied, Lemma 4's own induction is field
arithmetic from two pinned inputs:

(F1) Lidl–Niederreiter, *Finite Fields* (2nd ed., CUP 1997), Theorem 3.46:
an irreducible ψ of degree g over a finite field E stays irreducible over the
degree-δ′ extension E′ iff gcd(g, δ′) = 1; in general it factors into
gcd(g, δ′) conjugate irreducible factors of degree g/gcd(g, δ′). [PINNED]

(F2) compositum degrees of finite fields inside F̄_p:
[E·F_q : E] = δ / gcd(δ, [E : F_p]). [standard; e.g. Lidl–Niederreiter §2.1
subfield lattice]

MATH PROOF (M14's, re-run here — CONDITIONAL on (F1)/(F2) + DICT-1, which
is itself conditional on its four named inputs including the open [IN-C]):
induct up the prefix, writing m_1 := d, m_{j+1} := m_j·g_j (so the
base stage is the j = 0 step with current degree m_0 := 1 and "residual
degree" d over F_p). At each step the current field F_j has
[F_j : F_p] = m_j; by (F2) the compositum extension F_j·F_q/F_j has degree
δ/gcd(δ, m_j); by (F1) the transported ψ_j persists iff
gcd(g_j, δ/gcd(δ, m_j)) = 1. Direction (⇐): if gcd(m, δ) = 1 with
m = d·g₁···g_k then every m_j is coprime to δ, each relative degree is
exactly δ, and each gcd(g_j, δ) = 1 gives persistence. Direction (⇒): if all
stages persist then inductively gcd(m_j, δ) = 1 (base: persistence of the
degree-d residual over F_q forces gcd(d, δ) = 1 since the relative degree is
δ; step: relative degree δ again, so persistence forces gcd(g_j, δ) = 1 and
m_{j+1} stays coprime). At the first failure the residual splits ((F1)'s
factor count gcd > 1), the species letter changes (g drops), x is out of
domain. Hence: δ-stable ⟺ gcd(m, δ) = 1, and along the way
F_j^{(δ)} = F_j·F_q with relative degree δ. ∎

LEAN FACE (honesty display sharpened at REVISION 1, pass-1 finding 6). The
induction's entire arithmetic skeleton is proved UNCONDITIONALLY below
(`persistsFrom_iff`, `lemma4_arith` — no hypotheses at all, not even
positivity). But `lemma4_arith` is a statement about the recursively defined
predicate `persistsFrom` ONLY — it does NOT prove that actual residual
polynomials persist exactly when `persistsFrom` holds. That hard
field-theoretic identification enters as the NAMED HYPOTHESIS row
`l4_persist` of `GcdSlice` (reading `splitFree` through the
(F1)/(F2)-criterion chain), and DICT-1's transport identity as the NAMED
HYPOTHESIS row `coincide` — both ASSUMED, supplied by every instance, never
proved in this note. The chained theorems `splitFree_iff_coprime`,
`stable_iff_coprime`, `alphabetData_stable_iff_coprime` are then PROVED
CONDITIONALLY on those rows: the missing mathematical content sits inside
the hypotheses, displayed, and the earlier summary phrase "Lemma 4 PROVED as
a lemma of the dictionary" is retired for this conditional form.
-/

/-- (F2) as bookkeeping: the relative degree of the compositum,
[E·F_q : E] = δ / gcd(δ, [E : F_p]). -/
def relDeg (δ m : ℕ) : ℕ := δ / Nat.gcd δ m

theorem relDeg_eq_of_coprime {δ m : ℕ} (h : Nat.Coprime m δ) : relDeg δ m = δ := by
  have h' : Nat.gcd δ m = 1 := Nat.coprime_comm.mp h
  simp [relDeg, h']

/-- The per-stage persistence chain of Lemma 4's induction: at current
accumulated degree m, the next residual of degree g persists iff
gcd(g, relDeg δ m) = 1 (this is (F1) read at (F2)'s relative degree), then
recurse at m·g. `persistsFrom δ 1 (d :: gs)` is "the whole prefix persists"
(base stage = first entry, current degree 1). -/
def persistsFrom (δ : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | m, g :: gs => Nat.Coprime g (relDeg δ m) ∧ persistsFrom δ (m * g) gs

theorem coprime_list_prod_left_iff (δ : ℕ) :
    ∀ gs : List ℕ, Nat.Coprime gs.prod δ ↔ ∀ g ∈ gs, Nat.Coprime g δ
  | [] => by simp
  | g :: gs => by
    rw [List.prod_cons, Nat.coprime_mul_iff_left, List.forall_mem_cons]
    exact and_congr_right fun _ => coprime_list_prod_left_iff δ gs

/-- The induction of Lemma 4, arithmetic skeleton (UNCONDITIONAL): from a
coprime current degree, the persistence chain is exactly stagewise
coprimality to δ. -/
theorem persistsFrom_iff (δ : ℕ) :
    ∀ (gs : List ℕ) (m : ℕ), Nat.Coprime m δ →
      (persistsFrom δ m gs ↔ ∀ g ∈ gs, Nat.Coprime g δ)
  | [], m, _ => by simp [persistsFrom]
  | g :: gs, m, hm => by
    simp only [persistsFrom, List.forall_mem_cons]
    rw [relDeg_eq_of_coprime hm]
    constructor
    · rintro ⟨hg, htail⟩
      exact ⟨hg, (persistsFrom_iff δ gs (m * g) (Nat.Coprime.mul_left hm hg)).mp htail⟩
    · rintro ⟨hg, htail⟩
      exact ⟨hg, (persistsFrom_iff δ gs (m * g) (Nat.Coprime.mul_left hm hg)).mpr htail⟩

/-- **Lemma 4, arithmetic core (UNCONDITIONAL Lean)**: the full prefix (base
residual degree d, then residual degrees gs) persists iff
gcd(d·g₁···g_k, δ) = 1. -/
theorem lemma4_arith (δ d : ℕ) (gs : List ℕ) :
    persistsFrom δ 1 (d :: gs) ↔ Nat.Coprime (d * gs.prod) δ := by
  rw [persistsFrom_iff δ (d :: gs) 1 (Nat.coprime_one_left δ),
    List.forall_mem_cons, Nat.coprime_mul_iff_left, coprime_list_prod_left_iff δ gs]

/-- The gcd slice of the dictionary: per position, the prefix degree data
(d; g₁, …, g_k) the device transports, plus the two [M]-rows. `l4_persist`
is (F1)+(F2) read stagewise at the slice (Lidl–Niederreiter 3.46 + compositum
degrees, PINNED literature — texts not on file, §5 item 7); `coincide` is
the pdata-level SHAPE of DICT-1's (2) ⇒ (3) leg (argued in §1 as a math
lemma conditional on [IN-R1]/[IN-U]/[IN-C], the last displayed open). Both
are NAMED HYPOTHESIS rows: ASSUMED by every `GcdSlice`, proved nowhere in
this note (pass-1 findings 3/6); the carrier caveat on `DictModel` (`Data`
unconstrained) bounds what `coincide` can mean until H4-F6 supplies faithful
carriers. -/
structure GcdSlice {Sp : SpeciesSyntax} {Pos : Type} (M : DictModel Sp Pos) where
  /-- base residual degree d = [F₁ : F_p] at x's prefix -/
  dDeg : Pos → ℕ
  /-- the residual degrees g₁, …, g_k up x's prefix -/
  gDegs : Pos → List ℕ
  /-- [M] (F1)+(F2): split-freeness is the stagewise persistence chain -/
  l4_persist : ∀ (δ : ℕ+) (x : Pos),
    M.splitFree δ x ↔ persistsFrom (δ : ℕ) 1 (dDeg x :: gDegs x)
  /-- [M] DICT-1 (2) ⇒ (3) at pdata: split-free prefixes realize the
  transported (= base-side) prefix data -/
  coincide : ∀ (δ : ℕ+) (x : Pos), M.splitFree δ x → M.pdata δ x = M.pdata 1 x

/-- **Lemma 4 at the dictionary (item (iii), CONDITIONAL on this
`GcdSlice`'s [M]-rows)**: x's prefix is split-free iff gcd(m, δ) = 1 with
m = d·g₁···g_k. -/
theorem GcdSlice.splitFree_iff_coprime {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.splitFree δ x ↔ Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [G.l4_persist δ x, lemma4_arith]

/-- With the transport identity, (R4) collapses to split-freeness (the data
clause comes for free at split-free prefixes — DICT-1's content). -/
theorem GcdSlice.R4_iff_splitFree {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.R4 δ x ↔ M.splitFree δ x :=
  ⟨fun h => h.1, fun h => ⟨h, G.coincide δ x h⟩⟩

/-- **The full chain: Stable ⟺ gcd(m, δ) = 1** at the dictionary's
posLetter. -/
theorem GcdSlice.stable_iff_coprime {Sp : SpeciesSyntax} {Pos : Type}
    {M : DictModel Sp Pos} (G : GcdSlice M) (δ : ℕ+) (x : Pos) :
    M.posLetterD δ x = M.posLetterD 1 x ↔
      Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [M.stable_iff_R4 δ x, G.R4_iff_splitFree δ x, G.splitFree_iff_coprime δ x]

/-- **Corpus-verbatim: `AlphabetData.Stable` ⟺ gcd(m, δ) = 1** at any
§7.2-conforming instance carrying the gcd slice. -/
theorem alphabetData_stable_iff_coprime (p : ℕ) [Fact p.Prime]
    {Sp : SpeciesSyntax} (AD : AlphabetData p Sp) (M : DictModel Sp AD.Pos)
    (G : GcdSlice M) (hE : Encodes p AD M) (δ : ℕ+) (x : AD.Pos) :
    AlphabetData.Stable p AD δ x ↔
      Nat.Coprime (G.dDeg x * (G.gDegs x).prod) (δ : ℕ) := by
  rw [alphabetData_stable_iff_R4 p AD M hE δ x, G.R4_iff_splitFree δ x,
    G.splitFree_iff_coprime δ x]

/-!
## §4. Item (iv) — the worked F₉ instance, re-derived as the out-of-domain example

The recorded instance (M14 brief "Status in the corpus"; M14 attempt Lemma 4
status + T3): p = 3, base key x (so d = 1, F₁ = F₃), stage-1 read
(e₁, h₁) = (2, 1), residual ψ = z² + 1 over F₃ (g₁ = 2, irreducible since −1
is not a square mod 3), δ = 2.

Lemma-4 read: the accumulated residue degree through the stage-2 letter is
m = d·g₁ = 1·2 = 2, and gcd(m, δ) = gcd(2, 2) = 2 ≠ 1 — OUT OF DOMAIN. By
(F1) the transported residual splits into gcd(2, 2) = 2 conjugate factors of
degree 2/2 = 1 over F₉ = F₃·F_q: concretely F₉ = F₃[i] with i² = −1, and
z² + 1 = (z − i)(z + i). Under the REVISION-2 factor correspondence BOTH
branch positions are matched to the base position x: the ℤ_p-factor of f
routed through x (residue degree m = 2) factors over O_2 into
gcd(2, 2) = 2 irreducible factors, each lying over it and each routed
through one branch — the match's one-to-many shape realized concretely
(and why uniqueness is DICT-0(d)'s split-free-only clause, not a
definition). The realized letters at the two branch positions
have g = 1 ≠ 2: the species changes, `posLetterD` returns the off-domain
letter, `Stable` fails — consistent with `stable_iff_coprime` (gcd ≠ 1) and
with `not_stable_of_not_splitFree`. Per-branch continuation field is F₉ and
the per-branch full-height alphabet is F₉ (a_branch = 2 ≠ δ·a₁ = 4): interior
splitting genuinely redistributes alphabet dimensions — the §7.2 evidence,
re-derived. (Numerics: M14 T3 re-ran exactly these numbers, PASS.)

Lean witnesses: the split is compiled below over the CONCRETE model
F9 := F₃[z]/(z² + 1) (the root i and the factorization are theorems; that
z² + 1 is irreducible over F₃ — so that F9 IS the field F₉ — is classical
and stays prose). The Lemma-4/gcd reads and the N-K3 table seed are
decide-checked.

SCOPE OF THE LEAN WITNESSES (REVISION 1, pass-1 finding 8): the compiled
content of this section is EXACTLY `f9_residual_splits` (the factorization
over the concrete F9) and `f9_out_of_domain` (¬ `persistsFrom 2 1 [1, 2]`),
plus the decide-checked tables. NO `DictModel`, `GcdSlice`, reconstructed
classifier tower, or `AlphabetData` instance is constructed for this
example: ¬ `splitFree`, failure of corpus `Stable`, the realized branch
letters, `posLetterD` returning the off-domain letter, and the
alphabet-dimension redistribution (a_branch = 2 ≠ δ·a₁ = 4) are PROSE
predictions, conditional on the (R) package and the instance rows — not
Lean theorems. The "dictionary/out-of-domain realization" of the example is
therefore NOT formalized here; it waits on the H4-F1/H4-F6 instances.
-/

/-- F₉ modeled concretely: F₃[i] = F₃[z]/(z² + 1). -/
abbrev F9 : Type := AdjoinRoot (X ^ 2 + 1 : Polynomial (ZMod 3))

/-- i ∈ F₉, the adjoined root of z² + 1. -/
noncomputable def imag : F9 := AdjoinRoot.root (X ^ 2 + 1 : Polynomial (ZMod 3))

theorem imag_sq_add_one : imag ^ 2 + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : Polynomial (ZMod 3))
  simpa [imag] using h

theorem imag_sq : imag ^ 2 = -1 :=
  eq_neg_of_add_eq_zero_left imag_sq_add_one

/-- **The split witness**: over F₉ the transported residual z² + 1 factors,
z² + 1 = (z − i)(z + i) — the F₉ instance is out of domain exactly as Lemma
4's gcd read predicts. -/
theorem f9_residual_splits :
    (X - C imag) * (X + C imag) = (X ^ 2 + 1 : Polynomial F9) := by
  have h : (C imag) ^ 2 = C (-1 : F9) := by rw [← C_pow, imag_sq]
  calc (X - C imag) * (X + C imag) = X ^ 2 - (C imag) ^ 2 := by ring
    _ = X ^ 2 + 1 := by rw [h, map_neg, map_one, sub_neg_eq_add]

/-- The F₉ instance's Lemma-4 read: m = d·g₁ = 1·2 = 2, δ = 2,
gcd(2, 2) = 2 ≠ 1 — the persistence chain FAILS. -/
theorem f9_out_of_domain : ¬ persistsFrom 2 1 [1, 2] := by
  rw [show ([1, 2] : List ℕ) = 1 :: [2] from rfl, lemma4_arith]
  decide

/-- The in-domain contrast (M14 T1's δ = 3 run): same prefix, δ = 3,
gcd(2, 3) = 1 — the chain persists. -/
theorem f9_delta3_in_domain : persistsFrom 3 1 [1, 2] := by
  rw [show ([1, 2] : List ℕ) = 1 :: [2] from rfl, lemma4_arith]
  decide

/-!
### The N-K3 gcd-table seed

M14 T3's prediction family, now READ THROUGH THE PROVED LEMMA (the table
N-K3 consumes when it enumerates the n = 3 pack's realized δ > 1 pools; a
realized pool violating its row kills Route A's cheap match — blueprint §3.2).
Rows: (g, δ) with d = 1, flag = stable iff gcd(g, δ) = 1.

  (2, 2) split · (2, 3) stable · (2, 4) split · (2, 5) stable ·
  (3, 3) split · (3, 2) stable

plus the N-T4 two-stage row (d = 1, g₁ = 2, g₂ = 3, δ = 5: m = 6,
gcd(6, 5) = 1 — stable; M14's Test-4 tower).
-/

theorem nk3_gcd_table :
    ¬ Nat.Coprime 2 2 ∧ Nat.Coprime 2 3 ∧ ¬ Nat.Coprime 2 4 ∧
      Nat.Coprime 2 5 ∧ ¬ Nat.Coprime 3 3 ∧ Nat.Coprime 3 2 := by
  decide

theorem nk3_stability_table :
    ¬ persistsFrom 2 1 [1, 2] ∧ persistsFrom 3 1 [1, 2] ∧
      ¬ persistsFrom 4 1 [1, 2] ∧ persistsFrom 5 1 [1, 2] ∧
      ¬ persistsFrom 3 1 [1, 3] ∧ persistsFrom 2 1 [1, 3] := by
  simp only [lemma4_arith]
  decide

theorem nt4_two_stage_stable : persistsFrom 5 1 [1, 2, 3] := by
  rw [show ([1, 2, 3] : List ℕ) = 1 :: [2, 3] from rfl, lemma4_arith]
  decide

/-!
## §5. Consumption map, risk, and the honest residue

WHAT DOWNSTREAM UNITS READ FROM HERE — every consumer of "matched" now
carries the displayed hypothesis [IN-C] (REVISION 1; honesty direction:
consumers GAIN a hypothesis, nothing strengthens; REVISION 2 strengthens
the carried hypothesis to the four-clause DICT-0 and re-bases "matched" on
the factor correspondence). H4-M4 (the
(UB-X)(b)/(K3-δ) precision step) reads: the factor-correspondence matching
definition +
DICT-0/[IN-C] (§1), `stable_iff_coprime` (the refutation-pressure
quantifier: a realized pool whose accumulated residue degrees share a factor
with δ is UNSTABLE under this matching — a reading now conditional on the
`GcdSlice` rows and [IN-C]), and the risk note below. H4-M5 Route A reads:
DICT-1 (MATH-conditional, four named inputs, [IN-C] open) + `GcdSlice` (the
per-pool matched-prefix letter-equality obligation is exactly
`stable_iff_coprime`'s left-to-right reading at the pool's data, under the
same rows). H4-M1 reads nothing from here (this unit is downstream of M1's
(R1)-slice via [IN-R1] only; [IN-C]'s discharge route also runs through it).
The eventual Lean instance (fenced H4-F1/H4-F6) must supply `Encodes` (§7.2
conformance), the `henc`/`hoff` rows, NON-TRIVIAL carriers (`Data`/`pdata`
per the `DictModel` caveat, and `Pos` keyed so the §1 factor correspondence
is realized — the Lean carriers are factor-blind, REVISION 2), and the
`GcdSlice` rows — per M14 §7.2, an
instance with a coarser `posLetter` is NOT covered and is expected to admit
countermodels.

RISK (blueprint §2, displayed): H4-M2 is the SHARED GATE unit — both the
(H4a) retirement chain and the §3.2 adjudication consume this dictionary. A
hostile pass overturning DICT-1's named inputs or the §7.2 encoding ripples
into both.

HONEST RESIDUE (what this note does NOT prove; expanded at REVISION 1):
1. [IN-R1] — the device's (S1)–(S6)/D.0 package over O_δ at split-free
   prefixes: a face of REL.1's tower slice, H4-M1's charge. NAMED, open.
2. [IN-U] — MacLane-chain essential uniqueness: pinned to MacLane 1936 /
   Vaquié / GMN's Okutsu framework, exact printed theorem number FLAGGED for
   the LITUNIT roster. NAMED, literature. As quoted it yields ISOMORPHIC
   residue towers only and applies only to chains already realizing the same
   valuation — it does NOT supply valuation-equality or embedded-field
   equality (those are item 3's content; pass-1 findings 2/7).
3. [IN-C] = DICT-0 (§1) — THE headline residue of BOTH passes; restated at
   REVISION 2 at exactly consumer strength, FOUR clauses: (a) valuation
   coincidence at every matched position; (b) embedded fields
   F_j^{(δ)} = F_j·F_q for ALL j ≤ k+1 (range fixed, pass-2 finding 3);
   (c) next-read divisibility of the realized residuals into the
   transported one (consumed by the (1) ⇒ (2) leg TOGETHER WITH (b) —
   the divisibility comparison is meaningful only under (b)'s
   residue-field identification; audit corrected at REVISION 3, pass-3
   finding 1 — pass-2 critical 2: REVISION 1's bare Okutsu-equivalence
   form was WEAKER than this consumer, while the pre-REVISION-1
   literal-keys clause was STRONGER than any consumer); (d) uniqueness of
   the matched position at
   split-free prefixes (the canonicity content pass 2 found hidden behind
   "position class"). DISPLAYED OPEN; pre-REVISION-1 it was hidden inside
   the matched-position definition (circular), now a named lemma every
   consumer of "matched" carries as a hypothesis, with a two-directional
   consumer audit displayed in §1. ROUTE: GMN Okutsu-canonicity of
   per-factor OM data (+ the residual-of-a-factor divisibility staple for
   (c)) + [IN-R1]; the factor correspondence supplies the route's
   common-factor identification non-circularly; pins = LITUNIT duty.
4. The rows `l4_persist` ((F1) LN 3.46 + (F2) compositum degrees, read at
   the slice) and `coincide` (the pdata SHAPE of DICT-1 (2) ⇒ (3)) are
   [M]-rows of `GcdSlice`: ASSUMED by every instance, proved nowhere in
   Lean here; their MATH arguments are §3 and §1 above (themselves
   conditional per items 1–3), their Lean discharge waits on the H4-F6
   carriers.
5. NEITHER direction of DICT-1 is a Lean theorem (pass-1 finding 3): the
   three clauses have no Lean definition and the biconditional no Lean
   proof; §1's argument is MATH, conditional on the four named inputs.
6. Trivializable carriers (pass-1 finding 4): `DictModel.Data`/`pdata` are
   unconstrained — a singleton carrier satisfies every row and voids
   `coincide`/(R4)'s data clause. FACTOR-BLIND carriers (REVISION 2):
   `Pos` is likewise unconstrained, so the §1 factor correspondence is
   invisible in Lean. Faithful carriers (encoded stage
   tuples/degrees/side data; the device's realized read; positions keyed
   to realize the factor correspondence, `pdata` single-valued per
   DICT-0(d)) are an
   H4-F1/H4-F6 INSTANCE OBLIGATION, as is discharging `henc`/`hoff`.
7. Literature texts NOT on file (pass-1 finding 7): the printed statements
   of (F1) LN 3.46 and the (F2) compositum-degree source are not supplied
   here, so their attribution and printed generality are unchecked —
   LITUNIT-roster duty; the statements AS QUOTED suffice for §3's
   standalone arithmetic if assumed.
8. The FULL (a6) dictionary (all read fields, (a1)–(a5) frames, measure
   transport) is NOT built here — only the slice this group needs. (EQ-1)
   itself ("no species definition consumes q") stays H4-M1 step 8's walk.
9. Whether the O_δ classifier's REALIZED ledger contains a matched position
   with gcd(m, δ) > 1 at a given (n, p, δ) is the OPEN realization question
   of blueprint §3.2 — N-K3's empirical probe, nothing here settles it.
10. The F₉ example's dictionary-level realization is NOT formalized (pass-1
   finding 8): compiled = the split witness + the `persistsFrom` failure
   only; no instance, no `¬ splitFree`, no corpus `Stable` failure in Lean.

DECLARATION LIST (all in `LeanUrat.Scaffold.HDischarge.H4.Dict`, this file,
zero sorry): `DictModel`, `letter_unique_of_triple`,
`enc_injective_of_faithful`, `off_not_mem_range_of_reserved`,
`DictModel.posLetterD`, `DictModel.R4`, `DictModel.posLetterD_one`,
`DictModel.stable_iff_R4`, `DictModel.not_stable_of_not_splitFree`,
`Encodes`, `alphabetData_stable_iff_R4`, `relDeg`, `relDeg_eq_of_coprime`,
`persistsFrom`, `coprime_list_prod_left_iff`, `persistsFrom_iff`,
`lemma4_arith`, `GcdSlice`, `GcdSlice.splitFree_iff_coprime`,
`GcdSlice.R4_iff_splitFree`, `GcdSlice.stable_iff_coprime`,
`alphabetData_stable_iff_coprime`, `F9`, `imag`, `imag_sq_add_one`,
`imag_sq`, `f9_residual_splits`, `f9_out_of_domain`, `f9_delta3_in_domain`,
`nk3_gcd_table`, `nk3_stability_table`, `nt4_two_stage_stable`.

AXIOM FOOTPRINT (checked 2026-08-01, external `#print axioms` run over all
key theorems): Lean-core only — {propext, Classical.choice, Quot.sound};
the arithmetic core (`lemma4_arith`, `f9_out_of_domain`, the tables, the
grammar lemmas) is even choice-free: {propext, Quot.sound}. REVISIONS 1–3
are all comment/docstring-and-prose-only folds — no Lean statement or
proof term changed; gate re-run green after each (see §6).

STATEMENT-FENCE RECORD: the blueprint has NO §L Lean spec for H4-M2 (it is a
§M math-note unit); the charge text is transcribed verbatim in the header
above and each item is fulfilled at its stated strength. The corpus carriers
(`SpeciesSyntax`, `AlphabetData`, `AlphabetData.Stable`) are consumed by
IMPORT, verbatim, never re-transcribed or weakened; every new declaration
here is dictionary-layer vocabulary of this unit, colliding with nothing
(fresh namespace `LeanUrat.Scaffold.HDischarge.H4.Dict`).
-/

/-!
## §6. REVISION record

REVISION 1 (2026-08-08; fold of hostile pass 1,
`H4M2_pass1_2026-08-08.md`, verdict CRITICAL — 5 critical + 3 gap, ALL 8
findings folded):

1. CRIT — the matched-position definition included "same prefix keys",
   presupposing the key-level coincidence the dictionary must prove
   (circular). FOLDED (the headline): the definition is now KEY-FREE
   (matching by the invariant data both classifiers independently compute,
   §1) [SUPERSEDED at REVISION 2: pass 2 found THIS replacement not
   well-defined; the standing definition is the factor correspondence —
   see the REVISION 2 record below]; the coincidence is the new lemma
   DICT-0, DISPLAYED OPEN as [IN-C].
   Checked against the material on file: NOT provable from [IN-U] (which
   presupposes same-valuation — circular); route named (GMN
   Okutsu-canonicity of per-factor OM data + [IN-R1], LITUNIT pin owed).
   Every downstream consumer of "matched" re-scoped to GAIN the displayed
   hypothesis (§5).
2. CRIT — DICT-1's main implication did not follow from its two advertised
   inputs (same-valuation premise assumed; [IN-U] gives isomorphisms, not
   embedded equalities; (F1) silently used). FOLDED: FOUR named inputs
   ([IN-R1], [IN-U], [IN-C], [IN-F1]); the same-valuation premise and the
   embedded-field upgrade both live in [IN-C], displayed; (F1) named as
   [IN-F1] at the (1) ⇒ (2) leg; "two named inputs" retired.
3. CRIT — DICT-1 was called proved though it is no Lean lemma. FOLDED:
   re-labeled MATH-conditional everywhere (header, §1, §3); the Lean face
   displayed as HYPOTHESIS SHAPE (`coincide`/`l4_persist` rows supplied by
   instances, neither biconditional direction established in Lean).
4. CRIT — the Lean `coincide` row is trivializable (`Data` an unconstrained
   `Type`, singleton + constant `pdata` satisfies every row). FOLDED:
   trivializable-carrier caveat displayed on `DictModel`; faithful carriers
   re-classified as an H4-F1/H4-F6 instance obligation (§5 item 6).
5. CRIT — `stable_iff_R4` consumes a third substantive row
   (`splitFree_one`, logically essential), contradicting "exactly two
   hypotheses". FOLDED: "exactly two" retired in header/§2/docstring; the
   dependency displayed load-bearing with the both-off-domain
   counterexample; `henc`/`hoff` noted as still-assumed rows and the corpus
   wiring's extra `Encodes` assumption displayed.
6. GAP — "Lemma 4 PROVED as a lemma of the dictionary" overclaimed (the
   finite-field content is assumed via `l4_persist`). FOLDED: §3
   header/LEAN FACE/VERDICT re-scoped — arithmetic core (`lemma4_arith`)
   unconditional, field content in named hypothesis rows.
7. GAP — cited literature cannot support the load-bearing uses from the
   supplied material alone. FOLDED: §5 items 2/7 — (F1)/(F2) texts not on
   file, pins = LITUNIT duty; [IN-U]'s quoted strength bounded honestly.
8. GAP — the F₉ dictionary/out-of-domain realization is not formalized.
   FOLDED: §4 SCOPE display — compiled content = split witness +
   `persistsFrom` failure ONLY; instance-level claims marked prose.

LEAN DELTA: comment/docstring/prose-only; no statement or proof term
changed. Gate `lake env lean notes/openmath/H4M2_dict_attempt.md` re-run
GREEN at REVISION 1, zero sorry, footprint unchanged (Lean-core).

REVISION 2 (2026-08-08; fold of hostile pass 2,
`H4M2_pass2_2026-08-08.md`, verdict CRITICAL — 2 critical + 1 gap + 1
confirmation, ALL findings folded):

1. CRIT — the REVISION-1 key-free match (numerical prefix ledger: stage
   tuples (e_j, h_j, g_j)_{j≤k} + base degree d) was NOT WELL-DEFINED:
   distinct branches of the same input can share identical ledgers, so
   either ledger-EQUALITY defines the match (presupposing the
   numerical-coincidence half of DICT-1(1)) or the ledger merely names the
   base position (determining no counterpart) — an unresolved
   correspondence-and-canonicity assumption hidden behind "position
   class". FOLDED (the headline): the match is redefined by the FACTOR
   CORRESPONDENCE (§1) — matched = routing a common irreducible factor of
   f itself; f's factorizations are classifier-independent data, each
   O_δ-factor lies over a unique ℤ_p-factor, and each run's factor-routing
   is its own data ((i-a) consumed / accepted base theory) — a
   well-defined RELATION presupposing NO coincidence, honestly one-to-many
   (§4's F₉ branches realize it); uniqueness at split-free prefixes
   extracted as the OPEN clause DICT-0(d) (the hidden canonicity, now
   displayed); the ledger match RETIRED with both failing readings on
   record (§1). Lean carriers are factor-blind (`Pos` unconstrained) —
   displayed on `DictModel` and folded into the instance obligation.
2. CRIT — [IN-C]'s REVISION-1 Okutsu-equivalence form was WEAKER than the
   retired literal-keys presupposition where it mattered: the (1) ⇒ (2)
   leg's "the reconstructed stage-j₀ read sees the same residual ψ_{j₀}"
   was supplied by NO named input (valuation equality + Okutsu equivalence
   + field equality do not give residual-operator compatibility). FOLDED:
   DICT-0/[IN-C] restated at EXACTLY consumer strength — four clauses
   (a) valuations, (b) embedded fields (j ≤ k+1), (c) next-read
   divisibility, (d) split-free uniqueness — with the two-directional
   CONSUMER AUDIT displayed in §1: (a)/(b)/(d) serve (2) ⇒ (3), (c) serves
   (1) ⇒ (2) (its exact consumed fragment; "sees the same residual"
   retired for the divisibility step) [AUDIT TALLY CORRECTED at REVISION 3,
   pass-3 finding 1: the (1) ⇒ (2) leg consumes (b) AND (c) — (c)'s
   divisibility comparison is meaningful only under (b)'s identification],
   `l4_persist` consumes none, and NO
   consumer uses literal transported-key equality (so it is asserted
   nowhere: the old clause OVERSHOT, REVISION 1's UNDERSHOT — both
   mismatches closed). Both DICT-1 proof legs re-cited clause-by-clause;
   pass-1 finding 2's "not fully folded" disposition thereby CLOSED.
3. GAP — DICT-0's field clause carried no explicit range while DICT-1(3)
   is quantified through k+1 (the terminal field is load-bearing at the
   next residual read). FOLDED: clause (b) quantified "for ALL j ≤ k+1",
   and the (1) ⇒ (2) leg now displays where the k+1 instance is consumed
   (the stage-j₀ read at the sub-prefix through j₀ − 1).
4. CONFIRMED, no change owed — pass 2 re-affirmed the [IN-U] circularity
   adjudication at its quoted strength ([IN-U] cannot supply DICT-0's
   premise; a per-factor canonicity result would, and would itself need a
   non-circular common-factor identification — which the REVISION-2
   factor correspondence now supplies by definition). Pass-2 dispositions
   of pass-1 findings 3–8: all confirmed folded, no action.

LEAN DELTA (REVISION 2): comment/docstring/prose-only; no statement or
proof term changed. Gate `lake env lean notes/openmath/H4M2_dict_attempt.md`
re-run GREEN at REVISION 2, zero sorry, footprint unchanged (Lean-core).

REVISION 3 (2026-08-08; fold of hostile pass 3,
`H4M2_pass3_2026-08-08.md`, verdict GAPS-ONLY — 1 gap + 4 confirmations,
ALL findings folded):

1. GAP — the DICT-0 CONSUMER AUDIT misclassified clause (b): the display
   said the (1) ⇒ (2) leg "consumes (c) ONLY", but clause (c)'s
   divisibility comparison is meaningful only after (b)'s identification
   of the reconstructed residue field with F_{j₀}·F_q — the leg consumes
   (b) AND (c), exactly as the proof leg itself already cited ("under
   [IN-C](b)'s identification"). FOLDED (display-only, NO strength change
   — the four-clause DICT-0/[IN-C] hypothesis already supplies both):
   audit corrected at its §1 statement, at the (1) ⇒ (2) proof-leg tag,
   at §5 item 3, and at the §6 REVISION-2 record (bracketed correction).
   DICT-1 is NOT invalidated.
2. CONFIRMED — the factor correspondence's "lies over" is WELL-DEFINED:
   O_δ a DVR ⇒ O_δ[x] a UFD (irreducibles prime) [Stacks 0BC1], so each
   O_δ[x]-irreducible factor of f divides some ℤ_p-factor; distinct
   ℤ_p-factors stay relatively prime over Frac(O_δ) [Stacks 09GY], so
   exactly one. FOLDED: argument + references + the coprimality
   qualification (gcd sense, NOT comaximality) into §1's WELL-DEFINEDNESS
   display.
3. CONFIRMED — no audited consumer silently requires a functional branch
   selection outside the split-free locus (DICT-0(d) supplies the single
   position exactly where DICT-1(3)/`pdata`/(2) ⇒ (3) need it;
   `posLetterD` collapses off-locus ambiguity to `offLetter`). FOLDED
   into §1's WELL-DEFINEDNESS display.
4. CONFIRMED — full proof-leg replay, modulo finding 1: (2) ⇒ (3)
   consumes (a)/(b)/(d) + [IN-R1] + [IN-U]; (3) ⇒ (1) no additional
   clause; (1) ⇒ (2) consumes (b)/(c) + [IN-F1]; `l4_persist` none;
   literal transported-key equality unused. FOLDED: the §1 audit now
   displays this exact tally.
5. CONFIRMED — disposition audit: both predecessor matching definitions
   correctly retired; pass-2's gaps (next-read compatibility = clause (c),
   field range j ≤ k+1, split-free uniqueness = clause (d)) supplied;
   factor-blind Lean carriers honestly fenced (H4-F1/H4-F6). No fresh
   circularity or missing premise. No action owed.

LEAN DELTA (REVISION 3): comment/docstring/prose-only; no statement or
proof term changed. Gate `lake env lean notes/openmath/H4M2_dict_attempt.md`
re-run GREEN at REVISION 3, zero sorry, footprint unchanged (Lean-core).

COUNTER (gate: hostile pass ×1): pass 1 = CRITICAL (folded at REVISION 1);
pass 2 = CRITICAL (folded at REVISION 2); pass 3 = GAPS-ONLY (folded
here). Clean counter 0/1 — the final clean hostile pass runs on THIS
revision.
-/

end LeanUrat.Scaffold.HDischarge.H4.Dict
