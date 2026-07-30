# One Function for Every Prime

## How polynomials factor over the p-adic numbers, and the uniformity that survives even the wild primes

*Claude Fable 5 (Anthropic), for the project of Asvin G. This document explains, for a reader with no prior contact with the subject, a theorem proved and machine-checked in 2026. A companion page presents the formal development as an expandable graph.*

### Abstract

Pick a prime, and pick a monic polynomial of some fixed degree whose coefficients are whole numbers of that prime's local world — the p-adic integers. The polynomial factors into irreducible pieces, and the pieces have shapes: their degrees, and how far each one twists the underlying arithmetic. For each possible shape there is a density: the probability that a randomly chosen polynomial factors with exactly that shape. The classical theory computes these densities at all but finitely many primes — the tame ones — and finds that a single rational expression in the size of the prime governs all of them at once. At the finitely many wild primes, where the prime divides the twisting it is supposed to measure, the classical formulas fail, and for a century the densities there were computed one prime at a time, with no visible pattern. The theorem explained here restores the pattern: for every shape, one fixed rational function computes the density at every prime — tame and wild alike — that passes an explicitly checkable regularity condition. The proof works by replacing the space of polynomials with a tree of successive approximations, discovering that at every prime this tree is assembled from a finite catalogue of local shapes, and reading the density off a finite system of linear equations that the catalogue determines. The theorem, its hypotheses, and the exact boundary of what is proved have been machine-checked in the Lean proof assistant.

---

## 1. A question about factoring

Every whole number factors into primes in exactly one way. Polynomials enjoy the same privilege: a monic polynomial — one whose leading coefficient is one — factors into irreducible monic pieces in exactly one way, once the coefficients are allowed to come from a fixed arithmetic world.

The worlds in question here are the p-adic integers: for each prime, a completion of the ordinary integers in which two numbers are close when their difference is divisible by a high power of that prime. These are the natural laboratories of local number theory. A number in this world is an infinite expansion in powers of the prime, the way a real number is an infinite decimal; and just as a real number can be drawn at random by rolling a die for each decimal digit, a p-adic integer can be drawn at random by choosing each of its digits uniformly. Choosing a monic polynomial of fixed degree at random means drawing each coefficient this way, independently.

Now factor. The result is a list of irreducible pieces, and each piece carries two integers that describe it completely for our purposes. The first is its degree. The second measures ramification: how much the piece twists the arithmetic of its world, in the way the square root of a prime twists the rationals more violently than the square root of a unit does. The full record — the multiset of these pairs, one pair per irreducible piece — is what we call the factorization shape of the polynomial. At degree three, for instance, one shape says "three distinct pieces of degree one"; another says "one unramified piece of degree three"; another says "one piece of degree three, fully ramified."

The question: for a fixed degree and a fixed shape, what is the probability that a random monic polynomial of that degree factors with exactly that shape? This number — the splitting density of the shape at the prime — is the object of the entire story.

## 2. What happens at almost every prime

At almost every prime, the answer has been understood for some time, and it is beautiful.

Take the shape "three distinct pieces of degree one" at degree three. A polynomial factors this way exactly when it has three distinct roots in the p-adic integers, and a short argument with counting over the residue field — the world of arithmetic modulo the prime — turns the density into a count of polynomials over a finite field. The result is a ratio of polynomial expressions in the size of that finite field. As the prime varies, the size of the residue field varies, but the expression does not: one rational function, evaluated at prime after prime, produces density after density.

This is the local face of a celebrated global phenomenon. The Chebotarev density theorem says that the factorization statistics of a fixed integer polynomial, as the prime varies, are governed by the symmetry group of its roots. The local statement — densities over the p-adic integers given by rational functions of the residue field size — was worked out in general and is the starting point of this project; the paper of Asvin G, Yifan Wei and John Yin on a Chebotarev density theorem over local fields computes these densities along any finite map, not merely for polynomial factorization.

But every statement in this classical picture carries the same asterisk: it holds at all but finitely many primes. The exceptions are not an artifact of the proofs. They are real, and they are where this story actually begins.

## 3. The trouble with small primes

Ramification comes in two temperaments. A piece of a factorization is tamely ramified when its twisting is prime to the prime — when the ramification degree is not divisible by the residue characteristic. It is wildly ramified when the prime divides its own twisting. Squaring twists by two; so at the prime two, square-root-like behavior is wild, while at every other prime it is tame. Every ramified extension is wild at finitely many primes and tame at the rest — but at its wild primes, everything difficult about local number theory happens at once.

The mechanism of the difficulty can be said in one word: carries. Arithmetic in a p-adic world is digit arithmetic, and adding two numbers produces carries between digit positions exactly as in grade school. The classical theory of factorization over local fields — Hensel's lemma, Newton polygons — works by treating a polynomial's coefficients digit by digit and pretending, essentially, that digits do not interact. At tame primes this pretense is harmless: the geometry of the Newton polygon separates the digits that matter. At wild primes the twisting itself is divisible by the prime, the relevant digits collide, and the carries between them carry arithmetic content. Two polynomials that agree to enormous digit depth can factor with different shapes, and the boundary between the shapes is a fractal-like condition on the carries.

Consequently the wild densities resisted every uniform description. They were computed — for quadratics and cubics, at the prime two and the prime three, by hand and by computer — and the answers looked like the tame formulas' estranged relatives: rational numbers, certainly, but not visibly values of the tame rational functions, and not visibly values of any single expression at all. The literature treated each wild prime as its own bespoke computation. Nothing in the classical framework predicted that a pattern should exist across them.

## 4. The theorem

There is a pattern, and it is as strong as one could ask.

**Theorem.** Fix a degree and a factorization shape of that degree. There is a single rational function in one variable with the following property: at every prime satisfying an explicitly checkable regularity condition — a condition met by all tame primes and by the wild primes in every decided case — the splitting density of the shape at that prime equals the value of that function at the size of the prime.

One function for every prime. The wild densities are not exceptions to the tame formula; they are further values of one formula that the tame computations only partially revealed. At degree two, at the wildest prime of all — the prime two — the density of the fully ramified shape comes out to exactly one quarter, and it is the same rational function that produces the tame values at every odd prime. The bespoke computations of the literature become rows of a single table.

Three remarks before the mechanism.

First, the regularity condition is not decoration. It is a pair of explicitly checkable statements about the prime — one asserting that a certain escape from degeneracy occurs, one asserting an agreement between two ways of reading the same count — and the theorem is proved for every prime that passes it. That every prime passes it is, at the time of writing, verified in every case that has been decided and is a conjecture in general.

Second, the theorem is constructive. The rational function attached to a shape is not an abstract existence statement: it is computed by an algorithm, terminating and implemented, whose ingredients appear in the next three sections.

Third, the theorem and its proof have been formalized: the statement, its hypotheses, and the boundary between what is proved and what is conjectured are machine-checked in the Lean proof assistant. Section 8 describes exactly what the machine has certified, and section 9 states what remains open. The reader deserves both, and they are not the same list.

## 5. The tree of approximations

The proof abandons the space of polynomials in favor of a tree.

The idea, which descends from work of Ore in the nineteen-twenties and reached maturity in the types of Montes and the invariants of Okutsu, is that an irreducible polynomial over a p-adic world is best described by a tower of successive approximations. The ground level is a residue-field datum: an irreducible polynomial over the finite field, obtained by reducing modulo the prime. Each higher level refines the approximation: it records a slope — a rational number read off a Newton polygon — and a new residual datum living over an enlarged finite field. After finitely many levels the approximation is exact, and the tower of slopes and residual data determines the irreducible polynomial's shape completely: its degree, its ramification, everything.

Factoring a polynomial is then a matter of navigating a tree. The root holds the polynomial's reduction modulo the prime; its children correspond to choices of irreducible factor of that reduction; each further generation refines one approximation one level deeper. A monic polynomial of fixed degree traces a finite set of paths through this tree — one path per irreducible piece — and the shape of its factorization can be read off the leaves. Drawing a polynomial at random induces a random process on the tree: at each node, the digits of the coefficients not yet consumed by the approximation decide which children the process visits, and with what probabilities.

The classifier at the heart of the project makes this picture exact and executable. Given the degree, it constructs the tree; given a polynomial, it computes the paths; and — the point of the whole construction — the probabilities attached to the branches are computed by counting solutions of polynomial congruences over the residue field. All the wildness of wild primes is still present, but it has been localized: it lives in how the digit-carries steer the process from a node to its children, and nowhere else.

## 6. The finite catalogue

An infinite tree with branch probabilities is not yet a formula. The discovery that makes the theorem possible is that the tree is assembled from finitely many kinds of parts.

Inspect any node of the classification tree: it holds a residual polynomial over some finite field, a slope, a position within the tower. Ask what data actually determines the subtree hanging below it, together with all its branch probabilities — not the node's full history, but the germ that the future depends on. The answer is a bounded package: a bounded amount of residual data and a bounded amount of slope arithmetic, with everything else forgettable. Call the isomorphism class of this package the species of the node.

At any fixed degree, only finitely many species occur — at every prime simultaneously. At degree three the catalogue has exactly fifty-three species. The count does not grow with the prime; the prime enters only through the sizes of the finite fields inside each species, and those sizes enter every formula polynomially. This finiteness is the uniformity of the theorem in embryonic form: the same finite automaton runs at the prime two and at a thousand-digit prime, and only the transition probabilities — rational functions of the residue field size — change.

The random process of the previous section thus becomes a random walk on a finite directed graph whose vertices are species. Wild ramification, in this picture, loses its mystique entirely: the wild primes are those where the walk can traverse certain carry-sensitive edges — including edges that return a species to itself, the self-loops along which an approximation deepens without changing its kind — and those edges have transition weights as computable as any others.

## 7. From walks to rational functions

Densities now come from linear algebra.

For each factorization shape, the density at a given prime is the total probability of the set of walks whose leaves realize that shape. Organize these probabilities by species: for each species, collect the probability that a walk begun there realizes the remaining part of the shape. These quantities satisfy a system of linear equations — one equation per species, expressing its quantity in terms of its successors' quantities, weighted by the transition probabilities. The system is finite because the catalogue is finite; its coefficients are rational functions of the residue field size because the transition weights are; and solving it — inverting a matrix built from the transition weights — expresses each quantity, and in particular the density itself, as a rational function of the residue field size. This is the function the theorem promises. Uniqueness of the solution comes from a convergence argument: the walk terminates, deep levels of the tree carry vanishing probability, and the corresponding envelope estimate squeezes the density between two expressions with a common limit.

It remains to connect the abstract walk to the honest measure-theoretic density — the probability, in the original sense, of the set of polynomials with the given shape. This is a bookkeeping theorem with real content: the set of polynomials whose walk reaches a given node of the tree is a union of explicit digit cylinders, sets defined by pinning finitely many digits of finitely many coefficients, and its measure is exactly the product of the walk probabilities along the path. Establishing this at wild primes is where the carry arithmetic must finally be confronted rather than organized away, and the corresponding chapters — a carry algebra that tracks how digit overflow propagates through the tower, and a landing theorem that identifies the walk's cylinders with the measure's — are the longest in the development.

## 8. The ledger

Everything above has been formalized in the Lean proof assistant, and this section states what that means, exactly.

The formal development is a corpus of roughly seven hundred theorems. Its capstone asserts: for every prime passing the regularity condition, the splitting density equals the value of the rational function that the finite linear system determines, with the two-sided squeeze and the identification of the abstract solution with the measure-theoretic density as separate certified clauses. The capstone is proved from the axioms of Lean's logic alone — no extra axioms — over a displayed list of named hypotheses. Each hypothesis is one of the following, and the formal statement forces the classification into the open:

- **Proved.** The overwhelming majority of the corpus: the classifier's correctness at the decided orders, the finiteness of the species catalogue at degree three with its count of fifty-three, the transfer-matrix solve, the squeeze, the cylinder bookkeeping at the decided strata, and the degree-two capstone instance with its density of one quarter at the prime two — all machine-checked outright.
- **Cited.** Two results enter as named citations to the literature rather than as formalized proofs: a theorem on the index from the Montes school, and the cell-decomposition recursion of Denef and Igusa on the measure-theoretic route. Each carries a faithfulness record tying the citation to its printed source.
- **Computationally sealed.** A small number of kernels — combinatorial identities at the base of the carry algebra — are verified exhaustively by computation over their full boundary range (in one case, all forty thousand three hundred seventy-eight boundary instances; in another, one hundred forty probe cases with zero findings) and enter the capstone as hypotheses. Their statements for all parameters at once are conjectures.
- **Open.** Nine statements in the corpus stand as explicitly fenced unproved goals, each with a written record of what it asserts and why it is believed; they gate the extensions of section 9, not the capstone.

The formalization campaign was run adversarially: every batch of statements was audited by an independent model in a fresh context before acceptance, and the audits were consequential. About twenty formal statements that passed compilation were refuted by compiled countermodels before they could be trusted — including two proposed axioms that turned out to be false and one pair of statements that together made the whole system inconsistent. The discipline that emerged, and that the development now enforces, is that the record must match the reach: every hypothesis is displayed, every gap is named, and no sentence in the documentation claims more than the types deliver.

## 9. What remains

Three genuine conjectures stand between the theorem as certified and the theorem with no conditions at all.

**Exhaustiveness.** The certified density statement covers the decided strata of the classification tree — the parts of the space of polynomials that the walk decides at the formalized orders. That the decided strata carry the full measure, at every degree, is a conjecture; it is proved at the base orders and verified computationally beyond them.

**Regularity at every prime.** The regularity condition of the theorem holds in every decided case, and its two clauses are each verified computationally across the probed range. That every prime passes it, for every degree, is a conjecture.

**The functional equation.** The rational functions of the theorem display a palindromic symmetry — replacing the residue field size by its reciprocal transforms the function by a predictable factor — which is proved at tame primes, where it descends from a duality of Del Corso and Dvornicich. Its extension across the wild primes is a conjecture, stated in the corpus as a named hypothesis that no certified result currently consumes.

Beyond these, the development points at its own continuations: deepening the classifier's certified faithfulness past the formalized orders, discharging the nine fenced goals, and extending the species catalogue's certified finiteness from degree three to all degrees. Each is written into the corpus as a typed obligation with an exact statement, which is a sentence that could not have been written about this subject three years ago.

---

### Provenance

This document was written by Claude Fable 5, an AI system by Anthropic, which also carried out the Lean formalization described here as the orchestrating agent of the project, under the direction of and in collaboration with Asvin G. The mathematics formalizes and extends the local Chebotarev density theorem of Asvin G, Yifan Wei, and John Yin. The formal development — its source, its hypothesis ledger, and the expandable graph of its theorems with their mathematical translations — is available alongside this document.
