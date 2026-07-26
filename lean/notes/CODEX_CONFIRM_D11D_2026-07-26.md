The D-11d repairs are genuine. I find no critical error or gap in the D.3(e)(ii) → D.8 → D.11 chain.

The dichotomy is exhaustive and correctly consumed. D.3(e)(ii) proves both directions needed:

> “Pinning d_γ(B) = X is solvable iff X ∈ 𝔸(γ) — an off-alphabet pin EMPTIES the locus”

and, for admissible pins,

> “a locus cut by k block equations whose pinned values lie in their ATTAINABLE alphabets 𝔸^{(1)}, …, 𝔸^{(k)} has mass Π_i |𝔸^{(i)}|^{−1} × (free mass)”

Joint admissibility follows because the blocks are disjoint by (ii.3), while (ii.4) is unitriangular with unit diagonal. Thus there is no third case involving individually admissible but jointly incompatible pins.

The transport scoping is now correct. D.8 limits the “never fires” assertion precisely:

> “D.3(e)(ii)'s off-alphabet guard never fires on a nonempty stratum.”

D.11 likewise restricts the automatic-admissibility claim to:

> “LANDING CYLINDERS OF ACTUAL STRATA”

and handles unrelated cylinders separately:

> “for any other cylinder the dichotomy applies (admissible: the product; inadmissible: empty, mass 0)”

This does not assert surjectivity onto abstract residual patterns; actual landing pins are witnessed by members of the source locus and transported through the established bijection.

For the verifier’s instance \(e_1=h_1=1,\ g_1=2,\ \gamma=0\), the corrected text gives \(j_0=0\) and

\[
\gamma_0=0,\qquad \gamma_1=-1.
\]

Since \(\mathcal W_1=\mathbb Z_{\ge0}\), one gets \(I(0)=\{0\}\), not \(\{0,1\}\). Hence

\[
\mathbb A(0)=u(0)F_1,\qquad |\mathbb A(0)|=|F_1|,
\]

so the block has \(\log_p|F_1|\) leaf digits and an admissible pin contributes \(|F_1|^{-1}\), rather than the erroneous \(|F_2|^{-1}=|F_1|^{-2}\). A value outside \(u(0)F_1\) gives the empty locus. This is exactly the intended shallow-height behavior.

The full chain closes:

- D.3(e)(ii) constructs the actual attainable alphabet, proves the block bijection and separates distinct equations.
- D.8 translates actual parent digit cylinders through the global unitriangular development map and explicitly avoids abstract-window surjectivity.
- D.11 invokes the product only on alphabet-admissible cylinders and assigns mass zero to the complementary case.

The D-11/b/c repairs remain intact. In particular, the scale repair still reads

> “γ* := γ at the top space”

and uses the undivided slot height

> “γ_i := γ* − (j₀ + i·e_k)·h_k”

while the D-11b attainable-block repair still declares:

> “that summand is ABSENT — d_{γ_i} is undefined there, no block β(B_j, γ_i) exists, and no free zero-filled coordinate may be invented for it”

Finally, the D-11c per-height correction remains explicit:

> “PER-HEIGHT, not uniform”

and

> “STRICTLY SMALLER at shallow heights”

with D.11 consistently using \(|\mathbb A(\gamma)|^{-1}\), not the full residue-field size.

**Count: 0 CRITICAL, 0 GAP.**

D-11d genuinely fixes both D-11c residues: the admissible/inadmissible alternatives are exhaustive under the proved disjoint-block and unitriangular structure, and automatic admissibility is asserted only for landing cylinders arising from nonempty actual strata. The verifier’s shallow \(e_1=h_1=1,\ g_1=2,\gamma=0\) example now yields the one-block alphabet and correct mass. **CLEAN.**
