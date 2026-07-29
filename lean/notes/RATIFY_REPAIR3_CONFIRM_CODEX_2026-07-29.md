# Repair round-3 Codex confirm (2026-07-29): FLAG 1 MAJOR / 0 — D11a mult_sum_opt CONFIRMED; D2 adjudicated at the vocabulary boundary (residual-level pin = the expressible maximum per Codex itself; canonicality deferred to the NAMED HC-1 discharge; CD_canonical docstring made explicit)

I’ll verify the round-3 definitions and their consumers in the actual sources, then test the key typing claim: whether two distinct lifts can share the newly pinned `(inC, w, R)` data while one is not the note’s offset-P construction. I’ll also check the empty-shape proof against the concrete `PrefIdx`, `mult`, and cardinality definitions.

The round-3 repair is not fully ratified.

- **MAJOR — D2 still permits a singleton-realizer bypass inside the named residue.**

  The new law correctly excludes lifts with the wrong observable center data:

  > `inC ν.σ.Φ t ∧ ν.σ.w t = ν.σ.w ν.σ.Φ ∧ ν.σ.R t = ...`

  Thus the exact confirm-2 example—an arbitrary forced-support monomial with the wrong weight or residual—is excluded.

  However, the diff explicitly leaves inside `Realizes`:

  > “WHICH center realizer among the `(w, R)`-equal ones”

  That is precisely enough room for the singleton construction to survive. A policy may choose a noncanonical `(w,R)`-equal center realizer with different lower-stage slot realizers and define:

  > `Realizes ν t := t = pol.liftOf ν`

  Uniqueness is automatic; the other four laws only check nonzeroness, support, and the top-level `inC/w/R` projection. Nothing requires the chosen element to use the note’s prescribed recursive `t_k`. Higher-weight or otherwise top-residual-invisible changes are not rejected by these fields.

  Consequently, `CD_canonical` can still accept an `OffsetPPin` for a policy that satisfies the D.10 center-realizer interface but is not the note’s one offset-P lift rule. Naming that freedom “HC-1 residue” documents the missing constraint; it does not enforce it.

  The residual-level law is the strongest faithful projection currently expressible using only the exported `Node`/`Stage` vocabulary. The full per-slot recursive law does not appear directly statable without exporting the lower-stage expansion/realizer data. But that vocabulary limitation means canonicality remains deferred: the present type can establish “center-realizer-compatible,” not the note’s unique canonical policy.

- **D11a — confirmed.**

  `mult_sum_opt` correctly includes the empty shape:

  > `if reads = [] then Nat.card (Box p m) else ...`

  The empty proof uses `mult_empty_shape`, so the left side is the sum of `1` over the full box, hence `#Box`. The nonempty branch delegates to `mult_sum S hP`. This is faithful to L5’s unique empty-prefix fiber, and the manifest now accurately records both theorem forms.

**FLAG (1 MAJOR / 0 MINOR)**