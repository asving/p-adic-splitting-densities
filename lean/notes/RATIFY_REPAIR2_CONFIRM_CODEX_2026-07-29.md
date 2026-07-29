# Repair round-2 Codex confirm (2026-07-29): FLAG 2/1 — D4 wiring CONFIRMED (hne = honest minimal repair; note-faithful RHS = the option-level form, queued); D2 narrowed but the singleton-realizer bypass remains; S5 MovesS-side shape done, enforcement point = the V-side identification (V7-9)

I’ll inspect the actual round-2 sources and repository-wide consumers, with special attention to whether the new predicates constrain the intended semantics rather than merely excluding the single counterexample. I’ll also check the note’s empty-prefix incidence display against the supplied excerpt and nearby local note material if present.

The round-2 repairs are not fully ratified.

- **CRITICAL — D2 narrows, but does not eliminate, the semantic bypass.**

  The literal round-1 claim that *any* nonzero-lift policy qualifies is now false: `support_forced` excludes arbitrary nonzero polynomials, and `realizes_unique` excludes `Realizes := (t ≠ 0)`.

  But `OffsetPPin` still permits:
  > `Realizes ν t := t = pol.liftOf ν`

  for a policy whose recentering lift is any nonzero monomial in the forced congruence class. Totality and uniqueness are then automatic, and `support_forced` holds, while the prescribed digit values, weight equation, and actual offset-P formula may all be wrong. In particular, the support law requires only a **subset** of the progression, not the formula’s prescribed coefficients or complete slot data.

  Thus `CD_canonical` can still certify a support-compatible but noncanonical policy. The specific `t ≠ 0` counterexample is killed; the underlying arbitrary-predicate/singleton-realizer bypass remains.

- **GAP — D4 is correctly wired, but `mult_sum` no longer states the note’s empty-prefix incidence identity.**

  The dispatch is now genuinely installed in:
  > `def Presented.event ... := if ... then Set.univ else ...`  
  > `def Presented.mult ... := if ... then 1 else ...`

  and `eventO`/`multO` are deleted. D11b’s hne-free case split is correct, and the nonempty consumers pass `hne` correctly.

  Adding:
  > `(hne : (P : ShapePrefix).reads ≠ [])`

  is the honest minimal repair for the existing `PrefIdx`-indexed RHS, because that RHS is incorrectly zero at the empty shape. It is not the note-faithful incidence statement. L5 explicitly includes the empty prefix as the base of L6, and the quoted note data say `Pref(∅) = {∅}` with its unique fiber equal to the full box. Hence the note’s empty-shape display has:
  \[
  \sum_x \mathrm{mult}_{\varnothing}(x)=\#\mathrm{Box}
  \]
  on the left and the cardinality of the unique empty-prefix fiber, also `#Box`, on the right—not zero.

  D14c separately recovers the empty mass law, so this is a coverage gap rather than parallel semantics.

  The manifest is also stale:
  > `"statement": "mult_sum (S) ..."`  
  > `"hypothesis_fields": "none"`

  despite the new `hne`.

- **CRITICAL — S5’s local premise-use bypass is fixed, but the CL-6 semantic/consumer bypass remains.**

  The new `_countFactored` proofs genuinely consume `tcount_val` and `scount_val`, and the old `_counted` wrappers are deleted. However:
  > `tCount : ... → ℚ → ℕ`

  remains unconstrained by the actual CTS/[1] event-side table count. Choosing `countT = 1`, `tCount = 1`, and absorbing the genuine count into another factor can still satisfy `CountFactored` and the new degree law.

  Moreover, the established `ksub`, `ksub_eval`, and `ksub_pool` chain remains available without `PolyGeomLaws`; no downstream CL-6/CTS consumer shown here is retyped to require a `CountFactored` conclusion. The assertion:
  > “MUST route through this”

  is therefore prose, not enforced by the consumer types. Scheduling the missing identification for V7–9 records the debt but does not resolve S5 at the present CL-6 consumer.

**FLAG (2 CRITICAL / 1 GAP)**