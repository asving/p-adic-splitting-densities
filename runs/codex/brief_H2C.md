# CODEX BRIEF H2C — the slope-h≥2 deep-primary recentring: design the statement currency

You are the mathematical designer for the ONE structural gap the Lean campaign flagged as
"statement currency doesn't exist yet" (unit CP2's loud flag; unit PSL4's item-2 obstruction).

CONTEXT (read these files in the repo):
- runs/wave-c/verdict_PSL4.md (§item 2: the (h,1) axis at h ≥ 2 — "the h > 1 key ring is not
  a DVR"; the general-(h,d) instruments landed except this)
- runs/wave-c/verdict_CP2.md (the consolidated FGMN cite package; the h≥2 step deliberately
  NOT smuggled in)
- runs/wave-c/verdict_PSL3.md + leanfinal/Uniformity/ChapI/IFCG43.lean §1-2 (the Eisenstein
  h=1 cascade: AdjoinRoot(X^{e'}+cπ) is a complete DVR — the h ≥ 2 analogue AdjoinRoot(X^{e'}+cπ^h)
  is NOT a DVR (its π-valuation has gcd content h), which is the obstruction)
- runs/wave-c/verdict_MFL.md (remainder 1: the Bézout-ring currency question)

THE QUESTION: for a pure face of slope h/e' with gcd(h,e') = 1 and h ≥ 2, the classical OM
recentring adjoins a root of the key x^{e'} = c·π^h. The right integral model over a complete
DVR O: (a) the Bézout/valuation-ring closure of O[x]/(x^{e'} − cπ^h) (the integral closure IS
a DVR since gcd(h,e')=1 — the valuation extends uniquely with value group (1/e')ℤ); (b) its
explicit presentation (the standard trick: y = x^a·π^{−b} with a·h − b·e' = ±1 gives the
uniformizer — Bezout on (h,e')); (c) the coordinate lattice over it (the analogue of PSL2's
eis_root_pow_dvd_mk_iff: divisibility ceilings on the O-coordinates).

DELIVERABLE (write to runs/codex/H2C_design.md): the precise Lean-ready statement family —
(1) the presentation of the h≥2 recentring ring as an explicit AdjoinRoot/quotient with a
proof sketch that it is a complete DVR (via the Bezout uniformizer y); (2) the coordinate
lattice statement; (3) the dev-transform/cellTransport analogue's exact form; (4) which of
the landed h=1 proofs (IFCG39 §3-5) generalize verbatim vs need new arguments — a per-lemma
table; (5) any faithfulness caveats if a cite would be cleaner than a proof. Rigor: every
claim either proved-in-sketch or flagged as a gap. Do NOT write Lean code — the statement
design is the deliverable.
