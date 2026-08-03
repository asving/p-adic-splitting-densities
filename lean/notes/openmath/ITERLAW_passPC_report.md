# ITERLAW-PC — Codex content pass 1 on ITERLAW_2026-08-08.md (hostile, quote-and-classify)

Charge: /tmp/openmath/ITERLAW_PC_charge.txt (59,009 bytes; appendices = full note + sealed falsifier + full DITER_RESTATE). Run detached, window-label dating per standing disclosure; git chain authoritative. Division of labor: content leg only (Fable PE leg carries execution). Orchestrator verification: finding 1 CONFIRMED against sources (DITER_RESTATE:33 'E₂ := e₀e₁ > 1' vs ITERLAW:45 unconstrained + :81 'verbatim' claim); finding 2 textually confirmed (F8 tests only simultaneous-translation blocks). Acceptance counter: 0 (pass 1 NOT-CLEAN). Remedies queued for the errata unit after PE returns: (1) honest scope bracket replacing the verbatim claim; (2) supplementary mixed-block COR-4 test in a NEW file — sealed falsifier untouched.

## Codex output (verbatim)

I’m checking the algebraic chain and the static falsifier tie independently, treating execution as out of scope as instructed.
1. [CRITICAL] “* Read 0: e₀ ≥ 1, h₀ ≥ 1, gcd(e₀,h₀) = 1; …” / “* Read 1: e₁ ≥ 1, h₁ ≥ 1, gcd(e₁,h₁) = 1; …” / “This is DITER_RESTATE §S2's (ITER-LAW) display verbatim, on the class its setting pins” — DITER_RESTATE §S2 explicitly assumes `E₂ := e₀e₁ > 1`, whereas the proof note permits `e₀=e₁=1` and never imposes `E₂>1`. Thus its theorem silently strengthens the statement to an excluded degenerate tower while claiming a verbatim statement match. Under the prescribed statement-match rule, this is critical, even though the extra case may itself be algebraically harmless.

2. [GAP] “    t1 = table(W1)
    for name, win in ((\"W2\", W2), (\"W3\", W3)):
        t = table(win)
        for k in t1:
            note(\"F8\")
            if t[k] != t1[k]:
                viol(\"F8\", T.tag, f\"rep-dependence {name} at {k}\")” — F8 compares `W2×W2` and `W3×W3` only with `W1×W1`, so it tests simultaneous translation of both representatives. COR-4 asserts independence under changing either representative separately; the mixed tables `W2×W1`, `W1×W2`, `W3×W1`, and `W1×W3` are not compared with the base table. Other families sample one mixed block but do not perform the representative-equality comparison, so F8 does not fully test its named corollary.

ITERLAW-PC FINDINGS: 1 critical, 1 gaps
VERDICT: NOT-CLEAN
