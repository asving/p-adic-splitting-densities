#!/usr/bin/env python3
"""S-0 STATEMENT LEDGER — the simplification campaign's byte-tracking instrument.

Spec: docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md S5 (unit S-0). For every NAMED
STATEMENT (THEOREM/LEMMA/COROLLARY/COR/PROPOSITION/PROP/DEFINITION/DEF block with
its label) in the 26-text accepted corpus (blueprint S1 corpus map), this tool:
  (a) extracts the statement's display text span (line range in the note);
  (b) records note path + line range + md5 of the NORMALIZED statement text +
      the note's last-touching commit;
  (c) emits the human ledger doc (docs/STATEMENT_LEDGER_2026-08-10.md) — one row
      per statement (label, note, lines, md5-8, grade) — and a machine baseline
      (verification/openmath/statement_ledger_baseline.json).

THE INSTRUMENT: `statement_ledger.py --check` re-extracts at the working tree and
compares against the baseline BY (note, label): any md5 mismatch (CHANGED) or
missing label (DELETED) => exit 1 with a diff. New labels (ADDED) are allowed and
reported as info. This is the "a simplification never weakens a statement"
tripwire (blueprint S5.3 item 3): consumption checks require md5-identical
absorbed statements against this ledger.

NORMALIZATION (declared): blockquote markers ('> ' prefixes) are stripped at
extraction time as block syntax; then whitespace-collapse ONLY (all runs of
whitespace, including newlines, -> one space; strip). Any single-token change to
a statement changes its md5.

EXTRACTION RULE (S0-v1, deterministic; capture starts at column 0 only):
  form A  **KW ...                and  > **KW ...
  form B  > * **KW ...            (quote-bullet; sole corpus instance: W-12.C)
  form C  **(i) [KW ...           and  > **(i) [KW ...   (W12 verdict items)
KW in {THEOREM, LEMMA, COROLLARY, COR, PROPOSITION, PROP, DEFINITION, DEF}.
Span runs from the start line until the FIRST of: next statement start; a line
opening with *Proof/**Proof (optionally quoted); [plain spans] a markdown
heading or a '---' rule; [quoted spans] the end of the '>' block, a W12
roman-numeral item marker '> **(ii) ', or '> **GRADE'; a 120-line cap (cut back
to the last blank line; flagged T). Spans may OVER-capture trailing non-statement
prose (inline proofs, notation brackets) — conservative for a tripwire: the pin
fires on any change inside the span. Known skipped classes are enumerated in the
ledger doc's ambiguity record (no universal claims).

Usage:
  python3 statement_ledger.py --build [--force]   # write baseline + ledger doc
  python3 statement_ledger.py --check             # tripwire; exit 1 on change
"""

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
NOTES_DIR = os.path.join("lean", "notes", "openmath")
BASELINE = os.path.join(HERE, "statement_ledger_baseline.json")
LEDGER_DOC = os.path.join(REPO, "docs", "STATEMENT_LEDGER_2026-08-10.md")
EXTRACTOR_VERSION = "S0-v1"
MAXLINES = 120

# The 26-text accepted corpus (blueprint S1 corpus map, in its order) with the
# per-note grade AS DECLARED THERE (25 ACCEPTED 2/2; JD0 PROVED grade, sub-bar).
# Grade provenance is the blueprint's corpus map, not a per-note regex: the
# notes' own status headers are heterogeneous free text (see ledger doc S3).
G = "ACCEPTED 2/2"
CORPUS = [
    ("LIFTCORNER_2026-08-08.md", G),
    ("GRTW2_PROOF_2026-08-08.md", G),
    ("GRTJA_PROOF_2026-08-08.md", G),
    ("GRTJB_PROOF_2026-08-08.md", G),
    ("GRTJC_PROOF_2026-08-08.md", G),
    ("WELDMASTER_2026-08-08.md", G),
    ("JD0_PROOF_2026-08-08.md", "PROVED (machine 68,523/0; sub-bar)"),
    ("SIGMALAW_PROOF_2026-08-08.md", G),
    ("W11_PROOF_2026-08-08.md", G),
    ("W12_PROOF_2026-08-08.md", G),
    ("HMENU3_PROOF_2026-08-08.md", G),
    ("HEX3_PROOF_2026-08-08.md", G),
    ("GENIND_PROOF_2026-08-08.md", G),
    ("GENH4_PROOF_2026-08-08.md", G),
    ("GENHN_PROOF_2026-08-08.md", G),
    ("HE3_PROOF_2026-08-08.md", G),
    ("HE6_PROOF_2026-08-08.md", G),
    ("HE7_PROOF_2026-08-08.md", G),
    ("HE6R1_RECON_2026-08-08.md", G),
    ("HETOW_RECON_2026-08-09.md", G),
    ("GENTOW1_PROOF_2026-08-09.md", G),
    ("GENTOW2_PROOF_2026-08-09.md", G),
    ("GENTOW3_PROOF_2026-08-09.md", G),
    ("GENTOW4_PROOF_2026-08-09.md", G),
    ("GENTOW5_PROOF_2026-08-09.md", G),
    ("GENTOW6_PROOF_2026-08-09.md", G),
]

KW = r"(?P<kw>THEOREM|LEMMA|COROLLARY|PROPOSITION|DEFINITION|COR|PROP|DEF)"
RE_A = re.compile(r"^(?P<q>> ?)?\*\*" + KW + r"\b")
RE_B = re.compile(r"^(?P<q>> ?)\* \*\*" + KW + r"\b")
RE_C = re.compile(r"^(?P<q>> ?)?\*\*\((?:[ivxIVX]+|\d+)\)\s*\[" + KW + r"\b")
RE_PROOF = re.compile(r"^(> ?)?\*{1,2}Proof")
RE_HEADING = re.compile(r"^#{1,6} ")
RE_HR = re.compile(r"^---")
RE_W12_ITEM = re.compile(r"^> ?\*\*\([ivx]+\) ")
RE_GRADE = re.compile(r"^> ?\*\*GRADE")
RE_LABEL_TOK = re.compile(r"\s+([^\s(\[\]]+)")
# Audit regexes for the honesty record (skipped classes; NOT captured as rows):
RE_AUDIT_BULLET = re.compile(r"^[*+-] \*\*" + KW + r"\b")  # plain-bullet recaps
RE_AUDIT_NAMED = re.compile(r"^(> ?)?\*\*\(")  # bold named displays "(X)..."


def match_start(line):
    """Return (match, form) if line opens a statement block, else (None, None)."""
    for form, rx in (("C", RE_C), ("B", RE_B), ("A", RE_A)):
        m = rx.match(line)
        if m:
            return m, form
    return None, None


def extract_label(line, m):
    """Label = keyword + first token after it (trailing punctuation stripped),
    or None when unlabeled (next char opens a paren/bracket or a period)."""
    kw = m.group("kw")
    rest = line[m.end("kw"):]
    t = RE_LABEL_TOK.match(rest)
    if not t:
        return kw, None
    tok = t.group(1).rstrip(".,:;*~—–-")
    tok = tok.strip("*")
    if not tok:
        return kw, None
    return kw, tok


def dequote(line):
    return re.sub(r"^> ?", "", line)


def normalize(span_lines, quoted):
    lines = [dequote(l) for l in span_lines] if quoted else list(span_lines)
    return " ".join("\n".join(lines).split())


def extract_note(path):
    """Return (statements, audit) for one note file."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    n = len(lines)
    starts = []
    for i, line in enumerate(lines):
        m, form = match_start(line)
        if m:
            starts.append((i, m, form))
    stmts = []
    for i, m, form in starts:
        quoted = bool(m.group("q"))
        truncated = False
        j = i + 1
        while j < n:
            line = lines[j]
            if match_start(line)[0] is not None:
                break
            if RE_PROOF.match(line):
                break
            if quoted:
                if not line.startswith(">"):
                    break
                if RE_W12_ITEM.match(line) or RE_GRADE.match(line):
                    break
            else:
                if RE_HEADING.match(line) or RE_HR.match(line):
                    break
            if j - i >= MAXLINES:
                truncated = True
                break
            j += 1
        end = j  # exclusive
        if truncated:
            for k in range(end - 1, i, -1):
                if not lines[k].strip():
                    end = k
                    break
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1
        span = lines[i:end]
        kw, tok = extract_label(lines[i], m)
        text = normalize(span, quoted)
        stmts.append({
            "kw": kw, "tok": tok, "form": form,
            "start": i + 1, "end": end,  # 1-indexed inclusive range
            "truncated": truncated,
            "struck": "~~" in "\n".join(span),
            "md5": hashlib.md5(text.encode("utf-8")).hexdigest(),
            "text_norm": text,
        })
    # deterministic labels: keyword+token; unlabeled/duplicates numbered in order
    seen = {}
    for s in stmts:
        base = f"{s['kw']} {s['tok']}" if s["tok"] else f"{s['kw']} (unlabeled)"
        seen[base] = seen.get(base, 0) + 1
        s["label"] = base if seen[base] == 1 else f"{base} #{seen[base]}"
    audit = {"bullet_recaps": [], "named_display_count": 0}
    captured = {i for i, _, _ in starts}
    for i, line in enumerate(lines):
        if RE_AUDIT_BULLET.match(line) and i not in captured:
            audit["bullet_recaps"].append((i + 1, line.strip()[:90]))
        if RE_AUDIT_NAMED.match(line) and i not in captured:
            audit["named_display_count"] += 1
    return stmts, audit


def git(*args):
    return subprocess.run(["git"] + list(args), cwd=REPO, check=True,
                          capture_output=True, text=True).stdout.strip()


def build_snapshot():
    snap = {"extractor_version": EXTRACTOR_VERSION,
            "head_commit": git("rev-parse", "HEAD"),
            "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "notes": {}}
    audits = {}
    for fname, grade in CORPUS:
        rel = os.path.join(NOTES_DIR, fname)
        path = os.path.join(REPO, rel)
        stmts, audit = extract_note(path)
        commit = git("log", "-n1", "--format=%h", "--", rel)
        snap["notes"][fname] = {"path": rel, "commit": commit, "grade": grade,
                                "statements": stmts}
        audits[fname] = audit
    return snap, audits


def write_ledger_doc(snap, audits):
    L = []
    total = sum(len(v["statements"]) for v in snap["notes"].values())
    trunc = sum(1 for v in snap["notes"].values()
                for s in v["statements"] if s["truncated"])
    unlab = sum(1 for v in snap["notes"].values()
                for s in v["statements"] if not s["tok"])
    L.append("# STATEMENT LEDGER — 2026-08-10 (unit S-0)")
    L.append("")
    L.append("**Unit:** S-0, the simplification campaign's byte-tracking instrument")
    L.append("(SIMPLIFICATION_BLUEPRINT_2026-08-10.md S5.1). One row per NAMED")
    L.append("STATEMENT (THEOREM/LEMMA/COROLLARY/PROPOSITION/DEFINITION block with its")
    L.append("label) in the 26-text accepted corpus (blueprint S1 corpus map).")
    L.append("**Instrument:** `verification/openmath/statement_ledger.py --check`")
    L.append("re-extracts and compares md5s against the sealed baseline")
    L.append("(`statement_ledger_baseline.json`); exit 1 with a diff on ANY changed or")
    L.append("deleted statement; additions allowed. This is blueprint S5.3 item 3's")
    L.append('tripwire: "a simplification never weakens a statement" — consumption')
    L.append("checks must display absorbed statements md5-identical to this ledger.")
    L.append("")
    L.append(f"**Baseline:** repo HEAD `{snap['head_commit'][:12]}`, generated")
    L.append(f"{snap['generated_at']}, extractor {snap['extractor_version']}.")
    L.append(f"**Totals:** {total} statements over 26 notes; {unlab} unlabeled")
    L.append(f"(numbered deterministically); {trunc} truncated at the 120-line cap.")
    L.append("")
    L.append("**Normalization (declared):** blockquote markers stripped as block")
    L.append("syntax at extraction; then whitespace-collapse ONLY. A single-token")
    L.append("change to any statement changes its md5 and fires the tripwire.")
    L.append("**Grade provenance:** the blueprint S1 corpus map (25 texts ACCEPTED 2/2;")
    L.append("JD0 PROVED grade, machine 68,523/0, sub-bar) — the notes' own status")
    L.append("headers are heterogeneous free text and are NOT parsed for grades.")
    L.append("**Flags:** T = span truncated at cap; S = span contains struck (~~)")
    L.append("text; U = unlabeled (label assigned by deterministic numbering).")
    L.append("")
    L.append("## S1. The ledger (one row per statement)")
    for fname, _g in [(f, g) for f, g in CORPUS]:
        note = snap["notes"][fname]
        st = note["statements"]
        L.append("")
        L.append(f"### {fname} — commit `{note['commit']}`, grade: {note['grade']}, "
                 f"{len(st)} statements")
        L.append("")
        L.append("| # | label | lines | md5-8 | flags |")
        L.append("|---|---|---|---|---|")
        for k, s in enumerate(st, 1):
            flags = "".join(["T" if s["truncated"] else "",
                             "S" if s["struck"] else "",
                             "U" if not s["tok"] else ""]) or "—"
            L.append(f"| {k} | {s['label']} | {s['start']}–{s['end']} | "
                     f"`{s['md5'][:8]}` | {flags} |")
    L.append("")
    L.append("## S2. Extraction rule (S0-v1, verbatim from the instrument)")
    L.append("")
    L.append("Capture starts at column 0 only, three forms: (A) `**KW ...` and")
    L.append("`> **KW ...`; (B) `> * **KW ...` (quote-bullet; sole corpus instance")
    L.append("THEOREM W-12.C); (C) `**(i) [KW ...` / `> **(i) [KW ...` (W12 verdict")
    L.append("items). KW in {THEOREM, LEMMA, COROLLARY, COR, PROPOSITION, PROP,")
    L.append("DEFINITION, DEF}. Span ends at the FIRST of: next statement start; a")
    L.append("line opening `*Proof`/`**Proof` (optionally quoted); [plain] a heading")
    L.append("or `---` rule; [quoted] end of the `>` block, a `> **(ii) ` roman item")
    L.append("marker, or `> **GRADE`; 120-line cap (cut to last blank line, flag T).")
    L.append("Labels: keyword + first token after it (trailing punctuation stripped);")
    L.append("unlabeled and duplicate labels numbered in document order.")
    L.append("")
    L.append("## S3. Ambiguity & skip record (honest; enumerative, no universal claims)")
    L.append("")
    L.append("1. **Over-capture is possible and accepted.** Spans may include")
    L.append("   trailing non-statement prose (inline `*Proof.*` inside a statement's")
    L.append("   own paragraph, notation brackets, correction brackets) up to the next")
    L.append("   terminator — e.g. LIFTCORNER's unlabeled THEOREM span carries its")
    L.append("   inline proof and the [r4, F4-5] notation bracket. Conservative for a")
    L.append("   tripwire: edits there also fire. Line ranges let a human adjudicate.")
    L.append("2. **Skipped class — plain-bullet keyword recaps** (consumption/")
    L.append("   hypothesis-set lists, not statement displays), enumerated:")
    for fname, _g in CORPUS:
        for ln, txt in audits[fname]["bullet_recaps"]:
            L.append(f"   - {fname}:{ln} `{txt}`")
    L.append("3. **Skipped class — bold NAMED displays without a keyword opener**")
    L.append("   (outside S-0's THEOREM/LEMMA/COR/DEF scope by the blueprint's own")
    L.append("   definition): e.g. `> **W-12 (the general-n assembly).**`,")
    L.append("   `> **(J-D1) THE FAITHFULNESS HANDOFF.**`, GRTW2's `> **(CLAUSE 1..3)`")
    L.append("   blocks, SIGMALAW's `**(Σ-DEF)`/`**(U-REC)` definitional displays, and")
    L.append("   per-clause `**(a)**...` markers. Audit count of `**(`-opening bold")
    L.append("   lines not captured, per note (size of this residue class):")
    counts = ", ".join(f"{f.split('_')[0]} {audits[f]['named_display_count']}"
                       for f, _ in CORPUS if audits[f]["named_display_count"])
    L.append(f"   {counts}.")
    L.append("   These are pinned only when inside a captured span; a statement whose")
    L.append("   ONLY display is such a form has no ledger row.")
    L.append("4. **Headings are not rows.** Section headings that restate labels")
    L.append("   (`## S4. THEOREM GENTOW2-A ...`) are not captured; the bold block")
    L.append("   below them is.")
    L.append("5. **Baseline matching is by (note, label), not line numbers** — dated")
    L.append("   appends that shift line numbers do NOT fire the tripwire; only text")
    L.append("   changes inside a span do. If an append INSERTS a same-labeled")
    L.append("   statement before an existing one, deterministic numbering shifts and")
    L.append("   the tripwire fires — conservative, adjudicate by hand.")
    L.append("6. **Parenthetical name-parts are cut from labels** (the token stops at")
    L.append("   `(`): observed instances at baseline — `THEOREM W-11` (displayed as")
    L.append("   `W-11(n = 2)`), `LEMMA GENHN-T #2` (displayed `GENHN-T(b)′`, GENHN")
    L.append("   L1127), `LEMMA HE6R1-2 #2` (displayed `HE6R1-2(b)(c)`, HE7 L1337).")
    L.append("   The md5 pins the FULL display text either way.")
    L.append("7. **Quoted keyword-opening RECAPS are captured as rows** (conservative")
    L.append("   over-inclusion; they pin cross-note quotes, which S5.3's record rule")
    L.append("   wants stable anyway): observed at baseline — HE7 L294 (`> **LEMMA")
    L.append("   HE6R1-2** when the block is PROPER ...`, a recap of HE6R1's export)")
    L.append("   and HE7 L307 vs L994 (`THEOREM HE7.D` summary display + full")
    L.append("   statement => rows HE7.D and HE7.D #2, both pinned).")
    L.append("")
    L.append("## S4. Teeth record (instrument validated before seal, 2026-08-10)")
    L.append("")
    L.append("Three momentary working-tree mutations, each restored via git checkout")
    L.append("immediately after the check (notes verified unmodified afterward):")
    L.append("")
    L.append("1. Single-token change inside THEOREM W-12.D's span (W12 L267,")
    L.append("   `REDUCTION` -> `REDUCTIONX`): CHANGED reported with diff, **exit 1**.")
    L.append("2. Whitespace-only rewrap inside the same span (W12 L268-269 spacing):")
    L.append("   **exit 0**, GREEN — the declared whitespace-collapse tolerance.")
    L.append("3. Label rename (JD0 L49, `LEMMA J-D0.` -> `LEMMA J-D0X.`): DELETED")
    L.append("   (LEMMA J-D0) + ADDED-as-info (LEMMA J-D0X), **exit 1** — deletions")
    L.append("   fire, additions alone do not.")
    L.append("")
    L.append("Verdict-of-record runs are appended below (S5) after the seal commit;")
    L.append("a --force rebuild regenerates S1-S4 only, so S5 appends must be")
    L.append("re-attached if the ledger is ever legitimately re-pinned.")
    L.append("")
    with open(LEDGER_DOC, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L) + "\n")
    return total


def cmd_build(force):
    if os.path.exists(BASELINE) and not force:
        print("Baseline exists; --build refused without --force (the baseline is a"
              " sealed instrument; re-pinning is legitimate only at S-unit"
              " acceptance events).", file=sys.stderr)
        return 2
    snap, audits = build_snapshot()
    with open(BASELINE, "w", encoding="utf-8") as fh:
        json.dump(snap, fh, indent=1, ensure_ascii=False)
    total = write_ledger_doc(snap, audits)
    print(f"BUILT: {total} statements over {len(CORPUS)} notes at HEAD "
          f"{snap['head_commit'][:12]}")
    print(f"  baseline: {os.path.relpath(BASELINE, REPO)}")
    print(f"  ledger:   {os.path.relpath(LEDGER_DOC, REPO)}")
    return 0


def cmd_check():
    with open(BASELINE, encoding="utf-8") as fh:
        base = json.load(fh)
    if base["extractor_version"] != EXTRACTOR_VERSION:
        print(f"FATAL: baseline extractor {base['extractor_version']} != "
              f"instrument {EXTRACTOR_VERSION}; rebuild required.")
        return 1
    changed, deleted, added = [], [], []
    for fname, _g in CORPUS:
        rel = os.path.join(NOTES_DIR, fname)
        path = os.path.join(REPO, rel)
        bnote = base["notes"].get(fname)
        if bnote is None:
            print(f"WARN: {fname} not in baseline (corpus list drifted?)")
            continue
        if not os.path.exists(path):
            for s in bnote["statements"]:
                deleted.append((fname, s["label"], "NOTE FILE MISSING"))
            continue
        cur, _ = extract_note(path)
        cmap = {s["label"]: s for s in cur}
        bmap = {s["label"]: s for s in bnote["statements"]}
        for label, bs in bmap.items():
            cs = cmap.get(label)
            if cs is None:
                deleted.append((fname, label, f"was L{bs['start']}–{bs['end']}"))
            elif cs["md5"] != bs["md5"]:
                diff = "\n".join(difflib.unified_diff(
                    [bs["text_norm"]], [cs["text_norm"]],
                    fromfile=f"baseline {bs['md5'][:8]}",
                    tofile=f"current  {cs['md5'][:8]}", lineterm=""))
                changed.append((fname, label, diff))
        for label in cmap:
            if label not in bmap:
                added.append((fname, label))
    for fname, label, diff in changed:
        print(f"CHANGED: {fname} :: {label}\n{diff}\n")
    for fname, label, where in deleted:
        print(f"DELETED: {fname} :: {label} ({where})")
    for fname, label in added:
        print(f"ADDED (allowed): {fname} :: {label}")
    nbase = sum(len(v["statements"]) for v in base["notes"].values())
    print(f"CHECK: {nbase} baseline statements; {len(changed)} changed, "
          f"{len(deleted)} deleted, {len(added)} added.")
    if changed or deleted:
        print("TRIPWIRE FIRED: a statement changed or vanished. A simplification"
              " never weakens a statement (blueprint S5.3).")
        return 1
    print("GREEN: every baseline statement byte-stable (normalized).")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--build", action="store_true")
    g.add_argument("--check", action="store_true")
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()
    sys.exit(cmd_build(args.force) if args.build else cmd_check())


if __name__ == "__main__":
    main()
