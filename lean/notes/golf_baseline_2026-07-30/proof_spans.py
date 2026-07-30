import re, glob
IDENT = r"[A-Za-z_][A-Za-z0-9_.!?" + "'" + r"]*"
decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*(theorem|lemma)\s+(" + IDENT + r")")
# a "boundary" is any top-level declaration/namespace/section/end starting at col 0-ish
bound_re = re.compile(r"^\s{0,2}(theorem|lemma|def|structure|inductive|instance|abbrev|namespace|section|end|class|@\[|/--)\b")
spans = []
for f in glob.glob("LeanUrat/MovesV/*.lean"):
    lines = open(f).readlines()
    n = len(lines)
    starts = []
    for i, ln in enumerate(lines):
        m = decl_re.match(ln)
        if m: starts.append((i, m.group(2)))
    for idx,(i,name) in enumerate(starts):
        j = i+1
        while j < n and not bound_re.match(lines[j]):
            j += 1
        spans.append((j-i, f.split('/')[-1], name, i+1))
spans.sort(reverse=True)
for length, fn, name, line in spans[:18]:
    print(f"{length:4d} lines  {fn}:{line}  {name}")
