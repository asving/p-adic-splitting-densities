import re, glob
IDENT = r"[A-Za-z_][A-Za-z0-9_.!?" + "'" + r"]*"
decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*(theorem|lemma)\s+(" + IDENT + r")")
priv_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:protected|noncomputable|scoped|local)\s+)*private\s+(?:theorem|lemma)\b")
ns_re  = re.compile(r"^\s*namespace\s+(" + IDENT + r")")
sec_re = re.compile(r"^\s*section\b\s*(" + IDENT + r")?")
end_re = re.compile(r"^\s*end\b\s*(" + IDENT + r")?")
files = sorted(glob.glob("LeanUrat/MovesV/*.lean"))
results = []
for f in files:
    stack = []
    depth = 0  # block comment nesting
    for ln in open(f):
        code = ln.split('--')[0]
        o = code.count('/-'); c = code.count('-/')
        if depth == 0:
            if ns_re.match(code):
                stack.append(('ns', ns_re.match(code).group(1)))
            elif code.strip().startswith('section') and sec_re.match(code):
                stack.append(('sec', sec_re.match(code).group(1)))
            elif code.strip().startswith('end') and end_re.match(code):
                if stack: stack.pop()
            else:
                dm = decl_re.match(code)
                if dm:
                    name = dm.group(2)
                    pref = '.'.join(n for (k,n) in stack if k=='ns')
                    fqn = (pref + '.' + name) if pref else name
                    results.append((fqn, f, bool(priv_re.match(code))))
        depth += o - c
        if depth < 0: depth = 0
names = [r[0] for r in results if not r[1] is None and not r[2]]
with open("/tmp/golf_baseline/names.txt","w") as out:
    for n in names: out.write(n+"\n")
print("total:", len(results), "non-private:", len(names), "private:", sum(1 for r in results if r[2]))
print("names with ? or !:", [n for n in names if '?' in n or '!' in n])
