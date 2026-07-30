import re, glob
IDENT = r"[A-Za-z_][A-Za-z0-9_.!?" + "'" + r"]*"
declkw = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|scoped|local)\s+)*(theorem|lemma|def|instance|abbrev|structure|inductive|class)\s+(" + IDENT + r")")
nse = re.compile(r"^\s*(namespace|end|section)\b")
spans=[]
for f in glob.glob("LeanUrat/MovesV/*.lean"):
    lines=open(f).readlines(); n=len(lines)
    marks=[]
    for i,ln in enumerate(lines):
        m=declkw.match(ln)
        if m: marks.append((i,m.group(1),m.group(2)))
        elif nse.match(ln): marks.append((i,'BND',None))
    for k,(i,kind,name) in enumerate(marks):
        if kind not in ('theorem','lemma'): continue
        j = marks[k+1][0] if k+1<len(marks) else n
        spans.append((j-i,f.split('/')[-1],name,i+1))
spans.sort(reverse=True)
for length,fn,name,line in spans[:15]:
    print(f"{length:4d}  {fn}:{line}  {name}")
