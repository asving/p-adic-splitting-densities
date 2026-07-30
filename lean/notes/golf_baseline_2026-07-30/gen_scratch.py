names = [l.strip() for l in open("/tmp/golf_baseline/names.txt") if l.strip()]
with open("LeanUrat/MovesV_AxScratch.lean","w") as out:
    out.write("-- AUTO-GENERATED #print axioms scratch (safe to delete)\n")
    for f in __import__("glob").glob("LeanUrat/MovesV/*.lean"):
        pass
    import glob
    for base in sorted(glob.glob("LeanUrat/MovesV/*.lean")):
        b=base.split("/")[-1][:-5]
        out.write(f"import LeanUrat.MovesV.{b}\n")
    out.write("\n")
    for n in names:
        out.write(f'#print axioms {n}\n')
print("names:", len(names))
