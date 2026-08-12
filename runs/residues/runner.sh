#!/bin/bash
# Residue-priority sequential runner (Asvin 2026-08-12: "prioritize the honest residues")
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] residue queue start" > runs/residues/progress.txt
for name in R1_drainn4 R2_wi_r1 R3_w12 R4_genhn R5_hex3 R6_he6 R7_he6r1 R8_he3; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/residues/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/residues/${name}_brief.txt \
    > runs/residues/${name}_output.log 2> runs/residues/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/residues/${name}_output.log) B; $(tail -1 runs/residues/${name}_output.log | cut -c1-70))" >> runs/residues/progress.txt
  git add -f runs/residues/${name}_output.log runs/residues/${name}_brief.txt runs/residues/progress.txt 2>/dev/null
  git commit -q -m "Residue queue: ${name} run of record committed" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] residue queue done" >> runs/residues/progress.txt
