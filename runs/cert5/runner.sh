#!/bin/bash
# SOL cert5 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="TC1_w12ht TC2_genhn_cr TC3_gentow3 T1R1 P4_rm1"
echo "[$(date -u +%H:%M:%S)] cert5 queue start" > runs/cert5/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/cert5/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/cert5/${name}_brief.txt > runs/cert5/${name}_output.log 2> runs/cert5/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/cert5/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/cert5/${name}_output.log | tail -1 | cut -c1-90))" >> runs/cert5/progress.txt
  git add -f runs/cert5/${name}_output.log runs/cert5/${name}_brief.txt runs/cert5/progress.txt 2>/dev/null
  git commit -q -m "SOL cert5: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] cert5 queue done" >> runs/cert5/progress.txt
