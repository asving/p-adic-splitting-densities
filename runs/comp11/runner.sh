#!/bin/bash
# SOL comp11 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1R8 T2R1v2 T4P4 T5P4"
echo "[$(date -u +%H:%M:%S)] comp11 queue start" > runs/comp11/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp11/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp11/${name}_brief.txt > runs/comp11/${name}_output.log 2> runs/comp11/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp11/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp11/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp11/progress.txt
  git add -f runs/comp11/${name}_output.log runs/comp11/${name}_brief.txt runs/comp11/progress.txt 2>/dev/null
  git commit -q -m "SOL comp11: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp11 queue done" >> runs/comp11/progress.txt
