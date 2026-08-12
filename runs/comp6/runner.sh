#!/bin/bash
# SOL comp6 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1P6 T2P2 T4R1 T5R1"
echo "[$(date -u +%H:%M:%S)] comp6 queue start" > runs/comp6/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp6/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp6/${name}_brief.txt > runs/comp6/${name}_output.log 2> runs/comp6/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp6/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp6/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp6/progress.txt
  git add -f runs/comp6/${name}_output.log runs/comp6/${name}_brief.txt runs/comp6/progress.txt 2>/dev/null
  git commit -q -m "SOL comp6: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp6 queue done" >> runs/comp6/progress.txt
