#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] QGEN start" >> runs/qgen/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/qgen/QGEN_brief.txt > runs/qgen/QGEN_output.log 2> runs/qgen/QGEN_stderr.log
echo "[$(date -u +%H:%M:%S)] QGEN exit $? ($(wc -c < runs/qgen/QGEN_output.log) B; $(grep -E '^QGEN VERDICT' runs/qgen/QGEN_output.log | tail -1 | cut -c1-80))" >> runs/qgen/progress.txt
