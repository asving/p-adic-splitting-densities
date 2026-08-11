#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] leansimp (post-crash relaunch, stdin, in-repo) start" > runs/leansimp_progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - < runs/leansimp_brief.txt > runs/leansimp_output.log 2>runs/leansimp_stderr.log
echo "[$(date -u +%H:%M:%S)] exit $? ($(wc -c < runs/leansimp_output.log) B; $(tail -1 runs/leansimp_output.log | cut -c1-60))" >> runs/leansimp_progress.txt
