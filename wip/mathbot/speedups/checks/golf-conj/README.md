Audit harness for golf.ts conjugation (cut-conjugation-audit.md §3). Applies audit-patch.diff to a scratch
`git archive a764c58` copy (/workspace/mathbot-scratch/golfconj, node_modules symlinked from eml-live), never to a
checkout. Run: `node_modules/.bin/tsx audit.ts <maxK> nowatch` (pool only) or without `nowatch` (with the hit pipeline).
