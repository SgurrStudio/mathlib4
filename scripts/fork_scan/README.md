# Fork scan

Tools for finding related work in the mathlib4 fork network.

* `scan_forks.py` lists forks of mathlib4 pushed since `--since` (GitHub repository search,
  sliced by push date to stay under the 1000-result cap, plus the forks endpoint of
  `--extra-parent`), then uses anonymous `git` only: one blobless bare repo per fork borrowing
  upstream objects through alternates, a cheap tip-only probe to keep branches with commits newer
  than `--since`, and a shallow fetch of those branches. It writes one JSON line per commit not in
  upstream `master` (`sha`, `fork`, `branches`, `author`, `date`, `subject`, `body`, `files`).
* `search_commits.py` runs keyword searches over commit messages on all public GitHub repos
  (default branches only), as a complement for work outside forks.

Example (676 forks since 2026-08-01 took about 10 minutes with 8 jobs and 340 MB of disk):

```
python3 scripts/fork_scan/scan_forks.py --since 2026-08-01 --workdir /tmp/fork_scan --jobs 8 \
  --out fork_commits.jsonl
python3 scripts/fork_scan/search_commits.py --out search_hits.jsonl
```

Branch diffs can then be read from `<workdir>/forks/<owner>__<repo>.git` (blobs are fetched
lazily), e.g. `git -C ... diff $(git -C ... merge-base refs/forks/<owner>/<repo>/<branch>
refs/upstream/master) refs/forks/<owner>/<repo>/<branch>`.
