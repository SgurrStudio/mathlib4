#!/usr/bin/env python3
"""Keyword search over GitHub commit messages (all public repos, default
branches only) as a complement to scan_forks.py, which only sees forks.

Usage: search_commits.py [--out search_hits.jsonl] [keywords...]
"""
import argparse, json, subprocess, time

DEFAULT = ["normal number", "Normal number", "absolutely normal", "Borel normal", "equidistribution",
           "equidistributed", "uniformly distributed", "Weyl criterion", "Weyl's criterion",
           "Weyl inequality", "Weyl differencing", "van der Corput", "exponential sum",
           "Erdős–Turán", "Erdos-Turan", "discrepancy", "Koksma", "Champernowne", "Davenport",
           "Schmidt subspace", "subspace theorem", "Roth's theorem", "Ridout", "Liouville number",
           "Diophantine approximation", "continued fraction", "digit expansion", "base-b expansion",
           "Real.digits", "beta expansion", "ergodic", "Birkhoff ergodic", "Gauss map", "Mahler",
           "Pisot", "Stoneham", "Bailey Crandall", "Nakai", "Shiokawa", "Copeland", "Besicovitch",
           "Pillai", "Wall's theorem", "algebraic irrational"]


def search(q, pages=3):
    out = []
    for page in range(1, pages + 1):
        r = subprocess.run(["gh", "api", "-X", "GET", "search/commits", "-f", f"q={q}",
                            "-f", "per_page=100", "-f", f"page={page}", "-f", "sort=committer-date"],
                           capture_output=True, text=True)
        if r.returncode != 0:
            if "rate limit" in (r.stdout + r.stderr).lower():
                time.sleep(60); continue
            break
        items = json.loads(r.stdout)["items"]
        out += items
        time.sleep(2.5)
        if len(items) < 100:
            break
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", default="search_hits.jsonl")
    p.add_argument("--pages", type=int, default=3)
    p.add_argument("keywords", nargs="*")
    a = p.parse_args()
    seen = {}
    for kw in a.keywords or DEFAULT:
        for it in search(f'"{kw}"', a.pages):
            sha = it["sha"]
            if sha in seen:
                seen[sha]["keywords"].append(kw); continue
            seen[sha] = {"sha": sha, "repo": it["repository"]["full_name"],
                         "fork": it["repository"].get("fork"), "keywords": [kw],
                         "date": it["commit"]["committer"]["date"],
                         "author": it["commit"]["author"]["name"],
                         "message": it["commit"]["message"][:1500], "url": it["html_url"]}
    with open(a.out, "w") as f:
        for c in sorted(seen.values(), key=lambda c: c["date"], reverse=True):
            f.write(json.dumps(c) + "\n")
    print(f"{len(seen)} commits")


if __name__ == "__main__":
    main()
