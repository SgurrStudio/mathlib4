#!/usr/bin/env python3
"""Scan the mathlib4 fork network for recent commits that are not in upstream.

Pipeline:
  1. List forks of mathlib4 pushed since --since, via the GitHub repository
     search API (sliced by push date so each query stays under the 1000-result
     search cap).  Forks of --extra-parent (e.g. SgurrStudio/mathlib4) are
     listed through the forks endpoint.
  2. Fetch upstream master into a blobless bare repo, then fetch every fork's
     branches into refs/forks/<owner>/<branch> (blobless, shallow since the
     window start).  Branches whose tip already exists upstream are skipped.
  3. For each fork branch, log commits reachable from it but not from
     upstream master and newer than --since; write one JSON line per unique
     commit (sha, fork, branches, author, date, subject, body, files).

The output JSONL is intended to be screened (e.g. by an LLM) for topics of
interest; `--keywords` prints a quick keyword pre-filter as well.

Requires: git, gh (authenticated or proxied for the search API).
"""
import argparse, concurrent.futures as cf, datetime as dt, json, os, re, shutil, subprocess, sys, time

UPSTREAM = "https://github.com/leanprover-community/mathlib4"


def sh(*args, check=True, timeout=None, cwd=None):
    r = subprocess.run(args, capture_output=True, text=True, timeout=timeout, cwd=cwd)
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(args)}\n{r.stderr[-2000:]}")
    return r.stdout


def gh_json(path, **params):
    args = ["gh", "api", "-X", "GET", path]
    for k, v in params.items():
        args += ["-f", f"{k}={v}"]
    for attempt in range(6):
        r = subprocess.run(args, capture_output=True, text=True)
        if r.returncode == 0:
            return json.loads(r.stdout)
        if "rate limit" in (r.stdout + r.stderr).lower():
            time.sleep(20 * (attempt + 1))
            continue
        raise RuntimeError(r.stderr)
    raise RuntimeError("rate limited")


def search_forks(name_query, since, until):
    """All forks matching name_query pushed in [since, until], slicing dates."""
    out = {}
    stack = [(since, until)]
    while stack:
        a, b = stack.pop()
        q = f"{name_query} fork:only pushed:{a.isoformat()}..{b.isoformat()}"
        first = gh_json("search/repositories", q=q, per_page=100, page=1)
        total = first["total_count"]
        if total > 1000 and (b - a).days >= 1:
            mid = a + (b - a) / 2
            stack += [(a, mid), (mid + dt.timedelta(days=1), b)]
            continue
        items = first["items"]
        page = 2
        while len(items) < min(total, 1000):
            more = gh_json("search/repositories", q=q, per_page=100, page=page)["items"]
            if not more:
                break
            items += more
            page += 1
            time.sleep(2)  # search API: 30 req/min
        for it in items:
            out[it["full_name"]] = {"full_name": it["full_name"], "pushed_at": it["pushed_at"],
                                    "parent_guess": "mathlib4", "description": it.get("description")}
        time.sleep(2)
    return out


def list_forks_endpoint(repo):
    out, page = {}, 1
    while True:
        items = gh_json(f"repos/{repo}/forks", per_page=100, page=page, sort="newest")
        for it in items:
            out[it["full_name"]] = {"full_name": it["full_name"], "pushed_at": it["pushed_at"],
                                    "parent_guess": repo, "description": it.get("description")}
        if len(items) < 100:
            return out
        page += 1


def ls_remote(url):
    try:
        txt = sh("git", "ls-remote", "--heads", url, timeout=120)
    except Exception as e:
        return None, str(e)
    refs = {}
    for line in txt.splitlines():
        sha, ref = line.split("\t")
        refs[ref[len("refs/heads/"):]] = sha
    return refs, None


def safe(s):
    return re.sub(r"[^A-Za-z0-9._/-]", "_", s)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--since", default=(dt.date.today() - dt.timedelta(days=120)).isoformat())
    p.add_argument("--workdir", default="fork_scan_work")
    p.add_argument("--extra-parent", action="append", default=["SgurrStudio/mathlib4"])
    p.add_argument("--max-forks", type=int, default=0, help="0 = all, most recently pushed first")
    p.add_argument("--max-branches", type=int, default=40)
    p.add_argument("--depth", type=int, default=40, help="fallback fetch depth")
    p.add_argument("--jobs", type=int, default=6)
    p.add_argument("--out", default="fork_commits.jsonl")
    args = p.parse_args()

    since = dt.date.fromisoformat(args.since)
    os.makedirs(args.workdir, exist_ok=True)
    git_dir = os.path.join(args.workdir, "repo.git")

    # 1. fork list (cached)
    forks_path = os.path.join(args.workdir, "forks.json")
    if os.path.exists(forks_path):
        forks = json.load(open(forks_path))
    else:
        forks = search_forks("mathlib4 in:name", since, dt.date.today())
        for extra in args.extra_parent:
            try:
                forks.update(list_forks_endpoint(extra))
            except Exception as e:
                print(f"warning: cannot list forks of {extra}: {e}", file=sys.stderr)
        forks = sorted(forks.values(), key=lambda f: f["pushed_at"], reverse=True)
        json.dump(forks, open(forks_path, "w"), indent=1)
    forks = [f for f in forks if f["pushed_at"][:10] >= args.since]
    if args.max_forks:
        forks = forks[: args.max_forks]
    print(f"{len(forks)} forks pushed since {since}", file=sys.stderr)

    # 2. upstream
    if not os.path.exists(git_dir):
        sh("git", "init", "--bare", "-q", git_dir)
        sh("git", "-C", git_dir, "config", "remote.upstream.url", UPSTREAM)
        sh("git", "-C", git_dir, "config", "remote.upstream.promisor", "true")
        sh("git", "-C", git_dir, "config", "remote.upstream.partialclonefilter", "blob:none")
        deep = (since - dt.timedelta(days=90)).isoformat()
        sh("git", "-C", git_dir, "fetch", "-q", "--filter=blob:none", f"--shallow-since={deep}",
           "upstream", "+refs/heads/master:refs/upstream/master", timeout=3600)
    up_heads, _ = ls_remote(UPSTREAM)
    upstream_shas = set((up_heads or {}).values())
    upstream_master = sh("git", "-C", git_dir, "rev-parse", "refs/upstream/master").strip()

    done_path = os.path.join(args.workdir, "fetched.txt")
    done = set(open(done_path).read().split()) if os.path.exists(done_path) else set()

    def fetch_fork(f):
        name = f["full_name"]
        if name in done:
            return name, "cached"
        url = f"https://github.com/{name}"
        heads, err = ls_remote(url)
        if heads is None:
            return name, f"ls-remote failed: {err[:200]}"
        own = {b: s for b, s in heads.items() if s not in upstream_shas}
        if not own:
            return name, "no own branches"
        # One small bare repo per fork borrowing upstream's objects through
        # alternates: concurrent shallow fetches into one repo would race.
        fdir = os.path.join(args.workdir, "forks", safe(name).replace("/", "__") + ".git")
        if not os.path.exists(fdir):
            sh("git", "init", "--bare", "-q", fdir)
            with open(os.path.join(fdir, "objects", "info", "alternates"), "w") as a:
                a.write(os.path.abspath(os.path.join(git_dir, "objects")) + "\n")
            shallow = os.path.join(git_dir, "shallow")
            if os.path.exists(shallow):
                open(os.path.join(fdir, "shallow"), "w").write(open(shallow).read())
            sh("git", "-C", fdir, "update-ref", "refs/upstream/master", upstream_master)
            sh("git", "-C", fdir, "config", "remote.origin.url", url)
            sh("git", "-C", fdir, "config", "remote.origin.promisor", "true")
            sh("git", "-C", fdir, "config", "remote.origin.partialclonefilter", "blob:none")
        # Probe: fetch only the tip commits (no trees, no blobs) of every own
        # branch, then keep the branches whose tip is newer than --since,
        # most recent first.
        pdir = fdir[:-4] + ".probe.git"
        shutil.rmtree(pdir, ignore_errors=True)
        sh("git", "init", "--bare", "-q", pdir)
        probe = [f"+refs/heads/{b}:refs/probe/{safe(b)}" for b in own]
        for i in range(0, len(probe), 500):
            subprocess.run(["git", "-C", pdir, "fetch", "-q", "--no-tags", "--filter=tree:0",
                            "--depth=1", url, *probe[i:i + 500]],
                           capture_output=True, text=True, timeout=1800)
        dated = []
        for line in sh("git", "-C", pdir, "for-each-ref", "--format=%(committerdate:short) %(refname)",
                       "refs/probe/").splitlines():
            d, ref = line.split(" ", 1)
            if d >= since.isoformat():
                dated.append((d, ref[len("refs/probe/"):]))
        shutil.rmtree(pdir, ignore_errors=True)
        recent = {safe(b): b for b in own}
        branches = [recent[b] for d, b in sorted(dated, reverse=True) if b in recent][: args.max_branches]
        if not branches:
            return name, f"no branches newer than {since}"
        specs = [f"+refs/heads/{b}:refs/forks/{safe(name)}/{safe(b)}" for b in branches]
        r = subprocess.run(["git", "-C", fdir, "fetch", "-q", "--no-tags", "--filter=blob:none",
                            f"--shallow-since={since.isoformat()}", "origin", *specs],
                           capture_output=True, text=True, timeout=1800)
        if r.returncode != 0 and "shallow info" in r.stderr:
            # Some branch has no commit newer than --since; fall back to a
            # fixed depth (old commits are dropped by the date filter later).
            r = subprocess.run(["git", "-C", fdir, "fetch", "-q", "--no-tags", "--filter=blob:none",
                                f"--depth={args.depth}", "origin", *specs],
                               capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            return name, "fetch failed: " + r.stderr[-300:]
        return name, f"ok {len(branches)} recent of {len(heads)} branches"

    with cf.ThreadPoolExecutor(args.jobs) as ex, open(done_path, "a") as donef:
        for i, (name, status) in enumerate(ex.map(fetch_fork, forks)):
            print(f"[{i+1}/{len(forks)}] {name}: {status}", file=sys.stderr)
            if not status.startswith(("fetch failed", "ls-remote failed")):
                donef.write(name + "\n"); donef.flush()

    # 3. commits not in upstream
    refs = []
    fork_root = os.path.join(args.workdir, "forks")
    for d in sorted(os.listdir(fork_root)) if os.path.isdir(fork_root) else []:
        fdir = os.path.join(fork_root, d)
        for r in sh("git", "-C", fdir, "for-each-ref", "--format=%(refname)", "refs/forks/").split():
            refs.append((fdir, r))
    commits = {}
    SEP, BEGIN = "\x1f", "\x1e"
    fmt = BEGIN + SEP.join(["%H", "%an", "%aI", "%s", "%b"]) + SEP
    for fdir, ref in refs:
        _, _, rest = ref.split("/", 2)
        owner, repo, branch = rest.split("/", 2)
        txt = sh("git", "-C", fdir, "log", "--no-merges", f"--since={since.isoformat()}",
                 f"--format={fmt}", "--name-only", ref, "--not", "refs/upstream/master", check=False)
        for chunk in txt.split(BEGIN):
            parts = chunk.split(SEP)
            if len(parts) != 6:
                continue
            sha, author, date, subject, body, files = parts
            c = commits.setdefault(sha, {"sha": sha, "fork": f"{owner}/{repo}", "branches": [],
                                         "author": author, "date": date, "subject": subject,
                                         "body": body.strip()[:1500],
                                         "files": [x for x in files.split("\n") if x.strip()][:60]})
            c["branches"].append(branch)
    with open(args.out, "w") as out:
        for c in sorted(commits.values(), key=lambda c: c["date"], reverse=True):
            out.write(json.dumps(c) + "\n")
    print(f"wrote {len(commits)} commits from {len(refs)} branches to {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
