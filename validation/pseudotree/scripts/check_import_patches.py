#!/usr/bin/env python3
"""Verify the pinned, import-only dependency variant after applying the patches.

From validation/pseudotree:
    python3 scripts/check_import_patches.py

No network access is needed. This checks the actual working trees and the
pinned upstream Git objects, rather than relying on a previous audit log.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALIASES = {"milliken": "milliken", "ramsey-space": "ramsey-space-todorcevic"}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def sha(data):
    return hashlib.sha256(data).hexdigest()


def body(data):
    return b"".join(line for line in data.splitlines(keepends=True)
                    if not line.startswith(b"import "))


def main():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    revisions = {p["name"].strip("«»"): p.get("rev") for p in manifest["packages"]}
    entries = json.loads((ROOT / "import-patches/source-integrity.json").read_text())
    errors = []
    expected_changes = {}
    for entry in entries:
        name = ALIASES[entry["repository"]]
        repo = ROOT / ".lake/packages" / name
        path, commit = entry["path"], entry["commit"]
        expected_changes.setdefault(name, set()).add(path)
        if revisions.get(name) != commit:
            errors.append(f"{name}: manifest revision differs from recorded revision")
        if git(repo, "rev-parse", "HEAD").decode().strip() != commit:
            errors.append(f"{name}: unexpected checkout revision")
        original = git(repo, "show", f"{commit}:{path}")
        patched = (repo / path).read_bytes()
        checks = {
            "upstream hash": sha(original) == entry["original_sha256"],
            "patched hash": sha(patched) == entry["patched_sha256"],
            "non-import hash": sha(body(original)) == entry["body_without_import_lines_sha256"],
            "unchanged non-import lines": body(original) == body(patched),
        }
        for label, ok in checks.items():
            if not ok:
                errors.append(f"{name}/{path}: {label} failed")
        print(f"{name}/{path}: " + ("PASS" if all(checks.values()) else "FAIL"))
    for name, expected in expected_changes.items():
        repo = ROOT / ".lake/packages" / name
        changed = set(git(repo, "diff", "--name-only", "-z", "HEAD").decode().split("\0")) - {""}
        if changed != expected:
            errors.append(f"{name}: unexpected tracked-file diff: {sorted(changed ^ expected)}")
    for error in errors:
        print("ERROR:", error, file=sys.stderr)
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
