#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

"""Insert or check SPDX license headers on tracked source files."""

from __future__ import annotations

import argparse
import fnmatch
import subprocess
import sys
from pathlib import Path

LICENSE_ID = "Apache-2.0"
SPDX_LINE = f"SPDX-License-Identifier: {LICENSE_ID}"

LINE_COMMENT_SUFFIXES = {
    ".dockerignore": "#",
    ".gitignore": "#",
    ".mettail": "#",
    ".py": "#",
    ".sh": "#",
    ".toml": "#",
    ".yaml": "#",
    ".yml": "#",
    ".dfl": "#",
    ".metta": ";",
    ".pl": "%",
}

LINE_COMMENT_NAMES = {
    "Dockerfile": "#",
    "Makefile": "#",
}

HTML_COMMENT_SUFFIXES = {".md", ".html", ".xml", ".svg"}
BLOCK_COMMENT_SUFFIXES = {".css"}
LEAN_SUFFIXES = {".lean"}

UNHEADERABLE_SUFFIXES = {
    ".gif",
    ".json",
    ".lock",
    ".png",
    ".snap",
    ".txt",
}

UNHEADERABLE_NAMES = {
    "LICENSE",
    "LICENSE-APACHE",
    "LICENSE-MIT",
    "NOTICE",
    "lean-toolchain",
    "Cargo.lock",
}

DEFAULT_EXCLUDES = {
    ".git/**",
    ".lake/**",
    "book/.lake/**",
    "docbuild/.lake/**",
    "dist/**",
    "target/**",
    "build/**",
    "lake-packages/**",
    "book/_out/**",
    "book/static/**",
    "tests/corpus/**",
}


def tracked_files(root: Path) -> list[Path]:
    raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
    return [root / p.decode() for p in raw.split(b"\0") if p]


def repo_rel(root: Path, path: Path) -> str:
    return path.relative_to(root).as_posix()


def is_excluded(root: Path, path: Path, extra: list[str]) -> bool:
    rel = repo_rel(root, path)
    return any(fnmatch.fnmatch(rel, pattern) for pattern in [*DEFAULT_EXCLUDES, *extra])


def comment_kind(path: Path) -> tuple[str, str] | tuple[None, None]:
    name = path.name
    suffix = path.suffix
    if name in UNHEADERABLE_NAMES or suffix in UNHEADERABLE_SUFFIXES:
        return None, None
    if name in LINE_COMMENT_NAMES:
        return "line", LINE_COMMENT_NAMES[name]
    if suffix in LEAN_SUFFIXES:
        return "line", "--"
    if suffix in LINE_COMMENT_SUFFIXES:
        return "line", LINE_COMMENT_SUFFIXES[suffix]
    if suffix in HTML_COMMENT_SUFFIXES:
        return "html", ""
    if suffix in BLOCK_COMMENT_SUFFIXES:
        return "block", ""
    return None, None


def header_text(kind: str, prefix: str, copyright_text: str | None) -> str:
    if kind == "line":
        lines = []
        if copyright_text:
            lines.append(f"{prefix} SPDX-FileCopyrightText: {copyright_text}")
        lines.append(f"{prefix} {SPDX_LINE}")
        return "\n".join(lines) + "\n\n"
    if kind == "html":
        lines = []
        if copyright_text:
            lines.append(f"<!-- SPDX-FileCopyrightText: {copyright_text} -->")
        lines.append(f"<!-- {SPDX_LINE} -->")
        return "\n".join(lines) + "\n\n"
    if kind == "block":
        lines = ["/*"]
        if copyright_text:
            lines.append(f" * SPDX-FileCopyrightText: {copyright_text}")
        lines.append(f" * {SPDX_LINE}")
        lines.append(" */")
        return "\n".join(lines) + "\n\n"
    raise ValueError(f"unknown comment kind: {kind}")


def has_spdx_header(text: str) -> bool:
    return SPDX_LINE in "\n".join(text.splitlines()[:12])


def insertion_offset(text: str) -> int:
    if text.startswith("#!"):
        end = text.find("\n")
        if end == -1:
            return len(text)
        return end + 1
    return 0


def add_header(path: Path, copyright_text: str | None) -> bool:
    kind, prefix = comment_kind(path)
    if kind is None:
        return False
    text = path.read_text()
    if has_spdx_header(text):
        return False
    offset = insertion_offset(text)
    prefix_text = text[:offset]
    rest = text[offset:]
    sep = "" if not prefix_text or prefix_text.endswith("\n") else "\n"
    path.write_text(prefix_text + sep + header_text(kind, prefix, copyright_text) + rest)
    return True


def missing_headers(root: Path, extra_excludes: list[str]) -> list[str]:
    missing = []
    for path in tracked_files(root):
        if is_excluded(root, path, extra_excludes):
            continue
        kind, _ = comment_kind(path)
        if kind is None:
            continue
        if not has_spdx_header(path.read_text(errors="ignore")):
            missing.append(repo_rel(root, path))
    return missing


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fix", action="store_true", help="insert missing headers")
    parser.add_argument("--check", action="store_true", help="fail if headers are missing")
    parser.add_argument("--copyright", help="SPDX-FileCopyrightText value to insert")
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="extra git-style path glob to exclude",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not args.fix and not args.check:
        print("choose --fix or --check", file=sys.stderr)
        return 2

    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"]).decode().strip())

    if args.fix:
        changed = []
        for path in tracked_files(root):
            if is_excluded(root, path, args.exclude):
                continue
            if add_header(path, args.copyright):
                changed.append(repo_rel(root, path))
        if changed:
            print("added SPDX headers:")
            for rel in changed:
                print(rel)

    if args.check:
        missing = missing_headers(root, args.exclude)
        if missing:
            print("missing SPDX-License-Identifier headers:", file=sys.stderr)
            for rel in missing:
                print(rel, file=sys.stderr)
            return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
