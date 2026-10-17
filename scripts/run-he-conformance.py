#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 LeaTTa contributors
# SPDX-License-Identifier: Apache-2.0

"""Check the HE repair fixtures with the Hyperon 0.2.10 interpreter."""

import re
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path


def main() -> int:
    try:
        installed = version("hyperon")
    except PackageNotFoundError:
        print("Install hyperon==0.2.10 in a compatible Python environment first.")
        return 2
    if installed != "0.2.10":
        print(f"Expected hyperon==0.2.10, found {installed}.")
        return 2

    from hyperon import MeTTa

    root = Path(__file__).resolve().parent.parent
    total = 0
    failed = False
    for name in ("typeops.metta", "he-conformance.metta"):
        source = (root / "tests" / "regression" / name).read_text()
        expected = len(re.findall(r"!\s*\(assertEqual(?:ToResult)?\b", source))
        try:
            results = [[str(atom) for atom in row] for row in MeTTa().run(source)]
        except RuntimeError as error:
            print(f"{name}: HE error: {error}")
            failed = True
            continue
        passed = sum(row == ["()"] for row in results)
        ok = len(results) == expected and passed == expected
        print(f"{name}: {passed}/{expected} assertions pass with HE 0.2.10")
        if not ok:
            print(f"Non-unit results: {[row for row in results if row != ['()']]}")
            failed = True
        total += expected
    if failed:
        return 1
    print(f"HE CONFORMANCE OK: {total}/{total} assertions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
