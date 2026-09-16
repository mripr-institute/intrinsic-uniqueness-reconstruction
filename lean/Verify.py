#!/usr/bin/env python3

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def strip_lean_comments(text: str) -> str:
    """Remove Lean line comments and nested block comments."""
    out = []
    i = 0
    depth = 0

    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                break
            out.append("\n")
            i = end + 1
            continue

        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue

        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue

        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")

        i += 1

    return "".join(out)


def source_audit() -> None:
    forbidden = re.compile(r"\b(sorry|admit|sorryAx)\b")
    violations = []

    for path in sorted(ROOT.glob("*.lean")):
        code = strip_lean_comments(path.read_text())

        for lineno, line in enumerate(code.splitlines(), 1):
            match = forbidden.search(line)
            if match:
                violations.append(
                    f"{path.name}:{lineno}: {match.group(1)}"
                )

    if violations:
        print("Admitted-proof markers found:")
        print("\n".join(violations))
        raise SystemExit(1)

    print("Source audit: no sorry, admit, or sorryAx.")


def run(command: list[str]) -> str:
    print("+", " ".join(command), flush=True)

    proc = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )

    print(proc.stdout, end="")

    if proc.returncode != 0:
        raise SystemExit(proc.returncode)

    return proc.stdout


def main() -> None:
    source_audit()

    run(["lake", "build", "SigmaFormalization"])

    axiom_output = run(
        ["lake", "env", "lean", "SigmaAxioms.lean"]
    )

    if "sorryAx" in axiom_output:
        print("Axiom audit contains sorryAx.", file=sys.stderr)
        raise SystemExit(1)

    print()
    print("Verification completed successfully.")


if __name__ == "__main__":
    main()
