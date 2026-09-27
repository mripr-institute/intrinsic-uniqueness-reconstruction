#!/usr/bin/env python3
"""Build Lean, hiding cached Mathlib docPrime diagnostics from the console."""

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
JOB = re.compile(r"^[✔⚠✖ℹ] \[")
DIAGNOSTIC = re.compile(r"^(?:warning|error|info|trace):")


def visible_job(lines: list[str]) -> list[str]:
    """Remove only complete Mathlib docPrime warning blocks, never errors."""
    retained = []
    removed = False
    i = 1 if lines and JOB.match(lines[0]) else 0
    while i < len(lines):
        end = i + 1
        while end < len(lines) and not DIAGNOSTIC.match(lines[end]):
            end += 1
        block = lines[i:end]
        is_doc_prime = (
            lines[i].startswith("warning:")
            and ".lake/packages/mathlib/" in lines[i]
            and any("linter.docPrime" in line for line in block)
        )
        if is_doc_prime:
            removed = True
        else:
            retained.extend(block)
        i = end
    if lines and JOB.match(lines[0]) and (retained or not removed):
        retained.insert(0, lines[0])
    return retained


def main() -> int:
    args = sys.argv[1:]
    show_all = "--all-warnings" in args
    args = [arg for arg in args if arg != "--all-warnings"]
    command = ["lake", "--no-ansi", "build", *(args or ["SigmaFormalization"])]
    log = ROOT / ".lake" / "build.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    pending = []

    def emit() -> None:
        sys.stdout.writelines(pending if show_all else visible_job(pending))
        sys.stdout.flush()
        pending.clear()

    with log.open("w") as raw:
        with subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT) as process:
            assert process.stdout is not None
            for line in process.stdout:
                raw.write(line)
                if JOB.match(line) or line.startswith("Build completed"):
                    emit()
                pending.append(line)
            emit()
            return process.wait()


if __name__ == "__main__":
    raise SystemExit(main())
