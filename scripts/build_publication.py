#!/usr/bin/env python3
"""Build the complete publication from fresh auxiliary files in three passes."""

from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def main():
    source_dir = Path(__file__).resolve().parent.parent / "paper"
    build_dir = source_dir / "publication-build"
    build_dir.mkdir(exist_ok=True)
    engine = shutil.which("pdflatex")
    if engine is None:
        raise SystemExit("pdflatex is required (TeX Live or MacTeX).")

    with tempfile.TemporaryDirectory(prefix="clean-", dir=build_dir) as staging:
        stage = Path(staging)
        command = [
            engine,
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-file-line-error",
            "-synctex=1",
            f"-output-directory={stage}",
            "intrinsic-uniqueness-reconstruction.tex",
        ]
        previous_aux = None
        for pass_number in range(1, 4):
            result = subprocess.run(
                command, cwd=source_dir, capture_output=True, text=True
            )
            if result.returncode:
                raise SystemExit(result.stdout + result.stderr)
            aux = (stage / "intrinsic-uniqueness-reconstruction.aux").read_bytes()
            if pass_number == 3 and aux != previous_aux:
                raise SystemExit("Cross-references did not stabilize in three passes.")
            previous_aux = aux

        log = (stage / "intrinsic-uniqueness-reconstruction.log").read_text()
        problems = re.findall(
            r"^.*(?:Warning:|Overfull|Underfull|Missing character:|^!).*$",
            log,
            re.MULTILINE,
        )
        if problems:
            raise SystemExit("Unresolved build diagnostics:\n" + "\n".join(problems))
        # The bibliography is in the source and resolves in the same three passes.
        for artifact in stage.iterdir():
            shutil.copy2(artifact, build_dir / artifact.name)
        target = source_dir / "intrinsic-uniqueness-reconstruction.pdf"
        shutil.copy2(stage / "intrinsic-uniqueness-reconstruction.pdf", target)
        print(f"Built {target} from a clean state in three pdfLaTeX passes.")
        print("Cross-references stabilized; no LaTeX warnings or box warnings.")


if __name__ == "__main__":
    main()
