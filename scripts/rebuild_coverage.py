#!/usr/bin/env python3
"""Reconstruct the ledger from current LaTeX and independently reviewed maps.

This checks inventory and mappings, not mathematical entailment. The latter is
recorded by the independent auditors in the input artifacts. --check never
writes; --write mechanically regenerates both human and machine ledgers.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ("core", "probability", "operators", "series-realizations", "closure")
MAPS = ("core-closure", "probability", "operator", "realizations")
ENV = re.compile(
    r"\\begin\{(definition|theorem|proposition|lemma|corollary)\}"
    r"(?:\[([^\n]*)\])?\s*(.*?)\\end\{\1\}", re.S
)
LABEL = re.compile(r"\\label\{([^}]+)\}")


def reconstruct():
    records = {}
    additional = []
    for group in MAPS:
        path = ROOT / f"audits/formalization/current-{group}-audit.json"
        audit = json.loads(path.read_text())
        for claim in audit.get("additional_labelled_claims", []):
            additional.append({**claim, "independent_audit": str(path.relative_to(ROOT))})
        for item in audit["statements"]:
            label = item["latex_label"]
            if label in records:
                raise ValueError(f"Duplicate audit record: {label}")
            records[label] = (item, str(path.relative_to(ROOT)))

    items = []
    for chapter in CHAPTERS:
        source = f"paper/sections/{chapter}.tex"
        tex = (ROOT / source).read_text()
        for match in ENV.finditer(tex):
            kind, title, statement = match.groups()
            labels = LABEL.findall(statement)
            if not labels or labels[0] not in records:
                raise ValueError(f"Unaudited named statement in {source}: {title}")
            audit, audit_source = records[labels[0]]
            status = audit["status"]
            if status not in {"definition", "complete", "partial", "missing"}:
                raise ValueError(f"Unknown status: {labels[0]}: {status}")
            remaining = list(audit["unproved_components"])
            declarations = list(audit["lean_declarations"])
            proved = list(audit["proved_components"])
            # Some theorem environments carry two independent clause labels.
            for label in labels[1:]:
                if label in records:
                    other, _ = records[label]
                    if other["status"] != status:
                        raise ValueError(f"Alias status mismatch: {label}")
                    remaining += other["unproved_components"]
                    declarations += other["lean_declarations"]
                    proved += other["proved_components"]
            remaining = list(dict.fromkeys(remaining))
            declarations = list(dict.fromkeys(declarations))
            if status in {"definition", "complete"} and remaining:
                raise ValueError(f"False completion with residuals: {labels[0]}")
            if status == "complete" and not declarations:
                raise ValueError(f"Unmapped completion: {labels[0]}")
            if status in {"partial", "missing"} and not remaining:
                raise ValueError(f"Unspecified residual: {labels[0]}")
            items.append({
                "id": labels[0], "labels": labels, "kind": kind,
                "title": title, "source": source,
                "line": tex.count("\n", 0, match.start()) + 1,
                "statement_tex": statement,
                "statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
                "lean_status": status, "lean_theorems": declarations,
                "proved_components": list(dict.fromkeys(proved)),
                "unproved_components": remaining, "gaps": remaining,
                "independent_audit": audit_source, "notes": audit.get("notes", ""),
            })
    return {
        "scope": "All named mathematical environments in the current paper. "
                 "Equation labels inside statements are retained as component labels. "
                 "Proof-only assertions and the software-status remark are distinguished "
                 "in the independent audit artifacts. The paper supplies mathematical proofs; "
                 "the statuses here measure their Lean formalization only. "
                 "Complete Lean coverage is not yet established.",
        "count": len(items),
        "totals": dict(Counter(item["lean_status"] for item in items)),
        "pending_exact_statement_matches": 0,
        "additional_labelled_claims": additional,
        "obligations": items,
    }


def markdown(ledger):
    totals = ledger["totals"]
    lines = ["# Current paper-to-Lean formalization coverage", "", ledger["scope"], "",
             "**Terminology:** `complete`, `partial`, and `missing` describe Lean coverage, "
             "not the existence of mathematical proofs in the paper. Remaining components "
             "are formalization work, not unproved paper results.", "",
             f"Total: {ledger['count']}; definitions: {totals.get('definition', 0)}; "
             f"complete: {totals.get('complete', 0)}; partial: {totals.get('partial', 0)}; "
             f"missing: {totals.get('missing', 0)}; pending matches: 0.", "",
             "Generated by `python3 scripts/rebuild_coverage.py --write`. "
             "A zero pending count means classification is finished, not that every proof "
             "has been formalized in Lean.", "",
             "| Label | Paper result | Lean coverage | Existing Lean declarations | Remaining Lean formalization |",
             "|---|---|---|---|---|"]
    def cell(text):
        return text.replace("|", "&#124;").replace("\n", " ")
    for item in ledger["obligations"]:
        lines.append("| " + " | ".join(map(cell, (
            item["id"], item["title"], item["lean_status"],
            "; ".join(f"`{d}`" for d in item["lean_theorems"]),
            "; ".join(item["unproved_components"]) or "None",
        ))) + " |")
    lines += ["", "## Remaining Lean formalization components", ""]
    for item in ledger["obligations"]:
        for component in item["unproved_components"]:
            lines.append(f"- `{item['id']}`: {component}")
    lines += ["", "## Additional labelled mathematical results", "",
              "These component-level checks include standalone formulas outside named "
              "theorem environments. They also participate in the Lean-coverage completion gate.", "",
              "| Label | Lean coverage | Lean declarations / remaining formalization |",
              "|---|---|---|"]
    for claim in ledger["additional_labelled_claims"]:
        lines.append("| " + " | ".join(map(cell, (
            claim["latex_label"], claim["status"],
            "; ".join(claim.get("unproved_components", [])) or
            "; ".join(f"`{d}`" for d in claim["lean_declarations"]),
        ))) + " |")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--lean", action="store_true", help="kernel-elaborate all declaration names")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    ledger = reconstruct()
    outputs = {"audits/lean-coverage.json": json.dumps(ledger, indent=2, ensure_ascii=False) + "\n",
               "audits/lean-coverage.md": markdown(ledger)}
    for name, content in outputs.items():
        path = ROOT / name
        if args.write:
            path.write_text(content)
        elif not path.exists() or path.read_text() != content:
            raise SystemExit(f"Stale coverage artifact: {name}")
    if args.lean:
        names = sorted({d for item in ledger["obligations"] for d in item["lean_theorems"]})
        names = sorted(set(names) | {d for item in ledger["additional_labelled_claims"]
                                     for d in item["lean_declarations"]})
        proc = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "lean",
                              input="import Sigma\n" + "\n".join(f"#check {d}" for d in names) + "\n",
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if proc.returncode:
            print(proc.stdout)
            raise SystemExit(proc.returncode)
        print(f"Lean declaration checks: {len(names)} PASS")
    print(f"TOTAL PAPER ITEMS: {ledger['count']}")
    for status in ("definition", "complete", "partial", "missing"):
        print(f"{status.upper()}: {ledger['totals'].get(status, 0)}")
    incomplete = any(ledger["totals"].get(s, 0) for s in ("partial", "missing")) or any(
        claim["status"] not in {"definition", "complete"} or claim.get("unproved_components")
        for claim in ledger["additional_labelled_claims"])
    if args.require_complete and incomplete:
        raise SystemExit("Exact coverage remains incomplete.")


if __name__ == "__main__":
    main()
