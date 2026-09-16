"""Independent structural audit of the Phase IV graph, not a theorem prover."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
graph_path = BASE / "sigma-phase-iv-graph.json"
raw = graph_path.read_bytes()
record = json.loads(raw)
nodes = {node["id"]: node for node in record["full"]["nodes"]}
edges = record["full"]["edges"]
assert len(nodes) == len(record["full"]["nodes"])
assert len({edge["id"] for edge in edges}) == len(edges)
assert all(edge["source"] in nodes and edge["target"] in nodes for edge in edges)
assert all(set(edge["required_nodes"]) <= nodes.keys() for edge in edges)


def reachable(adjacency, start):
    seen, pending = {start}, [start]
    while pending:
        for other in adjacency[pending.pop()] - seen:
            seen.add(other)
            pending.append(other)
    return seen


# Reconstruct the directed identification graph without consulting any node's
# intrinsic_member flag or the asserted intrinsic_component. Include spectral
# identifications and one-way identification arrows as well as equivalences.
allowed_kinds = {"identification", "spectral identification"}
forward = {node: set() for node in nodes}
reverse = {node: set() for node in nodes}
for edge in edges:
    if edge["required_nodes"] or edge["kind"] not in allowed_kinds:
        continue
    if edge["status"] not in {"iff", "implies"}:
        continue
    source, target = edge["source"], edge["target"]
    forward[source].add(target)
    reverse[target].add(source)
    if edge["status"] == "iff":
        forward[target].add(source)
        reverse[source].add(target)

components, remaining = [], set(nodes)
while remaining:
    start = min(remaining)
    component = reachable(forward, start) & reachable(reverse, start)
    components.append(component)
    remaining -= component
intrinsic = next(component for component in components if "S" in component)
assert intrinsic == set(record["intrinsic_component"])
assert intrinsic == {node for node in nodes if nodes[node]["intrinsic_member"]}

# Independently reconstruct the quotient, preserving original signatures.
projection = {node: "E_S" if node in intrinsic else node for node in nodes}
expected_edges = []
for edge in edges:
    quotient = dict(edge)
    quotient["original_source"] = edge["source"]
    quotient["original_target"] = edge["target"]
    quotient["source_signature"] = nodes[edge["source"]]["complete_datum"]
    quotient["target_signature"] = nodes[edge["target"]]["complete_datum"]
    quotient["source"] = projection[edge["source"]]
    quotient["target"] = projection[edge["target"]]
    quotient["required_nodes"] = [projection[node] for node in edge["required_nodes"]]
    if quotient["source"] != quotient["target"]:
        expected_edges.append(quotient)
assert expected_edges == record["quotient"]["edges"]
assert {node["id"] for node in record["quotient"]["nodes"]} == set(projection.values())

# A genuine identification must have the retained target context available in
# each asserted direction. Forgetful consequences are intentionally exempt.
context_errors = []
for edge in edges:
    if edge["status"] not in {"iff", "implies", "conditional_iff", "conditional_implies"}:
        continue
    if edge["kind"] in {"forgetful consequence", "consequence"}:
        continue
    pairs = [(edge["source"], edge["target"])]
    if edge["status"] in {"iff", "conditional_iff"}:
        pairs.append((edge["target"], edge["source"]))
    for source, target in pairs:
        available = set(nodes[source]["retained_context"]) | set(edge["required_nodes"]) | {source}
        missing = set(nodes[target]["retained_context"]) - available
        if missing:
            context_errors.append([edge["id"], source, target, sorted(missing)])
assert not context_errors, context_errors


def fibre_members(contexts):
    """Identification SCC with exactly these extra inputs retained.

    Construction/forgetful arrows remain excluded. This does not infer a
    conditional input merely because it is constructible from S elsewhere.
    """
    adjacency = {node: set() for node in nodes}
    for edge in edges:
        if edge["status"] not in {"iff", "conditional_iff"}:
            continue
        if edge["kind"] not in allowed_kinds | {"conditional identification"}:
            continue
        if not set(edge["required_nodes"]) <= contexts:
            continue
        source, target = edge["source"], edge["target"]
        if not set(nodes[source]["retained_context"]) <= contexts:
            continue
        if not set(nodes[target]["retained_context"]) <= contexts:
            continue
        adjacency[source].add(target)
        adjacency[target].add(source)
    return sorted(reachable(adjacency, "S") - intrinsic)


fibre_inputs = [
    {"PLACEMENT"}, {"OP_CONTEXT"}, {"CONV_CONTEXT"},
    {"CONV_CONTEXT", "NO_DRIFT"}, {"SPD_CONTEXT"},
    {"SPD_CONTEXT", "MATRIX_ANCHORS"}, {"GAUSS_CONTEXT"},
    {"GW_CONTEXT"}, {"TOP_CONTEXT"}, {"TILT_MARK"}, {"INVOL"},
    {"SELFDECOMP_LINK"},
]
missing_proof_paths = sorted({
    path.split("#")[0] for path in record["theorem_register"].values()
    if not (BASE / path.split("#")[0]).exists()
})
result = {
    "graph_sha256": hashlib.sha256(raw).hexdigest(),
    "nodes": len(nodes), "edges": len(edges),
    "intrinsic_size": len(intrinsic),
    "nontrivial_unconditional_identification_sccs": sorted(
        [sorted(component) for component in components if len(component) > 1],
        key=lambda component: (-len(component), component),
    ),
    "quotient_exact_with_source_signatures": True,
    "context_availability_errors": context_errors,
    "conditional_edges_without_required_nodes": [
        edge["id"] for edge in edges
        if edge["status"].startswith("conditional") and not edge["required_nodes"]
    ],
    "conditional_fibre_additions": [
        {"inputs": sorted(inputs), "additional_members": fibre_members(inputs)}
        for inputs in fibre_inputs
    ],
    "missing_proof_paths_at_check_time": missing_proof_paths,
    "mathematical_proof": False,
}
(BASE / "phase-iv-audit" / "global-graph-checks.json").write_text(
    json.dumps(result, ensure_ascii=False, indent=2) + "\n"
)
print(json.dumps(result, ensure_ascii=False, indent=2))
