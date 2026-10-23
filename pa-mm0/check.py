"""Check the arithmetic proof-sequence library against its source specification."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "artifacts"
MODULE_NAME = re.compile(r"[a-z][a-z0-9_]*\Z")
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.MULTILINE)
NON_CODE = re.compile(r'--[^\n]*|"(?:\\.|[^"\\])*"|\$[^$]*\$', re.DOTALL)
CURRENT_MODULE = None


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_graph(module):
    """Read the complete project include graph, allowing only pinned vendor files."""
    if not MODULE_NAME.fullmatch(module):
        raise ValueError("Invalid module name")
    vendor = (ROOT.parent / "lean-mm0/vendor").resolve()
    allowed_vendor = {vendor / ("peano." + suffix) for suffix in ("mm0", "mm1", "mmu")}
    pending = [ROOT / (module + ".mm0"), ROOT / (module + ".mm1")]
    found = {}
    while pending:
        path = pending.pop().resolve()
        if path in found:
            continue
        if path in allowed_vendor:
            found[path] = sha(path)
            continue
        if not path.is_relative_to(ROOT.resolve()):
            raise ValueError("Unpinned external import: " + str(path))
        raw = path.read_bytes()
        if b"\r" in raw:
            raise ValueError("MM0 sources require LF line endings: " + str(path))
        content = raw.decode("utf-8")
        if re.search(r"\baxiom\b", NON_CODE.sub(" ", content)):
            raise ValueError("Project source adds an axiom: " + str(path))
        found[path] = hashlib.sha256(raw).hexdigest()
        pending.extend(path.parent / child for child in IMPORT.findall(content))
    return found


def flat_proof_input(module, graph):
    """Linearize project MM1 imports; leave the checked MM0 spec untouched.

    A fixed topological order avoids the observed missing-definition/frozen-
    environment failures in concurrent project imports. This is a proof-input
    transformation only. MM0-C still checks the original specification.
    """
    vendor = (ROOT.parent / "lean-mm0/vendor/peano.mm1").resolve()
    seen, order, chunks = set(), [], []

    def visit(path):
        path = path.resolve()
        if path in seen:
            return
        seen.add(path)
        if path == vendor:
            return
        if path.suffix != ".mm1":
            raise ValueError("Unexpected project proof import: " + str(path))
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != graph[path]:
            raise RuntimeError("Source changed before flattening: " + str(path))
        content = raw.decode("utf-8")
        for child in IMPORT.findall(content):
            visit(path.parent / child)
        order.append(path.relative_to(ROOT).as_posix())
        chunks.append("\n-- Original proof module: " + order[-1] + "\n" + IMPORT.sub("", content))

    visit(ROOT / (module + ".mm1"))
    target = OUT / (module + "-proof-input.mm1")
    vendor_import = os.path.relpath(vendor, target.parent).replace("\\", "/")
    target.write_bytes(('import "' + vendor_import + '";\n' + "\n".join(chunks) + "\n").encode("utf-8"))
    return target, order


def main():
    global CURRENT_MODULE
    parser = argparse.ArgumentParser()
    parser.add_argument("--tools", type=Path, required=True)
    parser.add_argument("--module", default="proof_sequence")
    parser.add_argument("--proof-input", choices=("flat", "modular"), default="flat",
                        help="Default: deterministic project import order; MM0 spec is unchanged")
    args = parser.parse_args()
    if not MODULE_NAME.fullmatch(args.module):
        raise ValueError("Invalid module name")
    CURRENT_MODULE = args.module
    OUT.mkdir(exist_ok=True)
    (OUT / "report.json").write_text('{"status": "IN_PROGRESS"}\n', encoding="utf-8")
    (OUT / (args.module + "-report.json")).write_text(
        '{"status": "IN_PROGRESS"}\n', encoding="utf-8")
    module = args.module
    source = ROOT / (module + ".mm0")
    vendor = ROOT.parent / "lean-mm0/vendor"
    expected_vendor = {
        "peano.mm0": "463a7d6e4f4791313dedcfd737053dcf2cc07b466371e263c38a994c6fb72052",
        "peano.mm1": "13fd383aa02e434cba1350e9a8f12c440b5114d22f26506fece4aecdf1370079",
        "peano.mmu": "3405aa9f99417850acb766845cc0031651bcaacb7dc9b87e25e6598bdf872cfd",
    }
    if any(sha(vendor / name) != digest for name, digest in expected_vendor.items()):
        raise RuntimeError("The pinned PA library changed")
    graph = source_graph(module)
    source_hashes = {p.relative_to(ROOT).as_posix(): digest for p, digest in graph.items()
                     if p.is_relative_to(ROOT.resolve())}
    timings = {}

    def run(label, command, *, data=None, reject=False):
        started = time.perf_counter()
        result = subprocess.run([str(x) for x in command], cwd=ROOT,
                                input=data, capture_output=True)
        timings[label] = time.perf_counter() - started
        output = result.stdout + result.stderr
        (OUT / (module + "-" + label + ".log")).write_bytes(output)
        if reject:
            if result.returncode == 0:
                raise RuntimeError("Checker accepted the deliberately false specification")
        elif result.returncode or b"contains sorry" in output:
            raise RuntimeError(f"{label} failed; see {OUT / (module + '-' + label + '.log')}")
        return result

    compiler = args.tools / "mm0-rs.exe"
    checker = args.tools / "mm0-c.exe"
    binary = OUT / (module + ".mmb")
    joined = OUT / (module + "-joined.mm0")
    proof_input, proof_order = ((ROOT / (module + ".mm1"), []) if args.proof_input == "modular"
                                else flat_proof_input(module, graph))
    run("compile", [compiler, "compile", "--cache=false", proof_input, binary])
    run("join", [compiler, "join", source, joined])
    spec_bytes = joined.read_bytes()
    run("check-original", [checker, binary], data=spec_bytes)
    theorem_names = re.findall(r"(?m)^theorem\s+(\w+)", source.read_text(encoding="utf-8"))
    changed_theorem = theorem_names[-1]
    marker = b"theorem " + changed_theorem.encode("ascii")
    prefix, tail = spec_bytes.rsplit(marker, 1)
    binders, body = tail.split(b"$", 1)
    _, suffix = body.split(b"$;", 1)
    wrong = prefix + marker + binders + b"$ F. $;" + suffix
    run("reject-false", [checker, binary], data=wrong, reject=True)
    if graph != {path: sha(path) for path in graph}:
        raise RuntimeError("A source changed during verification")
    report = {
        "status": "PASSED",
        "module": module,
        "scope": {
            "proof_sequence": "Arithmetic proof-sequence checker, rule inclusion, and concatenation under an append-stability hypothesis",
            "mp_kernel": "Arithmetic proof-sequence checker and numerical modus ponens",
            "fol_kernel": "Numerical proof constructors for axioms, modus ponens, and unary universal generalization; syntax and logical axiom recognition remain open",
            "k230_codes": "Exact four-tag named-variable constructors, logical rows, and gated theory bundle from the literal K230 source",
            "k230_axioms": "Fixed numerical K230 axiom predicate and proofs that its generating rows are members; no arbitrary axiom-class parameter",
            "k230_proofs": "Arithmetic reverse-list proof checker for the fixed K230 axiom family, modus ponens, and named generalization",
            "k230_commands": "Exact enumerator command-prefix decoding and fixed DISCARD execution; reverse completeness remains open",
            "k230_search": "PA induction proves every candidate number is reached at a reload boundary unless the exact enumerator halts",
            "k230_reverse": "Exact numerical K230 enumerator halts iff the fixed K calculus has a finite proof of code 1; no literal-TM or full K/ZFC bridge is asserted",
            "literal_tape": "Literal K230 transition table, numeric run state bounds, and binary tape read/write equations; no enumerator bridge yet",
            "literal_iteration": "Arithmetic composition, halted-state preservation and reachability of the literal TM run function; no register/enumerator simulation yet",
            "raw_source_equality": "Actual raw K equality axiom rows 3, 5 and 7 decode to ZFC-provable formulas with exact zero handling",
            "raw_source_falsity": "ZFC provability of the decoded raw K contradiction is equivalent to concrete ZFC inconsistency",
            "zfc_proofs": "Concrete ZFC axiom contexts and full classical ND proof predicate, with explicit axiom, weakening, and MP proofs; consistency comparison remains open",
        }.get(module, "PA theorems in " + module + "; exact claims are in the separately checked source specification"),
        "checked_theorems": theorem_names,
        "new_project_axioms": False,
        "K215_halts_iff_ZFC_inconsistent_proved": False,
        "Con_ZFC_iff_K215_nonhalting_proved": False,
        "Con_ZFC_iff_BB215_has_no_ZFC_provable_value_proved": False,
        "K218_halts_iff_ZFC_inconsistent_proved": False,
        "K230_halts_iff_ZFC_inconsistent_proved": False,
        "Con_ZFC_iff_K218_nonhalting_proved": False,
        "Con_ZFC_iff_BB218_has_no_ZFC_provable_value_proved": False,
        "expanded_final_endpoint_proved": False,
        "sources": source_hashes,
        "dependency_graph_closed": True,
        "project_source_files": len(source_hashes),
        "spec_sha256": sha(joined),
        "binary_sha256": sha(binary),
        "binary_bytes": binary.stat().st_size,
        "proof_input_mode": args.proof_input,
        "proof_input_sha256": sha(proof_input),
        "proof_module_order": proof_order,
        "timings_seconds": timings,
        "wrong_conclusion_rejected": True,
        "wrong_conclusion_control": f"Only {changed_theorem} is replaced by false; all other declarations are preserved",
        "vendor": expected_vendor,
        "checker_sha256": sha(checker),
        "compiler_sha256": sha(compiler),
    }
    baseline = ROOT.parent / "lean-mm0/artifacts/peano-baseline.mmb"
    if baseline.exists():
        report["bytes_above_library_baseline"] = binary.stat().st_size - baseline.stat().st_size
    (OUT / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    (OUT / (module + "-report.json")).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        OUT.mkdir(exist_ok=True)
        failure = json.dumps({"status": "FAILED", "error": str(error)}) + "\n"
        (OUT / "report.json").write_text(failure, encoding="utf-8")
        if CURRENT_MODULE is not None:
            (OUT / (CURRENT_MODULE + "-report.json")).write_text(failure, encoding="utf-8")
        raise
