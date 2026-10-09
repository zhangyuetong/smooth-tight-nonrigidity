"""Check compiled proof closure, upstream provenance, and honest paper coverage."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys
import argparse

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
sys.stdout.reconfigure(encoding="utf-8")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed comment")
    return "".join(out)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    target_lock = json.loads((ROOT / "target-lock.json").read_text(encoding="utf-8"))
    active_manuscript = ROOT.parent / target_lock["manuscript"]
    assert target_lock["active_formalization"] == "lean" and target_lock["target"] == "ver503"
    assert sha(active_manuscript) == target_lock["sha256"]
    assert active_manuscript.read_bytes() == (ROOT / "target/manuscript.tex").read_bytes()
    review_path = ROOT / "target/ver503-reuse-review.json"
    review = json.loads(review_path.read_text(encoding="utf-8"))
    assert review["manuscript_sha256"] == target_lock["sha256"]
    report_path = ROOT / "kernel-report.json"
    if report_path.exists():
        report_path.unlink()
    command = [sys.executable, str(ROOT / "scripts/build.py"), "--module", "Audit", "--jobs", str(args.jobs)]
    if args.fresh:
        command.append("--fresh")
    subprocess.run(command, cwd=ROOT, check=True)
    build = json.loads((ROOT / "build-logs/Audit.build.json").read_text())
    assert build["success"]
    for row in build["modules"]:
        src = ROOT / row["source"]
        compiled = ROOT / row["compiled_source"]
        assert sha(src) == row["key"]["source_sha256"], src
        assert sha(compiled) == row["key"]["compiled_source_sha256"], compiled
        tokens = re.findall(r"\b(?:sorry|admit|axiom|unsafe|implemented_by)\b",
                            code_only(compiled.read_text(encoding="utf-8-sig")))
        assert not tokens, (compiled, tokens)
        obj = ROOT / ".lake/build/lib/lean" / (row["module"].replace(".", "/") + ".olean")
        assert sha(obj) == row["olean_sha256"], obj
        log = ROOT / "build-logs" / (row["module"] + ".log")
        assert sha(log) == row["log_sha256"], log
    audit = (ROOT / "build-logs/Audit.log").read_text(encoding="utf-8")
    declarations = [json.loads(line.removeprefix("VER401_AUDIT "))
                    for line in audit.splitlines() if line.startswith("VER401_AUDIT ")]
    counts = re.findall(r"^VER401_AUDIT_COUNT (\d+)$", audit, re.M)
    assert len(counts) == 1 and int(counts[0]) == len(declarations) > 0
    names = {r["name"] for r in declarations}
    assert len(names) == len(declarations)
    for row in declarations:
        assert set(row["axioms"]) <= ALLOWED and row["kind"] != "axiom", row
    subprocess.run([sys.executable, str(ROOT / "scripts/inventory.py")], check=True)
    coverage = json.loads((ROOT / "coverage.json").read_text(encoding="utf-8"))
    for claim in coverage["claims"]:
        assert set(claim["proved_declarations"]) <= names
    for exports in coverage["additional_checked_scope"].values():
        assert set(exports) <= names
    lock = json.loads((ROOT / "upstream-lock.json").read_text())
    external_lock = ROOT / "schoenflies-lock.json"
    if any(row["module"].startswith("Schoenflies.") for row in build["modules"]):
        assert external_lock.exists() and sha(external_lock) == build["schoenflies_lock_sha256"]
    result = {"result": "PASS", "generated_at_utc": datetime.now(timezone.utc).isoformat(),
              "paper_completion": "INCOMPLETE", "target": coverage["target"],
              "primary_objective": coverage["primary_objective"], "manuscript_sha256": coverage["manuscript_sha256"],
              "upstream_commit": lock["commit"], "upstream_lock_sha256": sha(ROOT / "upstream-lock.json"),
              "schoenflies_lock_sha256": build.get("schoenflies_lock_sha256"),
              "build_profile": build["build_profile"], "version": build["version"],
              "mathlib_pin": build["mathlib_pin"], "allowed_axioms": sorted(ALLOWED),
              "custom_axioms": [], "admissions": [], "modules": build["modules"],
              "coverage_sha256": sha(ROOT / "coverage.json"),
              "declarations": sorted(declarations, key=lambda r: r["name"]),
              "warning": "Checks the declared Lean types and exact compiled closure; not full-paper completion."}
    closure = [{"module": row["module"], "source_sha256": row["key"]["source_sha256"],
                "compiled_source_sha256": row["key"]["compiled_source_sha256"],
                "dependencies": row["key"]["dependencies"], "olean_sha256": row["olean_sha256"]}
               for row in sorted(build["modules"], key=lambda r: r["module"])]
    result["source_closure_sha256"] = hashlib.sha256(json.dumps(closure, sort_keys=True).encode()).hexdigest()
    result["source_git_commit"] = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    result["target_lock_sha256"] = sha(ROOT / "target-lock.json")
    result["migration_review_sha256"] = sha(review_path)
    result["classical_registry_sha256"] = sha(ROOT / "classical-external-results.json")
    result["lean_toolchain_sha256"] = sha(ROOT / "lean-toolchain")
    result["lakefile_sha256"] = sha(ROOT / "lakefile.toml")
    result["verification_scripts"] = {name: sha(ROOT / "scripts" / name) for name in ["build.py", "verify.py", "inventory.py"]}
    report_path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: OpenAI foundation and retained exports compiled and audited against {coverage['target']}; full paper remains incomplete.")

if __name__ == "__main__":
    main()
