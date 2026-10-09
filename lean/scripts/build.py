"""Compile the selected exact OpenAI sources and ver401 proofs in isolation."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
import sys
import shutil
from concurrent.futures import ThreadPoolExecutor

sys.stdout.reconfigure(encoding="utf-8")
sys.stderr.reconfigure(encoding="utf-8")

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parents[1]
MATHLIB_PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
LEAN_VERSION = "4.33.0-rc1"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--module", default="Audit")
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        raise SystemExit("Choose between one and four compiler jobs")
    if not re.fullmatch(r"[A-Za-z0-9_.]+", args.module):
        raise SystemExit("Invalid module name")
    candidates = [ROOT / ".lake/packages",
                  WORKSPACE / "old/html_system-before-ver21-2026-09-19/formalization/lean/.lake/packages"]
    if os.environ.get("VER401_PACKAGES"):
        candidates.insert(0, Path(os.environ["VER401_PACKAGES"]))
    packages = next((p for p in candidates if (p / "mathlib/Mathlib").exists()), None)
    if packages is None:
        raise SystemExit("Missing pinned Mathlib dependency cache; run lake exe cache get.")
    executable = "lean.exe" if os.name == "nt" else "lean"
    pinned_lean = Path.home() / f".elan/toolchains/leanprover--lean4---v{LEAN_VERSION}/bin/{executable}"
    lean = Path(os.environ.get("VER401_LEAN") or (str(pinned_lean) if pinned_lean.exists() else shutil.which(executable) or executable))
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if f"version {LEAN_VERSION}," not in version:
        raise SystemExit(f"Unexpected Lean version: {version}")
    revision = subprocess.check_output(["git", "-C", str(packages / "mathlib"),
                                      "rev-parse", "HEAD"], text=True).strip()
    if revision != MATHLIB_PIN:
        raise SystemExit(f"Unexpected Mathlib revision: {revision}")
    lock = json.loads((ROOT / "upstream-lock.json").read_text(encoding="utf-8"))
    inventory = ROOT / "research/openai-math-tree.json"
    blobs = {}
    if inventory.exists():
        tree = json.loads(inventory.read_text(encoding="utf-8-sig"))
        blobs = {r["path"]: r["sha"] for r in tree["tree"] if r["type"] == "blob"}
    geometry_inventory = ROOT / "research/openai-geometry-tree.json"
    if geometry_inventory.exists():
        geometry_tree = json.loads(geometry_inventory.read_text(encoding="utf-8-sig"))
        blobs.update({"lean/OAI/Geometry/" + r["path"]: r["sha"]
                      for r in geometry_tree["tree"] if r["type"] == "blob"})
    for row in lock["modules"]:
        path = ROOT / "vendor/openai-math" / row["path"]
        if digest(path) != row["sha256"]:
            raise SystemExit(f"Changed upstream source: {path}")
        data = path.read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
        expected = row.get("git_blob_sha1") or blobs.get(row["path"])
        if expected is None or expected != blob:
            raise SystemExit(f"Upstream Git blob mismatch: {path}")
        row["git_blob_sha1"] = blob
    (ROOT / "upstream-lock.json").write_text(json.dumps(lock, indent=2) + "\n", encoding="utf-8")
    schoenflies_lock_path = ROOT / "schoenflies-lock.json"
    schoenflies_lock = json.loads(schoenflies_lock_path.read_text(encoding="utf-8")) if schoenflies_lock_path.exists() else None
    if schoenflies_lock:
        if schoenflies_lock["commit"] != "05a43d29cde026618777db3d4e4316204ccca237":
            raise SystemExit("Unexpected Schoenflies dependency revision")
        for row in [*schoenflies_lock["modules"], schoenflies_lock["license"]]:
            path = ROOT / "vendor/schoenflies" / row["path"]
            data = path.read_bytes()
            blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
            if digest(path) != row["sha256"] or blob != row["git_blob_sha1"]:
                raise SystemExit(f"Changed pinned Schoenflies source: {path}")
    out, logs = ROOT / ".lake/build/lib/lean", ROOT / "build-logs"
    out.mkdir(parents=True, exist_ok=True)
    logs.mkdir(exist_ok=True)
    paths = [out] + sorted(p / ".lake/build/lib/lean" for p in packages.iterdir()
                           if (p / ".lake/build/lib/lean").exists())
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    results, seen, prepared = [], set(), {}

    def source(module):
        base = (ROOT / "vendor/openai-math/lean" if module.startswith("OAI.") else
                ROOT / "vendor/schoenflies" if module.startswith("Schoenflies.") else ROOT)
        return base / (module.replace(".", "/") + ".lean")

    def prepare_module(module):
        if module in seen:
            return
        seen.add(module)
        src = source(module)
        text = src.read_text(encoding="utf-8-sig")
        compile_src = src
        if module == "Schoenflies.Subarc":
            before = "simpa [reparam, smul_eq_mul] using h"
            after = "change (fun θ : ℝ => a + θ * (b - a)) '' Icc (0 : ℝ) 1 = uIcc a b\n  simpa only [smul_eq_mul] using h"
            if text.count(before) != 1:
                raise RuntimeError("Pinned Schoenflies interval proof changed; review compatibility.")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module in {"Schoenflies.InitialPair", "Schoenflies.Endgame"}:
            # Mathlib renamed the restriction operation. The deprecated theorem
            # already states the new operation, while deprecated definitions
            # appearing in the original proof no longer rewrite syntactically.
            text = text.replace("continuousOn_iff_continuous_restrict", "continuousOn_iff_continuous_domRestrict")
            text = re.sub(r"\brestrict\b", "domRestrict", text)
            text = text.replace("Set.restrict_apply", "Set.domRestrict_apply")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Topology.CutoffStaircase":
            before = """convert hd using 1
  · rfl
  · ext v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, Pi.sub_apply,
      Function.comp_apply]
    ring"""
            after = """convert! hd using 1 <;> ext v <;>
    simp [cutoffStaircase, Function.comp_def] <;> ring"""
            if text.count(before) != 1:
                raise RuntimeError("Pinned cutoff derivative proof changed")
            text = "set_option backward.isDefEq.respectTransparency false\n" + text.replace(before, after)
            # Imports must remain the first commands in Lean source.
            text = text.replace("set_option backward.isDefEq.respectTransparency false\nimport OAI.Analysis.CircleDomains.Topology.ComponentControl",
                "import OAI.Analysis.CircleDomains.Topology.ComponentControl\nset_option backward.isDefEq.respectTransparency false")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Probability.PathLengthMeasure":
            before = "(γ.property.continuousAt_variationOnFromTo_iff ⊥ t).mpr γ.val.continuous.continuousAt"
            if text.count(before) != 1:
                raise RuntimeError("Pinned path-length variation continuity proof changed")
            text = "import TightVer401.VariationContinuity\n" + text.replace(before,
                "TightVer401.continuousAt_variationOnFromTo_of_continuousAt γ.property γ.val.continuous.continuousAt")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Selection.FinitelySuslinian":
            before = "hSfinite.sdiff.isClosed_sUnion (fun C hC => (hS C hC.1).1.isClosed)"
            if text.count(before) != 1:
                raise RuntimeError("Pinned finite continuum closed union changed")
            text = text.replace(before,
                "by\n      rw [show B = ⋃ C ∈ S \\ {C₀}, C from Set.sUnion_eq_biUnion]\n      exact hSfinite.sdiff.isClosed_biUnion (fun C hC => (hS C hC.1).1.isClosed)")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Topology.ClopenNeighborhood":
            before = "(fun V => V.property.1.isClosed) hd"
            if text.count(before) != 1 or text.count("Set.disjoint_left.mp hs hyO hy") != 1:
                raise RuntimeError("Pinned clopen-neighborhood intersection proof changed")
            text = text.replace(before, "(fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)")
            text = text.replace("Set.disjoint_left.mp hs hyO hy",
                "Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Topology.BoundaryBumping":
            before = "(fun U => U.property.1.isClosed) hd"
            if text.count(before) != 1 or text.count("Set.disjoint_left.mp hs hzK hz") != 1:
                raise RuntimeError("Pinned boundary-bumping finite-intersection proof changed")
            text = text.replace(before, "(fun U => U.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)")
            text = text.replace("Set.disjoint_left.mp hs hzK hz",
                "Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hzK hz")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Selection.DustCover":
            before = "  let : CompactSpace B := isCompact_iff_compactSpace.mp hB"
            if text.count(before) != 1:
                raise RuntimeError("Pinned dust cover subtype instance site changed")
            text = "import Mathlib.Topology.MetricSpace.Basic\n" + text
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Selection.RegularLevelFlow":
            before = "exact (hV.of_le (by simp)).comp ih"
            after = "exact (hV.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).comp ih"
            if text.count(before) != 1:
                raise RuntimeError("Pinned regular-level smooth induction changed")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Selection.RegularContours":
            before = "ContinuousLinearMap.isOpen_setOfPred_isInvertible"
            if text.count(before) != 1 or text.count("dite_eq_left hy") != 1:
                raise RuntimeError("Pinned regular-contour compatibility sites changed")
            text = "import TightVer401.TopologyCompatibility\n" + text.replace(
                before, "TightVer401.continuousLinearMap_isOpen_isInvertible").replace(
                "dite_eq_left hy", "dite_eq_left_decidable hy").replace(
                "simp only [levelChartInverse, dite_eq_left_decidable hy]",
                "classical\n  simp only [levelChartInverse, dite_eq_left_decidable hy]")
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic":
            before = "AddCircle.continuous_equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero"
            after = "(AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).continuous"
            if text.count(before) != 1:
                raise RuntimeError("Pinned normalized-argument continuity proof changed")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Sobolev.ClosedDiskIntegral":
            before = "simp only [mem_inter_iff,mem_closedBall,mem_ball]"
            after = "change (z ∈ U ∧ dist z c ≤ r) ↔ (z ∈ U ∧ dist z c < r)"
            if text.count(before) != 1:
                raise RuntimeError("Pinned closed-disk integral compatibility site changed")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module in {"OAI.Geometry.IsometricImmersion.Immersions.InducedMetric",
                      "OAI.Geometry.WeakMTW.Geodesics.IntrinsicExp"}:
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            text = "import TightVer401.Compatibility\n" + text
            compile_src.write_text(text, encoding="utf-8")
        if module.startswith("OAI.Geometry.Borsuk.") and re.search(
                r"\b(?:d?ite_eq_(?:left|right))\b", text):
            text = re.sub(r"\b(d?ite_eq_(?:left|right))\b", r"\1_decidable", text)
            text = "import TightVer401.BorsukCompatibility\n" + text
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Selection.FinitePatching":
            # Preserve the decidability instances in the exact pinned proof.
            # The same aliases are already checked for the Borsuk sources.
            if text.count("dite_eq_left") != 2 or text.count("dite_eq_right") != 1:
                raise RuntimeError("Pinned finite-patching compatibility sites changed")
            text = re.sub(r"\b(dite_eq_(?:left|right))\b", r"\1_decidable", text)
            text = "import TightVer401.BorsukCompatibility\n" + text
            text = text.replace("namespace OAI", "attribute [local instance] Classical.propDecidable\nset_option backward.isDefEq.respectTransparency false\n\nnamespace OAI", 1)
            before = "  · simp only [patchOpenRegions, dite_eq_left_decidable hm]\n    exact hy (Classical.choose hm) (Classical.choose_spec hm)"
            after = """  · unfold patchOpenRegions
    split_ifs
    exact hy (Classical.choose hm) (Classical.choose_spec hm)"""
            if text.count(before) != 1:
                raise RuntimeError("Pinned finite-patching reduction site changed")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Sobolev.WedgeIntegrability":
            # Local MemLp.mul takes the scalar factor second, opposite to
            # the native pinned profile; real multiplication is commutative.
            for before, after in [(":= hu1.mul hv2", ":= hv2.mul (r := 1) hu1"),
                                  (":= hu2.mul hv1", ":= hv1.mul (r := 1) hu2")]:
                if text.count(before) != 1:
                    raise RuntimeError("Pinned wedge-integrability product site changed")
                text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        conditional_sites = {
            "OAI.Analysis.CircleDomains.Topology.CircleLifts": {"dite_eq_left": 3},
            "OAI.Analysis.CircleDomains.Transfer.FilledCoordinates": {
                "ite_eq_left": 2, "ite_eq_right": 3},
            "OAI.Analysis.CircleDomains.Transfer.FilledMetric": {
                "dite_eq_left": 3, "dite_eq_right": 1},
            "OAI.Analysis.CircleDomains.Selection.UpperPairs": {"dite_eq_left": 2},
            "OAI.Analysis.CircleDomains.Sobolev.OriginalDomainMetric": {"dite_eq_left": 2},
            "OAI.Analysis.CircleDomains.Rigidity.MaskedMetric": {"dite_eq_left": 1},
        }
        if module in conditional_sites:
            for name, count in conditional_sites[module].items():
                if len(re.findall(r"\b" + name + r"\b", text)) != count:
                    raise RuntimeError("Pinned circle-coordinate conditional sites changed")
                text = re.sub(r"\b" + name + r"\b", name + "_decidable", text)
            text = "import TightVer401.BorsukCompatibility\n" + text
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Sobolev.CircleDifferentialClosed":
            replacements = {
                "huAt.fderiv_right (m := 1) (by simp)":
                    "huAt.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))",
                "huAt.isSymmSndFDerivAt (by simp)":
                    "huAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)",
            }
            for before, after in replacements.items():
                if text.count(before) != 1:
                    raise RuntimeError("Pinned circle Hessian-order proof sites changed")
                text = text.replace(before, after)
            text = text.replace("namespace OAI", "set_option backward.isDefEq.respectTransparency false\nnamespace OAI", 1)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Topology.PlanarFormPullback":
            replacements = {
                "hF.contDiffAt.fderiv_right (m := 1) (by simp)":
                    "hF.contDiffAt.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))",
                "(hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)":
                    "(hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)",
            }
            for before, after in replacements.items():
                if text.count(before) != 1:
                    raise RuntimeError("Pinned planar pullback Hessian-order sites changed")
                text = text.replace(before, after)
            text = text.replace("namespace OAI", "set_option backward.isDefEq.respectTransparency false\nnamespace OAI", 1)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization":
            before = """  convert (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
    ((hasDerivAt_id t).const_mul (2*Real.pi)) using 1 <;>
    simp only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_one]
  ring"""
            after = """  simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one, mul_one, one_mul, mul_comm] using
    (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
      ((hasDerivAt_id t).const_mul (2*Real.pi))"""
            if text.count(before) != 1:
                raise RuntimeError("Pinned round-circle chain-rule simplification site changed")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        if module == "OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus":
            before = "exact (HasMFDerivAt.sum (fun i hi => (hf i hi).hasMFDerivAt)).mfderiv"
            after = """classical
  have hsum : ∀ t : Finset ι,
      (∀ i ∈ t, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) →
      HasMFDerivAt planeModel 𝓘(ℝ,V) (∑ i ∈ t, f i) p
        (∑ i ∈ t, surfaceDifferential (f i) p) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        convert! (hasMFDerivAt_const (I := planeModel) (I' := 𝓘(ℝ,V)) (0 : V) p) using 1 <;> simp
    | @insert i t hi ih =>
        intro ht
        have hdi := (ht i (by simp)).hasMFDerivAt
        have hdt := ih (fun j hj => ht j (by simp [hj]))
        convert! hdi.add hdt using 1 <;> simp [Finset.sum_insert hi, surfaceDifferential]
  exact (hsum s hf).mfderiv"""
            if text.count(before) != 1:
                raise RuntimeError("Upstream manifold proof changed; review the compatibility transformation.")
            text = text.replace(before, after)
            compile_src = ROOT / ".lake/compatibility-source" / (module.replace(".", "/") + ".lean")
            compile_src.parent.mkdir(parents=True, exist_ok=True)
            compile_src.write_text(text, encoding="utf-8")
        imports = re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", text, re.M)
        local = [i for i in imports if i.startswith(("OAI.", "TightVer401.", "Schoenflies."))
                 or i == "TightVer401"]
        if any(i.startswith(("IdentityHolonomy", "ProofAtlas", "GeometricFoundations")) for i in imports):
            raise SystemExit(f"Legacy project import is prohibited: {module}")
        if module.startswith("OAI.") and module not in {r["module"] for r in lock["modules"]}:
            raise SystemExit(f"Unlocked OpenAI module: {module}")
        if module.startswith("Schoenflies.") and (not schoenflies_lock or
                module not in {r["module"] for r in schoenflies_lock["modules"]}):
            raise SystemExit(f"Unlocked Schoenflies module: {module}")
        for dep in local:
            prepare_module(dep)
        prepared[module] = (src, compile_src, local)

    def compile_module(module):
        src, compile_src, local = prepared[module]
        obj = out / (module.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        key = {"source_sha256": digest(src), "compiled_source_sha256": digest(compile_src), "lean_version": version,
               "mathlib_pin": MATHLIB_PIN,
               "dependencies": {dep: digest(out / (dep.replace(".", "/") + ".olean")) for dep in local}}
        lean_options = []
        if module in {"OAI.Geometry.SurfaceImmersion.Geometry.ManifoldMetricCalculus",
                      "TightVer401.ManifoldBranching"}:
            lean_options = ["-Dbackward.isDefEq.respectTransparency=false"]
            key["lean_options"] = lean_options
        stamp, log = logs / (module + ".json"), logs / (module + ".log")
        if not args.fresh and stamp.exists() and obj.exists() and log.exists():
            record = json.loads(stamp.read_text())
            if record["key"] == key and record["exit_code"] == 0 and record["olean_sha256"] == digest(obj):
                results.append(record)
                print(f"{module}: current", flush=True)
                return
        start = time.monotonic()
        run = subprocess.run([str(lean), *lean_options, "-o", str(obj), str(compile_src)], cwd=ROOT, env=env,
                             capture_output=True, text=True, encoding="utf-8", errors="replace")
        log.write_text(run.stdout + run.stderr, encoding="utf-8")
        record = {"module": module, "source": str(src.relative_to(ROOT)),
                  "compiled_source": str(compile_src.relative_to(ROOT)), "key": key,
                  "exit_code": run.returncode, "elapsed_seconds": round(time.monotonic()-start, 3),
                  "olean_sha256": digest(obj) if run.returncode == 0 else None,
                  "log_sha256": digest(log)}
        stamp.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        results.append(record)
        print(f"{module}: exit {run.returncode} ({record['elapsed_seconds']}s)", flush=True)
        if run.returncode:
            print(run.stdout + run.stderr, flush=True)
            raise RuntimeError(f"Compilation failed: {module}")
    success = False
    try:
        prepare_module(args.module)
        todo, done = set(prepared), set()
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while todo:
                ready = sorted(m for m in todo if set(prepared[m][2]) <= done)
                if not ready:
                    raise RuntimeError("Cyclic local import graph")
                futures = [pool.submit(compile_module, m) for m in ready]
                for future in futures:
                    future.result()
                done.update(ready)
                todo.difference_update(ready)
        success = True
    finally:
        report = {"success": success, "upstream_commit": lock["commit"],
                  "upstream_native_lean": "4.34.1",
                  "upstream_native_mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
                  "build_profile": "source-compatibility", "version": version,
                  "mathlib_pin": MATHLIB_PIN, "compiler_jobs": args.jobs,
                  "schoenflies_lock_sha256": digest(schoenflies_lock_path) if schoenflies_lock else None,
                  "search_paths": list(map(str, paths)), "modules": sorted(results, key=lambda r: r["module"])}
        (logs / (args.module + ".build.json")).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

if __name__ == "__main__":
    main()
