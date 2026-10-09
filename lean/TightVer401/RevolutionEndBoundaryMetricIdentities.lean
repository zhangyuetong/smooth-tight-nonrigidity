import TightVer401.RevolutionEndBoundaryCompleteness

namespace TightVer401
noncomputable section
open Set Bundle OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEndBoundaryEMetricSpace_edist {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) (p s : RevolutionClosedEnd H) :
    @edist (RevolutionClosedEnd H) (revolutionEndBoundaryEMetricSpace hq hpos).toEDist p s =
      (letI : RiemannianBundle
        (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
          ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
       Manifold.riemannianEDist revolutionEndBoundaryModel p s) := rfl

theorem revolutionEndBoundaryEMetricSpace_topology {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    (revolutionEndBoundaryEMetricSpace hq hpos).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (RevolutionClosedEnd H)) := rfl

end
end TightVer401
