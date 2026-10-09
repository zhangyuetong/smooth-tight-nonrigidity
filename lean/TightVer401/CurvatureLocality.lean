import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality
import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric

/-! The unchanged-region part of the curvature argument, on actual maps. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Filter
open scoped Topology

theorem inducedMetric_eventuallyEq {X Z : Coord → Ambient} {p : Coord}
    (h : X =ᶠ[𝓝 p] Z) : inducedMetric X =ᶠ[𝓝 p] inducedMetric Z := by
  filter_upwards [h.eventuallyEq_nhds] with q hq
  ext i j
  simp only [inducedMetric, coordPartial, hq.fderiv_eq]

theorem curvature_unchanged_off_support (X y : Coord → Ambient) {p : Coord}
    (hp : p ∉ tsupport y) :
    gaussianCurvature (inducedMetric (fun q => X q + y q)) p =
      gaussianCurvature (inducedMetric X) p := by
  have hy : y =ᶠ[𝓝 p] (fun _ => (0 : Ambient)) :=
    notMem_tsupport_iff_eventuallyEq.mp hp
  have hmaps : (fun q => X q + y q) =ᶠ[𝓝 p] X := by
    filter_upwards [hy] with q hq
    simp [hq]
  exact gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hmaps)

end
end TightVer401
