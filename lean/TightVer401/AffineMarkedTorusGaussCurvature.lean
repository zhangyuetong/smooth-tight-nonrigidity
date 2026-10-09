import TightVer401.AffineMarkedTorusLinearCurvature
import TightVer401.AffineMarkedTorusLinearApplications
import TightVer401.NativeProductPlaneTorusCoordinates
import TightVer401.ClassicalExternalApplications

/-! Actual preferred native curvature and positive image after the literal
linear marker. The metric changes; curvature has the derived positive factor. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- The global actual sphere normal is also an actual normal to the preferred
coordinate representative at its center. -/
theorem affineMarkedTorusGauss_coordinate_normal {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) (p : NonrigidTorusSource) :
    IsUnitNormalAt (nativeProductCoordinateMap X p) (data.normal p : Ambient) 0 := by
  constructor
  · rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
  · intro v
    have hd := nativeProductPlane_coordinate_fderiv
      ((data.embedding.1 p).mdifferentiableAt (by simp))
    rw [protectedTorusPositiveGauss_chart_center] at hd
    have hdv : fderiv ℝ (nativeProductCoordinateMap X p) 0 v =
        (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p : (ℝ × ℝ) →L[ℝ] Ambient)
          ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) v) :=
      congrArg (fun A : Coord →L[ℝ] Ambient => A v) hd
    apply (congrArg (fun z : Ambient => inner ℝ z (data.normal p : Ambient)) hdv).trans
    exact (real_inner_comm _ _).trans
      (data.normal_orthogonal p ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) v))

theorem affineMarkedTorusGauss_native_curvature {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) (p : NonrigidTorusSource) :
    nativeTorusChartCurvature (affineMarkedTorusLinearBase X) p =
      nativeTorusChartCurvature X p / (4 * ‖torusAffineMarkerContra (data.normal p : Ambient)‖^4) := by
  have hx := nativeProductTorusCoordinateMap_contDiff data.embedding.1 p
  have hi := nativeProductTorusCoordinateMap_fderiv_injective data.embedding.1 data.embedding.2.1 p
  have hn := affineMarkedTorusGauss_coordinate_normal data p
  have he := affineMarkedTorusLinear_gaussianCurvature isOpen_univ hx.contDiffOn
    (fun q _ => hi q) (mem_univ (0 : Coord)) hn
  have hmap : nativeProductCoordinateMap (affineMarkedTorusLinearBase X) p =
      (fun q : Coord => torusAffineMarker (nativeProductCoordinateMap X p q)) := rfl
  simp only [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center]
  rw [hmap]
  exact he

theorem affineMarkedTorusGauss_positive_iff {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) (p : NonrigidTorusSource) :
    0 < nativeTorusChartCurvature (affineMarkedTorusLinearBase X) p ↔
      0 < nativeTorusChartCurvature X p := by
  rw [affineMarkedTorusGauss_native_curvature data p]
  have hn := affineMarkedTorusGauss_coordinate_normal data p
  have hc := affineMarkedTorusLinearNormal_scale_pos hn.1
  exact div_pos_iff_of_pos_right (by positivity)

theorem affineMarkedTorusGauss_positive_region {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) :
    nativeTorusPositiveRegion (affineMarkedTorusLinearBase X) = nativeTorusPositiveRegion X := by
  ext p
  exact affineMarkedTorusGauss_positive_iff data p

/-- The actual whole positive image is marked by B, with no placement premise. -/
theorem affineMarkedTorusGauss_positive_image {X : NonrigidTorusSource → Ambient}
    (data : NativeTorusPositiveGaussData X) :
    affineMarkedTorusLinearBase X '' nativeTorusPositiveRegion (affineMarkedTorusLinearBase X) =
      torusAffineMarker '' (X '' nativeTorusPositiveRegion X) := by
  rw [affineMarkedTorusGauss_positive_region data, image_image]
  rfl

end
end TightVer401
