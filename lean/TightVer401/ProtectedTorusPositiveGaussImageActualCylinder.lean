import TightVer401.ProtectedTorusPositiveGaussImage
import TightVer401.ProtectedTorusPositiveGaussCurvatureActualGraphCylinder

/-! The positive-curvature image of the actual completed saddle and SAME
constructed meridian. The actual K-sign classification, not a sign grant,
identifies the source phase; the exact producer image bridge identifies its
ambient image. No metric or image-inequality integration is duplicated. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Actual completed graph-cylinder K-positive region is the actual open convex phase. -/
theorem protectedTorusPositiveGauss_actualCylinder_region_eq_phase {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h) =
      (protectedTorusPositiveGaussRegion : Set NonrigidTorusSource) := by
  ext p
  exact (protectedTorusPositiveGauss_actualCylinder_curvature_pos_iff S D C p).trans
    (protectedTorusPositiveGaussRegion_iff p).symm

/-- Actual positive-curvature image is exactly the full SAME-meridian lateral carrier. -/
theorem protectedTorusPositiveGauss_actualCylinder_positive_image {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    protectedTorusMap S.saddle D.meridian h ''
      nativeTorusPositiveRegion (protectedTorusMap S.saddle D.meridian h) =
      parabolicConvexClosureLateralCarrier D.meridian h := by
  rw [protectedTorusPositiveGauss_actualCylinder_region_eq_phase S D C]
  exact protectedTorusPositiveGauss_phase_image S.saddle D

end
end TightVer401
