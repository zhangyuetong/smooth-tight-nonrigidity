import TightVer401.AffineMarkedTorusGaussApplications
import TightVer401.TorusMarkedImageNoncongruenceConnection

/-! Connect the proved literal same-meridian marker stabilizer to the actual
ambient affine-isometry predicate used by native image noncongruence. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem affineMarkedTorus_actual_positive_image_affine_rigid
    (axes : MarkerEllipseAxesRecognition) {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hp : A '' (affineMarkedTorusLinearBase
        (protectedTorusMap S.saddle D.meridian h) '' nativeTorusPositiveRegion
          (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h))) =
      affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) ''
        nativeTorusPositiveRegion
          (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h))) :
    ∀ p, A p = p := by
  have hfun : torusAffineMarkerIsometry A.linearIsometryEquiv (A 0) = A := by
    funext p
    symm
    simpa only [torusAffineMarkerIsometry, vadd_eq_add, add_zero] using
      A.map_vadd (0 : Ambient) p
  have hrigid := affineMarkedTorusGauss_actualCylinder_positive_image_rigid
    axes S D C A.linearIsometryEquiv (A 0)
  rw [hfun] at hrigid
  exact hrigid hp

end
end TightVer401
