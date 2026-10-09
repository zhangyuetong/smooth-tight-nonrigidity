import TightVer401.AffineMarkedTorusGaussData
import TightVer401.ProtectedTorusPositiveGaussData
import TightVer401.ProtectedTorusPositiveGaussImageActualCylinder
import TightVer401.TorusAffineMarkerEllipseAnnulus
import TightVer401.AffineMarkedTorusLinearNativeNormals

/-! The literal marker applied to the same completed saddle and constructed
meridian. Actual curvature transport identifies the entire positive image;
the derived endpoint ellipses and actual meridian asymmetry force its rigid
stabilizer to be the identity. The generic single-ellipse recognition result
remains an explicit background parameter, not a stabilizer hypothesis. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- The same marked producer uses the actual global native cross normal,
so off-support branch normal identities preserve its chosen orientation. -/
theorem affineMarkedTorusGauss_actualCylinder_normal_eq_native {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S) (p : NonrigidTorusSource) :
    let data := protectedTorusActualCylinderPositiveGaussData S D C
    (affineMarkedTorusPositiveGaussData data).normal p =
      nativeTorusImmersionNormal
        (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h))
        (affineMarkedTorusLinearBase_immersion data.embedding.1 data.embedding.2.1) p := by
  let data := protectedTorusActualCylinderPositiveGaussData S D C
  change torusAffineMarkerContraSphereDiffeomorph
    (nativeTorusImmersionNormal (protectedTorusMap S.saddle D.meridian h)
      data.embedding.2.1 p) = _
  exact (affineMarkedTorusLinear_nativeNormal data.embedding.1 data.embedding.2.1 p).symm

/-- Exact whole marked positive image of the same actual constructed torus. -/
theorem affineMarkedTorusGauss_actualCylinder_positive_image {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) ''
      nativeTorusPositiveRegion
        (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h)) =
      torusAffineMarker '' parabolicConvexClosureLateralCarrier D.meridian h := by
  rw [affineMarkedTorusGauss_positive_image
    (protectedTorusActualCylinderPositiveGaussData S D C),
    protectedTorusPositiveGauss_actualCylinder_positive_image S D C]

/-- Every rigid motion preserving the entire actual marked positive image
is the identity; no positive-image or stabilizer conclusion is an input. -/
theorem affineMarkedTorusGauss_actualCylinder_positive_image_rigid
    (axes : MarkerEllipseAxesRecognition) {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S)
    (L : Ambient ≃ₗᵢ[ℝ] Ambient) (b : Ambient)
    (hp : torusAffineMarkerIsometry L b ''
        (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) ''
          nativeTorusPositiveRegion
            (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h))) =
      affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) ''
        nativeTorusPositiveRegion
          (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h))) :
    ∀ p, torusAffineMarkerIsometry L b p = p := by
  rw [affineMarkedTorusGauss_actualCylinder_positive_image S D C] at hp
  exact torusAffineMarker_actual_meridian_rigid axes D L b hp

end
end TightVer401
