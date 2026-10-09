import TightVer401.AffineMarkedTorusGaussApplications
import TightVer401.ProtectedTorusActualCylinderNoPlanarConnection
import TightVer401.TorusMarkedBranchGermConnection

/-! Actual nonzero-curvature density and absence of open planar patches for
literal marked branches on the SAME cylinder and once-chosen full meridian.
No branch is identified with an affine image of an unmarked branch. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem affineMarkedTorus_nonzero_curvature_dense
    {F : NonrigidTorusSource → Ambient} (data : NativeTorusPositiveGaussData F)
    (hdense : Dense {p | nativeTorusChartCurvature F p ≠ 0}) :
    Dense {p | nativeTorusChartCurvature (affineMarkedTorusLinearBase F) p ≠ 0} := by
  apply hdense.mono
  intro p hp
  change nativeTorusChartCurvature F p ≠ 0 at hp
  change nativeTorusChartCurvature (affineMarkedTorusLinearBase F) p ≠ 0
  rw [affineMarkedTorusGauss_native_curvature data p]
  have hn := affineMarkedTorusGauss_coordinate_normal data p
  have hc := affineMarkedTorusLinearNormal_scale_pos hn.1
  exact div_ne_zero hp (mul_pos (by norm_num) (pow_pos hc _)).ne'

theorem affineMarkedTorus_actualCylinder_nonzero_curvature_dense {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    Dense {p | nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h)) p ≠ 0} :=
  affineMarkedTorus_nonzero_curvature_dense
    (protectedTorusActualCylinderPositiveGaussData S D C)
    (protectedTorusActualCylinder_nonzero_curvature_dense S D C)

theorem affineMarkedTorus_actualCylinder_bending_hasNoOpenPlanarPatch
    {RN mu h T w : ℝ} [Fact (0 < T)]
    (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (a : ℝ)
    (hplus : NativeTorusSmoothEmbedding
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)))
    (hminus : NativeTorusSmoothEmbedding
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)))
    (hplusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) p < 0)
    (hminusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) p < 0) :
    HasNoOpenPlanarPatch
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) ∧
    HasNoOpenPlanarPatch
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) := by
  let F := protectedTorusMap S.saddle D.meridian h
  let B := torusAffineMarkerLinearEquiv.toContinuousLinearMap
  let V := torusAffineMarkerContraLinearEquiv.toContinuousLinearMap
  have hdense := affineMarkedTorus_actualCylinder_nonzero_curvature_dense S D C
  have hdplus := nativeTorus_nonzero_curvature_dense_of_support_negative
    (e '' tsupport Y) hdense hplusneg
    (fun p hp => (protectedTorus_marked_curvature_off_support
      e A hcompact hsupport F B V a hp).1)
  have hdminus := nativeTorus_nonzero_curvature_dense_of_support_negative
    (e '' tsupport Y) hdense hminusneg
    (fun p hp => (protectedTorus_marked_curvature_off_support
      e A hcompact hsupport F B V a hp).2)
  exact ⟨nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature
      hplus.1 hplus.2.1 hdplus,
    nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature
      hminus.1 hminus.2.1 hdminus⟩

end
end TightVer401
