import TightVer401.TorusMarkedRigidityConnection
import TightVer401.TorusMarkedBranchGermConnection
import TightVer401.TorusMetricBranching

/-! Connect literal marked opposite branches to actual image noncongruence.
The SAME original cylinder, full meridian, protected field and amplitude occur
in every premise and conclusion. Branch embedding/support negativity are outputs
of the separate actual small-amplitude stability caller. No original object is
granted; the classical premises remain explicit. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem affineMarkedTorus_actualCylinder_bending_imageNoncongruent
    (background : ClassicalExternalResults)
    (reparam : ClassicalEmbeddedImageReparametrizationClaim)
    (axes : MarkerEllipseAxesRecognition) {RN mu h T w : ℝ} [Fact (0 < T)]
    (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (Cdata : ProtectedTorusActualGraphCylinderData S)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (hnonzero : ∃ p, Y p ≠ 0)
    (hZ : nativeProductIsBending (protectedTorusMap S.saddle D.meridian h)
      (protectedTorusBendingField e A Y))
    (hout : ∃ q, q ∉ e '' tsupport Y)
    {a : ℝ} (ha : a ≠ 0)
    (hplus : NativeTorusSmoothEmbedding
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)))
    (hminus : NativeTorusSmoothEmbedding
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)))
    (hFneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h)) p < 0)
    (hplusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) p < 0)
    (hminusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) p < 0) :
    ImageNoncongruent
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) +
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y))
      (affineMarkedTorusLinearBase (protectedTorusMap S.saddle D.meridian h) -
        a • affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)) := by
  let F := protectedTorusMap S.saddle D.meridian h
  let G := affineMarkedTorusLinearBase F
  let W := affineMarkedTorusLinearBending (protectedTorusBendingField e A Y)
  let B := torusAffineMarkerLinearEquiv.toContinuousLinearMap
  let C := torusAffineMarkerContraLinearEquiv.toContinuousLinearMap
  let U := (e '' tsupport Y)ᶜ
  have hF := (protectedTorusActualCylinderPositiveGaussData S D Cdata).embedding
  obtain ⟨_hpr,_hmr,_hpa,_hma,hpi,hmi,_himages⟩ :=
    protectedTorus_marked_positive_regions e A hcompact hsupport F B C a
      hFneg hplusneg hminusneg
  have hopen : IsOpen U :=
    (protectedTorusBendingField_support_image_isCompact e hcompact hsupport).isClosed.isOpen_compl
  have hagree : EqOn (G + a • W) (G - a • W) U := by
    intro p hp
    have hgerm := protectedTorus_marked_branch_germs_off_support
      e A hcompact hsupport F B C a hp
    exact hgerm.1.self_of_nhds.trans hgerm.2.self_of_nhds.symm
  have hnonzeroW : ∃ p, W p ≠ 0 :=
    (affineMarkedTorusLinearBending_nonzero_iff _).mpr
      (protectedTorusBendingField_nonzero e A hsupport hnonzero)
  have hmaps : G + a • W ≠ G - a • W := by
    intro heq
    obtain ⟨p,hp⟩ := hnonzeroW
    have he' : G p + a • W p = G p + -(a • W p) := by
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]
        using congrFun heq p
    have he := add_left_cancel he'
    have hz : (a+a) • W p = 0 := by
      rw [add_smul]
      exact (congrArg (fun z : Ambient => z+a • W p) he).trans (neg_add_cancel _)
    have hs : a+a ≠ 0 := by intro h; apply ha; linarith
    exact hp ((smul_eq_zero.mp hz).resolve_left hs)
  exact torusImageNoncongruent_of_positive_marker_and_open_agreement
    reparam background (G+a • W) (G-a • W) hplus hminus
    (affineMarkedTorusLinear_opposite_native_forms hF.1 hZ a)
    U hopen hout hagree hmaps (G '' nativeTorusPositiveRegion G) hpi hmi
    (affineMarkedTorus_actual_positive_image_affine_rigid axes S D Cdata)

end
end TightVer401
