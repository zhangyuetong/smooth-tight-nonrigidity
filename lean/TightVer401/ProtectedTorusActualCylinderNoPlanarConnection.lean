import TightVer401.ProtectedTorusPositiveGaussCurvatureActualGraphCylinder
import TightVer401.CompletedSaddleTorusMeridianWitnessConnection
import TightVer401.TorusNonzeroCurvatureDensityConnection
import TightVer401.TorusNoPlanarPatchConnection

/-! Actual nonzero curvature and absence of open planar patches for the SAME
completed saddle and full convex meridian. No curvature, density or planar-patch
conclusion is an input: the actual-cylinder scalar data supplies the saddle sign,
and the chosen full meridian supplies the convex sign and native embedding. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Actual curvature is nonzero off the two literal quotient phase seams.
The scalar period representative falls in exactly one of the strict phases. -/
theorem protectedTorusActualCylinder_curvature_ne_zero_off_seams {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h)
    (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S)
    (p : NonrigidTorusSource) (hsouth : p.2 ≠ 0)
    (hnorth : p.2 ≠ periodProjection (2 * Real.pi) Real.pi) :
    nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p ≠ 0 := by
  let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  have hu : u ∈ Ico (0 : ℝ) (2 * Real.pi) := by
    simpa [u] using (AddCircle.equivIco (2 * Real.pi) 0 p.2).property
  have hp : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
  have hu0 : u ≠ 0 := by
    intro hu0
    apply hsouth
    rw [← hp, hu0]
    rfl
  have huPi : u ≠ Real.pi := by
    intro huPi
    apply hnorth
    rw [← hp, huPi]
  by_cases hup : u < Real.pi
  · exact (protectedTorusPositiveGauss_actualCylinder_saddle_curvature_neg
      S C D.meridian p
      (show u ∈ Ioo (0 : ℝ) Real.pi from
        ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hup⟩)).ne
  · have hconvex : u ∈ Ioo Real.pi (2 * Real.pi) :=
      ⟨lt_of_le_of_ne (le_of_not_gt hup) (Ne.symm huPi), hu.2⟩
    exact ((protectedTorusPositiveGauss_actualCylinder_curvature_pos_iff S D C p).mpr
      hconvex).ne'

/-- Density is derived on the same native torus from its two literal phase seams. -/
theorem protectedTorusActualCylinder_nonzero_curvature_dense {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h)
    (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    Dense {p : NonrigidTorusSource |
      nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p ≠ 0} := by
  exact nativeTorus_nonzero_curvature_dense_of_off_seams
    (protectedTorusMap S.saddle D.meridian h)
    (protectedTorusActualCylinder_curvature_ne_zero_off_seams S D C)

/-- The SAME actual cylinder and chosen full meridian have no open planar patch.
Smoothness and rank are derived by the retained native assembly, without choosing
another meridian or requiring an additional embedding premise. -/
theorem protectedTorusActualCylinder_hasNoOpenPlanarPatch {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h)
    (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    HasNoOpenPlanarPatch (protectedTorusMap S.saddle D.meridian h) := by
  have hF := completedSaddleTorusAssemblyFromMeridian_embedding S D
  exact nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature hF.1 hF.2.1
    (protectedTorusActualCylinder_nonzero_curvature_dense S D C)

/-- A same-field branch consumer: actual negativity on the SAME support image
and actual locality off that image transfer the proved baseline density. The
branch embeddings and support negativity are supplied by their retained actual
stability bounds, not constructed or assumed as an original torus producer. -/
theorem protectedTorusActualCylinder_bending_hasNoOpenPlanarPatch
    {RN μ h T w : ℝ} [Fact (0 < T)]
    (S : ProtectedSaddleCylinderInput RN μ h)
    (D : ParabolicConvexClosureData RN μ h)
    (C : ProtectedTorusActualGraphCylinderData S)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) NonrigidTorusSource)
    (A : Ambient ≃ᵃⁱ[ℝ] Ambient)
    (hcompact : HasCompactSupport Y) (hsupport : tsupport Y ⊆ e.source)
    (a : ℝ)
    (hplus : NativeTorusSmoothEmbedding
      (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y))
    (hminus : NativeTorusSmoothEmbedding
      (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y))
    (hplusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y) p < 0)
    (hminusneg : ∀ p ∈ e '' tsupport Y, nativeTorusChartCurvature
      (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y) p < 0) :
    HasNoOpenPlanarPatch
      (protectedTorusMap S.saddle D.meridian h + a • protectedTorusBendingField e A Y) ∧
    HasNoOpenPlanarPatch
      (protectedTorusMap S.saddle D.meridian h - a • protectedTorusBendingField e A Y) := by
  let F := protectedTorusMap S.saddle D.meridian h
  have hdense := protectedTorusActualCylinder_nonzero_curvature_dense S D C
  have hdplus := nativeTorus_nonzero_curvature_dense_of_support_negative
    (e '' tsupport Y) hdense hplusneg
    (fun p hp => (protectedTorus_bending_curvature_off_support
      e A hcompact hsupport F a hp).1)
  have hdminus := nativeTorus_nonzero_curvature_dense_of_support_negative
    (e '' tsupport Y) hdense hminusneg
    (fun p hp => (protectedTorus_bending_curvature_off_support
      e A hcompact hsupport F a hp).2)
  exact ⟨nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature
      hplus.1 hplus.2.1 hdplus,
    nativeTorus_hasNoOpenPlanarPatch_of_dense_nonzero_curvature
      hminus.1 hminus.2.1 hdminus⟩

end
end TightVer401
