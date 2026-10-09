import TightVer401.ProtectedTorusPositiveGaussHomeomorph
import TightVer401.ProtectedTorusPositiveGaussCurvature
import TightVer401.ProtectedTorusPositiveGaussCurvatureActualGraphCylinder
import TightVer401.ClassicalExternalApplications

/-! Same-object producer for the classical positive-Gauss consumer.
No normal, curvature-region, or Gauss-image conclusion is granted. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def protectedTorusPositiveGaussExceptional : Set RoundSphere :=
  (Subtype.val : RoundSphere → Ambient) ⁻¹' {revolutionAxis, -revolutionAxis}

theorem protectedTorusPositiveGaussExceptional_finite :
    protectedTorusPositiveGaussExceptional.Finite :=
  Set.Finite.preimage Subtype.val_injective.injOn
    ((Set.finite_singleton _).insert _)

theorem protectedTorusPositiveGauss_target :
    (parabolicConvexClosureSphereBelt : Set RoundSphere) =
      univ \ protectedTorusPositiveGaussExceptional := by
  rw [parabolicConvexClosureSphereBelt_eq_poles_compl]
  ext n
  simp [protectedTorusPositiveGaussExceptional, not_or]

/-- Actual geometry of the literal protected map, usable by either branch.
The support-germ premise is the ordinary saddle-smoothing producer obligation. -/
def protectedTorusPositiveGaussData {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (hS : ProtectedTorusSaddleSphereSupportGerms S.saddle) :
    NativeTorusPositiveGaussData (protectedTorusMap S.saddle D.meridian h) where
  embedding := by
    have hs := protectedTorusMap_contMDiff_and_immersion (protectedTorusPositiveGaussAssembly S D)
    exact ⟨hs.1, hs.2,
      protectedTorusMap_embedding_of_annulus_and_meridian (protectedTorusPositiveGaussAssembly S D)⟩
  normal := protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D)
  normal_smooth := protectedTorusPositiveGaussNormal_contMDiff _
  normal_orthogonal := protectedTorusPositiveGaussNormal_orthogonal _
  exceptional := protectedTorusPositiveGaussExceptional
  exceptional_finite := protectedTorusPositiveGaussExceptional_finite
  gauss := protectedTorusPositiveGaussHomeomorph S D
  gauss_source := by
    change (protectedTorusPositiveGaussRegion : Set NonrigidTorusSource) = _
    rw [protectedTorusPositiveGauss_region_eq S D hS]
    ext p
    exact protectedTorusPositiveGaussRegion_iff p
  gauss_target := protectedTorusPositiveGauss_target
  gauss_eq := fun _ _ => rfl
  gauss_smooth := (protectedTorusPositiveGaussNormal_contMDiff _).contMDiffOn
  gauss_inverse_smooth := protectedTorusPositiveGaussInverse_contMDiffOn D

/-- The classical background remains an explicit theorem parameter. -/
theorem protectedTorusPositiveGauss_tight_of_classical (background : ClassicalExternalResults)
    {RN mu h : ℝ} (S : ProtectedSaddleCylinderInput RN mu h)
    (D : ParabolicConvexClosureData RN mu h)
    (hS : ProtectedTorusSaddleSphereSupportGerms S.saddle) :
    IsTightImage (protectedTorusMap S.saddle D.meridian h) :=
  nativeTorusPositiveGaussData_tight_of_classical background (protectedTorusPositiveGaussData S D hS)

/-- Same-object application of the completed cylinder's actual G/e/beta
producer, with no separate spherical support reconstruction obligation. -/
def protectedTorusActualCylinderPositiveGaussData {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    NativeTorusPositiveGaussData (protectedTorusMap S.saddle D.meridian h) where
  embedding := by
    have hs := protectedTorusMap_contMDiff_and_immersion (protectedTorusPositiveGaussAssembly S D)
    exact ⟨hs.1, hs.2,
      protectedTorusMap_embedding_of_annulus_and_meridian (protectedTorusPositiveGaussAssembly S D)⟩
  normal := protectedTorusPositiveGaussNormal (protectedTorusPositiveGaussAssembly S D)
  normal_smooth := protectedTorusPositiveGaussNormal_contMDiff _
  normal_orthogonal := protectedTorusPositiveGaussNormal_orthogonal _
  exceptional := protectedTorusPositiveGaussExceptional
  exceptional_finite := protectedTorusPositiveGaussExceptional_finite
  gauss := protectedTorusPositiveGaussHomeomorph S D
  gauss_source := by
    change (protectedTorusPositiveGaussRegion : Set NonrigidTorusSource) = _
    rw [protectedTorusPositiveGauss_actualCylinder_region_eq S D C]
    ext p
    exact protectedTorusPositiveGaussRegion_iff p
  gauss_target := protectedTorusPositiveGauss_target
  gauss_eq := fun _ _ => rfl
  gauss_smooth := (protectedTorusPositiveGaussNormal_contMDiff _).contMDiffOn
  gauss_inverse_smooth := protectedTorusPositiveGaussInverse_contMDiffOn D

theorem protectedTorusActualCylinderPositiveGauss_tight_of_classical
    (background : ClassicalExternalResults) {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (C : ProtectedTorusActualGraphCylinderData S) :
    IsTightImage (protectedTorusMap S.saddle D.meridian h) :=
  nativeTorusPositiveGaussData_tight_of_classical background
    (protectedTorusActualCylinderPositiveGaussData S D C)

end
end TightVer401
