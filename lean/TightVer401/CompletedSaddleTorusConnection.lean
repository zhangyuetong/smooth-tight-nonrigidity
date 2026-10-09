import TightVer401.ProtectedTorusMap
import TightVer401.ParabolicConvexClosureTorusInput
import TightVer401.ClassicalExternal

/-! Choose the convex closure once for the same actual completed saddle.
This is a conditional construction from ordinary saddle data, not a grant of
that data or of a tight/nonrigid torus. The selected meridian is exposed for
all subsequent Gauss and marker consumers. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

/-- Construct an actual smooth embedded torus from the same actual saddle,
choosing one strictly concave asymmetric meridian with the same endpoint radius.
All geometric facts refer to that single chosen meridian. -/
theorem exists_protectedTorusAssembly_from_saddle {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) :
    ∃ D : ProtectedTorusAssemblyInput RN μ h,
      D.toProtectedSaddleCylinderInput = S ∧
      NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h) ∧
      (∀ z ∈ Ioo (-h) h, deriv (deriv D.meridian) z < 0) ∧
      StrictConcaveOn ℝ (Icc (-h) h) D.meridian ∧
      D.meridian (-h) = RN ∧ D.meridian h = RN ∧
      ∃ z ∈ Ioo 0 h, D.meridian (-z) ≠ D.meridian z := by
  obtain ⟨m, hNeg, hConc, hSouth, hNorth, hAsym⟩ :=
    exists_protectedParabolicMeridianInput_geometry RN μ h
      S.radius_pos S.coefficient_pos S.height_pos
  let D : ProtectedTorusAssemblyInput RN μ h := {
    toProtectedSaddleCylinderInput := S
    toProtectedParabolicMeridianInput := m }
  have hSmooth := protectedTorusMap_contMDiff_and_immersion D
  refine ⟨D, rfl, ⟨hSmooth.1, hSmooth.2,
    protectedTorusMap_embedding_of_annulus_and_meridian D⟩,
    hNeg, hConc, hSouth, hNorth, hAsym⟩

end
end TightVer401
