import TightVer401.CompletedSaddleTorusConnection
import TightVer401.ParabolicConvexClosureComplete

/-! Retain one FULL constructed convex-closure witness for the same saddle.
Its literal meridian is used in both the native torus assembly and all later
Gauss/marking consumers. No independent second meridian choice is made. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

/-- Literal assembly from the actual saddle and the SAME full closure witness.
This is the same two-field assembly used by the transport positive-Gauss caller. -/
def completedSaddleTorusAssemblyFromMeridian {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (C : ParabolicConvexClosureData RN μ h) :
    ProtectedTorusAssemblyInput RN μ h where
  toProtectedSaddleCylinderInput := S
  toProtectedParabolicMeridianInput := C.toProtectedParabolicMeridianInput

@[simp] theorem completedSaddleTorusAssemblyFromMeridian_saddle {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (C : ParabolicConvexClosureData RN μ h) :
    (completedSaddleTorusAssemblyFromMeridian S C).toProtectedSaddleCylinderInput = S := rfl

@[simp] theorem completedSaddleTorusAssemblyFromMeridian_meridian {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (C : ParabolicConvexClosureData RN μ h) :
    (completedSaddleTorusAssemblyFromMeridian S C).meridian = C.meridian := rfl

/-- The actual literal map uses exactly S.saddle and C.meridian. -/
theorem completedSaddleTorusAssemblyFromMeridian_map {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (C : ParabolicConvexClosureData RN μ h) :
    protectedTorusMap (completedSaddleTorusAssemblyFromMeridian S C).saddle
      (completedSaddleTorusAssemblyFromMeridian S C).meridian h =
        protectedTorusMap S.saddle C.meridian h := rfl

/-- Actual baseline embedding for any given full witness, without choosing a
second closure. The existing seam and annulus proofs apply to this assembly. -/
theorem completedSaddleTorusAssemblyFromMeridian_embedding {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) (C : ParabolicConvexClosureData RN μ h) :
    NativeTorusSmoothEmbedding (protectedTorusMap S.saddle C.meridian h) := by
  let D := completedSaddleTorusAssemblyFromMeridian S C
  have hs := protectedTorusMap_contMDiff_and_immersion D
  exact ⟨hs.1, hs.2, protectedTorusMap_embedding_of_annulus_and_meridian D⟩

/-- Positive actual saddle parameters construct ONE full closure witness and
its exact matching assembly. All future Gauss data remains available as C. -/
theorem exists_completedSaddleTorusAssembly_with_full_meridian {RN μ h : ℝ}
    (S : ProtectedSaddleCylinderInput RN μ h) :
    ∃ C : ParabolicConvexClosureData RN μ h,
      ∃ D : ProtectedTorusAssemblyInput RN μ h,
        D = completedSaddleTorusAssemblyFromMeridian S C ∧
        D.toProtectedSaddleCylinderInput = S ∧
        D.toProtectedParabolicMeridianInput = C.toProtectedParabolicMeridianInput ∧
        D.meridian = C.meridian ∧
        NativeTorusSmoothEmbedding (protectedTorusMap D.saddle D.meridian h) := by
  obtain ⟨C⟩ := exists_parabolic_convex_closure RN μ h
    S.radius_pos S.coefficient_pos S.height_pos
  exact ⟨C, completedSaddleTorusAssemblyFromMeridian S C, rfl, rfl, rfl, rfl,
    completedSaddleTorusAssemblyFromMeridian_embedding S C⟩

end
end TightVer401
