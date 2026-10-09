import TightVer401.ParabolicConvexClosureBoundaryCosineCalculus
import TightVer401.ProtectedTorusMapDefinitions

/-! Literal identifications with the coordinator's two protected collars. -/
open scoped Manifold ContDiff
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem parabolicConvexClosureCircleCollar_eq_protectedNorth (RN mu h : ℝ) :
    parabolicConvexClosureCircleCollar 1 RN mu h = protectedTorusNorthCollar RN mu h := by
  funext p
  simp [parabolicConvexClosureCircleCollar, protectedTorusNorthCollar]

theorem parabolicConvexClosureCircleCollar_eq_protectedSouth (RN mu h : ℝ) :
    parabolicConvexClosureCircleCollar (-1) RN mu h = protectedTorusSouthCollar RN mu h := by
  funext p
  simp only [parabolicConvexClosureCircleCollar, protectedTorusSouthCollar]
  congr 1
  ring

theorem parabolicConvexClosure_protectedNorthCollar_contMDiff (RN mu h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (protectedTorusNorthCollar RN mu h) := by
  rw [← parabolicConvexClosureCircleCollar_eq_protectedNorth]
  exact parabolicConvexClosureCircleCollar_contMDiff 1 RN mu h

theorem parabolicConvexClosure_protectedSouthCollar_contMDiff (RN mu h : ℝ) :
    ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ (protectedTorusSouthCollar RN mu h) := by
  rw [← parabolicConvexClosureCircleCollar_eq_protectedSouth]
  exact parabolicConvexClosureCircleCollar_contMDiff (-1) RN mu h

theorem parabolicConvexClosure_protectedNorthCollar_mfderiv_injective {RN mu h : ℝ}
    (hmu : mu ≠ 0) (p : AddCircle (2 * Real.pi) × ℝ) (hr : RN + mu * p.2 ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (protectedTorusNorthCollar RN mu h) p) := by
  rw [← parabolicConvexClosureCircleCollar_eq_protectedNorth]
  exact parabolicConvexClosureCircleCollar_mfderiv_injective hmu p hr

theorem parabolicConvexClosure_protectedSouthCollar_mfderiv_injective {RN mu h : ℝ}
    (hmu : mu ≠ 0) (p : AddCircle (2 * Real.pi) × ℝ) (hr : RN + mu * p.2 ≠ 0) :
    Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient)
      (protectedTorusSouthCollar RN mu h) p) := by
  rw [← parabolicConvexClosureCircleCollar_eq_protectedSouth]
  exact parabolicConvexClosureCircleCollar_mfderiv_injective hmu p hr

end
end TightVer401
