import TightVer401.GaussTightnessSphereRegular
import TightVer401.GaussTightnessNativeCharts
import TightVer401.GaussTightnessNativeSign

/-! Dense actual regular ±normal directions for the native torus. The single
global smooth quotient cover avoids a choice of finite source atlas. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem gaussTightness_native_dense_regular_directions
    (N : NonrigidTorusSource → RoundSphere)
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N) :
    Dense {w : RoundSphere | ∀ p,
      (N p : Ambient) = (w : Ambient) ∨ (N p : Ambient) = -(w : Ambient) →
      Function.Injective (fderiv ℝ (gaussTightnessNativeNormalCoordinates N p) 0)} := by
  let L : Coord → Ambient := fun z => (N (nativeProductTorusCoordinateCover 0 0 z) : Ambient)
  have hL : ContDiff ℝ ∞ L :=
    (((contMDiff_coe_sphere (E := Ambient) (n := 2)).comp hN).comp
      (nativeProductTorusCoordinateCover_contMDiff 0 0)).contDiff
  have hunit : ∀ z, ‖L z‖ = 1 := fun z => roundSphere_norm _
  apply (gaussTightness_dense_both_regular_sphere_directions L hL hunit).mono
  intro w hw p hp
  obtain ⟨z, hz⟩ := nativeProductTorusCoordinateCover_zero_isQuotientMap.surjective p
  have hfiber : L z = (w : Ambient) ∨ L z = -(w : Ambient) := by
    simpa only [L, hz] using hp
  have hi : Function.Injective (fderiv ℝ L z) := hw z hfiber
  have hchart : gaussTightnessNativeNormalCoordinates N p = fun r => L (z + r) := by
    unfold gaussTightnessNativeNormalCoordinates
    rw [← hz, nativeProductCoordinateMap_at_cover_eq_translate]
    rfl
  rw [hchart]
  simpa only [fderiv_comp_add_left, add_zero] using hi

end
end TightVer401
