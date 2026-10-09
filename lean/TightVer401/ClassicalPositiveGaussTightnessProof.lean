import TightVer401.GaussTightnessNativeMaximumUnique
import TightVer401.GaussTightnessNativeRegular
import TightVer401.HeightTightnessSphereDirections
import TightVer401.HeightSuperlevelConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! Closed positive-Gauss tightness route. All height, regularity, curvature,
orientation, and component ingredients are proved in the import closure.
The Gauss chart has the ENTIRE actual positive-curvature source.
No outward-normal or zero-curvature-area premise is introduced. -/
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

theorem classicalPositiveGaussTightness_proved : ClassicalPositiveGaussTightnessClaim := by
  intro X hX N hN horth E hE e hsource htarget he hs hi
  let D : Set RoundSphere := {w | ∀ p,
    (N p : Ambient) = (w : Ambient) ∨ (N p : Ambient) = -(w : Ambient) →
    Function.Injective (fderiv ℝ (gaussTightnessNativeNormalCoordinates N p) 0)}
  have hD : Dense D := gaussTightness_native_dense_regular_directions N hN
  letI : CompactSpace NonrigidTorusSource := nonrigidTorusSource_compact
  letI : ChartedSpace OAI.ClosedSurfaceR4.Plane NonrigidTorusSource :=
    nativeProductPlaneChartedSpace NonrigidTorusSource
  letI : LocallyConnectedSpace NonrigidTorusSource :=
    ChartedSpace.locallyConnectedSpace OAI.ClosedSurfaceR4.Plane NonrigidTorusSource
  apply nativeTorus_isTightImage_of_dense_sphere_heightSuperlevels X hX.1.continuous D hD
  intro w hw a
  apply height_superlevel_isPreconnected_of_unique_localMax
    (continuous_const.inner hX.1.continuous)
  intro p q hp hq
  apply gaussTightness_native_localMax_unique_of_regular_direction X hX N hN horth E hE e
    hsource htarget he (w : Ambient)
    (by rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]) hw p q
  · simpa only [real_inner_comm] using hp
  · simpa only [real_inner_comm] using hq

end
end TightVer401
