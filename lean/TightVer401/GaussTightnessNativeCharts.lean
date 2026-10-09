import TightVer401.NativeProductPlaneTorusCoordinates
import TightVer401.SurfaceMetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! SAME-object native preferred charts for the positive Gauss criterion.

All representatives here are those of the actual supplied maps X and N.
No choice of outward orientation or additional geometry is imposed.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace TightVer401
noncomputable section
open Set _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance gaussTightnessNativeChartsPeriod : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩
local instance gaussTightnessNativeChartsDimension :
    Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- The preferred actual ambient representative of the supplied sphere normal. -/
def gaussTightnessNativeNormalCoordinates (N : NonrigidTorusSource → RoundSphere)
    (p : NonrigidTorusSource) : Coord → Ambient :=
  nativeProductCoordinateMap (fun z => (N z : Ambient)) p

theorem gaussTightness_native_normal_contDiff
    {N : NonrigidTorusSource → RoundSphere}
    (hN : ContMDiff nativeProductModel (𝓡 2) ∞ N) (p : NonrigidTorusSource) :
    ContDiff ℝ ∞ (gaussTightnessNativeNormalCoordinates N p) := by
  exact nativeProductTorusCoordinateMap_contDiff
    ((contMDiff_coe_sphere (E := Ambient) (n := 2)).comp hN) p

/-- The actual translated quotient cover takes zero to the chosen source point. -/
theorem gaussTightness_native_cover_zero (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) :
    nativeProductTorusCoordinateCover s u 0 = p := by
  apply Prod.ext
  · simpa [nativeProductTorusCoordinateCover] using hs
  · simpa [nativeProductTorusCoordinateCover] using hu

theorem gaussTightness_native_coordinates_zero (X : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) : nativeProductCoordinateMap X p 0 = X p := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective p.2
  rw [nativeProductTorusCoordinateMap_eq_cover X p s u hs hu]
  simp only [Function.comp_apply, gaussTightness_native_cover_zero p s u hs hu]

theorem gaussTightness_native_normal_zero (N : NonrigidTorusSource → RoundSphere)
    (p : NonrigidTorusSource) :
    gaussTightnessNativeNormalCoordinates N p 0 = (N p : Ambient) :=
  gaussTightness_native_coordinates_zero (fun z => (N z : Ambient)) p

/-- Exact native orthogonality gives an actual unit normal at every coordinate
point of the SAME globally smooth preferred representative. -/
theorem gaussTightness_native_coordinates_unitNormal
    {X : NonrigidTorusSource → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (N : NonrigidTorusSource → RoundSphere)
    (horth : ∀ p (v : ℝ × ℝ), inner ℝ (N p : Ambient)
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p v) = 0)
    (p : NonrigidTorusSource) (q : Coord) :
    IsUnitNormalAt (nativeProductCoordinateMap X p)
      (gaussTightnessNativeNormalCoordinates N p q) q := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective p.2
  have hn : gaussTightnessNativeNormalCoordinates N p q =
      (N (nativeProductTorusCoordinateCover s u q) : Ambient) := by
    unfold gaussTightnessNativeNormalCoordinates
    rw [nativeProductTorusCoordinateMap_eq_cover (fun z => (N z : Ambient)) p s u hs hu]
    rfl
  constructor
  · rw [hn, real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
  · intro v
    rw [hn, nativeProductTorusCoordinateMap_fderiv hX p s u hs hu q]
    change @inner ℝ Ambient _
      ((mfderiv nativeProductModel 𝓘(ℝ, Ambient) X
        (nativeProductTorusCoordinateCover s u q)
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) v)) : Ambient)
      (N (nativeProductTorusCoordinateCover s u q) : Ambient) = 0
    rw [real_inner_comm]
    exact horth (nativeProductTorusCoordinateCover s u q)
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) v)

/-- Native local height maxima transport through the actual continuous cover
to zero in the preferred physical coordinate representative. -/
theorem gaussTightness_native_localMax_height
    {X : NonrigidTorusSource → Ambient} {p : NonrigidTorusSource}
    (w : Ambient) (hmax : IsLocalMax (fun z => inner ℝ (X z) w) p) :
    IsLocalMax (height (nativeProductCoordinateMap X p) w) (0 : Coord) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective p.2
  have hp0 := gaussTightness_native_cover_zero p s u hs hu
  have hm : IsLocalMax (fun z => inner ℝ (X z) w)
      (nativeProductTorusCoordinateCover s u 0) := by
    simpa only [hp0] using hmax
  have ht := hm.comp_continuous
    (nativeProductTorusCoordinateCover_contMDiff s u).continuous.continuousAt
  rw [nativeProductTorusCoordinateMap_eq_cover X p s u hs hu]
  exact ht

/-- The exact curvature used by the criterion is evaluated at coordinate zero. -/
theorem gaussTightness_native_curvature_zero (X : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) :
    nativeTorusChartCurvature X p =
      gaussianCurvature (inducedMetric (nativeProductCoordinateMap X p)) 0 := by
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center]

/-- Smooth native immersions give the actual positive induced metric on the
whole physical coordinate plane. -/
theorem gaussTightness_native_inducedMetric_smoothPositiveOn
    {X : NonrigidTorusSource → Ambient} (hX : NativeTorusSmoothEmbedding X)
    (p : NonrigidTorusSource) :
    SmoothPositiveOn (inducedMetric (nativeProductCoordinateMap X p)) univ := by
  apply inducedMetric_smoothPositiveOn
    (nativeProductTorusCoordinateMap_contDiff hX.1 p).contDiffOn isOpen_univ
  intro q _
  exact nativeProductTorusCoordinateMap_fderiv_injective hX.1 hX.2.1 p q

end
end TightVer401
