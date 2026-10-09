import TightVer401.ProtectedTorusPositiveGaussCurvatureReparam
import TightVer401.SphereSupportOpenGeometry
import TightVer401.CurvatureLocality

/-! Ordinary sphere-support germs for the negative part of the literal torus.

The saddle smoothing producer must construct these actual potentials, normal
coordinates, and map germs. Its scalar input is negativity of the actual
sphere support tensor determinant. Smoothness, differential rank, normal
orthogonality, and negative Gaussian curvature of the surface are derived.
The normal chart is not restricted to a fixed hemisphere, so Fermi patches
through equatorial normals are supported. No producer inhabitant is asserted.
-/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual local potential/normal-coordinate data. The fields are ordinary
analytic data, not a supplied surface curvature or sign conclusion. -/
structure ProtectedTorusSphereSupportGerm (F : Coord → Ambient) (p : Coord) where
  U : Set Coord
  V : Set Coord
  open_U : IsOpen U
  open_V : IsOpen V
  point_mem : p ∈ V
  g : MetricField
  Q : Coord → Ambient
  H : Coord → ℝ
  κ : Coord → Coord
  metric : SmoothPositiveOn g U
  normal_isometric : IsometricOn g Q U
  normal_unit : ∀ q ∈ U, inner ℝ (Q q) (Q q) = 1
  potential_smooth : ContDiffOn ℝ ∞ H U
  tensor_negative : ∀ q ∈ U, (sphereSupportTensor g H q).det < 0
  coordinates_smooth : ContDiffOn ℝ ∞ κ V
  coordinates_mapsTo : MapsTo κ V U
  coordinates_regular : ∀ q ∈ V, Function.Injective (fderiv ℝ κ q)
  map_germ : F =ᶠ[𝓝 p] sphereSupportMap g Q H ∘ κ

/-- Negative surface curvature is a checked consequence of actual support
tensor negativity, regular coordinates, and the actual map germ. -/
theorem protectedTorus_sphereSupportGerm_curvature_neg {F : Coord → Ambient} {p : Coord}
    (d : ProtectedTorusSphereSupportGerm F p) :
    gaussianCurvature (inducedMetric F) p < 0 := by
  let X := sphereSupportMap d.g d.Q d.H
  have hs : ContDiffOn ℝ ∞ X d.U :=
    sphereSupportMap_contDiffOn d.metric d.normal_isometric.1 d.potential_smooth d.open_U
  have hi : ∀ q ∈ d.U, Function.Injective (fderiv ℝ X q) := by
    intro q hq
    exact sphereSupportMap_differential_injective d.metric d.normal_isometric
      d.potential_smooth d.open_U hq d.normal_unit (d.tensor_negative q hq).ne
  have hp := d.coordinates_mapsTo d.point_mem
  have hn : IsUnitNormalAt X (d.Q (d.κ p)) (d.κ p) :=
    sphereSupportMap_isUnitNormal d.metric d.normal_isometric d.potential_smooth
      d.open_U hp d.normal_unit
  have he := protectedTorus_curvature_reparam d.open_U d.open_V hs
    d.coordinates_smooth d.coordinates_mapsTo hi d.coordinates_regular d.point_mem hn
  have hdet : 0 < (d.g (d.κ p)).det := (d.metric.2 (d.κ p) hp).det_pos
  have hB : (sphereSupportEndomorphism d.g d.H (d.κ p)).det < 0 := by
    rw [sphereSupportEndomorphism, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hdet) (d.tensor_negative (d.κ p) hp)
  have hK : gaussianCurvature (inducedMetric X) (d.κ p) < 0 := by
    rw [sphereSupportMap_curvature_at d.metric d.normal_isometric d.potential_smooth
      d.open_U d.normal_unit hp (d.tensor_negative (d.κ p) hp).ne]
    exact div_neg_of_pos_of_neg zero_lt_one hB
  have hg := gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq d.map_germ)
  rw [hg, he]
  exact hK

/-- Moving the coordinate origin constructs the new potential-coordinate
data explicitly. It does not assume curvature invariance or a chart match. -/
def ProtectedTorusSphereSupportGerm.translate {F : Coord → Ambient} {p : Coord}
    (d : ProtectedTorusSphereSupportGerm F p) :
    ProtectedTorusSphereSupportGerm (fun q => F (p + q)) 0 where
  U := d.U
  V := (fun q : Coord => p + q) ⁻¹' d.V
  open_U := d.open_U
  open_V := d.open_V.preimage (continuous_const.add continuous_id)
  point_mem := by simpa using d.point_mem
  g := d.g
  Q := d.Q
  H := d.H
  κ := fun q => d.κ (p + q)
  metric := d.metric
  normal_isometric := d.normal_isometric
  normal_unit := d.normal_unit
  potential_smooth := d.potential_smooth
  tensor_negative := d.tensor_negative
  coordinates_smooth := d.coordinates_smooth.comp
    (contDiff_const.add contDiff_id).contDiffOn (fun q hq => hq)
  coordinates_mapsTo := fun q hq => d.coordinates_mapsTo hq
  coordinates_regular := by
    intro q hq
    have hd : DifferentiableAt ℝ d.κ (p + q) :=
      ((d.coordinates_smooth (p + q) hq).contDiffAt (d.open_V.mem_nhds hq)).differentiableAt (by simp)
    simpa only [fderiv_comp_add_left] using d.coordinates_regular (p + q) hq
  map_germ := by
    have hc : Tendsto (fun q : Coord => p + q) (𝓝 0) (𝓝 p) := by
      have hc' : Continuous (fun q : Coord => p + q) := continuous_const.add continuous_id
      have hc0 : ContinuousAt (fun q : Coord => p + q) 0 := hc'.continuousAt
      change Tendsto (fun q : Coord => p + q) (𝓝 (0 : Coord)) (𝓝 (p + 0)) at hc0
      simpa only [add_zero] using hc0
    exact d.map_germ.comp_tendsto hc

/-- In particular the exact translated actual representative has negative
curvature at its zero center, as used by the native quotient product chart. -/
theorem protectedTorus_sphereSupportGerm_translated_curvature_neg
    {F : Coord → Ambient} {p : Coord} (d : ProtectedTorusSphereSupportGerm F p) :
    gaussianCurvature (inducedMetric (fun q => F (p + q))) 0 < 0 :=
  protectedTorus_sphereSupportGerm_curvature_neg d.translate

end
end TightVer401
