import TightVer401.ProtectedTorusPositiveGaussCurvatureCharts
import TightVer401.ParabolicConvexClosureComplete

/-! Actual preferred-chart curvature on the literal convex phase.
The meridian is exactly the radius in the map. Only its actual interior
smoothness, positive radius and negative second derivative are used; the
aggregate curvature-positive output is not an input to these proofs.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussConvexPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def protectedTorusPositiveGaussHeightCoordinates (s h u : ℝ) (q : Coord) : Coord :=
  ![s + q 0, -h * Real.cos (u + q 1)]

theorem protectedTorusPositiveGaussHeightCoordinates_contDiff (s h u : ℝ) :
    ContDiff ℝ ∞ (protectedTorusPositiveGaussHeightCoordinates s h u) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : Coord => s + q 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun q : Coord => -h * Real.cos (u + q 1))
    fun_prop

theorem protectedTorusPositiveGaussHeightCoordinates_fderiv (s h u : ℝ) (q v : Coord) :
    fderiv ℝ (protectedTorusPositiveGaussHeightCoordinates s h u) q v =
      ![v 0, h * Real.sin (u + q 1) * v 1] := by
  let L : Fin 2 → Coord →L[ℝ] ℝ := fun i =>
    if i = 0 then ContinuousLinearMap.proj (R := ℝ) 0
    else (h * Real.sin (u + q 1)) • ContinuousLinearMap.proj (R := ℝ) 1
  have hd : HasFDerivAt (protectedTorusPositiveGaussHeightCoordinates s h u)
      (ContinuousLinearMap.pi L) q := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [protectedTorusPositiveGaussHeightCoordinates, L] using
        (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) q).const_add s
    · simpa [protectedTorusPositiveGaussHeightCoordinates, L, smul_smul] using
        (((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) q).const_add u).cos.const_mul (-h))
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [L, ContinuousLinearMap.pi_apply]

theorem protectedTorusPositiveGaussHeightCoordinates_regular (s h u : ℝ) (q : Coord)
    (hcoef : h * Real.sin (u + q 1) ≠ 0) :
    Function.Injective (fderiv ℝ (protectedTorusPositiveGaussHeightCoordinates s h u) q) := by
  intro v w he
  rw [protectedTorusPositiveGaussHeightCoordinates_fderiv,
    protectedTorusPositiveGaussHeightCoordinates_fderiv] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change v 0 = w 0 at h0
  change h * Real.sin (u + q 1) * v 1 = h * Real.sin (u + q 1) * w 1 at h1
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ hcoef h1

private theorem cosine_height_mem {h u : ℝ} (hh : 0 < h)
    (hu : u ∈ Ioo Real.pi (2 * Real.pi)) : -h * Real.cos u ∈ Ioo (-h) h := by
  let v := 2 * Real.pi - u
  have hv0 : 0 < v := by dsimp [v]; linarith [hu.2]
  have hvπ : v < Real.pi := by dsimp [v]; linarith [hu.1]
  have he : Real.cos v = Real.cos u := by simp [v, Real.cos_sub]
  have hc0 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hvπ.le hv0
  have hcπ := Real.cos_lt_cos_of_nonneg_of_le_pi hv0.le (le_refl Real.pi) hvπ
  simp only [Real.cos_zero, Real.cos_pi, he] at hc0 hcπ
  constructor
  · simpa using mul_lt_mul_of_neg_left hc0 (neg_neg_of_pos hh)
  · simpa using mul_lt_mul_of_neg_left hcπ (neg_neg_of_pos hh)

private theorem phase_sine_ne_zero {u : ℝ} (hu : u ∈ Ioo Real.pi (2 * Real.pi)) :
    Real.sin u ≠ 0 := by
  have hp := Real.sin_pos_of_pos_of_lt_pi (show 0 < u - Real.pi by linarith [hu.1])
    (show u - Real.pi < Real.pi by linarith [hu.2])
  rw [Real.sin_sub_pi] at hp
  exact (neg_pos.mp hp).ne

/-- The actual preferred inverse chart agrees with the actual revolution map
composed with its cosine height coordinates on the convex phase. -/
theorem protectedTorusPositiveGauss_convex_chart_germ
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) (hphase : u ∈ Ioo Real.pi (2 * Real.pi)) :
    nativeProductCoordinateMap (protectedTorusMap S r h) p =ᶠ[𝓝 (0 : Coord)]
      revolutionEnd r ∘ protectedTorusPositiveGaussHeightCoordinates s h u := by
  rw [protectedTorusPositiveGauss_chart_lift _ p s u hs hu]
  have hn : ∀ᶠ q : Coord in 𝓝 0, u + q 1 ∈ Ioo Real.pi (2 * Real.pi) :=
    (continuous_const.add (continuous_apply 1)).continuousAt
      (by simpa using Ioo_mem_nhds hphase.1 hphase.2)
  filter_upwards [hn] with q hq
  have he : (AddCircle.equivIco (2 * Real.pi) 0
      (periodProjection (2 * Real.pi) (u + q 1))).val = u + q 1 :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq
      (by constructor <;> linarith [hq.1, hq.2, Real.pi_pos]))
  simp only [protectedTorusMap, he, if_neg (not_le.mpr hq.1)]
  exact revolutionEndCircleFull_representative r (s + q 0) (-h * Real.cos (u + q 1))

/-- Exact actual native preferred-chart curvature formula for the same
constructed meridian in the literal protected torus map. -/
theorem protectedTorusPositiveGauss_convex_curvature {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : NonrigidTorusSource)
    (hphase : (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi)) :
    nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p =
      -deriv (deriv D.meridian) (-h * Real.cos (AddCircle.equivIco (2 * Real.pi) 0 p.2).val) /
        (D.meridian (-h * Real.cos (AddCircle.equivIco (2 * Real.pi) 0 p.2).val) *
          (1 + deriv D.meridian (-h * Real.cos (AddCircle.equivIco (2 * Real.pi) 0 p.2).val)^2)^2) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  have hu : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
  let U : Set Coord := {q | q 1 ∈ Ioo (-h) h}
  let V : Set Coord := {q | u + q 1 ∈ Ioo Real.pi (2 * Real.pi)}
  let κ := protectedTorusPositiveGaussHeightCoordinates s h u
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_apply 1)
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_const.add (continuous_apply 1))
  have hp : (0 : Coord) ∈ V := by simpa [V] using hphase
  have hmap : MapsTo κ V U := fun q hq => cosine_height_mem D.height_pos hq
  have hX : ContDiffOn ℝ ∞ (revolutionEnd D.meridian) U :=
    parabolicConvexClosure_revolution_contDiffOn isOpen_Ioo D.meridian_smooth
  have hXi : ∀ q ∈ U, Function.Injective (fderiv ℝ (revolutionEnd D.meridian) q) := by
    intro q hq
    exact parabolicConvexClosure_revolution_differential_injective isOpen_Ioo
      D.meridian_smooth hq (ne_of_gt (lt_trans D.radius_pos (D.meridian_exterior _ hq)))
  have hκi : ∀ q ∈ V, Function.Injective (fderiv ℝ κ q) := by
    intro q hq
    exact protectedTorusPositiveGaussHeightCoordinates_regular s h u q
      (mul_ne_zero D.height_pos.ne' (phase_sine_ne_zero hq))
  have hz : (κ 0) 1 ∈ Ioo (-h) h := hmap hp
  have hn := parabolicConvexClosureOutwardNormal_isUnitNormal isOpen_Ioo D.meridian_smooth hz
  have hr := protectedTorus_curvature_reparam hU hV hX
    (protectedTorusPositiveGaussHeightCoordinates_contDiff s h u).contDiffOn
    hmap hXi hκi hp hn
  have hg := protectedTorusPositiveGauss_convex_chart_germ S.saddle D.meridian h p s u hs hu hphase
  have hmetric := gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hg)
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center, hmetric, hr]
  have hpos : 0 < D.meridian ((κ 0) 1) :=
    lt_trans D.radius_pos (D.meridian_exterior _ hz)
  rw [parabolicConvexClosure_revolution_gaussianCurvature isOpen_Ioo D.meridian_smooth hz hpos]
  simp [κ, protectedTorusPositiveGaussHeightCoordinates, u]

/-- Positive curvature is derived from the actual negative second derivative,
not from the aggregate's surface-curvature field. -/
theorem protectedTorusPositiveGauss_convex_curvature_pos {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : NonrigidTorusSource)
    (hphase : (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo Real.pi (2 * Real.pi)) :
    0 < nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p := by
  rw [protectedTorusPositiveGauss_convex_curvature S D p hphase]
  have hz := cosine_height_mem D.height_pos hphase
  have hr := lt_trans D.radius_pos (D.meridian_exterior _ hz)
  exact div_pos (neg_pos.mpr (D.second_negative _ hz))
    (mul_pos hr (sq_pos_of_pos (by positivity)))

end
end TightVer401
