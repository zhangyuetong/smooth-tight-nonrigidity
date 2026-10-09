import TightVer401.ProtectedTorusPositiveGaussCurvatureConvex
import TightVer401.ProtectedTorusPositiveGaussCurvatureCollar

/-! Actual zero-curvature seams of the literal same-radius protected torus.
The private germs below concern only the literal map and the two polynomial
collars. They use the producer's saddle collar agreement and the very same
constructed meridian's checked polynomial collar agreement. The registered
atlas is retained, and no global torus gluing is reconstructed here.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussSeamsPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem collar_height {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h) (v : ℝ) :
    h - mu * (protectedTorusCollarScale h mu * Real.sin (v / 2))^2 / 2 = h * Real.cos v := by
  have hs := parabolicConvexClosure_cosineScale_sq hmu hh
  have hc := Real.cos_two_mul_eq_one_sub (v / 2)
  rw [show 2 * (v / 2) = v by ring] at hc
  rw [show mu * (protectedTorusCollarScale h mu * Real.sin (v / 2))^2 / 2 =
      (mu * (protectedTorusCollarScale h mu)^2 / 2) * (Real.sin (v / 2))^2 by ring, hs, hc]
  ring

private theorem north_radial (c v : ℝ) :
    -c * Real.cos ((Real.pi + v) / 2) = c * Real.sin (v / 2) := by
  rw [show (Real.pi + v) / 2 = Real.pi / 2 + v / 2 by ring, Real.cos_add]
  simp

private theorem real_representative (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (r : ℝ → ℝ) (h s u : ℝ) (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    protectedTorusMap S r h (periodProjection (2 * Real.pi) s, periodProjection (2 * Real.pi) u) =
      if u ≤ Real.pi then S (periodProjection (2 * Real.pi) s, u)
      else protectedTorusConvexCylinder r h (periodProjection (2 * Real.pi) s, u) := by
  have he : (AddCircle.equivIco (2 * Real.pi) 0
      (periodProjection (2 * Real.pi) u)).val = u :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hu))
  simp only [protectedTorusMap, he]

private theorem north_germ {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) (s : ℝ) :
    (fun q : Coord => protectedTorusMap S.saddle D.meridian h
      (periodProjection (2 * Real.pi) (s + q 0), periodProjection (2 * Real.pi) (Real.pi + q 1)))
      =ᶠ[𝓝 0] parabolicConvexClosureCollar 1 RN mu h ∘
        protectedTorusPositiveGaussScalarCoordinates s
          (fun v => protectedTorusCollarScale h mu * Real.sin (v / 2)) := by
  obtain ⟨ε, hε, hεπ, hg⟩ := S.north_germ
  have hn : ∀ᶠ q : Coord in 𝓝 0, q 1 ∈ Ioo (-ε) ε :=
    (continuous_apply 1).continuousAt (by simpa using Ioo_mem_nhds (by linarith) hε)
  have hsmall : ∀ᶠ q : Coord in 𝓝 0,
      mu * (protectedTorusCollarScale h mu * Real.sin (q 1 / 2))^2 / 2 < D.collarWidth :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds
      (by simpa using D.collarWidth_mem.1)
  filter_upwards [hn, hsmall] with q hq hsmall
  have hφ0 : 0 < Real.pi + q 1 := by linarith [hq.1, Real.pi_pos]
  have hφ2 : Real.pi + q 1 < 2 * Real.pi := by linarith [hq.2, Real.pi_pos]
  rw [real_representative _ _ _ _ _ ⟨hφ0.le, hφ2⟩]
  by_cases hv : q 1 ≤ 0
  · rw [if_pos (by linarith), hg _ _ ⟨by linarith [hq.1], by linarith⟩, north_radial]
    rw [← parabolicConvexClosureCircleCollar_eq_protectedNorth,
      parabolicConvexClosureCircleCollar_representative]
    rfl
  · rw [if_neg (by linarith)]
    have ht : 0 ≤ protectedTorusCollarScale h mu * Real.sin (q 1 / 2) :=
      mul_nonneg (parabolicConvexClosure_cosineScale_pos D.coefficient_pos D.height_pos).le
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hq.2, Real.pi_pos]))
    have hz : -h * Real.cos (Real.pi + q 1) =
        h - mu * (protectedTorusCollarScale h mu * Real.sin (q 1 / 2))^2 / 2 := by
      rw [collar_height D.coefficient_pos D.height_pos]
      simp [Real.cos_add]
    rw [protectedTorusConvexCylinder, revolutionEndCircleFull_representative, hz]
    exact (D.upper_collar_agreement (s + q 0)
      (protectedTorusCollarScale h mu * Real.sin (q 1 / 2)) ht hsmall.le).symm

private theorem south_germ {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h) (s : ℝ) :
    (fun q : Coord => protectedTorusMap S.saddle D.meridian h
      (periodProjection (2 * Real.pi) (s + q 0), periodProjection (2 * Real.pi) (q 1)))
      =ᶠ[𝓝 0] parabolicConvexClosureCollar (-1) RN mu h ∘
        protectedTorusPositiveGaussScalarCoordinates s
          (fun v => -protectedTorusCollarScale h mu * Real.sin (v / 2)) := by
  obtain ⟨ε, hε, hεπ, hg⟩ := S.south_germ
  have hn : ∀ᶠ q : Coord in 𝓝 0, q 1 ∈ Ioo (-ε) ε :=
    (continuous_apply 1).continuousAt (by simpa using Ioo_mem_nhds (by linarith) hε)
  have hsmall : ∀ᶠ q : Coord in 𝓝 0,
      mu * (-protectedTorusCollarScale h mu * Real.sin (q 1 / 2))^2 / 2 < D.collarWidth :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds
      (by simpa using D.collarWidth_mem.1)
  filter_upwards [hn, hsmall] with q hq hsmall
  by_cases hv : 0 ≤ q 1
  · rw [real_representative _ _ _ _ _ ⟨hv, by linarith [hq.2, Real.pi_pos]⟩,
      if_pos (by linarith [hq.2]), hg _ _ ⟨hv, hq.2.le⟩]
    rw [← parabolicConvexClosureCircleCollar_eq_protectedSouth,
      parabolicConvexClosureCircleCollar_representative]
    rfl
  · have hshift : periodProjection (2 * Real.pi) (q 1 + 2 * Real.pi) =
        periodProjection (2 * Real.pi) (q 1) := AddCircle.coe_add_period (2 * Real.pi) (q 1)
    rw [← hshift, real_representative _ _ _ _ _
      ⟨by linarith [hq.1, Real.pi_pos], by linarith⟩, if_neg (by linarith [hq.1, Real.pi_pos])]
    have ht : 0 ≤ -protectedTorusCollarScale h mu * Real.sin (q 1 / 2) :=
      mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr (parabolicConvexClosure_cosineScale_pos D.coefficient_pos D.height_pos).le)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hq.1, Real.pi_pos]))
    have hz : -h * Real.cos (q 1) =
        -h + mu * (-protectedTorusCollarScale h mu * Real.sin (q 1 / 2))^2 / 2 := by
      have he := collar_height D.coefficient_pos D.height_pos (q 1)
      nlinarith [he]
    rw [protectedTorusConvexCylinder, Real.cos_add_two_pi,
      revolutionEndCircleFull_representative, hz]
    exact (D.lower_collar_agreement (s + q 0)
      (-protectedTorusCollarScale h mu * Real.sin (q 1 / 2)) ht hsmall.le).symm

private theorem scalar_collar_zero {RN mu : ℝ} (hRN : RN ≠ 0) (hmu : mu ≠ 0)
    (σ h s c : ℝ) (hc : c ≠ 0) :
    gaussianCurvature (inducedMetric (parabolicConvexClosureCollar σ RN mu h ∘
      protectedTorusPositiveGaussScalarCoordinates s (fun v => c * Real.sin (v / 2)))) 0 = 0 := by
  let X := parabolicConvexClosureCollar σ RN mu h
  let b : ℝ → ℝ := fun v => c * Real.sin (v / 2)
  let κ := protectedTorusPositiveGaussScalarCoordinates s b
  let U : Set Coord := {q | RN + mu * q 1 ≠ 0}
  let V : Set Coord := {q | RN + mu * (κ q) 1 ≠ 0 ∧ Real.cos (q 1 / 2) ≠ 0}
  have hb : ContDiff ℝ ∞ b := by dsimp [b]; fun_prop
  have hκ := protectedTorusPositiveGaussScalarCoordinates_contDiff s hb
  have hU : IsOpen U := by
    change IsOpen ((fun q : Coord => RN + mu * q 1) ⁻¹' ({0}ᶜ : Set ℝ))
    exact isClosed_singleton.isOpen_compl.preimage
      (continuous_const.add (continuous_const.mul (continuous_apply 1)))
  have hV : IsOpen V := by
    apply IsOpen.inter
    · change IsOpen ((fun q : Coord => RN + mu * (κ q) 1) ⁻¹' ({0}ᶜ : Set ℝ))
      exact isClosed_singleton.isOpen_compl.preimage
        (continuous_const.add (continuous_const.mul ((continuous_apply 1).comp hκ.continuous)))
    · change IsOpen ((fun q : Coord => Real.cos (q 1 / 2)) ⁻¹' ({0}ᶜ : Set ℝ))
      have hcos : Continuous (fun q : Coord => Real.cos (q 1 / 2)) := by fun_prop
      exact isClosed_singleton.isOpen_compl.preimage hcos
  have hp : (0 : Coord) ∈ V := by simpa [V, κ, protectedTorusPositiveGaussScalarCoordinates, b] using hRN
  have hm : MapsTo κ V U := fun q hq => hq.1
  have hX : ContDiffOn ℝ ∞ X U := (parabolicConvexClosureCollar_contDiff σ RN mu h).contDiffOn
  have hXi : ∀ q ∈ U, Function.Injective (fderiv ℝ X q) :=
    fun q hq => parabolicConvexClosureCollar_differential_injective hmu hq
  have hκi : ∀ q ∈ V, Function.Injective (fderiv ℝ κ q) := by
    intro q hq
    have hd : HasDerivAt b ((c / 2) * Real.cos (q 1 / 2)) (q 1) := by
      convert! (((hasDerivAt_id (q 1)).div_const 2).sin.const_mul c) using 1 <;>
        simp only [Function.id_def] <;> first | rfl | ring
    exact protectedTorusPositiveGaussScalarCoordinates_regular s hd
      (mul_ne_zero (div_ne_zero hc (by norm_num)) hq.2)
  have hz : (κ 0) 1 = 0 := by simp [κ, protectedTorusPositiveGaussScalarCoordinates, b]
  rcases revolution_frame ((κ 0) 0) with ⟨_, _, hzz, _, hrz, haz⟩
  have hn : IsUnitNormalAt X revolutionAxis (κ 0) := by
    refine ⟨hzz, fun v => ?_⟩
    rw [fderiv_two_coordinates, parabolicConvexClosureCollar_partial_theta,
      parabolicConvexClosureCollar_partial_radial]
    simp only [hz, mul_zero, zero_smul, sub_zero, add_zero, inner_add_left, inner_sub_left,
      real_inner_smul_left, haz, hrz, mul_zero, zero_add]
  rw [protectedTorus_curvature_reparam hU hV hX hκ.contDiffOn hm hXi hκi hp hn]
  exact protectedTorusPositiveGauss_collar_curvature_zero hRN hmu σ h hz

/-- The actual native preferred-chart curvature is zero on the northern seam. -/
theorem protectedTorusPositiveGauss_north_curvature_zero {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : NonrigidTorusSource) (hp : p.2 = periodProjection (2 * Real.pi) Real.pi) :
    nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p = 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  have hu : periodProjection (2 * Real.pi) Real.pi = p.2 := hp.symm
  have hg : nativeProductCoordinateMap (protectedTorusMap S.saddle D.meridian h) p =ᶠ[𝓝 0]
      parabolicConvexClosureCollar 1 RN mu h ∘ protectedTorusPositiveGaussScalarCoordinates s
        (fun v => protectedTorusCollarScale h mu * Real.sin (v / 2)) := by
    rw [protectedTorusPositiveGauss_chart_lift _ p s Real.pi hs hu]
    exact north_germ S D s
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center,
    gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hg)]
  exact scalar_collar_zero D.radius_pos.ne' D.coefficient_pos.ne' 1 h s _
    (parabolicConvexClosure_cosineScale_pos D.coefficient_pos D.height_pos).ne'

/-- The actual native preferred-chart curvature is zero on the southern seam. -/
theorem protectedTorusPositiveGauss_south_curvature_zero {RN mu h : ℝ}
    (S : ProtectedSaddleCylinderInput RN mu h) (D : ParabolicConvexClosureData RN mu h)
    (p : NonrigidTorusSource) (hp : p.2 = 0) :
    nativeTorusChartCurvature (protectedTorusMap S.saddle D.meridian h) p = 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  have hu : periodProjection (2 * Real.pi) 0 = p.2 := by simpa using hp.symm
  have hg : nativeProductCoordinateMap (protectedTorusMap S.saddle D.meridian h) p =ᶠ[𝓝 0]
      parabolicConvexClosureCollar (-1) RN mu h ∘ protectedTorusPositiveGaussScalarCoordinates s
        (fun v => -protectedTorusCollarScale h mu * Real.sin (v / 2)) := by
    rw [protectedTorusPositiveGauss_chart_lift _ p s 0 hs hu]
    simpa only [zero_add] using south_germ S D s
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center,
    gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hg)]
  exact scalar_collar_zero D.radius_pos.ne' D.coefficient_pos.ne' (-1) h s _
    (neg_ne_zero.mpr (parabolicConvexClosure_cosineScale_pos D.coefficient_pos D.height_pos).ne')

end
end TightVer401
