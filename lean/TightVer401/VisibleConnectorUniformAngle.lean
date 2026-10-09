import TightVer401.VisibleConnectorAngularFrame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Uniform positive coefficients for the ACTUAL manuscript ruling.
This consumes the ordinary actual direction decomposition produced by
AngularFrame. A single small positive angle is selected from actual compact
strict margins; no connector coefficient signs are assumed after rotation. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def visibleConnectorShiftedDirection (theta : ℝ → ℝ) (eta s : ℝ) : Coord :=
  visibleConnectorUnitDirection (theta s - eta)

def visibleConnectorShiftedRuling (R : ℝ) (gamma : ℝ → Coord)
    (theta : ℝ → ℝ) (eta : ℝ) : ℝ → Coord :=
  visibleConnectorActualRuling R gamma (visibleConnectorShiftedDirection theta eta)

def visibleConnectorActualExcessRatio (R : ℝ) (kappa : ℝ → ℝ) (eta s : ℝ) : ℝ :=
  kappa s * Real.sinc eta - R * eta / 2 * Real.sinc (eta/2)^2

private theorem connectorUniform_unit (theta : ℝ) :
    visibleConnectorUnitDirection theta ⬝ᵥ visibleConnectorUnitDirection theta = 1 := by
  simpa [visibleConnectorUnitDirection,dotProduct,Fin.sum_univ_two,pow_two] using
    Real.cos_sq_add_sin_sq theta

theorem visibleConnector_shifted_ruling_zero {R : ℝ} {gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) (s : ℝ) :
    visibleConnectorShiftedRuling R gamma theta 0 s =
      -kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)) := by
  unfold visibleConnectorShiftedRuling visibleConnectorActualRuling visibleConnectorShiftedDirection
  rw [sub_zero,hdecomp]
  module

theorem visibleConnector_shifted_A_zero {R : ℝ} {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) (s : ℝ) :
    visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta 0) s =
      kappa s * (deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s)) := by
  unfold visibleConnectorA
  rw [visibleConnector_shifted_ruling_zero hdecomp s]
  simp [visibleConnectorDet,visibleConnectorJ,dotProduct,Fin.sum_univ_two]
  ring

theorem visibleConnector_shifted_B_zero {R : ℝ} {gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) (s : ℝ) :
    visibleConnectorB gamma (visibleConnectorShiftedRuling R gamma theta 0) s =
      kappa s * (visibleConnectorJ (deriv gamma s) ⬝ᵥ visibleConnectorUnitDirection (theta s)) := by
  unfold visibleConnectorB
  rw [visibleConnector_shifted_ruling_zero hdecomp s]
  simp [visibleConnectorJ,dotProduct,Fin.sum_univ_two]
  ring

theorem visibleConnector_actual_excess_factor {R : ℝ} {gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ}
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s))) (eta s : ℝ) :
    visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R =
      eta * visibleConnectorActualExcessRatio R kappa eta s := by
  have he : visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R =
      kappa s * Real.sin eta - R * (1-Real.cos eta) := by
    rw [hdecomp s]
    have hu := Real.cos_sq_add_sin_sq (theta s)
    simp only [visibleConnectorShiftedDirection,visibleConnectorUnitDirection,visibleConnectorJ,
      dotProduct,Fin.sum_univ_two,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_zero,Matrix.cons_val_one,Real.cos_sub,Real.sin_sub]
    linear_combination (R*Real.cos eta + kappa s*Real.sin eta)*hu
  rw [he]
  by_cases h : eta = 0
  · simp [h,visibleConnectorActualExcessRatio]
  · have hh : eta/2 ≠ 0 := div_ne_zero h (by norm_num)
    have hc : 1-Real.cos eta = 2*Real.sin (eta/2)^2 := by
      have hcos := Real.cos_two_mul' (eta/2)
      rw [show 2*(eta/2)=eta by ring] at hcos
      have hsum := Real.cos_sq_add_sin_sq (eta/2)
      linarith
    rw [hc]
    unfold visibleConnectorActualExcessRatio
    rw [Real.sinc_of_ne_zero h,Real.sinc_of_ne_zero hh]
    field_simp

private theorem connectorUniform_positive {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hpos : ∀ s ∈ K, 0 < f (0,s)) :
    ∀ᶠ eta in 𝓝 (0 : ℝ), ∀ s ∈ K, 0 < f (eta,s) := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  exact (isOpen_lt continuous_const hf).mem_nhds (hpos s hs)

/-- A single uniform small positive rotation makes E,A,B positive on the
whole compact actual trace. C positivity then follows from the actual angular
speed factorization in TerminalCircle, when the angle derivative is positive. -/
theorem visibleConnector_uniform_actual_small_angle
    {R : ℝ} {p gamma : ℝ → Coord} {theta kappa : ℝ → ℝ} {K : Set ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta) (hkappa : ContDiff ℝ ∞ kappa)
    (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hk : ∀ s ∈ K, 0 < kappa s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (hgv : ∀ s ∈ K, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s)) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s ∈ K,
      0 < visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R ∧
      0 < visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta) s ∧
      0 < visibleConnectorB gamma (visibleConnectorShiftedRuling R gamma theta eta) s := by
  have hgc := hgamma.continuous
  have htc := htheta.continuous
  have hdp := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdg := (contDiff_infty_iff_deriv.mp hgamma).2.continuous
  have hW : Continuous (fun q : ℝ × ℝ => visibleConnectorShiftedRuling R gamma theta q.1 q.2) := by
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp only [visibleConnectorShiftedRuling,visibleConnectorActualRuling,
        visibleConnectorShiftedDirection,visibleConnectorUnitDirection,visibleConnectorJ,
        Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
    <;> fun_prop
  have hA : Continuous (fun q : ℝ × ℝ =>
      visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta q.1) q.2) := by
    unfold visibleConnectorA visibleConnectorDet
    fun_prop
  have hB : Continuous (fun q : ℝ × ℝ =>
      visibleConnectorB gamma (visibleConnectorShiftedRuling R gamma theta q.1) q.2) := by
    unfold visibleConnectorB
    simp only [dotProduct,Fin.sum_univ_two]
    fun_prop
  have hEr : Continuous (fun q : ℝ × ℝ => visibleConnectorActualExcessRatio R kappa q.1 q.2) := by
    have hkc := hkappa.continuous
    unfold visibleConnectorActualExcessRatio
    fun_prop
  have hE := connectorUniform_positive hK hEr (fun s hs => by
    simpa [visibleConnectorActualExcessRatio] using hk s hs)
  have hAe := connectorUniform_positive hK hA (fun s hs => by
    rw [visibleConnector_shifted_A_zero hdecomp s]
    exact mul_pos (hk s hs) (hpv s hs))
  have hBe := connectorUniform_positive hK hB (fun s hs => by
    rw [visibleConnector_shifted_B_zero hdecomp s]
    exact mul_pos (hk s hs) (hgv s hs))
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (hE.and (hAe.and hBe))
  refine ⟨eps,heps,?_⟩
  intro eta heta hepseta s hs
  have hm : eta ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos heta] using hepseta
  obtain ⟨her,ha,hb⟩ := hball hm
  refine ⟨?_,ha s hs,hb s hs⟩
  rw [visibleConnector_actual_excess_factor hdecomp eta s]
  exact mul_pos heta (her s hs)

/-- The same single compact small-angle choice also makes the actual C
coefficient positive, by differentiating the constructed direction. -/
theorem visibleConnector_uniform_positive_actual_coefficients
    {R : ℝ} (hR : 0 < R) {p gamma : ℝ → Coord}
    {theta kappa : ℝ → ℝ} {K : Set ℝ}
    (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (htheta : ContDiff ℝ ∞ theta) (hkappa : ContDiff ℝ ∞ kappa)
    (hK : IsCompact K)
    (hdecomp : ∀ s, visibleConnectorJ (gamma s) =
      R • visibleConnectorUnitDirection (theta s) -
        kappa s • visibleConnectorJ (visibleConnectorUnitDirection (theta s)))
    (hk : ∀ s ∈ K, 0 < kappa s)
    (hpv : ∀ s ∈ K, 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s))
    (hgv : ∀ s ∈ K, 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s))
    (htpos : ∀ s ∈ K, 0 < deriv theta s) :
    ∃ eps > 0, ∀ eta, 0 < eta → eta < eps → ∀ s ∈ K,
      0 < visibleConnectorJ (gamma s) ⬝ᵥ visibleConnectorShiftedDirection theta eta s - R ∧
      0 < visibleConnectorA p (visibleConnectorShiftedRuling R gamma theta eta) s ∧
      0 < visibleConnectorB gamma (visibleConnectorShiftedRuling R gamma theta eta) s ∧
      0 < visibleConnectorC gamma (visibleConnectorShiftedRuling R gamma theta eta) s := by
  obtain ⟨eps,heps,h⟩ := visibleConnector_uniform_actual_small_angle
    hp hgamma htheta hkappa hK hdecomp hk hpv hgv
  refine ⟨eps,heps,?_⟩
  intro eta heta hepseta s hs
  obtain ⟨hE,hA,hB⟩ := h eta heta hepseta s hs
  refine ⟨hE,hA,hB,?_⟩
  have hdir := visibleConnectorUnitDirection_hasDerivAt
    (((htheta.differentiable (by simp) s).hasDerivAt).sub_const eta)
  have hc := visibleConnector_actual_ruling_C_formula (R := R) hgamma hdir
    (connectorUniform_unit (theta s - eta))
  change 0 < visibleConnectorC gamma
    (visibleConnectorActualRuling R gamma (fun r =>
      visibleConnectorUnitDirection (theta r - eta))) s
  rw [hc]
  exact mul_pos (mul_pos hR (htpos s hs)) hE

end
end TightVer401
