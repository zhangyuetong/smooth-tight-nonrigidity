import TightVer401.ConcaveJetJoinPrimitive

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem jetOriginalAcceleration_mass {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (A B : ℝ) :
    (∫ x in A..B, -deriv (deriv q) x) = deriv q A - deriv q B := by
  have hq₁ := (contDiff_infty_iff_deriv.mp hq).2
  have hq₂ := (contDiff_infty_iff_deriv.mp hq₁).2
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hq₁.differentiable (by simp) x) (hq₂.continuous.intervalIntegrable A B)]
  ring

theorem jetOriginalAcceleration_first_moment {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (A B : ℝ) :
    (∫ x in A..B, x * (-deriv (deriv q) x)) =
      A * deriv q A - B * deriv q B + q B - q A := by
  have hq₁ := (contDiff_infty_iff_deriv.mp hq).2
  have hq₂ := (contDiff_infty_iff_deriv.mp hq₁).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x) (v := deriv q) (u' := fun _ => (1 : ℝ)) (v' := deriv (deriv q))
    continuous_id.continuousOn hq₁.continuous.continuousOn (fun x _ => hasDerivAt_id x)
    (fun x _ => (hq₁.differentiable (by simp) x).hasDerivAt)
    intervalIntegrable_const (hq₂.continuous.intervalIntegrable A B)
  simp only [one_mul] at he
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hq.differentiable (by simp) x) (hq₁.continuous.intervalIntegrable A B)] at he
  simp_rw [mul_neg, intervalIntegral.integral_neg]
  rw [he]
  ring

theorem jetPiecewiseAcceleration_moments {qL qR : ℝ → ℝ}
    (hqL : ContDiff ℝ ∞ qL) (hqR : ContDiff ℝ ∞ qR) (A c B : ℝ)
    (hvalue : qL c = qR c) (hslope : deriv qL c = deriv qR c) :
    (∫ x in A..c, -deriv (deriv qL) x) + (∫ x in c..B, -deriv (deriv qR) x) =
        deriv qL A - deriv qR B ∧
    (∫ x in A..c, x * (-deriv (deriv qL) x)) +
      (∫ x in c..B, x * (-deriv (deriv qR) x)) =
        A * deriv qL A - B * deriv qR B + qR B - qL A := by
  constructor
  · rw [jetOriginalAcceleration_mass hqL, jetOriginalAcceleration_mass hqR, hslope]
    ring
  · rw [jetOriginalAcceleration_first_moment hqL, jetOriginalAcceleration_first_moment hqR,
      hslope, hvalue]
    ring

theorem concaveJetReconstruction_piecewise_endpoint {qL qR h : ℝ → ℝ}
    (hqL : ContDiff ℝ ∞ qL) (hqR : ContDiff ℝ ∞ qR) (hh : ContDiff ℝ ∞ h) (A c B : ℝ)
    (hvalue : qL c = qR c) (hslope : deriv qL c = deriv qR c)
    (hmass : (∫ x in A..B, h x) =
      (∫ x in A..c, -deriv (deriv qL) x) + (∫ x in c..B, -deriv (deriv qR) x))
    (hfirst : (∫ x in A..B, x * h x) =
      (∫ x in A..c, x * (-deriv (deriv qL) x)) +
        (∫ x in c..B, x * (-deriv (deriv qR) x))) :
    concaveJetReconstruction A (qL A) (deriv qL A) h B = qR B ∧
      deriv (concaveJetReconstruction A (qL A) (deriv qL A) h) B = deriv qR B := by
  obtain ⟨hM, hF⟩ := jetPiecewiseAcceleration_moments hqL hqR A c B hvalue hslope
  rw [hM] at hmass
  rw [hF] at hfirst
  constructor
  · simp only [concaveJetReconstruction, jetDoublePrimitive_moments hh, hmass, hfirst]
    ring
  · rw [concaveJetReconstruction_deriv hh, jetPrimitive_eq_interval hh.continuous, hmass]
    ring

end
end TightVer401
