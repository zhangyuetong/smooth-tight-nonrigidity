import TightVer401.RuledVectorReduction
import TightVer401.RuledBendingNecessity

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem supported_ruled_vector_reduction_global {L : ℝ} (d : PeriodicRuledFrame L)
    {Y : Coord → Ambient} {lower : ℝ} (hY : ContDiff ℝ ∞ Y) (hlower : 0 < lower)
    (hstrain : ∀ p : Coord, 0 < p 1 → strain (ruledMap d.γ d.E) Y p 1 1 = 0)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ p 1) :
    Y = ruledBending (frameCoefficient Y d.T) (frameCoefficient Y d.n) d.T d.n := by
  funext p
  by_cases hp : 0 < p 1
  · exact supported_ruled_vector_reduced d hY hlower hstrain hsupport p hp
  · have hz : Y p = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hs
      have hh := hsupport p hs
      exact hp (hlower.trans_le hh))
    simp only [ruledBending, frameCoefficient, hz, inner_zero_left, zero_smul, add_zero]

theorem frameCoefficient_periodic {L : ℝ} {Y : Coord → Ambient} {V : ℝ → Ambient}
    (hY : ∀ u, Function.Periodic (fun s => Y (![s, u] : Coord)) L)
    (hV : Function.Periodic V L) (s u : ℝ) :
    frameCoefficient Y V (![s + L, u] : Coord) = frameCoefficient Y V (![s, u] : Coord) := by
  change inner ℝ (Y (![s + L, u] : Coord)) (V (s + L)) =
    inner ℝ (Y (![s, u] : Coord)) (V s)
  have he : Y (![s + L, u] : Coord) = Y (![s, u] : Coord) := hY u s
  rw [he, hV s]

theorem supported_ruled_vector_period_zero {L lower upper : ℝ} (d : PeriodicRuledFrame L)
    {Y : Coord → Ambient} (hY : ContDiff ℝ ∞ Y) (hlower : 0 < lower) (hupper : 0 < upper)
    (hperiod : ∀ u, Function.Periodic (fun s => Y (![s, u] : Coord)) L)
    (hstrain : ∀ p : Coord, 0 < p 1 → ∀ i j : Fin 2, strain (ruledMap d.γ d.E) Y p i j = 0)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ p 1 ∧ p 1 ≤ upper)
    {p : Coord} (hp : 0 < p 1) (hne : Y p ≠ 0) :
    (∫ r in 0..L, ruledPeriodCoefficient d.k d.τ r) = 0 := by
  have he := supported_ruled_vector_reduction_global d hY hlower
    (fun q hq => hstrain q hq 1 1) (fun q hq => (hsupport q hq).1)
  have hα := frameCoefficient_contDiff hY d.smooth_T
  have hβ := frameCoefficient_contDiff hY d.smooth_n
  apply supported_ruled_bending_period_zero d.deriv_γ d.deriv_E d.deriv_T d.deriv_n
    d.smooth_k d.smooth_τ d.torsion_ne_zero d.period_k d.period_τ
    (frameCoefficient_periodic hperiod d.period_T) (frameCoefficient_periodic hperiod d.period_n)
    (fun q _ => hα.differentiable (by simp) q) (fun q _ => hβ.differentiable (by simp) q)
    d.orthonormal (by simpa only [← he] using hstrain) hlower hupper
  · intro q hq
    rw [← he]
    exact image_eq_zero_of_notMem_tsupport (fun hs => (not_le.mpr hq) (hsupport q hs).1)
  · intro q hq
    rw [← he]
    exact image_eq_zero_of_notMem_tsupport (fun hs => (not_le.mpr hq) (hsupport q hs).2)
  · exact hp
  · simpa only [← he] using hne

end
end TightVer401
