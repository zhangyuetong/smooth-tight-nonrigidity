import TightVer401.ReciprocalNecessity
import TightVer401.RuledPotentialPDE

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem ruled_potential_period_necessity {k τ : ℝ → ℝ} {P : Coord → ℝ} {L lower upper : ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hP : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ P p)
    (hsupportLower : ∀ p : Coord, p 1 < lower → P p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → P p = 0)
    (hPL : ∀ s u, P (![s + L, u] : Coord) = P (![s, u] : Coord))
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 P p -
      p 1 / 2 * (ruledLambda τ (p 0) + p 1 * ruledD k τ (p 0)) * coordPartial 1 P p =
        -p 1 * ruledD k τ (p 0) * P p)
    {p : Coord} (hp : 0 < p 1) (hne : P p ≠ 0) :
    (∫ r in 0..L, ruledPeriodCoefficient k τ r) = 0 := by
  apply ruled_transport_period_necessity (f := ruledTransportWeight τ P)
    hk hτ hτ0 hkL hτL hlower hupper
  · intro q hq
    exact ruledTransportWeight_differentiableAt (hτ.differentiable (by simp) (q 0))
      (hP q hq) (hτ0 _) (ne_of_gt hq)
  · intro q hq
    simp [ruledTransportWeight, hsupportLower q hq]
  · intro q hq
    simp [ruledTransportWeight, hsupportUpper q hq]
  · intro s u
    simp [ruledTransportWeight, hτL s, hPL s u]
  · intro q hq
    have hτeq : HasDerivAt τ (ruledLambda τ (q 0) * τ (q 0)) (q 0) := by
      convert! (hτ.differentiable (by simp) (q 0)).hasDerivAt using 1
      dsimp only [ruledLambda]
      field_simp [hτ0 (q 0)]
    exact ruledTransportWeight_transport hτeq (hP q hq) (hτ0 _) (ne_of_gt hq) (hpde q hq)
  · exact hp
  · exact div_ne_zero hne (mul_ne_zero (mul_ne_zero (hτ0 _) (ne_of_gt hp)) (ne_of_gt hp))

end
end TightVer401
