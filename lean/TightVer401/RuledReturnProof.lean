import TightVer401.RuledPrimitives
import TightVer401.RuledCharacteristics

/-! The principal return with its actual torsion factor and period integral.
The primitive is constructed by OpenAI's integration operator. -/
namespace TightVer401
noncomputable section
open OAI.ClosedSurfaceR4.PeriodicPrimitive MeasureTheory
open scoped ContDiff

def ruledOmega (k τ : ℝ → ℝ) : ℝ → ℝ := rawPrimitive (ruledPeriodCoefficient k τ)

theorem ruledOmega_hasDerivAt {k τ : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0) (s : ℝ) :
    HasDerivAt (ruledOmega k τ) (ruledPeriodCoefficient k τ s) s :=
  rawPrimitive_hasDerivAt (ruledPeriodCoefficient_contDiff hk hτ hτ0).continuous s

theorem ruledOmega_increment {k τ : ℝ → ℝ} {L : ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L) (s : ℝ) :
    ruledOmega k τ (s + L) - ruledOmega k τ s =
      ∫ r in 0..L, ruledPeriodCoefficient k τ r := by
  have hc := (ruledPeriodCoefficient_contDiff hk hτ hτ0).continuous
  unfold ruledOmega rawPrimitive
  rw [(ruledPeriodCoefficient_periodic hkL hτL).intervalIntegral_add_eq_add 0 s
    (fun a b => hc.intervalIntegrable a b)]
  simp only [zero_add, add_sub_cancel_left]

theorem ruled_return_of_actual_ODE {k τ u : ℝ → ℝ} {L s : ℝ} {J : Set ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ r, τ r ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hJ : IsOpen J) (hc : IsPreconnected J) (hs : s ∈ J) (ht : s + L ∈ J)
    (hu0 : ∀ r ∈ J, u r ≠ 0)
    (hu : ∀ r ∈ J, HasDerivAt u
      (-(u r / 2) * (ruledLambda τ r + u r * ruledD k τ r)) r) :
    u (s + L) = projectiveReturn
      (ruledRho τ s * (∫ r in 0..L, ruledPeriodCoefficient k τ r)) (u s) := by
  apply principal_return_of_characteristic (ρ := ruledRho τ) («ω» := ruledOmega k τ)
    (lam := ruledLambda τ) (D := ruledD k τ) hJ hc _ hu _ _ hu0 hs ht
    (ruledRho_periodic hτL s) (ruledOmega_increment hk hτ hτ0 hkL hτL s)
  · intro r hr
    exact ruledRho_hasDerivAt (hτ.differentiable (by simp) r).hasDerivAt (hτ0 r)
  · intro r hr
    exact ruledOmega_hasDerivAt hk hτ hτ0 r
  · intro r hr
    exact ne_of_gt (ruledRho_pos (hτ0 r))

end
end TightVer401
