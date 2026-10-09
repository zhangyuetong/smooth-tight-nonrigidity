import TightVer401.ReciprocalTransport
import TightVer401.ReciprocalSupport
import TightVer401.RuledReturnProof

/-! Compactly supported solutions of the actual principal transport PDE
force the actual torsion period integral to vanish. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem ruled_transport_period_necessity {k τ : ℝ → ℝ} {f : Coord → ℝ} {L lower upper : ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ s, τ s ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupportLower : ∀ p : Coord, p 1 < lower → f p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → f p = 0)
    (hfL : ∀ s u, f (![s + L, u] : Coord) = f (![s, u] : Coord))
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 f p -
      p 1 / 2 * (ruledLambda τ (p 0) + p 1 * ruledD k τ (p 0)) * coordPartial 1 f p = 0)
    {p : Coord} (hp : 0 < p 1) (hne : f p ≠ 0) :
    (∫ r in 0..L, ruledPeriodCoefficient k τ r) = 0 := by
  have hρpos : ∀ s, 0 < ruledRho τ s := fun s => ruledRho_pos (hτ0 s)
  have hρ : ∀ s, HasDerivAt (ruledRho τ)
      (ruledLambda τ s * ruledRho τ s / 2) s := fun s =>
    ruledRho_hasDerivAt (hτ.differentiable (by simp) s).hasDerivAt (hτ0 s)
  have hW0 : ruledOmega k τ 0 = 0 := by simp [ruledOmega, rawPrimitive]
  have hWL := ruledOmega_increment hk hτ hτ0 hkL hτL 0
  rw [hW0, zero_add, sub_zero] at hWL
  apply advection_period_zero_of_compact_support
    (reciprocalExtension_differentiable (fun s => (hρ s).differentiableAt)
      hρpos hupper hf hsupportUpper)
    (ruledOmega_hasDerivAt hk hτ hτ0) hW0 hWL
  · exact reciprocalExtension_transport hρ hρpos hupper hf hsupportUpper hpde
  · exact reciprocalExtension_periodic (ruledRho_periodic hτL) hfL
  · exact reciprocalExtension_slice_hasCompactSupport hρpos hlower hsupportLower 0
  · exact reciprocalExtension_nonzero hρpos hp hne

end
end TightVer401
