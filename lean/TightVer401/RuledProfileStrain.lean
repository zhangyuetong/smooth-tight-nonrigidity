import TightVer401.RuledProfiles

/-! The displayed profile has zero actual linearized induced metric. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem strain_symmetric (X y : Coord → Ambient) (p : Coord) (i j : Fin 2) :
    strain X y p i j = strain X y p j i := by
  unfold strain
  rw [real_inner_comm (coordPartial i X p) (coordPartial j y p),
    real_inner_comm (coordPartial i y p) (coordPartial j X p)]
  exact add_comm _ _

theorem ruled_profile_zero_strain
    {γ T E n : ℝ → Ambient} {k τ ρ W F : ℝ → ℝ} {p : Coord} {ks lam f₁ f₂ : ℝ}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hk : HasDerivAt k ks (p 0))
    (hτ : HasDerivAt τ (lam * τ (p 0)) (p 0))
    (hρ : HasDerivAt ρ (lam * ρ (p 0) / 2) (p 0))
    (hW : HasDerivAt W ((ks - k (p 0) * lam) / (2 * ρ (p 0))) (p 0))
    (hρ0 : ρ (p 0) ≠ 0) (hu0 : p 1 ≠ 0)
    (hF : HasDerivAt F f₁ (ruledFirstIntegral ρ W p))
    (hF' : HasDerivAt (deriv F) f₂ (ruledFirstIntegral ρ W p))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    ∀ i j : Fin 2, strain (ruledMap γ E)
      (ruledBending (ruledProfileAlpha τ ρ W F) (ruledProfileBeta k ρ W F) T n) p i j = 0 := by
  obtain ⟨hα, hβ, hP⟩ := ruledProfile_differential hk hτ hρ hW hρ0 hu0 hF hF'
  obtain ⟨_, _, hfac⟩ := ruledProfile_factors hk hτ hρ hρ0
  have hss : (1 - k (p 0) * p 1) * coordPartial 0 (ruledProfileAlpha τ ρ W F) p +
      τ (p 0) * p 1 * coordPartial 0 (ruledProfileBeta k ρ W F) p = 0 := by
    rw [(hP 0).1, (hP 0).2, (hfac 0).1, (hfac 0).2,
      ruledFirstIntegral_partial hρ hW hρ0 hu0 0]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
    dsimp only [ruledAlphaFactor, ruledBetaFactor]
    field_simp
    <;> ring
  have hmix : (1 - k (p 0) * p 1) * coordPartial 1 (ruledProfileAlpha τ ρ W F) p +
      τ (p 0) * p 1 * coordPartial 1 (ruledProfileBeta k ρ W F) p +
      k (p 0) * ruledProfileAlpha τ ρ W F p - τ (p 0) * ruledProfileBeta k ρ W F p = 0 := by
    rw [(hP 1).1, (hP 1).2, (hfac 1).1, (hfac 1).2,
      ruledFirstIntegral_partial hρ hW hρ0 hu0 1]
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    dsimp only [ruledAlphaFactor, ruledBetaFactor, ruledProfileAlpha, ruledProfileBeta]
    rw [hF.deriv]
    field_simp
    <;> ring
  obtain ⟨h00, h01, h11⟩ := ruled_strain_equations hγ hE hT hn hα hβ hf
  rw [hss, mul_zero] at h00
  rw [hmix] at h01
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · rw [strain_symmetric]
    exact h01
  · exact h11

end
end TightVer401
