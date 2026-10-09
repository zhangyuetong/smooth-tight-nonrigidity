import TightVer401.ReciprocalLevelBounds

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set

theorem reciprocalProfile_support_bounds {ρ lam D W : ℝ → ℝ} {f : Coord → ℝ}
    {lower upper : ℝ} (hρ : ∀ s, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hρpos : ∀ s, 0 < ρ s) (hlower : 0 < lower) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupportLower : ∀ p : Coord, p 1 < lower → f p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → f p = 0)
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 f p -
      p 1 / 2 * (lam (p 0) + p 1 * D (p 0)) * coordPartial 1 f p = 0)
    (hW : ∀ s, HasDerivAt W (D s / (2 * ρ s)) s) (hW0 : W 0 = 0)
    (s : ℝ) : tsupport (reciprocalProfile ρ f) ⊆
      Icc (1 / (ρ s * upper) - W s) (1 / (ρ s * lower) - W s) := by
  apply closure_minimal _ isClosed_Icc
  intro c hc
  exact reciprocalProfile_level_bounds hρ hρpos hlower hupper hf hsupportLower hsupportUpper
    hpde hW hW0 hc s

theorem strict_band_cutoff_of_upper_support {ρ W : ℝ → ℝ} {F : ℝ → ℝ} {upper b : ℝ}
    (hρpos : ∀ s, 0 < ρ s) (hupper : 0 < upper) (hb : upper < b)
    (hsupport : ∀ s, ∀ c ∈ tsupport F, 1 / (ρ s * upper) - W s ≤ c)
    (s c : ℝ) (hc : c ∈ tsupport F) : 1 / (ρ s * b) - W s < c := by
  have hi := one_div_lt_one_div_of_lt (mul_pos (hρpos s) hupper)
    (mul_lt_mul_of_pos_left hb (hρpos s))
  have hlo := hsupport s c hc
  linarith

end
end TightVer401
