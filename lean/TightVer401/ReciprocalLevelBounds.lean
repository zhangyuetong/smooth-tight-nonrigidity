import TightVer401.ReciprocalClassification

/-! Support bounds in u force the manuscript's bounds on every nonzero
transverse profile level, using the complete additive-coordinate trajectory. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem reciprocalProfile_level_bounds {ρ lam D W : ℝ → ℝ} {f : Coord → ℝ}
    {lower upper c : ℝ} (hρ : ∀ s, HasDerivAt ρ (lam s * ρ s / 2) s)
    (hρpos : ∀ s, 0 < ρ s) (hlower : 0 < lower) (hupper : 0 < upper)
    (hf : ∀ p : Coord, 0 < p 1 → DifferentiableAt ℝ f p)
    (hsupportLower : ∀ p : Coord, p 1 < lower → f p = 0)
    (hsupportUpper : ∀ p : Coord, upper < p 1 → f p = 0)
    (hpde : ∀ p : Coord, 0 < p 1 → coordPartial 0 f p -
      p 1 / 2 * (lam (p 0) + p 1 * D (p 0)) * coordPartial 1 f p = 0)
    (hW : ∀ s, HasDerivAt W (D s / (2 * ρ s)) s) (hW0 : W 0 = 0)
    (hc : reciprocalProfile ρ f c ≠ 0) (s : ℝ) :
    1 / (ρ s * upper) - W s ≤ c ∧ c ≤ 1 / (ρ s * lower) - W s := by
  have hg := reciprocalExtension_differentiable (fun t => (hρ t).differentiableAt)
    hρpos hupper hf hsupportUpper
  have he := advection_first_integral_formula hg hW hW0
    (reciprocalExtension_transport hρ hρpos hupper hf hsupportUpper hpde) s (c + W s)
  simp only [add_sub_cancel_right] at he
  have hgn : reciprocalExtension ρ f (![s, c + W s] : Coord) ≠ 0 := by
    rw [he]
    exact hc
  have hr : 0 < c + W s := by
    by_contra hn
    exact hgn (if_neg hn)
  have hfn : f (![s, 1 / (ρ s * (c + W s))] : Coord) ≠ 0 := by
    simpa [reciprocalExtension, reciprocalChart, hr] using hgn
  have hlo : lower ≤ 1 / (ρ s * (c + W s)) := by
    apply le_of_not_gt
    intro hn
    exact hfn (hsupportLower _ hn)
  have hhi : 1 / (ρ s * (c + W s)) ≤ upper := by
    apply le_of_not_gt
    intro hn
    exact hfn (hsupportUpper _ hn)
  have hprod := mul_pos (hρpos s) hr
  have hlowprod := (le_div_iff₀ hprod).mp hlo
  have hhighprod := (div_le_iff₀ hprod).mp hhi
  constructor
  · have hx : 1 / (ρ s * upper) ≤ c + W s := by
      apply (div_le_iff₀ (mul_pos (hρpos s) hupper)).mpr
      nlinarith
    linarith
  · have hx : c + W s ≤ 1 / (ρ s * lower) := by
      apply (le_div_iff₀ (mul_pos (hρpos s) hlower)).mpr
      nlinarith
    linarith

end
end TightVer401
