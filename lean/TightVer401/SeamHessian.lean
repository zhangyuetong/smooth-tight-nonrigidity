import TightVer401.PlanarGradientInverse

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix Topology

/-- Differentiating the common actual gradient trace fixes the tangent Hessian column. -/
theorem seam_hessian_tangent_action {G H : Coord → ℝ} {U : Set Coord}
    (hG : ContDiffOn ℝ ∞ G U) (hH : ContDiffOn ℝ ∞ H U) (hU : IsOpen U)
    {γ : ℝ → Coord} {t : ℝ} (hγ : DifferentiableAt ℝ γ t) (hp : γ t ∈ U)
    (htrace : (fun s => planarGradient G (γ s)) =ᶠ[𝓝 t]
      (fun s => planarGradient H (γ s))) :
    planarHessian G (γ t) *ᵥ deriv γ t = planarHessian H (γ t) *ᵥ deriv γ t := by
  have hg := (((planarGradient_contDiffOn hG hU) (γ t) hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hh := (((planarGradient_contDiffOn hH hU) (γ t) hp).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdG := hg.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  have hdH := hh.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  have he := (hdG.congr_of_eventuallyEq htrace.symm).unique hdH
  simpa only [planarGradient_fderiv_apply hG hU hp,
    planarGradient_fderiv_apply hH hU hp] using he

def seamSecondJet (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

theorem seamSecondJet_det (a b c : ℝ) : (seamSecondJet a b c).det = a * c - b^2 := by
  simp [seamSecondJet, Matrix.det_fin_two, pow_two]

theorem seamSecondJet_saddle_iff {a b c : ℝ} (ha : 0 < a) :
    (seamSecondJet a b c).det < 0 ↔ c < b^2 / a := by
  rw [seamSecondJet_det, lt_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

theorem seamSecondJet_blend (a b c₀ c₁ θ : ℝ) :
    (1 - θ) • seamSecondJet a b c₀ + θ • seamSecondJet a b c₁ =
      seamSecondJet a b ((1 - θ) * c₀ + θ * c₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> ring

theorem seamSecondJet_det_blend (a b c₀ c₁ θ : ℝ) :
    (seamSecondJet a b ((1 - θ) * c₀ + θ * c₁)).det =
      (1 - θ) * (seamSecondJet a b c₀).det + θ * (seamSecondJet a b c₁).det := by
  simp only [seamSecondJet_det]
  ring

theorem seamSecondJet_blend_margin {a b c₀ c₁ θ μ : ℝ}
    (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (h₀ : (seamSecondJet a b c₀).det ≤ -μ)
    (h₁ : (seamSecondJet a b c₁).det ≤ -μ) :
    (seamSecondJet a b ((1 - θ) * c₀ + θ * c₁)).det ≤ -μ := by
  rw [seamSecondJet_det_blend]
  nlinarith [mul_le_mul_of_nonneg_left h₀ (by linarith : 0 ≤ 1 - θ),
    mul_le_mul_of_nonneg_left h₁ hθ.1]

theorem seamSecondJet_blend_saddle {a b c₀ c₁ θ : ℝ}
    (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (h₀ : (seamSecondJet a b c₀).det < 0)
    (h₁ : (seamSecondJet a b c₁).det < 0) :
    (seamSecondJet a b ((1 - θ) * c₀ + θ * c₁)).det < 0 := by
  let μ := min (-(seamSecondJet a b c₀).det) (-(seamSecondJet a b c₁).det)
  have hμ : 0 < μ := lt_min (neg_pos.mpr h₀) (neg_pos.mpr h₁)
  have hb := seamSecondJet_blend_margin hθ
    (show (seamSecondJet a b c₀).det ≤ -μ by
      dsimp [μ]; linarith [min_le_left (-(seamSecondJet a b c₀).det) (-(seamSecondJet a b c₁).det)])
    (show (seamSecondJet a b c₁).det ≤ -μ by
      dsimp [μ]; linarith [min_le_right (-(seamSecondJet a b c₀).det) (-(seamSecondJet a b c₁).det)])
  exact hb.trans_lt (neg_neg_of_pos hμ)

end
end TightVer401
