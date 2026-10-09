import TightVer401.GeneralRuledSecondForm
import TightVer401.AmbientCrossSmooth

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def generalRuledQ₁ (c₁ e e₁ c₂ e₂ : ℝ → Ambient) (t : ℝ) : ℝ :=
  -(inner ℝ (c₂ t) (ambientCross (e₁ t) (e t)) +
    inner ℝ (e₂ t) (ambientCross (c₁ t) (e t))) / (2 * generalRuledDelta c₁ e e₁ t)

def generalRuledQ₂ (c₁ e e₁ e₂ : ℝ → Ambient) (t : ℝ) : ℝ :=
  -inner ℝ (e₂ t) (ambientCross (e₁ t) (e t)) / (2 * generalRuledDelta c₁ e e₁ t)

theorem general_ruled_numerator_polynomial (c₁ e e₁ c₂ e₂ : ℝ → Ambient) (p : Coord) :
    inner ℝ (c₂ (p 0) + p 1 • e₂ (p 0)) (generalRuledCross c₁ e e₁ p) =
      inner ℝ (c₂ (p 0)) (ambientCross (c₁ (p 0)) (e (p 0))) +
      (inner ℝ (c₂ (p 0)) (ambientCross (e₁ (p 0)) (e (p 0))) +
        inner ℝ (e₂ (p 0)) (ambientCross (c₁ (p 0)) (e (p 0)))) * p 1 +
      inner ℝ (e₂ (p 0)) (ambientCross (e₁ (p 0)) (e (p 0))) * (p 1)^2 := by
  simp only [generalRuledCross, ambientCross_add_left, ambientCross_smul_left,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem general_ruled_q_polynomial {c₁ e e₁ c₂ e₂ : ℝ → Ambient} {p : Coord}
    (hcentral : inner ℝ (c₂ (p 0)) (ambientCross (c₁ (p 0)) (e (p 0))) = 0) :
    -inner ℝ (c₂ (p 0) + p 1 • e₂ (p 0)) (generalRuledCross c₁ e e₁ p) /
      (2 * generalRuledDelta c₁ e e₁ (p 0)) =
      generalRuledQ₁ c₁ e e₁ c₂ e₂ (p 0) * p 1 +
        generalRuledQ₂ c₁ e e₁ e₂ (p 0) * (p 1)^2 := by
  rw [general_ruled_numerator_polynomial, hcentral]
  simp only [generalRuledQ₁, generalRuledQ₂, zero_add, div_eq_mul_inv]
  ring

theorem general_ruled_coefficients_contDiff {c₁ e e₁ c₂ e₂ : ℝ → Ambient}
    (hc₁ : ContDiff ℝ ∞ c₁) (he : ContDiff ℝ ∞ e) (he₁ : ContDiff ℝ ∞ e₁)
    (hc₂ : ContDiff ℝ ∞ c₂) (he₂ : ContDiff ℝ ∞ e₂)
    (hδ : ∀ s, generalRuledDelta c₁ e e₁ s ≠ 0) :
    ContDiff ℝ ∞ (generalRuledQ₁ c₁ e e₁ c₂ e₂) ∧
      ContDiff ℝ ∞ (generalRuledQ₂ c₁ e e₁ e₂) := by
  have hcross₁ := ambientCross_contDiff hc₁ he
  have hcross₂ := ambientCross_contDiff he₁ he
  have hdelta : ContDiff ℝ ∞ (generalRuledDelta c₁ e e₁) := he₁.inner ℝ hcross₁
  have hden : ContDiff ℝ ∞ (fun s => 2 * generalRuledDelta c₁ e e₁ s) :=
    contDiff_const.mul hdelta
  have hden0 : ∀ s, 2 * generalRuledDelta c₁ e e₁ s ≠ 0 :=
    fun s => mul_ne_zero (by norm_num) (hδ s)
  exact ⟨((hc₂.inner ℝ hcross₂).add (he₂.inner ℝ hcross₁)).neg.div hden hden0,
    (he₂.inner ℝ hcross₂).neg.div hden hden0⟩

end
end TightVer401
