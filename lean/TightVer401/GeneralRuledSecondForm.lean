import TightVer401.GeneralRuledDifferential
import TightVer401.RuledCharacteristics

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def generalRuledNormal (c₁ e e₁ : ℝ → Ambient) (p : Coord) : Ambient :=
  ‖generalRuledCross c₁ e e₁ p‖⁻¹ • generalRuledCross c₁ e e₁ p

theorem general_ruled_normal_unit {c₁ e e₁ : ℝ → Ambient} {p : Coord}
    (hδ : generalRuledDelta c₁ e e₁ (p 0) ≠ 0) :
    inner ℝ (generalRuledNormal c₁ e e₁ p) (generalRuledNormal c₁ e e₁ p) = 1 := by
  have hnorm : ‖generalRuledCross c₁ e e₁ p‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (general_ruled_cross_ne_zero hδ)
  simp only [generalRuledNormal]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

theorem general_ruled_isUnitNormal {c e c₁ e₁ : ℝ → Ambient} {p : Coord}
    (hc : HasDerivAt c (c₁ (p 0)) (p 0)) (he : HasDerivAt e (e₁ (p 0)) (p 0))
    (hδ : generalRuledDelta c₁ e e₁ (p 0) ≠ 0) :
    IsUnitNormalAt (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p := by
  refine ⟨general_ruled_normal_unit hδ, ?_⟩
  intro v
  rw [fderiv_two_coordinates, general_ruled_partial_t hc he, general_ruled_partial_u hc he]
  have ht : inner ℝ (c₁ (p 0) + p 1 • e₁ (p 0)) (generalRuledNormal c₁ e e₁ p) = 0 := by
    simp only [generalRuledNormal, generalRuledCross, real_inner_smul_right,
      ambientCross_orthogonal_left, mul_zero]
  have hu : inner ℝ (e (p 0)) (generalRuledNormal c₁ e e₁ p) = 0 := by
    simp only [generalRuledNormal, generalRuledCross, real_inner_smul_right,
      ambientCross_orthogonal_right, mul_zero]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ht, hu]
  simp

theorem general_ruled_second_forms {c e c₁ e₁ c₂ e₂ : ℝ → Ambient} {p : Coord}
    (hc : ∀ s, HasDerivAt c (c₁ s) s) (he : ∀ s, HasDerivAt e (e₁ s) s)
    (hc₁ : HasDerivAt c₁ (c₂ (p 0)) (p 0))
    (he₁ : HasDerivAt e₁ (e₂ (p 0)) (p 0)) :
    secondFundamental (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p 0 0 =
      inner ℝ (c₂ (p 0) + p 1 • e₂ (p 0)) (generalRuledCross c₁ e e₁ p) /
        ‖generalRuledCross c₁ e e₁ p‖ ∧
    secondFundamental (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p 0 1 =
      generalRuledDelta c₁ e e₁ (p 0) / ‖generalRuledCross c₁ e e₁ p‖ ∧
    secondFundamental (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p 1 1 = 0 := by
  obtain ⟨htu, huu⟩ := general_ruled_second_tu hc he (p := p)
  simp [secondFundamental, general_ruled_second_tt hc he hc₁ he₁, htu, huu,
    generalRuledNormal, real_inner_smul_right, general_ruled_mixed_numerator,
    inner_zero_left, mul_zero, div_eq_mul_inv, mul_comm]

theorem general_ruled_asymptotic_slope {c e c₁ e₁ c₂ e₂ : ℝ → Ambient}
    {p : Coord} {w : ℝ}
    (hc : ∀ s, HasDerivAt c (c₁ s) s) (he : ∀ s, HasDerivAt e (e₁ s) s)
    (hc₁ : HasDerivAt c₁ (c₂ (p 0)) (p 0))
    (he₁ : HasDerivAt e₁ (e₂ (p 0)) (p 0))
    (hX : ContDiff ℝ ∞ (ruledMap c e))
    (hδ : generalRuledDelta c₁ e e₁ (p 0) ≠ 0) :
    dotProduct (![1, w] : Coord)
      ((secondFundamental (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p).mulVec ![1, w]) = 0 ↔
    w = -inner ℝ (c₂ (p 0) + p 1 • e₂ (p 0)) (generalRuledCross c₁ e e₁ p) /
      (2 * generalRuledDelta c₁ e e₁ (p 0)) := by
  obtain ⟨h00, h01, h11⟩ := general_ruled_second_forms hc he hc₁ he₁
  have h10 : secondFundamental (ruledMap c e) (generalRuledNormal c₁ e e₁ p) p 1 0 =
      generalRuledDelta c₁ e e₁ (p 0) / ‖generalRuledCross c₁ e e₁ p‖ := by
    rw [secondFundamental, coordPartial_comm hX.contDiffOn isOpen_univ (Set.mem_univ p) 1 0]
    exact h01
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, h00, h01, h10, h11,
    one_mul, mul_one, zero_mul, mul_zero, add_zero]
  have hnorm : ‖generalRuledCross c₁ e e₁ p‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (general_ruled_cross_ne_zero hδ)
  constructor
  · intro hz
    field_simp at hz ⊢
    nlinarith
  · intro hw
    rw [hw]
    field_simp
    <;> ring

end
end TightVer401
