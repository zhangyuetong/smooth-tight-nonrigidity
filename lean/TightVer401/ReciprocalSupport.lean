import TightVer401.ReciprocalExtension

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem reciprocalChart_involution {ρ : ℝ → ℝ} {p : Coord}
    (hρ : ρ (p 0) ≠ 0) (hp : p 1 ≠ 0) :
    reciprocalChart ρ (reciprocalChart ρ p) = p := by
  ext i
  fin_cases i
  · rfl
  · change 1 / (ρ (p 0) * (1 / (ρ (p 0) * p 1))) = p 1
    field_simp

theorem reciprocalExtension_nonzero {ρ : ℝ → ℝ} {f : Coord → ℝ}
    (hρpos : ∀ s, 0 < ρ s) {p : Coord} (hp : 0 < p 1) (hf : f p ≠ 0) :
    reciprocalExtension ρ f ≠ 0 := by
  intro hz
  have hr : 0 < (reciprocalChart ρ p) 1 := one_div_pos.mpr (mul_pos (hρpos _) hp)
  have he := congrFun hz (reciprocalChart ρ p)
  rw [reciprocalExtension, if_pos hr,
    reciprocalChart_involution (ne_of_gt (hρpos _)) (ne_of_gt hp)] at he
  exact hf he

theorem reciprocalExtension_periodic {ρ : ℝ → ℝ} {f : Coord → ℝ} {L : ℝ}
    (hρ : Function.Periodic ρ L)
    (hf : ∀ s u, f (![s + L, u] : Coord) = f (![s, u] : Coord)) (s r : ℝ) :
    reciprocalExtension ρ f (![s + L, r] : Coord) =
      reciprocalExtension ρ f (![s, r] : Coord) := by
  simp only [reciprocalExtension, reciprocalChart, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, hρ s, hf]

theorem reciprocalExtension_slice_hasCompactSupport {ρ : ℝ → ℝ} {f : Coord → ℝ}
    {lower : ℝ} (hρpos : ∀ s, 0 < ρ s) (hlower : 0 < lower)
    (hsupport : ∀ p : Coord, p 1 < lower → f p = 0) (s : ℝ) :
    HasCompactSupport (fun r => reciprocalExtension ρ f (![s, r] : Coord)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc 0 (1 / (ρ s * lower))) isCompact_Icc
  intro r hr
  change reciprocalExtension ρ f (![s, r] : Coord) ≠ 0 at hr
  have hrpos : 0 < r := by
    by_contra hn
    exact hr (if_neg hn)
  have hval : f (reciprocalChart ρ (![s, r] : Coord)) ≠ 0 := by
    simpa [reciprocalExtension, hrpos] using hr
  have hlow : lower ≤ 1 / (ρ s * r) := by
    apply le_of_not_gt
    intro hn
    exact hval (hsupport _ hn)
  refine ⟨le_of_lt hrpos, ?_⟩
  apply (le_div_iff₀ (mul_pos (hρpos _) hlower)).mpr
  have hm := (le_div_iff₀ (mul_pos (hρpos _) hrpos)).mp hlow
  nlinarith

end
end TightVer401
