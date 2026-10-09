import TightVer401.RuledReturnProof
import Mathlib.Analysis.Normed.Group.Bounded

/-! Explicit characteristic flow, including the central leaf. The denominator
is uniformly positive for small initial data over any compact time interval. -/
namespace TightVer401
noncomputable section
open scoped ContDiff

def principalTrajectory (ρ W : ℝ → ℝ) (s u : ℝ) : ℝ → ℝ :=
  fun t => (ρ s * u) / (ρ t * (1 + ρ s * u * (W t - W s)))

theorem principalTrajectory_initial {ρ W : ℝ → ℝ} {s u : ℝ}
    (hρ : ρ s ≠ 0) : principalTrajectory ρ W s u s = u := by
  simp [principalTrajectory, hρ]

theorem principalTrajectory_central (ρ W : ℝ → ℝ) (s t : ℝ) :
    principalTrajectory ρ W s 0 t = 0 := by
  simp [principalTrajectory]

theorem principalTrajectory_hasDerivAt {ρ W : ℝ → ℝ} {s u t lam D : ℝ}
    (hρ : HasDerivAt ρ (lam * ρ t / 2) t)
    (hW : HasDerivAt W (D / (2 * ρ t)) t)
    (hρ0 : ρ t ≠ 0) (hd : 1 + ρ s * u * (W t - W s) ≠ 0) :
    HasDerivAt (principalTrajectory ρ W s u)
      (-(principalTrajectory ρ W s u t / 2) *
        (lam + principalTrajectory ρ W s u t * D)) t := by
  have hden := hρ.mul (((hW.sub_const (W s)).const_mul (ρ s * u)).const_add 1)
  convert! (hasDerivAt_const t (ρ s * u)).fun_div hden (mul_ne_zero hρ0 hd) using 1
  dsimp only [principalTrajectory]
  field_simp
  <;> simp only [Pi.mul_apply]
  <;> ring

theorem principalTrajectory_return {ρ W : ℝ → ℝ} {s u L I : ℝ}
    (hρ0 : ρ s ≠ 0) (hρL : ρ (s + L) = ρ s)
    (hW : W (s + L) - W s = I) :
    principalTrajectory ρ W s u (s + L) = projectiveReturn (ρ s * I) u := by
  dsimp only [principalTrajectory, projectiveReturn]
  rw [hρL, hW]
  rw [mul_div_mul_left _ _ hρ0]
  congr 1
  ring

theorem principalTrajectory_uniform_denominator {ρ W : ℝ → ℝ} {s : ℝ}
    {J : Set ℝ} (hJ : IsCompact J) (hW : ContinuousOn W J) :
    ∃ δ > 0, ∀ u : ℝ, |u| < δ → ∀ t ∈ J,
      1 / 2 < 1 + ρ s * u * (W t - W s) := by
  obtain ⟨C, hC⟩ := hJ.exists_bound_of_continuousOn
    (continuousOn_const.mul (hW.sub continuousOn_const))
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨1 / (2 * B), one_div_pos.mpr (mul_pos (by norm_num) hB), ?_⟩
  intro u hu t ht
  have hb : |ρ s * (W t - W s)| ≤ B := by
    have hh := hC t ht
    have hCB : C ≤ B := by
      change C ≤ max C 0 + 1
      exact le_trans (le_max_left _ _) (by linarith)
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply] using hh.trans hCB
  have hp : |ρ s * u * (W t - W s)| < 1 / 2 := by
    have hm := mul_lt_mul_of_pos_right hu hB
    have he : (1 / (2 * B)) * B = 1 / 2 := by field_simp
    rw [he] at hm
    calc
      |ρ s * u * (W t - W s)| = |u| * |ρ s * (W t - W s)| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |u| * B := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ < 1 / 2 := hm
  have hn := (abs_lt.mp hp).1
  linarith

theorem ruled_flow_over_period {k τ : ℝ → ℝ} {s L : ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hτ0 : ∀ t, τ t ≠ 0)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L) :
    ∃ δ > 0, ∀ u : ℝ, |u| < δ →
      principalTrajectory (ruledRho τ) (ruledOmega k τ) s u s = u ∧
      (∀ t ∈ Set.Icc s (s + L), HasDerivAt
        (principalTrajectory (ruledRho τ) (ruledOmega k τ) s u)
        (-(principalTrajectory (ruledRho τ) (ruledOmega k τ) s u t / 2) *
          (ruledLambda τ t +
            principalTrajectory (ruledRho τ) (ruledOmega k τ) s u t * ruledD k τ t)) t) ∧
      principalTrajectory (ruledRho τ) (ruledOmega k τ) s u (s + L) =
        projectiveReturn (ruledRho τ s *
          (∫ r in 0..L, ruledPeriodCoefficient k τ r)) u := by
  have hW : Continuous (ruledOmega k τ) :=
    continuous_iff_continuousAt.mpr
      (fun t => (ruledOmega_hasDerivAt hk hτ hτ0 t).continuousAt)
  obtain ⟨δ, hδ, hd⟩ := principalTrajectory_uniform_denominator
    (ρ := ruledRho τ) (s := s) isCompact_Icc hW.continuousOn
  refine ⟨δ, hδ, fun u hu => ⟨principalTrajectory_initial
    (ne_of_gt (ruledRho_pos (hτ0 s))), ?_, ?_⟩⟩
  · intro t ht
    exact principalTrajectory_hasDerivAt
      (ruledRho_hasDerivAt (hτ.differentiable (by simp) t).hasDerivAt (hτ0 t))
      (ruledOmega_hasDerivAt hk hτ hτ0 t)
      (ne_of_gt (ruledRho_pos (hτ0 t)))
      (ne_of_gt (lt_trans (by norm_num) (hd u hu t ht)))
  · exact principalTrajectory_return (ne_of_gt (ruledRho_pos (hτ0 s)))
      (ruledRho_periodic hτL s) (ruledOmega_increment hk hτ hτ0 hkL hτL s)

end
end TightVer401
