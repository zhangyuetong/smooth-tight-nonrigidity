import TightVer401.SmoothingProfilePatch

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology

theorem smoothingNormalStep_base_derivatives_zero {t : ℝ} (ht : t < 0 ∨ 3 < t) :
    deriv (smoothingNormalStep 1) t = 0 ∧ deriv (deriv (smoothingNormalStep 1)) t = 0 := by
  have hg : ∃ c : ℝ, smoothingNormalStep 1 =ᶠ[𝓝 t] (fun _ => c) := by
    rcases ht with ht | ht
    · refine ⟨0,?_⟩
      filter_upwards [isOpen_Iio.mem_nhds (show t < 1 by linarith)] with x hx
      exact smoothingNormalStep_zero zero_lt_one (le_of_lt hx)
    · refine ⟨1,?_⟩
      filter_upwards [isOpen_Ioi.mem_nhds (show 2 < t by linarith)] with x hx
      change 2 < x at hx
      exact smoothingNormalStep_one zero_lt_one (by linarith)
  obtain ⟨c,hc⟩ := hg
  exact ⟨by simpa using hc.deriv_eq, by simpa using hc.deriv.deriv_eq⟩

theorem smoothingNormalStep_base_derivative_bounds :
    ∃ B₁ > 0, ∃ B₂ > 0, ∀ t : ℝ,
      |deriv (smoothingNormalStep 1) t| ≤ B₁ ∧
      |deriv (deriv (smoothingNormalStep 1)) t| ≤ B₂ := by
  have hf := (contDiff_infty_iff_deriv.mp (smoothingNormalStep_contDiff 1)).2
  have hg := (contDiff_infty_iff_deriv.mp hf).2
  obtain ⟨B₁,hB₁⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 3)).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B₂,hB₂⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 3)).exists_bound_of_continuousOn hg.continuous.continuousOn
  refine ⟨max 1 B₁, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    max 1 B₂, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 3
  · exact ⟨(by simpa only [Real.norm_eq_abs] using (hB₁ t ht).trans (le_max_right _ _)),
      (by simpa only [Real.norm_eq_abs] using (hB₂ t ht).trans (le_max_right _ _))⟩
  · have ho : t < 0 ∨ 3 < t := by
      simp only [mem_Icc,not_and_or,not_le] at ht
      exact ht
    obtain ⟨h₁,h₂⟩ := smoothingNormalStep_base_derivatives_zero ho
    simp only [h₁,h₂,abs_zero]
    constructor <;> exact le_trans zero_le_one (le_max_left _ _)

theorem smoothingNormalStep_scale (h t : ℝ) :
    smoothingNormalStep h t = smoothingNormalStep 1 (t/h) := by
  unfold smoothingNormalStep
  congr 1
  ring

theorem smoothingNormalStep_deriv_scale (h t : ℝ) :
    deriv (smoothingNormalStep h) t = deriv (smoothingNormalStep 1) (t/h) / h := by
  have he : smoothingNormalStep h = fun x => smoothingNormalStep 1 (x/h) := by
    funext x
    exact smoothingNormalStep_scale h x
  rw [he]
  have hf := ((smoothingNormalStep_contDiff 1).differentiable (by simp) (t/h)).hasDerivAt
  simpa only [Function.comp_def,id_eq,one_div,mul_one,mul_comm,mul_inv_rev,div_eq_mul_inv] using
    (hf.comp t ((hasDerivAt_id t).div_const h)).deriv

theorem smoothingNormalStep_second_scale (h t : ℝ) :
    deriv (deriv (smoothingNormalStep h)) t =
      deriv (deriv (smoothingNormalStep 1)) (t/h) / h^2 := by
  have he : deriv (smoothingNormalStep h) = fun x => deriv (smoothingNormalStep 1) (x/h) / h := by
    funext x
    exact smoothingNormalStep_deriv_scale h x
  rw [he]
  have hf := (((contDiff_infty_iff_deriv.mp (smoothingNormalStep_contDiff 1)).2).differentiable
    (by simp) (t/h)).hasDerivAt
  have hd := ((hf.comp t ((hasDerivAt_id t).div_const h)).div_const h).deriv
  simpa only [Function.comp_def,id_eq,one_div,pow_two,div_eq_mul_inv,mul_inv_rev,mul_one,one_mul,mul_assoc] using hd

theorem smoothingNormalStep_uniform_derivative_bounds :
    ∃ B₁ > 0, ∃ B₂ > 0, ∀ h : ℝ, 0 < h → ∀ t : ℝ,
      |deriv (smoothingNormalStep h) t| ≤ B₁/h ∧
      |deriv (deriv (smoothingNormalStep h)) t| ≤ B₂/h^2 := by
  obtain ⟨B₁,hB₁,B₂,hB₂,hb⟩ := smoothingNormalStep_base_derivative_bounds
  refine ⟨B₁,hB₁,B₂,hB₂,fun h hh t => ?_⟩
  rw [smoothingNormalStep_deriv_scale,smoothingNormalStep_second_scale,
    abs_div,abs_div,abs_of_pos hh,abs_of_pos (sq_pos_of_pos hh)]
  exact ⟨div_le_div_of_nonneg_right (hb (t/h)).1 hh.le,
    div_le_div_of_nonneg_right (hb (t/h)).2 (sq_nonneg h)⟩

end
end TightVer401
