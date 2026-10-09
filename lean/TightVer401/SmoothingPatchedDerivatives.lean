import TightVer401.SmoothingStepBounds

namespace TightVer401
noncomputable section
open scoped ContDiff

theorem smoothingPatchedProfile_deriv (δ : ℝ) (hδ : 0 < δ) (h t : ℝ) :
    deriv (smoothingPatchedProfile δ hδ h) t = deriv (smoothingNormalProfile δ hδ) t -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) t := by
  have hq := ((smoothingNormalProfile_contDiff δ hδ).differentiable (by simp) t).hasDerivAt
  have hζ := ((smoothingNormalStep_contDiff h).differentiable (by simp) t).hasDerivAt
  exact (hq.sub (hζ.const_mul _)).deriv

theorem smoothingPatchedProfile_second (δ : ℝ) (hδ : 0 < δ) (h t : ℝ) :
    deriv (deriv (smoothingPatchedProfile δ hδ h)) t =
      2*smoothingNormalCDF δ hδ t -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (deriv (smoothingNormalStep h)) t := by
  have he : deriv (smoothingPatchedProfile δ hδ h) = fun x =>
      deriv (smoothingNormalProfile δ hδ) x -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) x := by
    funext x
    exact smoothingPatchedProfile_deriv δ hδ h x
  rw [he]
  have hq := (((contDiff_infty_iff_deriv.mp (smoothingNormalProfile_contDiff δ hδ)).2).differentiable
    (by simp) t).hasDerivAt
  have hζ := (((contDiff_infty_iff_deriv.mp (smoothingNormalStep_contDiff h)).2).differentiable
    (by simp) t).hasDerivAt
  have hd := (hq.sub (hζ.const_mul (smoothingNormalProfile δ hδ δ-δ^2))).congr_of_eventuallyEq
    (f₁ := fun x => deriv (smoothingNormalProfile δ hδ) x -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) x)
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hd.deriv,smoothingNormalProfile_second_deriv]

theorem smoothingPatchedProfile_first_error (δ : ℝ) (hδ : 0 < δ) {h B t : ℝ}
    (_hh : 0 < h) (_hB : 0 ≤ B) (hζ : |deriv (smoothingNormalStep h) t| ≤ B/h) :
    |deriv (smoothingPatchedProfile δ hδ h) t - 2*max t 0| ≤ 4*δ+3*δ^2*(B/h) := by
  rw [smoothingPatchedProfile_deriv]
  have he : deriv (smoothingNormalProfile δ hδ) t -
      (smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) t - 2*max t 0 =
      (deriv (smoothingNormalProfile δ hδ) t-2*max t 0) +
      (-((smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) t)) := by ring
  rw [he]
  calc
    _ ≤ |deriv (smoothingNormalProfile δ hδ) t-2*max t 0| +
      |(smoothingNormalProfile δ hδ δ-δ^2)*deriv (smoothingNormalStep h) t| :=
        (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ 4*δ+3*δ^2*(B/h) := by
      apply add_le_add (smoothingNormalProfile_uniform_first_error δ hδ t)
      rw [abs_mul]
      exact mul_le_mul (smoothingNormalProfile_offset_bound δ hδ) hζ (abs_nonneg _) (by positivity)

end
end TightVer401
