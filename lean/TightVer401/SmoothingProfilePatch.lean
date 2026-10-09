import TightVer401.SmoothingNormalProfileBounds

namespace TightVer401
noncomputable section
open Filter
open scoped ContDiff Topology

def smoothingNormalStep (h : ℝ) (t : ℝ) : ℝ :=
  smoothingNormalCDF 1 (by norm_num) (2*t/h-3)

def smoothingPatchedProfile (δ : ℝ) (hδ : 0 < δ) (h : ℝ) (t : ℝ) : ℝ :=
  smoothingNormalProfile δ hδ t -
    (smoothingNormalProfile δ hδ δ - δ^2) * smoothingNormalStep h t

theorem smoothingNormalStep_contDiff (h : ℝ) : ContDiff ℝ ∞ (smoothingNormalStep h) := by
  exact (smoothingNormalCDF_contDiff 1 (by norm_num)).comp (by fun_prop)

theorem smoothingNormalStep_bounds (h t : ℝ) :
    0 ≤ smoothingNormalStep h t ∧ smoothingNormalStep h t ≤ 1 :=
  smoothingNormalCDF_bounds 1 (by norm_num) _

theorem smoothingNormalStep_zero {h t : ℝ} (hh : 0 < h) (ht : t ≤ h) :
    smoothingNormalStep h t = 0 := by
  apply smoothingNormalCDF_zero
  have hs : 2*t/h ≤ 2 := (div_le_iff₀ hh).mpr (by linarith)
  linarith

theorem smoothingNormalStep_one {h t : ℝ} (hh : 0 < h) (ht : 2*h ≤ t) :
    smoothingNormalStep h t = 1 := by
  apply smoothingNormalCDF_one
  have hs : 4 ≤ 2*t/h := (le_div_iff₀ hh).mpr (by linarith)
  linarith

theorem smoothingPatchedProfile_contDiff (δ : ℝ) (hδ : 0 < δ) (h : ℝ) :
    ContDiff ℝ ∞ (smoothingPatchedProfile δ hδ h) :=
  (smoothingNormalProfile_contDiff δ hδ).sub (contDiff_const.mul (smoothingNormalStep_contDiff h))

theorem smoothingPatchedProfile_core (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (ht : t ≤ h) :
    smoothingPatchedProfile δ hδ h t = smoothingNormalProfile δ hδ t := by
  simp [smoothingPatchedProfile, smoothingNormalStep_zero hh ht]

theorem smoothingPatchedProfile_zero (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (ht : t ≤ -δ) : smoothingPatchedProfile δ hδ h t = 0 := by
  rw [smoothingPatchedProfile_core δ hδ hh (by linarith), smoothingNormalProfile_zero δ hδ ht]

theorem smoothingPatchedProfile_square (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (hδh : δ ≤ h) (ht : 2*h ≤ t) :
    smoothingPatchedProfile δ hδ h t = t^2 := by
  rw [smoothingPatchedProfile, smoothingNormalStep_one hh ht,
    smoothingNormalProfile_right δ hδ (by linarith)]
  ring

theorem smoothingPatchedProfile_core_germ (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (ht : t < h) :
    smoothingPatchedProfile δ hδ h =ᶠ[𝓝 t] smoothingNormalProfile δ hδ := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
  exact smoothingPatchedProfile_core δ hδ hh (le_of_lt hx)

theorem smoothingPatchedProfile_zero_germ (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (ht : t < -δ) :
    smoothingPatchedProfile δ hδ h =ᶠ[𝓝 t] (fun _ => 0) := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
  exact smoothingPatchedProfile_zero δ hδ hh (le_of_lt hx)

theorem smoothingPatchedProfile_square_germ (δ : ℝ) (hδ : 0 < δ) {h t : ℝ}
    (hh : 0 < h) (hδh : δ ≤ h) (ht : 2*h < t) :
    smoothingPatchedProfile δ hδ h =ᶠ[𝓝 t] (fun x => x^2) := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact smoothingPatchedProfile_square δ hδ hh hδh (le_of_lt hx)

theorem smoothingPatchedProfile_uniform_value_error (δ : ℝ) (hδ : 0 < δ) (h t : ℝ) :
    |smoothingPatchedProfile δ hδ h t - (max t 0)^2| ≤ 7*δ^2 := by
  have hC := smoothingNormalProfile_offset_bound δ hδ
  have hζ := smoothingNormalStep_bounds h t
  have he : smoothingPatchedProfile δ hδ h t - (max t 0)^2 =
      (smoothingNormalProfile δ hδ t - (max t 0)^2) -
      (smoothingNormalProfile δ hδ δ - δ^2) * smoothingNormalStep h t := by
    unfold smoothingPatchedProfile
    ring
  rw [he]
  calc
    _ ≤ |smoothingNormalProfile δ hδ t - (max t 0)^2| +
      |(smoothingNormalProfile δ hδ δ - δ^2) * smoothingNormalStep h t| := by
        rw [sub_eq_add_neg (smoothingNormalProfile δ hδ t - (max t 0)^2)]
        exact (abs_add_le (smoothingNormalProfile δ hδ t - (max t 0)^2)
          (-((smoothingNormalProfile δ hδ δ - δ^2) * smoothingNormalStep h t))).trans_eq
          (by rw [abs_neg])
    _ ≤ 4*δ^2 + 3*δ^2 := by
      apply add_le_add (smoothingNormalProfile_uniform_value_error δ hδ t)
      rw [abs_mul, abs_of_nonneg hζ.1]
      exact (mul_le_mul hC hζ.2 hζ.1 (by positivity)).trans_eq (mul_one _)
    _ = _ := by ring

end
end TightVer401
