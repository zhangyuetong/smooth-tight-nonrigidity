import TightVer401.SmoothingPositiveSquare
import TightVer401.SmoothingPatchedDerivatives

namespace TightVer401
noncomputable section
open Filter OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology

theorem smoothing_positive_square_normal_hasFDerivAt (p : Coord) :
    HasFDerivAt (fun q : Coord => (max (q 1) 0)^2)
      ((2*max (p 1) 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) p := by
  have h := (smoothing_positive_square_hasDerivAt (p 1)).hasFDerivAt.comp p
    (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have h' := h.congr_of_eventuallyEq (f₁ := fun q : Coord => (max (q 1) 0)^2)
    (Eventually.of_forall (fun _ => rfl))
  have he : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2*max (p 1) 0)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) =
      (2*max (p 1) 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) := by
    ext v
    simp [mul_comm]
  exact he ▸ h'

theorem smoothing_positive_square_normal_partial (p : Coord) (i : Fin 2) :
    coordPartial i (fun q : Coord => (max (q 1) 0)^2) p = if i=1 then 2*max (p 1) 0 else 0 := by
  unfold coordPartial
  rw [(smoothing_positive_square_normal_hasFDerivAt p).fderiv]
  fin_cases i <;> simp

theorem smoothingFlatOriginal_partial {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) (p : Coord) (i : Fin 2) :
    coordPartial i (smoothingFlatOriginal F G) p = coordPartial i G p +
      (if i=1 then 2*max (p 1) 0 else 0)*smoothingFlatRemainder (F-G) p +
      (max (p 1) 0)^2*coordPartial i (smoothingFlatRemainder (F-G)) p := by
  have he : smoothingFlatOriginal F G = fun q => G q+
      (max (q 1) 0)^2*smoothingFlatRemainder (F-G) q := by
    funext q
    exact smoothingFlatOriginal_eq hF hG hzero hfirst q
  have hR : ContDiff ℝ ∞ (smoothingFlatRemainder (F-G)) := smoothingFlatRemainder_contDiff (hF.sub hG)
  have hQ : Differentiable ℝ (fun q : Coord => (max (q 1) 0)^2) :=
    fun q => (smoothing_positive_square_normal_hasFDerivAt q).differentiableAt
  rw [he,coordPartial_add_at (f := G)
    (h := fun q => (max (q 1) 0)^2*smoothingFlatRemainder (F-G) q)
    (hG.differentiable (by simp) p)
    (hQ.mul (hR.differentiable (by simp)) p),
    coordPartial_mul_at (hQ p) (hR.differentiable (by simp) p),smoothing_positive_square_normal_partial]
  ring

/-- Actual C¹ error estimate, including the original function's actual derivative
on the seam, where the positive square is only C¹. -/
theorem smoothingFlatPatch_partial_bound {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0) (δ : ℝ) (hδ : 0 < δ)
    {h B M₀ M₁ : ℝ} (hh : 0 < h) (hB : 0 ≤ B) {p : Coord}
    (hζ : |deriv (smoothingNormalStep h) (p 1)| ≤ B/h)
    (hR₀ : |smoothingFlatRemainder (F-G) p| ≤ M₀)
    (hR₁ : ∀ i, |coordPartial i (smoothingFlatRemainder (F-G)) p| ≤ M₁) (i : Fin 2) :
    |coordPartial i (smoothingFlatPatch F G δ hδ h) p-
      coordPartial i (smoothingFlatOriginal F G) p| ≤
        (4*δ+3*δ^2*(B/h))*M₀+7*δ^2*M₁ := by
  have hq := smoothingPatchedProfile_uniform_value_error δ hδ h (p 1)
  have hd := smoothingPatchedProfile_first_error δ hδ hh hB hζ
  have hR : ContDiff ℝ ∞ (smoothingFlatRemainder (F-G)) := smoothingFlatRemainder_contDiff (hF.sub hG)
  have he : coordPartial i (smoothingFlatPatch F G δ hδ h) p-
      coordPartial i (smoothingFlatOriginal F G) p =
      (if i=1 then deriv (smoothingPatchedProfile δ hδ h) (p 1)-2*max (p 1) 0 else 0)*
        smoothingFlatRemainder (F-G) p +
      (smoothingPatchedProfile δ hδ h (p 1)-(max (p 1) 0)^2)*
        coordPartial i (smoothingFlatRemainder (F-G)) p := by
    change coordPartial i (smoothingNormalModel (smoothingPatchedProfile δ hδ h) G
      (smoothingFlatRemainder (F-G))) p-_ = _
    rw [smoothingNormalModel_partial (R := smoothingFlatRemainder (F-G))
      (smoothingPatchedProfile_contDiff δ hδ h) hG hR,
      smoothingFlatOriginal_partial hF hG hzero hfirst]
    split_ifs <;> ring
  have hi : |if i=1 then deriv (smoothingPatchedProfile δ hδ h) (p 1)-2*max (p 1) 0 else 0| ≤
      4*δ+3*δ^2*(B/h) := by
    split_ifs
    · exact hd
    · simp
      positivity
  rw [he]
  calc
    _ ≤ |(if i=1 then deriv (smoothingPatchedProfile δ hδ h) (p 1)-2*max (p 1) 0 else 0)*
        smoothingFlatRemainder (F-G) p| +
      |(smoothingPatchedProfile δ hδ h (p 1)-(max (p 1) 0)^2)*
        coordPartial i (smoothingFlatRemainder (F-G)) p| := abs_add_le _ _
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hi hR₀ (abs_nonneg _) (by positivity))
        (mul_le_mul hq (hR₁ i) (abs_nonneg _) (by positivity))

end
end TightVer401
