import TightVer401.FermiSupportLocalSeam

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set
open scoped ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def fermiCoordinateC2Size (J : Coord → ℝ) (p : Coord) : ℝ :=
  ‖J p‖ + (∑ i, ‖coordPartial i J p‖) +
    ∑ i, ∑ j, ‖coordPartial i (coordPartial j J) p‖

theorem fermiCoordinateC2Size_nonneg (J : Coord → ℝ) (p : Coord) :
    0 ≤ fermiCoordinateC2Size J p := by
  unfold fermiCoordinateC2Size
  positivity

theorem fermiCoordinateC2Size_continuous {J : Coord → ℝ} (hJ : ContDiff ℝ ∞ J) :
    Continuous (fermiCoordinateC2Size J) := by
  apply (hJ.continuous.norm.add ?_).add ?_
  · exact continuous_finset_sum _ fun i _ => (fermiCoordinatePartial_contDiff hJ i).continuous.norm
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (fermiCoordinatePartial_contDiff (fermiCoordinatePartial_contDiff hJ j) i).continuous.norm

theorem fermiCoordinatePartial_const_mul {J : Coord → ℝ} {p : Coord}
    (hJ : DifferentiableAt ℝ J p) (ε : ℝ) (i : Fin 2) :
    coordPartial i (fun q => ε * J q) p = ε * coordPartial i J p := by
  rw [coordPartial_scalar_mul (f := fun _ => ε) (g := J) (differentiableAt_const ε) hJ,
    coordPartial_scalar_const]
  ring

theorem fermiCoordinateC2Size_const_mul {J : Coord → ℝ} (hJ : ContDiff ℝ ∞ J)
    (ε : ℝ) (p : Coord) :
    fermiCoordinateC2Size (fun q => ε * J q) p = ‖ε‖ * fermiCoordinateC2Size J p := by
  have h1 (i : Fin 2) : coordPartial i (fun q => ε * J q) =
      (fun q => ε * coordPartial i J q) :=
    funext fun q => fermiCoordinatePartial_const_mul (hJ.differentiable (by simp) q) ε i
  have h2 (i j : Fin 2) : coordPartial i (coordPartial j (fun q => ε * J q)) p =
      ε * coordPartial i (coordPartial j J) p := by
    rw [h1 j]
    exact fermiCoordinatePartial_const_mul
      ((fermiCoordinatePartial_contDiff hJ j).differentiable (by simp) p) ε i
  unfold fermiCoordinateC2Size
  simp only [Fin.sum_univ_two]
  rw [h2 0 0, h2 0 1, h2 1 0, h2 1 1, h1 0, h1 1]
  simp only [norm_mul]
  ring

theorem exists_fermiPerturbation_C2_threshold {J : Coord → ℝ} (hJ : ContDiff ℝ ∞ J)
    {K : Set Coord} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ e > 0, ∀ ε : ℝ, |ε| < e → ∀ p ∈ K,
      fermiCoordinateC2Size (fun q => ε * J q) p < η := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (fermiCoordinateC2Size_continuous hJ).continuousOn
  let D := max C 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨η / D, div_pos hη hD, ?_⟩
  intro ε hε p hp
  have hsize : fermiCoordinateC2Size J p ≤ D := by
    have hc := hC p hp
    rw [Real.norm_of_nonneg (fermiCoordinateC2Size_nonneg J p)] at hc
    exact hc.trans (by dsimp [D]; linarith [le_max_left C 0])
  rw [fermiCoordinateC2Size_const_mul hJ ε p, Real.norm_eq_abs]
  calc
    |ε| * fermiCoordinateC2Size J p ≤ |ε| * D := mul_le_mul_of_nonneg_left hsize (abs_nonneg ε)
    _ < η := (lt_div_iff₀ hD).mp hε

end
end TightVer401
