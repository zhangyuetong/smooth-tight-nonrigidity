import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strict actual derivative of full rank on a finite-dimensional domain
gives local injectivity, even when the target has larger dimension. -/
theorem exists_local_injOn_of_injective_strictFDeriv {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f f' x) (hi : Function.Injective f') :
    ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  obtain ⟨K, hK, hanti⟩ := f'.toLinearMap.injective_iff_antilipschitz.mp hi
  let c : ℝ≥0 := K⁻¹ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨U, hU, happrox⟩ := hf.approximates_deriv_on_nhds (Or.inr hc)
  refine ⟨U, hU, fun y hy z hz he => ?_⟩
  have herr := happrox y hy z hz
  have hlow := hanti.le_mul_dist y z
  simp only [dist_eq_norm] at hlow
  change ‖y - z‖ ≤ (K : ℝ) * ‖f' y - f' z‖ at hlow
  rw [← f'.map_sub] at hlow
  rw [he, sub_self, zero_sub, norm_neg] at herr
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hcoeff : (K : ℝ) * (c : ℝ) = 1 / 2 := by
    change (K : ℝ) * ((K : ℝ)⁻¹ / 2) = 1 / 2
    field_simp
  have hh := mul_le_mul_of_nonneg_left herr (show (0 : ℝ) ≤ K from K.coe_nonneg)
  rw [← mul_assoc, hcoeff] at hh
  have hnorm : ‖y - z‖ = 0 := by nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end
end TightVer401
