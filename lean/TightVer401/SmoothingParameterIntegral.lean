import OAI.Geometry.IsometricImmersion.Calculus.CoordinateDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib

namespace TightVer401
noncomputable section
open Set MeasureTheory ContinuousLinearMap OAI.SmoothLocal.Geometry
open scoped ContDiff Convolution

/-- Smooth dependence of an actual compact interval integral, proved by a
parameterized convolution with a cutoff in the integration variable. -/
theorem smoothing_parameter_integral_contDiff {F : Coord × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : Coord => ∫ u in 0..1, F (p, u)) := by
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := 2, rOut := 3, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let f : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)
  let g : Coord → ℝ → ℝ := fun p x => φ x * F (p, -x)
  have hfi : Integrable f :=
    (integrableOn_const (μ := volume) (s := Icc (0 : ℝ) 1) (C := (1 : ℝ))
      isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    change ContDiff ℝ ∞ (fun q : Coord × ℝ => φ q.2 * F (q.1, -q.2))
    exact (φ.contDiff.comp contDiff_snd).mul (hF.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hgs : ∀ p, ∀ x, p ∈ (univ : Set Coord) → x ∉ Metric.closedBall (0 : ℝ) 3 → g p x = 0 := by
    intro p x _ hx
    have hφ : φ x = 0 := φ.zero_of_le_dist (le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall] using hx)))
    simp only [g, hφ, zero_mul]
  have hconv : ContDiff ℝ ∞ (fun p : Coord => (f ⋆[mul ℝ ℝ, volume] g p) 0) := by
    apply contDiffOn_univ.mp
    exact contDiffOn_convolution_right_with_param_comp (mul ℝ ℝ) (v := fun _ : Coord => 0)
      contDiffOn_const isOpen_univ (isCompact_closedBall (0 : ℝ) 3) hgs hfi.locallyIntegrable
      (by
        change ContDiffOn ℝ ∞ (Function.uncurry g) (univ ×ˢ univ)
        exact hg.contDiffOn)
  have he (p : Coord) : (f ⋆[mul ℝ ℝ, volume] g p) 0 = ∫ u in 0..1, F (p, u) := by
    have hint : (fun u : ℝ => f u * g p (0 - u)) =
        (Icc (0 : ℝ) 1).indicator (fun u => F (p, u)) := by
      funext u
      by_cases hu : u ∈ Icc (0 : ℝ) 1
      · have hφ : φ (-u) = 1 := by
          apply φ.one_of_mem_closedBall
          change dist (-u) 0 ≤ (2 : ℝ)
          rw [Real.dist_eq, sub_zero, abs_neg, abs_of_nonneg hu.1]
          linarith [hu.2]
        simp only [f, g, indicator_of_mem hu, zero_sub, neg_neg, hφ, one_mul]
      · simp only [f, indicator_of_notMem hu, zero_mul]
    change (∫ u : ℝ, f u * g p (0 - u)) = _
    rw [hint, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le zero_le_one]
  rw [show (fun p : Coord => (f ⋆[mul ℝ ℝ, volume] g p) 0) =
      (fun p : Coord => ∫ u in 0..1, F (p, u)) from funext he] at hconv
  exact hconv

end
end TightVer401
