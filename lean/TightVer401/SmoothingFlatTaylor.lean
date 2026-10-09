import TightVer401.SmoothingScalarTaylor
import TightVer401.SmoothingParameterIntegral

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

def smoothingFlatRemainder (D : Coord → ℝ) (p : Coord) : ℝ :=
  ∫ u in 0..1, (1 - u) * planarHessian D (![p 0, u * p 1]) 1 1

theorem smoothing_normalSlice_hasDerivAt {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D) (s x : ℝ) :
    HasDerivAt (fun t : ℝ => D (![s, t])) (coordPartial 1 D (![s, x])) x := by
  have hγ : HasDerivAt (fun t : ℝ => (![s, t] : Coord)) (Pi.single 1 1 : Coord) x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun _ : ℝ => s) 0 x
      exact hasDerivAt_const x s
    · change HasDerivAt (fun t : ℝ => t) 1 x
      exact hasDerivAt_id x
  exact (hD.differentiable (by simp) (![s, x])).hasFDerivAt.comp_hasDerivAt x hγ

theorem smoothing_normalSlice_deriv {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D) (s x : ℝ) :
    deriv (fun t : ℝ => D (![s, t])) x = coordPartial 1 D (![s, x]) :=
  (smoothing_normalSlice_hasDerivAt hD s x).deriv

theorem smoothing_normalSlice_second {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D) (s x : ℝ) :
    deriv (deriv (fun t : ℝ => D (![s, t]))) x = planarHessian D (![s, x]) 1 1 := by
  have he : deriv (fun t : ℝ => D (![s, t])) = fun t : ℝ => coordPartial 1 D (![s, t]) := by
    funext t
    exact smoothing_normalSlice_deriv hD s t
  rw [he]
  exact smoothing_normalSlice_deriv (smoothing_partial_contDiff hD 1) s x

theorem smoothingFlatRemainder_contDiff {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (smoothingFlatRemainder D) := by
  unfold smoothingFlatRemainder
  apply smoothing_parameter_integral_contDiff (F := fun q : Coord × ℝ =>
    (1 - q.2) * planarHessian D (![q.1 0, q.2 * q.1 1]) 1 1)
  have hD₂ := smoothing_partial_contDiff (smoothing_partial_contDiff hD 1) 1
  have hmap : ContDiff ℝ ∞ (fun q : Coord × ℝ => (![q.1 0, q.2 * q.1 1] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  change ContDiff ℝ ∞ (fun q : Coord × ℝ => (1 - q.2) * coordPartial 1 (coordPartial 1 D)
    (![q.1 0, q.2 * q.1 1]))
  exact (contDiff_const.sub contDiff_snd).mul (hD₂.comp hmap)

/-- Matching values and normal first derivatives produce a constructed smooth
Taylor factor, rather than an assumed seam remainder. -/
theorem smoothing_flat_taylor_factor {D : Coord → ℝ} (hD : ContDiff ℝ ∞ D)
    (hzero : ∀ s : ℝ, D (![s, 0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 D (![s, 0]) = 0) (p : Coord) :
    D p = (p 1)^2 * smoothingFlatRemainder D p := by
  have hγ : ContDiff ℝ ∞ (fun t : ℝ => (![p 0, t] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id
  have hz : deriv (fun t : ℝ => D (![p 0, t])) 0 = 0 := by
    rw [smoothing_normalSlice_deriv hD, hfirst]
  have ht := smoothing_scalar_taylor_second (f := fun t : ℝ => D (![p 0, t]))
    (hD.comp hγ) (hzero (p 0)) hz (p 1)
  simp only [smoothing_normalSlice_second hD] at ht
  have hp : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  rw [hp] at ht
  exact ht

end
end TightVer401
