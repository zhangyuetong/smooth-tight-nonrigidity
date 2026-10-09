import TightVer401.ExitPositiveGraphChoice
import TightVer401.FermiScaleCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiGraph_actual_speed_sq {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hv : ContDiff ℝ ∞ v)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (δ r : ℝ) :
    inner ℝ (deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r)
      (deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r) =
      (fermiNormalScale (normalLoopCurvature ζ) (exitGraphCurve v δ r))^2 +
        (δ * deriv v r)^2 := by
  have hd := ((fermiNormalMap_contDiff hζ).differentiable (by simp)
    (exitGraphCurve v δ r)).hasFDerivAt.comp_hasDerivAt r (exitGraphCurve_hasDerivAt hv δ r)
  rw [hd.deriv]
  have he := inducedMetric_bilinear (fermiNormalMap ζ) (exitGraphCurve v δ r)
    (![1, δ * deriv v r] : Coord) (![1, δ * deriv v r] : Coord)
  rw [fermiNormalMap_metric hζ hunit hspeed] at he
  simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two] using he

theorem fermiGraph_deriv_ne_zero_of_scale {ζ : ℝ → Ambient} {v : ℝ → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hv : ContDiff ℝ ∞ v)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) {δ r : ℝ}
    (hscale : 0 < fermiNormalScale (normalLoopCurvature ζ) (exitGraphCurve v δ r)) :
    deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r ≠ 0 := by
  intro hz
  have he := fermiGraph_actual_speed_sq hζ hv hunit hspeed δ r
  rw [hz, inner_zero_left] at he
  have hp := sq_pos_of_pos hscale
  nlinarith [sq_nonneg (δ * deriv v r)]

theorem fermiGraph_exists_regular_radius {ζ : ℝ → Ambient} {v : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ P)
    (hv : ContDiff ℝ ∞ v) (hvL : Function.Periodic v P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) :
    ∃ ε > 0, ∀ δ : ℝ, |δ| < ε → ∀ r,
      0 < fermiNormalScale (normalLoopCurvature ζ) (exitGraphCurve v δ r) ∧
      deriv (fermiNormalMap ζ ∘ exitGraphCurve v δ) r ≠ 0 := by
  let U := (fermiNormalScale (normalLoopCurvature ζ)) ⁻¹' Ioi 0
  have hs := fermiNormalScale_contDiff (normalLoop_actual_smooth hζ).2
  have hU : IsOpen U := isOpen_Ioi.preimage hs.continuous
  have hc : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ U := by
    intro r hr
    change 0 < fermiNormalScale (normalLoopCurvature ζ) ![r, 0]
    simp [fermiNormalScale]
  obtain ⟨ε, hε, he⟩ := exitGraphCurve_uniform_domain hv hU hc
  refine ⟨ε, hε, fun δ hδ r => ?_⟩
  have hp : Function.Periodic
      (fun r => fermiNormalScale (normalLoopCurvature ζ) (exitGraphCurve v δ r)) P := by
    intro r
    simp only [fermiNormalScale, exitGraphCurve, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, hvL r, (normalLoop_actual_periodic hζ hζL).2 r]
  have hpos := exitGraph_periodic_positive_of_period hP hp
    (fun s hs => he s hs δ hδ.le) r
  exact ⟨hpos, fermiGraph_deriv_ne_zero_of_scale hζ hv hunit hspeed hpos⟩

end
end TightVer401
