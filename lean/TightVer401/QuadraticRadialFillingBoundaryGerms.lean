import TightVer401.QuadraticRadialFillingGlue

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology

/-- Exact scalar outer germs retain the actual Cartesian first derivatives
as germs, not just their boundary values. -/
theorem quadraticRadialFilling_partial_germ {H F : Coord → ℝ} {x : Coord}
    (h : H =ᶠ[𝓝 x] F) (i : Fin 2) :
    coordPartial i H =ᶠ[𝓝 x] coordPartial i F := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun D => D (Pi.single i (1 : ℝ))) hy

theorem quadraticRadialFilling_gradient_germ {H F : Coord → ℝ} {x : Coord}
    (h : H =ᶠ[𝓝 x] F) : planarGradient H =ᶠ[𝓝 x] planarGradient F := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  ext i
  exact congrArg (fun D => D (Pi.single i (1 : ℝ))) hy

theorem quadraticRadialFilling_gradient_eq_of_germ {H F : Coord → ℝ} {x : Coord}
    (h : H =ᶠ[𝓝 x] F) : planarGradient H x = planarGradient F x :=
  (quadraticRadialFilling_gradient_germ h).eq_of_nhds

theorem quadraticRadialFilling_hessian_eq_of_germ {H F : Coord → ℝ} {x : Coord}
    (h : H =ᶠ[𝓝 x] F) : planarHessian H x = planarHessian F x := by
  ext i j
  change fderiv ℝ (coordPartial j H) x (Pi.single i 1) =
    fderiv ℝ (coordPartial j F) x (Pi.single i 1)
  rw [(quadraticRadialFilling_partial_germ h j).fderiv_eq]

/-- Retained exterior potential germs give the exact actual outer gradient
curve required by a later annular degree application. -/
theorem quadraticRadialFilling_outer_gradient_trace
    {H F : Coord → ℝ} {U N : Set Coord} {R S : ℝ}
    (hS : R < S)
    (hOuter : ∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![S,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![S,θ] ∉ N)
    (hposS : 0 < S) :
    (fun θ : ℝ => planarGradient H (saddlePolarChart ![S,θ])) =
      fun θ : ℝ => planarGradient F (saddlePolarChart ![S,θ]) := by
  funext θ
  apply quadraticRadialFilling_gradient_eq_of_germ
  apply hOuter _ (hCircleU θ) _ (hCircleN θ)
  simpa only [angularDescent_radius_polar (show (0:ℝ) < (![S,θ] : Coord) 0 from hposS),
    Matrix.cons_val_zero]
    using hS

end
end TightVer401
