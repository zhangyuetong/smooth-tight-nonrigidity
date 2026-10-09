import TightVer401.QuadraticRadialFilling
import TightVer401.QuadraticRadialFillingBoundaryGerms
import TightVer401.QuadraticFillerCartesianGradient

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators

/-- Transfer the generic filler owner's actual inner gradient circle through
the exact retained scalar germ of the constructed smoothed potential. -/
theorem quadraticRadialFilling_inner_gradient_circle {R : ℝ} (hR : 0 < R)
    (M : ℝ) (h b : ℝ → ℝ) {H : Coord → ℝ}
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R/2) (θ : ℝ) :
    planarGradient H (saddlePolarChart ![ρ,θ]) =
      quadraticFillerCartesianGradientCircle R M ρ h b θ := by
  have hradius : planarRadius (saddlePolarChart ![ρ,θ]) = ρ :=
    angularDescent_radius_polar (show (0:ℝ) < (![ρ,θ] : Coord) 0 from hρ)
  have hgH := quadraticRadialFilling_gradient_eq_of_germ
    (hInner (saddlePolarChart ![ρ,θ]) (by simpa only [hradius] using hρ)
      (by simpa only [hradius] using hρR))
  have hgA := quadraticFillerCartesian_inner_gradient hR M h b
    (p := saddlePolarChart ![ρ,θ]) (by simpa only [hradius] using hρR)
  rw [hgH, ← hgA]
  ext i
  fin_cases i <;> rfl

/-- The inner gradient of the smoothed filling can lie beyond any prescribed
finite radius, while the entire joined domain remains an actual saddle. -/
theorem exists_quadratic_radial_filling_large_gradient {R : ℝ} (hR : 0 < R)
    {F : Coord → ℝ} {U N : Set Coord} (hU : IsOpen U) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hF : ContDiffOn ℝ ∞ F U)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ))
    (M₀ B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (M : ℝ) (H : Coord → ℝ), M₀ < M ∧ 0 < M ∧
      ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        B < planarRadius (planarGradient H x) := by
  obtain ⟨M,H,hBound,hM,hH,hNeg,hExt,hInner,_hClose⟩ :=
    exists_quadratic_radial_filling hR hU hN hCircleU hCircleN hF hnegF
      hRadial hTangential (max M₀ (2*B/R)) hη
  have hM₀ : M₀ < M := (le_max_left _ _).trans_lt hBound
  have hMB : 2*B < M*R :=
    (div_lt_iff₀ hR).mp ((le_max_right _ _).trans_lt hBound)
  refine ⟨M,H,hM₀,hM,hH,hNeg,hExt,hInner,?_⟩
  intro x hx hxr
  rw [quadraticRadialFilling_gradient_eq_of_germ (hInner x hx hxr)]
  exact (show B < M*R/2 by linarith).trans_le
    (quadraticFillerCartesian_radial_gradient_radius_lower hR hM hx hxr.le)

end
end TightVer401
