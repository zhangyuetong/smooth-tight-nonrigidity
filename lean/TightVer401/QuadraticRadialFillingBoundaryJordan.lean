import TightVer401.QuadraticRadialFillingJordanImage
import TightVer401.QuadraticRadialFillingBoundaryConstruction

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Ordinary image-set Jordan data suffice for the constructed boundary data:
the once-traversed embedding is proved from the actual unit direction turn. -/
theorem exists_quadratic_radial_filling_boundary_data_of_jordan_image
    {R : ℝ} (hR : 0 < R) {F : Coord → ℝ} {U N : Set Coord}
    (hU : IsOpen U) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hF : ContDiffOn ℝ ∞ F U)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ))
    (hJ : Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘
      quadraticRadialFillingGradientComplexTrace F R)))
    (M₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (S B M : ℝ) (H : Coord → ℝ) (Γ : ℂ ≃ₜ ℂ),
      R < S ∧ 0 < B ∧ M₀ < M ∧ 0 < M ∧
      ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      quadraticRadialFillingClosedAnnulus (R/4) S ⊆ quadraticRadialFillingDomain R U ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      (∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F) ∧
      range (quadraticRadialFillingGradientComplexTrace H S) = Γ '' Metric.sphere (0:ℂ) 1 ∧
      InjOn (planarGradient H) (quadraticRadialFillingRadiusLevel S) ∧
      (0:ℂ) ∈ Γ '' Metric.ball (0:ℂ) 1 ∧
      Γ '' Metric.closedBall (0:ℂ) 1 ⊆ Metric.ball (0:ℂ) (M*(R-R/4)) ∧
      (∀ θ : ℝ, 0 < planarGradient H (saddlePolarChart ![S,θ]) ⬝ᵥ saddlePolarChart ![S,θ]) ∧
      (∀ θ : ℝ, planarRadius (planarGradient H (saddlePolarChart ![S,θ])) < B) ∧
      ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        B < planarRadius (planarGradient H x) := by
  have hCircle : {x : Coord | planarRadius x = R} ⊆ U := by
    intro x hx
    obtain ⟨θ,rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hx
    exact hCircleU θ
  have hinj := quadraticRadialFillingGradient_injOn_of_jordan_image hR hU hF hCircle
    (fun x hx => hnegF x (hCircle hx)) hRadial hJ
  exact exists_quadratic_radial_filling_boundary_data hR hU hN hCircleU hCircleN
    hF hnegF hRadial hTangential hinj M₀ hη

end
end TightVer401
