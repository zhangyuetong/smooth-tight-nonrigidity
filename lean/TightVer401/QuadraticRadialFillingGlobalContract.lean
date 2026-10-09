import TightVer401.QuadraticRadialFillingBoundaryJordan

/-! Precise ordinary-input specification of the pending full global filling.
No inhabitant, admission, assumed degree theorem or global construction is
asserted by this definition. Actual producer proof remains a separate task. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

def quadraticRadialFillingPuncturedDisk (S : ℝ) : Set Coord :=
  {x | 0 < planarRadius x ∧ planarRadius x < S}

def quadraticRadialFillingGlobalGradientTarget (Γ : ℂ ≃ₜ ℂ) (L : ℝ) : Set Coord :=
  seamComplexCoord '' (Metric.ball (0 : ℂ) L \ Γ '' Metric.closedBall (0 : ℂ) 1)

/-- Ordinary geometric data must construct the actual scalar filling and its
global gradient inverse. This proposition is a specification, not a theorem. -/
def QuadraticRadialFillingGlobalGradientClaim : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (F : Coord → ℝ) (U N : Set Coord),
    IsOpen U → IsOpen N →
    (∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U) →
    (∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N) →
    ContDiffOn ℝ ∞ F U →
    (∀ x ∈ U, (planarHessian F x).det < 0) →
    (∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ) →
    (∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ)) →
    Schoenflies.IsJordanCurve (range (jordanComplexCoordinates.symm ∘
      quadraticRadialFillingGradientComplexTrace F R)) →
    ∀ (M₀ η : ℝ), 0 < η →
    ∃ (S M : ℝ) (H : Coord → ℝ) (Γ : ℂ ≃ₜ ℂ)
      (e : OpenPartialHomeomorph Coord Coord),
      R < S ∧ M₀ < M ∧ 0 < M ∧
      ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      quadraticRadialFillingPuncturedDisk S ⊆ quadraticRadialFillingDomain R U ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      (∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F) ∧
      range (quadraticRadialFillingGradientComplexTrace H S) =
        Γ '' Metric.sphere (0 : ℂ) 1 ∧
      (0 : ℂ) ∈ Γ '' Metric.ball (0 : ℂ) 1 ∧
      Γ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) (M*R) ∧
      e.source = quadraticRadialFillingPuncturedDisk S ∧
      e.target = quadraticRadialFillingGlobalGradientTarget Γ (M*R) ∧
      (e : Coord → Coord) = planarGradient H ∧ ContDiffOn ℝ ∞ e.symm e.target

end
end TightVer401
