import TightVer401.QuadraticRadialFillingGlobalInverse
import TightVer401.QuadraticRadialFillingRetainedTrace

/-! The full ordinary filling producer with its SAME retained inverse-source
collar and the actual distinct retained Jordan boundary. The original filling
Gamma remains the hole of the returned actual inverse. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Output type of the actual ordinary filling with its own retained trace.
All earlier scalar, inverse, boundary and germ outputs are preserved. -/
def QuadraticRadialFillingGlobalGradientTrimmedClaim : Prop :=
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
      (e : Coord → Coord) = planarGradient H ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∃ (S0 δ : ℝ) (Γ0 : ℂ ≃ₜ ℂ), R < S0 ∧ S0 < S ∧ 0 < δ ∧
        IsOpen (quadraticRadialFillingRetainedCollar S0 δ) ∧
        quadraticRadialFillingRetainedCollar S0 δ ⊆
          (U ∩ quadraticRadialFillingDomain R U) ∩ e.source ∧
        EqOn H F (quadraticRadialFillingRetainedCollar S0 δ) ∧
        (∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F) ∧
        EqOn (e : Coord → Coord) (planarGradient F) (quadraticRadialFillingRetainedCollar S0 δ) ∧
        range (quadraticRadialFillingGradientComplexTrace H S0) =
          Γ0 '' Metric.sphere (0 : ℂ) 1 ∧
        Γ '' Metric.closedBall (0 : ℂ) 1 ⊆ Γ0 '' Metric.ball (0 : ℂ) 1 ∧
        Γ0 '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) (M*R) ∧
        (0 : ℂ) ∈ Γ0 '' Metric.ball (0 : ℂ) 1

/-- The actual ordinary full filling and actual same-inverse retained-trace
construction produce the stronger output. No producer is an input premise. -/
theorem exists_quadratic_radial_filling_global_gradient_with_retained_trace :
    QuadraticRadialFillingGlobalGradientTrimmedClaim := by
  intro R hR F U N hU hN hCircleU hCircleN hF hNegF hRadial hTangential hJordan M₀ η hη
  obtain ⟨S,M,H,Γ,e,hRS,hM₀,hM,hH,hNeg,hDisk,hExterior,hInner,hOuter,
    hTrace,hOrigin,hNested,hSource,hTarget,he,hi,hOverlap⟩ :=
    exists_quadratic_radial_filling_global_gradient_with_overlap
      R hR F U N hU hN hCircleU hCircleN hF hNegF hRadial hTangential hJordan M₀ η hη
  obtain ⟨S0,δ,hRS0,hS0S,hδ,hCollarOpen,hCollarSub,hScalar,hGerms,hGradient⟩ := hOverlap
  have hDomain : IsOpen (quadraticRadialFillingDomain R U) :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
      ((isOpen_lt quadraticRadialFillingRadius_continuous continuous_const).union hU)
  obtain ⟨Γ0,hTrace0,hOriginalNested,hNewBound,hNewOrigin⟩ :=
    quadraticRadialFillingRetainedTrace_exists_filling_with_origin
      Γ (hR.trans hRS0) hS0S (mul_pos hM hR) hDomain hH hDisk hSource hTarget he hOrigin
  exact ⟨S,M,H,Γ,e,hRS,hM₀,hM,hH,hNeg,hDisk,hExterior,hInner,hOuter,
    hTrace,hOrigin,hNested,hSource,hTarget,he,hi,
    S0,δ,Γ0,hRS0,hS0S,hδ,hCollarOpen,hCollarSub,hScalar,hGerms,hGradient,
    hTrace0,hOriginalNested,hNewBound,hNewOrigin⟩

end
end TightVer401
