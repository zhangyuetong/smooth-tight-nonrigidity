import TightVer401.QuadraticRadialFillingGlobalContract
import TightVer401.QuadraticRadialFillingRetainedOverlap

/-! The same actual filling and actual inverse retain a full ordinary open
collar strictly inside the inverse source. This stronger producer type has
no asserted inhabitant; its existence proof is a separate construction. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Ordinary incoming data must produce the SAME actual scalar potential
and global gradient inverse with a retained open inverse-source overlap. -/
def QuadraticRadialFillingGlobalGradientOverlapClaim : Prop :=
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
      ∃ S0 δ : ℝ, R < S0 ∧ S0 < S ∧ 0 < δ ∧
        IsOpen (quadraticRadialFillingRetainedCollar S0 δ) ∧
        quadraticRadialFillingRetainedCollar S0 δ ⊆
          (U ∩ quadraticRadialFillingDomain R U) ∩ e.source ∧
        EqOn H F (quadraticRadialFillingRetainedCollar S0 δ) ∧
        (∀ x ∈ quadraticRadialFillingRetainedCollar S0 δ, H =ᶠ[𝓝 x] F) ∧
        EqOn (e : Coord → Coord) (planarGradient F) (quadraticRadialFillingRetainedCollar S0 δ)

/-- Ordinary existential projection recovers the original exact producer
interface from the stronger same-object retained-overlap interface. -/
theorem quadraticRadialFillingGlobalGradientClaim_of_overlap
    (h : QuadraticRadialFillingGlobalGradientOverlapClaim) :
    QuadraticRadialFillingGlobalGradientClaim := by
  intro R hR F U N hU hN hCircleU hCircleN hF hNegF hRadial hTangential hJordan M₀ η hη
  obtain ⟨S,M,H,Γ,e,hRS,hM₀,hM,hH,hNeg,hDisk,hExterior,hInner,hOuter,
    hTrace,hOrigin,hNested,hSource,hTarget,he,hi,_hOverlap⟩ :=
    h R hR F U N hU hN hCircleU hCircleN hF hNegF hRadial hTangential hJordan M₀ η hη
  exact ⟨S,M,H,Γ,e,hRS,hM₀,hM,hH,hNeg,hDisk,hExterior,hInner,hOuter,
    hTrace,hOrigin,hNested,hSource,hTarget,he,hi⟩

end
end TightVer401
