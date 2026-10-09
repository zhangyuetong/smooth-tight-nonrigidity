import TightVer401.QuadraticRadialFillingOuterBoundary
import TightVer401.QuadraticRadialFillingBoundaryBounds
import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.QuadraticRadialFillingGradientJordan
import TightVer401.QuadraticRadialFillingLargeGradient
import TightVer401.QuadraticRadialFillingBoundaryOrigin
import TightVer401.QuadraticRadialFillingGradientNesting

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators

/-- Construct the actual annular application data. Boundary injectivity is
ordinary incoming geometry; the collar, outer radius, gradient bound, large
coefficient, smoothing and target Jordan filling are all derived. -/
theorem exists_quadratic_radial_filling_boundary_data {R : ℝ} (hR : 0 < R)
    {F : Coord → ℝ} {U N : Set Coord} (hU : IsOpen U) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hF : ContDiffOn ℝ ∞ F U)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ))
    (hinj : InjOn (planarGradient F) (quadraticRadialFillingRadiusLevel R))
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
  have hCircle : quadraticRadialFillingRadiusLevel R ⊆ U := by
    intro x hx
    obtain ⟨θ,rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hx
    exact hCircleU θ
  obtain ⟨Wi,hWi,hKi,hWiU,hInj⟩ :=
    quadraticRadialFillingGradient_exists_injective_neighborhood hR hU hF hCircle
      (fun x hx => hnegF x (hCircle hx)) hinj
  obtain ⟨Wp,hWp,_hWpU,hKp,hPositive⟩ :=
    quadraticRadialFilling_positive_radial_neighborhood hF hU hR hCircle hRadial
  let W := Wi ∩ Wp
  have hW : IsOpen W := hWi.inter hWp
  have hKW : quadraticRadialFillingRadiusLevel R ⊆ W := fun x hx => ⟨hKi hx,hKp hx⟩
  have hWU : W ⊆ U := fun x hx => hWiU hx.1
  have hInjW : InjOn (planarGradient F) W := hInj.mono inter_subset_left
  obtain ⟨δ,hδ,_hδR,hCollar⟩ := quadraticRadialFilling_exists_radial_collar hR hW hKW
  let S := R + δ/2
  have hS : R < S := by dsimp [S]; linarith
  have hSpos : 0 < S := lt_trans hR hS
  have hOuterW : quadraticRadialFillingRadiusLevel S ⊆ W := by
    intro x hx
    apply hCollar x
    change planarRadius x = S at hx
    rw [hx]
    dsimp [S]
    rw [show R + δ/2 - R = δ/2 by ring, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hOuterU : quadraticRadialFillingRadiusLevel S ⊆ U := hOuterW.trans hWU
  have hOuterPolarU (θ : ℝ) : saddlePolarChart ![S,θ] ∈ U :=
    hOuterU (angularDescent_radius_polar (show (0:ℝ) < (![S,θ] : Coord) 0 from hSpos))
  have hShell : quadraticRadialFillingClosedAnnulus R S ⊆ U := by
    intro x hx
    apply hWU
    apply hCollar x
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp [S] at hx
    linarith [hx.2]
  obtain ⟨B,hB,hBound⟩ := quadraticRadialFilling_incoming_gradient_boundary_bound hF hU hOuterU
  obtain ⟨Γ,hΓ⟩ := quadraticRadialFillingGradientComplexTrace_exists_filling
    hSpos hU hF hOuterU hOuterW hInjW
  obtain ⟨M,H,hMbound,hM,hH,hNeg,hExt,hInner,hOuter,hGrad⟩ :=
    exists_quadratic_radial_filling_retaining_outer_circle hR hS hU hN hCircleU hCircleN
      hOuterPolarU hF hnegF hRadial hTangential (max M₀ (2*B/R)) hη
  have hM₀ : M₀ < M := (le_max_left _ _).trans_lt hMbound
  have hMB : 2*B < M*R := (div_lt_iff₀ hR).mp ((le_max_right _ _).trans_lt hMbound)
  have hBoundary : range (quadraticRadialFillingGradientComplexTrace H S) =
      Γ '' Metric.sphere (0:ℂ) 1 := by
    have he : quadraticRadialFillingGradientComplexTrace H S =
        quadraticRadialFillingGradientComplexTrace F S :=
      funext fun θ => congrArg angularDescentComplex (hGrad θ)
    rw [he]
    exact hΓ
  have hPositiveH (θ : ℝ) : 0 < planarGradient H (saddlePolarChart ![S,θ]) ⬝ᵥ
      saddlePolarChart ![S,θ] := by
    rw [hGrad θ]
    exact hPositive _ (hOuterW
      (angularDescent_radius_polar (show (0:ℝ) < (![S,θ] : Coord) 0 from hSpos))).2
  have hBoundH (θ : ℝ) : planarRadius (planarGradient H (saddlePolarChart ![S,θ])) < B := by
    rw [hGrad θ]
    exact hBound _ (angularDescent_radius_polar
      (show (0:ℝ) < (![S,θ] : Coord) 0 from hSpos))
  have hEqOuter {x : Coord} (hx : x ∈ quadraticRadialFillingRadiusLevel S) :
      planarGradient H x = planarGradient F x := by
    obtain ⟨θ,rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hSpos hx
    exact hGrad θ
  have hD : IsOpen (quadraticRadialFillingDomain R U) :=
    (isOpen_lt continuous_const quadraticRadialFillingRadius_continuous).inter
      ((isOpen_lt quadraticRadialFillingRadius_continuous continuous_const).union hU)
  have hCircleD : quadraticRadialFillingRadiusLevel S ⊆ quadraticRadialFillingDomain R U :=
    fun x hx => ⟨by
      change 0 < planarRadius x
      change planarRadius x = S at hx
      rw [hx]
      exact hSpos, Or.inr (hOuterU hx)⟩
  have hC : 0 < M*(R-R/4) := mul_pos hM (by linarith)
  have hBC : B < M*(R-R/4) := by nlinarith [mul_pos hM hR]
  refine ⟨S,B,M,H,Γ,hS,hB,hM₀,hM,hH,hNeg,
    quadraticRadialFilling_closedAnnulus_subset_domain (by linarith) hShell,
    hExt,hInner,hOuter,hBoundary,?_,
    quadraticRadialFilling_origin_inside_of_position_pairing hSpos hD hH hCircleD
      hPositiveH hBoundary,?_,hPositiveH,hBoundH,?_⟩
  · intro x hx y hy he
    apply hInjW (hOuterW hx) (hOuterW hy)
    rw [← hEqOuter hx, ← hEqOuter hy]
    exact he
  · rw [← quadraticRadialFillingRoundFilling_ball _ hC]
    exact quadraticRadialFillingGradient_closedDisk_nested_round hC hBoundary hBoundH hBC
  · intro x hx hxr
    rw [quadraticRadialFilling_gradient_eq_of_germ (hInner x hx hxr)]
    exact (show B < M*R/2 by linarith).trans_le
      (quadraticFillerCartesian_radial_gradient_radius_lower hR hM hx hxr.le)

end
end TightVer401
