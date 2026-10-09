import TightVer401.QuadraticRadialFilling
import TightVer401.QuadraticRadialFillingBoundaryGerms

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators

/-- Shrink the chosen smoothing neighborhood so an actual exterior circle
retains the incoming potential's exact scalar germs and Cartesian gradient. -/
theorem exists_quadratic_radial_filling_retaining_outer_circle
    {R S : ℝ} (hR : 0 < R) (hS : R < S)
    {F : Coord → ℝ} {U N : Set Coord} (hU : IsOpen U) (hN : IsOpen N)
    (hCircleU : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U)
    (hCircleN : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ N)
    (hOuterU : ∀ θ : ℝ, saddlePolarChart ![S,θ] ∈ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hnegF : ∀ x ∈ U, (planarHessian F x).det < 0)
    (hRadial : ∀ θ : ℝ, 0 < planarGradient F (saddlePolarChart ![R,θ]) ⬝ᵥ
      quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R,θ]) *ᵥ quadraticRadialFillingTangentialUnit θ))
    (M₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ (M : ℝ) (H : Coord → ℝ), M₀ < M ∧ 0 < M ∧
      ContDiffOn ℝ ∞ H (quadraticRadialFillingDomain R U) ∧
      (∀ x ∈ quadraticRadialFillingDomain R U, (planarHessian H x).det < 0) ∧
      (∀ x ∈ U, R < planarRadius x → x ∉ N → H =ᶠ[𝓝 x] F) ∧
      (∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
        H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2)) ∧
      (∀ θ : ℝ, H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F) ∧
      ∀ θ : ℝ, planarGradient H (saddlePolarChart ![S,θ]) =
        planarGradient F (saddlePolarChart ![S,θ]) := by
  let N' : Set Coord := N ∩ {x | planarRadius x < S}
  have hN' : IsOpen N' := hN.inter
    (isOpen_lt quadraticRadialFillingRadius_continuous continuous_const)
  have hCircleN' (θ : ℝ) : saddlePolarChart ![R,θ] ∈ N' := by
    refine ⟨hCircleN θ, ?_⟩
    change planarRadius (saddlePolarChart ![R,θ]) < S
    rw [angularDescent_radius_polar (show (0:ℝ) < (![R,θ] : Coord) 0 from hR)]
    exact hS
  obtain ⟨M,H,hM₀,hM,hH,hNeg,hExt,hInner,_hClose⟩ :=
    exists_quadratic_radial_filling hR hU hN' hCircleU hCircleN' hF hnegF
      hRadial hTangential M₀ hη
  have hOuter (θ : ℝ) : H =ᶠ[𝓝 (saddlePolarChart ![S,θ])] F := by
    have hradius : planarRadius (saddlePolarChart ![S,θ]) = S :=
      angularDescent_radius_polar (show (0:ℝ) < (![S,θ] : Coord) 0 from lt_trans hR hS)
    apply hExt _ (hOuterU θ) (by simpa only [hradius] using hS)
    intro hx
    have hxS : planarRadius (saddlePolarChart ![S,θ]) < S := hx.2
    rw [hradius] at hxS
    exact lt_irrefl S hxS
  exact ⟨M,H,hM₀,hM,hH,hNeg,
    (fun x hx hr hn => hExt x hx hr (fun h => hn h.1)),hInner,hOuter,
    fun θ => quadraticRadialFilling_gradient_eq_of_germ (hOuter θ)⟩

end
end TightVer401
