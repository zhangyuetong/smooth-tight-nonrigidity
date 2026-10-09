import TightVer401.QuadraticRadialFillingBoundaryHomeomorph
import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.QuadraticRadialFillingLargeGradient

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Derive the boundary homeomorphism of the actual filled gradient from its
retained inner scalar germs, retained outer injectivity and separated radii.
The inner gradient formula is consumed from the generic filler proof. -/
theorem quadraticRadialFilling_exists_gradient_boundary_homeomorph
    {R M ρ S : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hρS : ρ < S)
    {H : Coord → ℝ} {V : Set Coord} (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hBoundaryV : quadraticRadialFillingBoundary ρ S ⊆ V)
    (hInner : ∀ x : Coord, 0 < planarRadius x → planarRadius x < R/2 →
      H =ᶠ[𝓝 x] dualRadialQuadraticPotential R M (-M*R^2/2))
    (hOuter : InjOn (planarGradient H) (quadraticRadialFillingRadiusLevel S))
    (hBound : ∀ x ∈ quadraticRadialFillingRadiusLevel S,
      planarRadius (planarGradient H x) < M*(R-ρ)) :
    ∃ Φ : quadraticRadialFillingBoundary ρ S ≃ₜ
        planarGradient H '' quadraticRadialFillingBoundary ρ S,
      ∀ x : quadraticRadialFillingBoundary ρ S, (Φ x : Coord) = planarGradient H x := by
  have hC : 0 < M*(R-ρ) := mul_pos hM (by linarith)
  have hG : ContinuousOn (planarGradient H) (quadraticRadialFillingBoundary ρ S) :=
    (planarGradient_contDiffOn hH hV).continuousOn.mono hBoundaryV
  have hFormula : ∀ x ∈ quadraticRadialFillingRadiusLevel ρ,
      planarGradient H x = (M*(R-ρ)/ρ) • x := by
    intro x hx
    obtain ⟨θ,rfl⟩ := quadraticRadialFilling_radiusLevel_exists_polar hρ hx
    let h := quadraticRadialFillingValueTrace H R
    let b := quadraticRadialFillingRadialTrace H R
    rw [quadraticRadialFilling_inner_gradient_circle hR M h b hInner hρ hρR,
      quadraticFillerCartesianGradientCircle_eq hR M h b hρ hρR]
    ext i
    fin_cases i <;> simp [saddlePolarChart]
    all_goals field_simp [hρ.ne'] <;> ring
  exact quadraticRadialFilling_exists_boundary_homeomorph hρ hρS hC hG hFormula hOuter hBound

end
end TightVer401
