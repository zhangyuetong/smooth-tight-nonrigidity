import TightVer401.QuadraticRadialFillingBoundaryRadial
import TightVer401.QuadraticRadialFillingGradientWinding

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators

/-- The constructed positive position pairing is sufficient for actual
origin enclosure; the continuous direction lift is derived by the retained
positive-radial winding proof, not supplied as boundary data. -/
theorem quadraticRadialFilling_origin_inside_of_position_pairing
    {H : Coord → ℝ} {S : ℝ} {V : Set Coord} {Γ : ℂ ≃ₜ ℂ}
    (hS : 0 < S) (hV : IsOpen V) (hH : ContDiffOn ℝ ∞ H V)
    (hCircleV : quadraticRadialFillingRadiusLevel S ⊆ V)
    (hpos : ∀ θ : ℝ, 0 < planarGradient H (saddlePolarChart ![S,θ]) ⬝ᵥ
      saddlePolarChart ![S,θ])
    (hboundary : range (quadraticRadialFillingGradientComplexTrace H S) =
      Γ '' Metric.sphere (0:ℂ) 1) :
    (0:ℂ) ∈ Γ '' Metric.ball (0:ℂ) 1 := by
  apply quadraticRadialFillingGradient_origin_inside hS hV hH hCircleV _ hboundary
  intro θ
  have hp := hpos θ
  rw [quadraticRadialFilling_polar_radial_pairing] at hp
  exact (mul_pos_iff_of_pos_left hS).mp hp

end
end TightVer401
