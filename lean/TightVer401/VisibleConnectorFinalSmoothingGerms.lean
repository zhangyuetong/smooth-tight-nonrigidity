import TightVer401.VisibleConnectorFinalSmoothingConstruction

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- Open scalar equality retains the actual gradient and Hessian of the SAME
final H. This supplies terminal/incoming differential data after smoothing. -/
theorem visibleConnectorFinalSmoothing_open_equality_derivatives
    {H f : Coord → ℝ} {O : Set Coord} (hO : IsOpen O) (heq : EqOn H f O) :
    EqOn (planarGradient H) (planarGradient f) O ∧
      EqOn (planarHessian H) (planarHessian f) O := by
  have hgerm (x : Coord) (hx : x ∈ O) : H =ᶠ[𝓝 x] f := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact heq hy
  exact ⟨fun x hx => smoothing_planarGradient_germ (hgerm x hx),
    fun x hx => smoothing_planarHessian_germ (hgerm x hx)⟩

end
end TightVer401
