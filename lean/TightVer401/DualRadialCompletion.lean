import TightVer401.DualRadialCompletionProducerApplication
import TightVer401.DualRadialCompletionCircularDegreeAdapter
import TightVer401.AnnularDegreeGradient

/-! The actual degree and retained-filling producers discharge those two
external calls. The visible connector remains an explicit novel construction
obligation. This is not an unconditional completion theorem. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Use the actual degree and SAME-inverse trimmed filling proofs in the
ordinary completion caller. Only the visible-connector producer remains
explicit; no completed potential or gradient-annulus package is assumed. -/
theorem exists_dual_radial_support_completion_of_visible_connector
    (hConnector : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R), VisibleConnectorConstructionStatement D) :
    DualRadialCompletionClaim :=
  dualRadialCompletionClaim_of_producers hConnector
    exists_quadratic_radial_filling_global_gradient_with_retained_trace
    (dualRadialCompletionCircularDegree_of_gradientClaim
      annular_degree_planarGradient_global_diffeomorphism)

end
end TightVer401
