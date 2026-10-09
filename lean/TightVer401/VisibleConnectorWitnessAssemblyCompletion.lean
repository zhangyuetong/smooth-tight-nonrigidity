import TightVer401.VisibleConnectorWitnessAssembly
import TightVer401.DualRadialCompletion

/-! The original completion caller after canonical witness assembly. The
remaining assumption is an ordinary final scalar/germ/boundary producer,
not an annular inverse package or completed connector witness. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Feed the canonical construction statement to the existing original
completion caller. Ordinary final DESC data remain the explicit obligation. -/
theorem exists_dual_radial_support_completion_of_ordinary_connector_data
    (hOrdinary : ∀ (Gin : Coord → ℝ) (Uin : Set Coord) (R : ℝ)
      (D : VisibleConnectorIncomingData Gin Uin 1 R),
      ∀ etaMax : ℝ, 0 < etaMax →
        Nonempty (VisibleConnectorWitnessAssemblyOrdinaryData D etaMax)) :
    DualRadialCompletionClaim :=
  exists_dual_radial_support_completion_of_visible_connector
    (fun Gin Uin R D => visibleConnectorWitnessAssembly_statement D (hOrdinary Gin Uin R D))

end
end TightVer401
