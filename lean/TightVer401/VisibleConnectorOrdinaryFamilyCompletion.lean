import TightVer401.VisibleConnectorOrdinaryFamilyFromIncomingAssembly
import TightVer401.VisibleConnectorWitnessAssemblyCompletion

/-! The actual incoming-data producer supplies the universal ordinary family,
and hence the canonical connector and original radial completion caller. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

/-- Every actual incoming datum supplies its canonical connector for every
positive angle bound, using the concrete ordinary-data producer. -/
theorem visibleConnectorOrdinaryFamily_construction_statement
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) :
    VisibleConnectorConstructionStatement D :=
  visibleConnectorWitnessAssembly_statement D
    (fun etaMax hetaMax => visibleConnectorOrdinaryFamily_nonempty_from_incoming D hetaMax)

/-- The universal concrete ordinary family discharges the connector input of
the existing completion caller. -/
theorem visibleConnectorOrdinaryFamily_dual_radial_completion :
    DualRadialCompletionClaim := by
  apply exists_dual_radial_support_completion_of_ordinary_connector_data
  intro Gin Uin R D etaMax hetaMax
  exact visibleConnectorOrdinaryFamily_nonempty_from_incoming D hetaMax

end
end TightVer401
