import TightVer401.QuadraticFillerCartesianLegendre
import TightVer401.SeamCoordinateChain

/-! The closed actual target used only for retained dual boundary data. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry

def quadraticFillerCartesianLegendreBoundaryClosedAnnulus (R M : ℝ) : Set Coord :=
  {y | M * R / 2 ≤ planarRadius y ∧ planarRadius y ≤ M * R}

/-- A concrete smooth radial continuation collar; no saddle sign is imposed here. -/
def quadraticFillerCartesianLegendreBoundaryCollar (R M : ℝ) : Set Coord :=
  {y | M * R / 4 < planarRadius y ∧ planarRadius y < 5 * M * R / 4}

end
end TightVer401
