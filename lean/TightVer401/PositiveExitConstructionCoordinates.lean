import TightVer401.GnomonicCoordinates
import TightVer401.FermiNormalGeometry

/-! Shared actual Cartesian/Fermi coordinate definitions. The names are
retained from the ordinary output contract; no construction result is
specified or assumed in this dependency. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Matrix

def positiveExitJacobian (P : Coord → Coord) (q : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ P q (Pi.single j 1 : Coord) i

def positiveExitFermiSource (ζ : ℝ → Ambient) (q : Coord) : Coord :=
  gnomonicInverse (fermiNormalMap ζ q)

end
end TightVer401
