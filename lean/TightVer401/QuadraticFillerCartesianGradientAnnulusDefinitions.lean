import TightVer401.QuadraticFillerCartesianGradient

/-! Explicit source, target and radial inverse for the retained inner gradient. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def quadraticFillerCartesianGradientInner (R : ℝ) : Set Coord :=
  {p | 0 < planarRadius p ∧ planarRadius p < R / 2}

def quadraticFillerCartesianGradientAnnulus (R M : ℝ) : Set Coord :=
  {y | M * R / 2 < planarRadius y ∧ planarRadius y < M * R}

def quadraticFillerCartesianGradientRadialMap (R M : ℝ) (p : Coord) : Coord :=
  (M * (R - planarRadius p) / planarRadius p) • p

def quadraticFillerCartesianGradientInverse (R M : ℝ) (y : Coord) : Coord :=
  ((R - planarRadius y / M) / planarRadius y) • y

end
end TightVer401
