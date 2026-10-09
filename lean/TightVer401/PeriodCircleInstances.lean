import TightVer401.PeriodCircle

namespace TightVer401
noncomputable section
open scoped Manifold ContDiff

instance periodCircle_chartedSpace (L : ℝ) [Fact (0 < L)] : ChartedSpace ℝ (AddCircle L) :=
  periodCircleChartedSpace L

instance periodCircle_manifold (L : ℝ) [Fact (0 < L)] :
    IsManifold 𝓘(ℝ, ℝ) ∞ (AddCircle L) := periodCircle_isManifold L

end
end TightVer401
