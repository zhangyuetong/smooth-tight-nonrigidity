import TightVer401.QuadraticFillerCartesianGradientAnnulus
import TightVer401.QuadraticFillerCartesianLegendreRadial
import TightVer401.PlanarLegendre

/-! The local Legendre potential uses the constructed actual gradient inverse. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

def quadraticFillerCartesianLegendrePotential {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (h b : ℝ → ℝ) : Coord → ℝ :=
  planarLegendre (quadraticFillerCartesianPotential R M h b)
    (quadraticFillerCartesianGradientEquiv hR hM h b)

end
end TightVer401
