import TightVer401.BandProfileSmooth

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped Manifold
set_option backward.isDefEq.respectTransparency false

def bandDifferential {A : Type*} [TopologicalSpace A] [ChartedSpace ℝ A] {b : ℝ}
    (f : A × Set.Ioo (0 : ℝ) b → Ambient) (p : A × Set.Ioo (0 : ℝ) b) :
    (ℝ × ℝ) →L[ℝ] Ambient := mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) f p

end
end TightVer401
