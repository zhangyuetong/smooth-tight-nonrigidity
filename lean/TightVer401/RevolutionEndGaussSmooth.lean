import TightVer401.RevolutionEndNativeNormal
import TightVer401.SphereCharts

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

 def revolutionEndCircleGauss (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) : RoundSphere :=
  ⟨revolutionEndCircleNormal q p, by simpa using revolutionEndCircleNormal_norm q p⟩

 theorem revolutionEndCircleGauss_contMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (revolutionEndCircleGauss q) := by
  exact (revolutionEndCircleNormal_contMDiff hq).codRestrict_sphere
    (fun p => by simpa using revolutionEndCircleNormal_norm q p)

 theorem revolutionEndGauss_eq_full (q : ℝ → ℝ) (H : ℝ)
    (p : AddCircle (2 * Real.pi) × Ici H) :
    revolutionEndGauss q H p = revolutionEndCircleGauss q (p.1, p.2.val) := rfl

 theorem revolutionEndCircleGauss_injOn {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z) :
    InjOn (revolutionEndCircleGauss q) {p | H ≤ p.2} := by
  intro p hp s hs heq
  exact revolutionEndCircleNormal_injOn hq hc hp hs (congrArg Subtype.val heq)

 theorem revolutionEndCircleGauss_height_tendsto {q : ℝ → ℝ}
    (hslope : Tendsto (deriv q) atTop atTop) (θ : AddCircle (2 * Real.pi)) :
    Tendsto (fun z => (revolutionEndCircleGauss q (θ, z)).val 2) atTop (𝓝 1) := by
  change Tendsto (fun z => revolutionEndCircleNormal q (θ, z) 2) atTop (𝓝 1)
  simp_rw [revolutionEndCircleNormal_height]
  exact revolutionNormalHeight_tendsto hslope

end
end TightVer401
