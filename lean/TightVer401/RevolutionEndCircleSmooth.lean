import TightVer401.RevolutionEndTopology
import TightVer401.PeriodCircleInstances

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 def revolutionCircleRadial (θ : AddCircle (2 * Real.pi)) : Ambient :=
  WithLp.toLp 2 ![Real.Angle.cos θ, Real.Angle.sin θ, 0]

 theorem revolutionCircleRadial_representative (θ : ℝ) :
    revolutionCircleRadial (periodProjection (2 * Real.pi) θ) = revolutionRadial θ := by
  ext i
  fin_cases i
  · change Real.Angle.cos (θ : Real.Angle) = Real.cos θ
    exact Real.Angle.cos_coe θ
  · change Real.Angle.sin (θ : Real.Angle) = Real.sin θ
    exact Real.Angle.sin_coe θ
  · rfl

 theorem revolutionCircleRadial_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) ∞ revolutionCircleRadial := by
  apply periodCircle_descend_smooth
  have heq : revolutionCircleRadial ∘ periodProjection (2 * Real.pi) = revolutionRadial :=
    funext revolutionCircleRadial_representative
  rw [heq]
  exact revolutionRadial_contDiff

 def revolutionEndCircleFull (q : ℝ → ℝ) (p : AddCircle (2 * Real.pi) × ℝ) : Ambient :=
  q p.2 • revolutionCircleRadial p.1 + p.2 • revolutionAxis

 theorem revolutionEndCircleFull_contMDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (revolutionEndCircleFull q) := by
  exact ((hq.contMDiff.comp contMDiff_snd).smul
    (revolutionCircleRadial_contMDiff.comp contMDiff_fst)).add
    (contMDiff_snd.smul contMDiff_const)

 theorem revolutionEndCircleFull_representative (q : ℝ → ℝ) (θ z : ℝ) :
    revolutionEndCircleFull q (periodProjection (2 * Real.pi) θ, z) =
      revolutionEnd q (![θ, z] : Coord) := by
  simp [revolutionEndCircleFull, revolutionCircleRadial_representative, revolutionEnd]

 theorem revolutionEndCircle_eq_full (q : ℝ → ℝ) (H : ℝ)
    (p : AddCircle (2 * Real.pi) × Ici H) :
    revolutionEndCircle q H p = revolutionEndCircleFull q (p.1, p.2.val) := by
  ext i
  fin_cases i <;> simp [revolutionEndCircle, revolutionEndCircleFull, revolutionCircleRadial, revolutionAxis]

end
end TightVer401


