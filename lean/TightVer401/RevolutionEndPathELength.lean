import TightVer401.RevolutionEndLength
import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace TightVer401
noncomputable section
open Set Filter Manifold OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold ENNReal Bundle
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

 theorem revolution_ambientCurve_edist_le_pathELength {F : ℝ → Ambient} {A B : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc A B)) (hAB : A ≤ B) :
    edist (F A) (F B) ≤ pathELength 𝓘(ℝ, Ambient) F A B := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, Ambient))]
  exact riemannianEDist_le_pathELength hF.contMDiffOn rfl rfl hAB

 theorem revolution_ambientCurve_height_edist_le_pathELength {F : ℝ → Ambient} {A B : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc A B)) (hAB : A ≤ B) :
    edist (F A 2) (F B 2) ≤ pathELength 𝓘(ℝ, Ambient) F A B := by
  have hp : dist (F A 2) (F B 2) ≤ dist (F A) (F B) := by
    simpa only [dist_eq_norm, PiLp.sub_apply] using PiLp.norm_apply_le (F A - F B) 2
  have he : edist (F A 2) (F B 2) ≤ edist (F A) (F B) := by
    simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hp
  exact he.trans (revolution_ambientCurve_edist_le_pathELength hF hAB)

 theorem revolutionEndCurve_height_edist_le_pathELength {q : ℝ → ℝ} {c : ℝ → Coord}
    (hq : ContDiff ℝ ∞ q) {A B : ℝ} (hc : ContDiffOn ℝ 1 c (Icc A B)) (hAB : A ≤ B) :
    edist (c A 1) (c B 1) ≤ pathELength 𝓘(ℝ, Ambient) (revolutionEnd q ∘ c) A B := by
  have hF : ContDiffOn ℝ 1 (revolutionEnd q ∘ c) (Icc A B) :=
    ((revolutionEnd_contDiff hq).of_le (by simp)).comp_contDiffOn hc
  simpa only [Function.comp_apply, revolutionEnd_height] using
    revolution_ambientCurve_height_edist_le_pathELength hF hAB

 theorem revolutionEndCircleCurve_height_edist_le_pathELength {q : ℝ → ℝ}
    {c : ℝ → AddCircle (2 * Real.pi) × ℝ} (hq : ContDiff ℝ ∞ q) {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 1 c (Icc A B)) (hAB : A ≤ B) :
    edist (c A).2 (c B).2 ≤ pathELength 𝓘(ℝ, Ambient) (revolutionEndCircleFull q ∘ c) A B := by
  have hF : ContDiffOn ℝ 1 (revolutionEndCircleFull q ∘ c) (Icc A B) :=
    (((revolutionEndCircleFull_contMDiff hq).of_le (by simp)).comp_contMDiffOn hc).contDiffOn
  simpa only [Function.comp_apply, revolutionEndCircleFull_height] using
    revolution_ambientCurve_height_edist_le_pathELength hF hAB

end
end TightVer401

