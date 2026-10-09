import TightVer401.RevolutionEndBoundaryCharts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace TightVer401
noncomputable section
open Set Bundle OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEndBoundaryCoordinate_contMDiff (H : ℝ) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (revolutionEndBoundaryCoordinate H) := by
  have hc := contMDiffOn_chart (I := 𝓡∂ 1) (n := ∞) (x := (⟨H, by simp⟩ : Ici H))
  change ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ (revolutionEndBoundaryCoordinate H) univ at hc
  exact contMDiffOn_univ.mp hc

theorem revolutionEndBoundaryVal_contMDiff (H : ℝ) :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun z : Ici H => (z : ℝ)) := by
  have hc := (ModelWithCorners.contMDiff (𝓡∂ 1) (n := ∞)).comp
    (revolutionEndBoundaryCoordinate_contMDiff H)
  have hp : ContDiff ℝ ∞ (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  have hh := (hp.contMDiff.comp hc).add (contMDiff_const (c := H))
  convert hh using 1
  funext z
  change (z : ℝ) = (z : ℝ) - H + H
  ring

theorem revolutionEndCircle_boundary_contMDiff {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (H : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Ambient) ∞ (revolutionEndCircle q H) := by
  have hinc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 1))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : AddCircle (2 * Real.pi) × Ici H => (p.1, (p.2 : ℝ))) :=
    contMDiff_fst.prodMk ((revolutionEndBoundaryVal_contMDiff H).comp contMDiff_snd)
  have h := (revolutionEndCircleFull_contMDiff hq).comp hinc
  convert h using 1
  funext p
  exact revolutionEndCircle_eq_full q H p

end
end TightVer401
