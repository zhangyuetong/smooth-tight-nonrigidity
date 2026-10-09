import TightVer401.CompleteProfile
import TightVer401.RevolutionEndBoundaryCompleteness
import TightVer401.RevolutionEndBoundaryNormal
import TightVer401.RevolutionEndCollar
import TightVer401.RevolutionEndAreaProduct

namespace TightVer401
noncomputable section
open Set Filter Bundle MeasureTheory OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

/-- Construct the actual complete rotational end from a strictly convex local radial germ. -/
theorem exists_revolutionEnd_complete_continuation {H β : ℝ} {q₀ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hH : H ∈ U) (hq₀ : ContDiffOn ℝ ∞ q₀ U)
    (hvalue : 0 < q₀ H) (hslope : 0 < deriv q₀ H)
    (hconvex : ∀ z ∈ U, 0 < deriv (deriv q₀) z) (hβ : 0 < β) :
    ∃ (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z),
      q =ᶠ[𝓝 H] q₀ ∧
      (∀ z ∈ Ici H, 0 < deriv q z ∧ 0 < deriv (deriv q) z) ∧
      (∀ᶠ z in atTop, deriv (deriv q) z = β) ∧ Tendsto (deriv q) atTop atTop ∧
      (∃ ε > 0, ∀ p : RevolutionClosedEnd H, (p.2 : ℝ) ≤ H + ε →
        revolutionEndCircle q H p = revolutionEndCircle q₀ H p) ∧
      ContMDiff revolutionEndBoundaryModel 𝓘(ℝ, Ambient) ∞ (revolutionEndCircle q H) ∧
      (∀ p : RevolutionClosedEnd H, Function.Injective
        (mfderiv revolutionEndBoundaryModel 𝓘(ℝ, Ambient) (revolutionEndCircle q H) p)) ∧
      Topology.IsClosedEmbedding (revolutionEndCircle q H) ∧
      @CompleteSpace (RevolutionClosedEnd H)
        (revolutionEndBoundaryEMetricSpace hq hpos).toUniformSpace ∧
      ContMDiff revolutionEndBoundaryModel (𝓡 2) ∞ (revolutionEndGauss q H) ∧
      Function.Injective (revolutionEndGauss q H) ∧
      (∫ p in Icc (0 : ℝ) (2 * Real.pi) ×ˢ Ici H,
        revolutionEndAbsoluteCurvatureDensity q (![p.1, p.2] : Coord) ∂volume.prod volume) <
          2 * Real.pi := by
  obtain ⟨q, hq, hgerm, hpositive, htail, hinfty⟩ :=
    exists_completeProfile hU hH hq₀ hvalue hslope hconvex hβ
  have hpos : ∀ z ∈ Ici H, 0 < q z := fun z hz => (hpositive z hz).1
  have hfirst : ∀ z ∈ Ici H, 0 < deriv q z := fun z hz => (hpositive z hz).2.1
  have hsecond : ∀ z ∈ Ici H, 0 < deriv (deriv q) z := fun z hz => (hpositive z hz).2.2
  refine ⟨q, hq, hpos, hgerm, ?_, htail, hinfty,
    revolutionEndCircle_eqOn_collar_of_germ hgerm,
    revolutionEndCircle_boundary_contMDiff hq H, ?_,
    revolutionEndCircle_isClosedEmbedding hq.continuous hpos,
    revolutionEnd_closedEnd_complete hq hpos,
    revolutionEndGauss_boundary_contMDiff hq H,
    revolutionEndGauss_injective hq hsecond, ?_⟩
  · exact fun z hz => ⟨hfirst z hz, hsecond z hz⟩
  · intro p
    exact revolutionEndCircle_boundary_mfderiv_injective hq p (hpos p.2 p.2.property).ne'
  · exact revolutionEnd_absoluteCurvature_product_integral_lt hq hpos hsecond hinfty
      (hfirst H (by simp))

end
end TightVer401
