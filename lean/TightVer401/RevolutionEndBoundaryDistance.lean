import TightVer401.RevolutionEndBoundaryLength

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEnd_boundary_height_edist_le_riemannianEDist {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) (p s : RevolutionClosedEnd H) :
    letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
    edist (p.2 : ℝ) (s.2 : ℝ) ≤ riemannianEDist revolutionEndBoundaryModel p s := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨c, hcp, hcs, hc, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have h := revolutionEnd_boundary_height_edist_le_pathELength hq hpos hc zero_le_one
  rw [hcp, hcs] at h
  exact h.trans_lt hlen

end
end TightVer401

