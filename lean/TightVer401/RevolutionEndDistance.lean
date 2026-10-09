import TightVer401.RevolutionEndNativeLength

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEnd_height_edist_le_riemannianEDist {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z, 0 < q z) (p s : RevolutionCylinder) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    edist p.2 s.2 ≤ riemannianEDist revolutionCylinderModel p s := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨c, hcp, hcs, hc, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have h := revolutionEnd_native_height_edist_le_pathELength hq hpos hc zero_le_one
  rw [hcp, hcs] at h
  exact h.trans_lt hlen

end
end TightVer401
