import TightVer401.RevolutionEndDistance

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem revolutionEnd_ambient_edist_le_native_pathELength {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z, 0 < q z)
    {c : ℝ → RevolutionCylinder} {A B : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) revolutionCylinderModel 1 c (Icc A B)) (hAB : A ≤ B) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    edist (revolutionEndCircleFull q (c A)) (revolutionEndCircleFull q (c B)) ≤
      pathELength revolutionCylinderModel c A B := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  rw [revolutionEnd_native_pathELength_eq_image hq hpos hc]
  apply revolution_ambientCurve_edist_le_pathELength _ hAB
  rw [← contMDiffOn_iff_contDiffOn]
  exact ((revolutionEndCircleFull_contMDiff hq).of_le (by simp)).comp_contMDiffOn hc

theorem revolutionEnd_ambient_edist_le_riemannianEDist {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z, 0 < q z) (p s : RevolutionCylinder) :
    letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      ⟨revolutionEndRiemannianMetric hq hpos⟩
    edist (revolutionEndCircleFull q p) (revolutionEndCircleFull q s) ≤
      riemannianEDist revolutionCylinderModel p s := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨c, hcp, hcs, hc, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have h := revolutionEnd_ambient_edist_le_native_pathELength hq hpos hc zero_le_one
  rw [hcp, hcs] at h
  exact h.trans_lt hlen

end
end TightVer401
