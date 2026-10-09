import TightVer401.RevolutionEndMetricCoordinates
import TightVer401.RevolutionEndDistance
import Mathlib.Topology.Sequences

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

@[reducible] def revolutionEndEMetricSpace {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z, 0 < q z) : EMetricSpace RevolutionCylinder := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  letI : IsContinuousRiemannianBundle (ℝ × ℝ)
    (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      revolutionEndRiemannianMetric_isContinuous hq hpos
  let pe : PseudoEMetricSpace RevolutionCylinder :=
    PseudoEMetricSpace.ofRiemannianMetric revolutionCylinderModel RevolutionCylinder
  exact @EMetricSpace.ofT0PseudoEMetricSpace RevolutionCylinder pe inferInstance

theorem revolutionEnd_fullCylinder_complete {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z, 0 < q z) :
    @CompleteSpace RevolutionCylinder (revolutionEndEMetricSpace hq hpos).toUniformSpace := by
  letI : RiemannianBundle (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
    ⟨revolutionEndRiemannianMetric hq hpos⟩
  letI : IsContinuousRiemannianBundle (ℝ × ℝ)
    (fun p : RevolutionCylinder => TangentSpace revolutionCylinderModel p) :=
      revolutionEndRiemannianMetric_isContinuous hq hpos
  let em : EMetricSpace RevolutionCylinder := revolutionEndEMetricSpace hq hpos
  letI : EMetricSpace RevolutionCylinder := em
  letI : PseudoEMetricSpace RevolutionCylinder := em.toPseudoEMetricSpace
  letI : UniformSpace RevolutionCylinder := em.toUniformSpace
  letI : EDist RevolutionCylinder := em.toEDist
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hz : CauchySeq (fun n => (u n).2) := by
    rw [EMetric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    change riemannianEDist revolutionCylinderModel (u m) (u n) < ε at hmn
    exact (revolutionEnd_height_edist_le_riemannianEDist hq hpos (u m) (u n)).trans_lt
      hmn
  obtain ⟨z, hzt⟩ := cauchySeq_tendsto_of_complete hz
  obtain ⟨θ, φ, hφ, hθ⟩ := CompactSpace.tendsto_subseq (fun n => (u n).1)
  have hp : Tendsto (u ∘ φ) atTop (𝓝 (θ, z)) := by
    have hp' := hθ.prodMk (hzt.comp hφ.tendsto_atTop)
    rw [← nhds_prod_eq] at hp'
    change Tendsto (fun n => u (φ n)) atTop (𝓝 (θ, z)) at hp'
    exact hp'
  exact ⟨(θ, z), tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hp⟩

end
end TightVer401

