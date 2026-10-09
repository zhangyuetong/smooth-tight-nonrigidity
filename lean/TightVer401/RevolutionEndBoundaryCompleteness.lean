import TightVer401.RevolutionEndBoundaryMetricCoordinates
import TightVer401.RevolutionEndBoundaryDistance
import Mathlib.Topology.Sequences

namespace TightVer401
noncomputable section
open Set Filter Bundle Manifold OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff Topology Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

@[reducible] def revolutionEndBoundaryEMetricSpace {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) : EMetricSpace (RevolutionClosedEnd H) := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  letI : IsContinuousRiemannianBundle (ℝ × EuclideanSpace ℝ (Fin 1))
    (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      revolutionEndBoundaryRiemannianMetric_isContinuous hq hpos
  let pe : PseudoEMetricSpace (RevolutionClosedEnd H) :=
    PseudoEMetricSpace.ofRiemannianMetric revolutionEndBoundaryModel (RevolutionClosedEnd H)
  exact @EMetricSpace.ofT0PseudoEMetricSpace (RevolutionClosedEnd H) pe inferInstance

theorem revolutionEnd_closedEnd_complete {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hpos : ∀ z ∈ Ici H, 0 < q z) :
    @CompleteSpace (RevolutionClosedEnd H) (revolutionEndBoundaryEMetricSpace hq hpos).toUniformSpace := by
  letI : RiemannianBundle (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
    ⟨revolutionEndBoundaryRiemannianMetric hq hpos⟩
  letI : IsContinuousRiemannianBundle (ℝ × EuclideanSpace ℝ (Fin 1))
    (fun p : RevolutionClosedEnd H => TangentSpace revolutionEndBoundaryModel p) :=
      revolutionEndBoundaryRiemannianMetric_isContinuous hq hpos
  let em : EMetricSpace (RevolutionClosedEnd H) := revolutionEndBoundaryEMetricSpace hq hpos
  letI : EMetricSpace (RevolutionClosedEnd H) := em
  letI : PseudoEMetricSpace (RevolutionClosedEnd H) := em.toPseudoEMetricSpace
  letI : UniformSpace (RevolutionClosedEnd H) := em.toUniformSpace
  letI : EDist (RevolutionClosedEnd H) := em.toEDist
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hz : CauchySeq (fun n => ((u n).2 : ℝ)) := by
    rw [EMetric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    change riemannianEDist revolutionEndBoundaryModel (u m) (u n) < ε at hmn
    exact (revolutionEnd_boundary_height_edist_le_riemannianEDist hq hpos (u m) (u n)).trans_lt hmn
  obtain ⟨z, hzt⟩ := cauchySeq_tendsto_of_complete hz
  have hzin : z ∈ Ici H := isClosed_Ici.mem_of_tendsto hzt
    (Filter.Eventually.of_forall (fun n => (u n).2.property))
  let zz : Ici H := ⟨z, hzin⟩
  have hsub : Tendsto (fun n => (u n).2) atTop (𝓝 zz) := by
    apply tendsto_subtype_rng.mpr
    exact hzt
  obtain ⟨θ, φ, hφ, hθ⟩ := CompactSpace.tendsto_subseq (fun n => (u n).1)
  have hp : Tendsto (u ∘ φ) atTop (𝓝 (θ, zz)) := by
    have hp' := hθ.prodMk (hsub.comp hφ.tendsto_atTop)
    rw [← nhds_prod_eq] at hp'
    change Tendsto (fun n => u (φ n)) atTop (𝓝 (θ, zz)) at hp'
    exact hp'
  exact ⟨(θ, zz), tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hp⟩

end
end TightVer401
