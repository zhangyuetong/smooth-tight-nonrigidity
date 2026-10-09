import TightVer401.ParabolicConvexClosureBoundaryCosineParameters

/-! The exact cosine boundary map is the retained closed-annulus map composed
with an actual continuous bijection of closed interval parameters. These are
topological/image statements; endpoint differential regularity is proved in
the separate calculus leaf. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
local instance boundaryCosineTopologyPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def parabolicConvexClosureCosineClosedHeight {h : ℝ} (hh : 0 < h) (t : unitInterval) :
    Icc (-h) h :=
  ⟨parabolicConvexClosureCosineHeight h t, parabolicConvexClosureCosineHeight_mem hh t⟩

theorem parabolicConvexClosureCosineClosedHeight_continuous {h : ℝ} (hh : 0 < h) :
    Continuous (parabolicConvexClosureCosineClosedHeight hh) := by
  exact ((parabolicConvexClosureCosineHeight_contDiff h).continuous.comp continuous_subtype_val).subtype_mk _

theorem parabolicConvexClosureCosineClosedHeight_injective {h : ℝ} (hh : 0 < h) :
    Function.Injective (parabolicConvexClosureCosineClosedHeight hh) := by
  intro s t he
  have hc : Real.cos (Real.pi * (s : ℝ)) = Real.cos (Real.pi * (t : ℝ)) := by
    have hv := congrArg Subtype.val he
    exact mul_left_cancel₀ hh.ne' hv
  have hpi := Real.strictAntiOn_cos.injOn
    (show Real.pi * (s : ℝ) ∈ Icc 0 Real.pi from
      ⟨mul_nonneg Real.pi_pos.le s.property.1, by nlinarith [s.property.2, Real.pi_pos]⟩)
    (show Real.pi * (t : ℝ) ∈ Icc 0 Real.pi from
      ⟨mul_nonneg Real.pi_pos.le t.property.1, by nlinarith [t.property.2, Real.pi_pos]⟩) hc
  exact Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero hpi)

theorem parabolicConvexClosureCosineClosedHeight_surjective {h : ℝ} (hh : 0 < h) :
    Function.Surjective (parabolicConvexClosureCosineClosedHeight hh) := by
  intro z
  have hratio : z.val / h ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ hh).mpr (by simpa using z.property.1)
    · exact (div_le_one hh).mpr z.property.2
  let t : unitInterval := ⟨Real.arccos (z.val / h) / Real.pi,
    ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
      (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)⟩⟩
  refine ⟨t, Subtype.ext ?_⟩
  change h * Real.cos (Real.pi * (Real.arccos (z.val / h) / Real.pi)) = z.val
  rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.cos_arccos hratio.1 hratio.2]
  exact mul_div_cancel₀ _ hh.ne'

theorem parabolicConvexClosureBoundaryCosineMap_factor {h : ℝ} (hh : 0 < h)
    (r : ℝ → ℝ) :
    parabolicConvexClosureBoundaryCosineMap r h =
      parabolicConvexClosureClosedMap r h ∘ Prod.map id (parabolicConvexClosureCosineClosedHeight hh) := by
  funext p
  exact parabolicConvexClosureBoundaryCosineMap_eq r h p

theorem parabolicConvexClosureBoundaryCosineMap_range {h : ℝ} (hh : 0 < h) (r : ℝ → ℝ) :
    range (parabolicConvexClosureBoundaryCosineMap r h) = range (parabolicConvexClosureClosedMap r h) := by
  rw [parabolicConvexClosureBoundaryCosineMap_factor hh r]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Prod.map id (parabolicConvexClosureCosineClosedHeight hh) p, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨t, ht⟩ := parabolicConvexClosureCosineClosedHeight_surjective hh p.2
    refine ⟨(p.1, t), ?_⟩
    change parabolicConvexClosureClosedMap r h
      (p.1, parabolicConvexClosureCosineClosedHeight hh t) = _
    rw [ht]

theorem parabolicConvexClosureBoundaryCosineMap_isEmbedding {h : ℝ} (hh : 0 < h)
    {r : ℝ → ℝ} (hr : ContinuousOn r (Icc (-h) h))
    (hrpos : ∀ z ∈ Icc (-h) h, 0 < r z) :
    Topology.IsEmbedding (parabolicConvexClosureBoundaryCosineMap r h) := by
  rw [parabolicConvexClosureBoundaryCosineMap_factor hh r]
  exact (parabolicConvexClosureClosedMap_isClosedEmbedding hr hrpos).isEmbedding.comp
    (Topology.IsEmbedding.id.prodMap
      ((parabolicConvexClosureCosineClosedHeight_continuous hh).isClosedEmbedding
        (parabolicConvexClosureCosineClosedHeight_injective hh)).isEmbedding)

end
end TightVer401
