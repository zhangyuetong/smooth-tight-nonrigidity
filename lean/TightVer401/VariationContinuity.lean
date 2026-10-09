import Mathlib.Topology.EMetricSpace.VariationOnFromTo

namespace TightVer401
open Set Filter
open scoped Topology

/-- Continuity of actual metric variation at every continuity point of the path. -/
theorem continuousAt_variationOnFromTo_of_continuousAt
    {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [PseudoMetricSpace E] {f : α → E} {a t : α}
    (hf : BoundedVariationOn f univ) (hc : ContinuousAt f t) :
    ContinuousAt (variationOnFromTo f univ a) t := by
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · have h := variationOnFromTo.tendsto_left (a := a) (b := t)
      (mem_univ a) (mem_univ t) hf.locallyBoundedVariationOn
      (hc.continuousWithinAt : ContinuousWithinAt f (univ ∩ Iio t) t)
    simpa only [ContinuousWithinAt, univ_inter, dist_self, sub_zero] using h
  · have h := variationOnFromTo.tendsto_right (a := a) (b := t)
      (mem_univ a) (mem_univ t) hf.locallyBoundedVariationOn
      (hc.continuousWithinAt : ContinuousWithinAt f (univ ∩ Ioi t) t)
    simpa only [ContinuousWithinAt, univ_inter, dist_self, add_zero] using h
end TightVer401
