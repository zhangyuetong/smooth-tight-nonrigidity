import TightVer401.PlanarSupportForms
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology

/-- Pointwise continuity on the compact zero-amplitude section supplies a
uniform amplitude preserving a strict negative scalar quantity. Continuity
away from the center section is not required. -/
theorem bandBending_compact_uniform_negative_parameter
    {K : Set Coord} (hK : IsCompact K) {F : ℝ × Coord → ℝ}
    (hF : ∀ p ∈ K, ContinuousAt F (0, p))
    (hneg : ∀ p ∈ K, F (0, p) < 0) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p ∈ K, F (a, p) < 0 := by
  let C : Set (ℝ × Coord) := (fun p : Coord => ((0 : ℝ), p)) '' K
  have hC : IsCompact C := hK.image (continuous_const.prodMk continuous_id)
  let O : Set (ℝ × Coord) := interior (F ⁻¹' Iio 0)
  have hCO : C ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact (hF p hp).preimage_mem_nhds (gt_mem_nhds (hneg p hp))
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open isOpen_interior hCO
  refine ⟨δ, hδ, fun a ha p hp => ?_⟩
  have hm : (a, p) ∈ O := by
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(0, p), ⟨p, hp, rfl⟩, ?_⟩
    simpa only [dist_prod_same_right, Real.dist_eq, sub_zero] using ha
  exact (show (a, p) ∈ F ⁻¹' Iio (0 : ℝ) from interior_subset hm)

end
end TightVer401
