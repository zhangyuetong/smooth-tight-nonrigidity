import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology

/-- Local injectivity and injectivity of the compact central curve imply
actual injectivity on a uniform strip. -/
theorem exists_thinBand_injective {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {F : X × ℝ → Y} (hF : Continuous F)
    (hcentral : Function.Injective (fun x => F (x, 0)))
    (hlocal : ∀ x, ∃ U ∈ 𝓝 (x, (0 : ℝ)), Set.InjOn F U) :
    ∃ δ > 0, Set.InjOn F (univ ×ˢ Icc (-δ) δ) := by
  let K : Set (X × ℝ) := (fun x : X => (x, (0 : ℝ))) '' univ
  have hK : IsCompact K := isCompact_univ.image (continuous_id.prodMk continuous_const)
  have hi : Set.InjOn F K := by
    rintro _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩ he
    exact congrArg (fun z : X => (z, (0 : ℝ))) (hcentral he)
  have hl : ∀ p ∈ K, ∃ U ∈ 𝓝 p, Set.InjOn F U := by
    rintro _ ⟨x, _, rfl⟩
    exact hlocal x
  obtain ⟨U, hU, hKU, hiU⟩ := hi.exists_isOpen_superset hK (fun p _ => hF.continuousAt) hl
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, hiU.mono ?_⟩
  intro p hp
  apply hthick
  apply Metric.thickening_subset_cthickening δ K
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(p.1, 0), ⟨p.1, mem_univ _, rfl⟩, ?_⟩
  rw [dist_prod_same_left, Real.dist_eq, sub_zero]
  have hv : |p.2| ≤ δ / 2 := abs_le.mpr hp.2
  exact hv.trans_lt (half_lt_self hδ)

/-- Compactness of a slightly larger closed strip also supplies the actual
topological embedding of the open thin band. -/
theorem exists_thinBand_embedding {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] {F : X × ℝ → Y} (hF : Continuous F)
    (hcentral : Function.Injective (fun x => F (x, 0)))
    (hlocal : ∀ x, ∃ U ∈ 𝓝 (x, (0 : ℝ)), Set.InjOn F U) :
    ∃ δ > 0, Set.InjOn F (univ ×ˢ Icc (-δ) δ) ∧
      Topology.IsEmbedding (fun p : ↥((univ : Set X) ×ˢ Ioo (-δ) δ) => F p) := by
  obtain ⟨δ, hδ, hi⟩ := exists_thinBand_injective hF hcentral hlocal
  let K : Set (X × ℝ) := univ ×ˢ Icc (-δ) δ
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hiK : Function.Injective (fun p : ↥K => F p) := by
    intro p q hpq
    exact Subtype.ext (hi p.property q.property hpq)
  have hemb := ((hF.comp continuous_subtype_val).isClosedEmbedding hiK).isEmbedding
  have hs : (univ ×ˢ Ioo (-δ) δ : Set (X × ℝ)) ⊆ K :=
    prod_mono Subset.rfl Ioo_subset_Icc_self
  exact ⟨δ, hδ, hi, hemb.comp (Topology.IsEmbedding.inclusion hs)⟩

end
end TightVer401
