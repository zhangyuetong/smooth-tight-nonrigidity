import TightVer401.ThinBandTopology
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening

/-! Compact support localizes an otherwise noncompact embedding perturbation.
The local graph and compactness inputs give injection; ambient localization
also proves continuity of the inverse onto the perturbed image. -/
namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology

/-- A continuous parameter family sends a compact set into an open set for
one uniform sufficiently small parameter. -/
theorem nativeSupportedEmbedding_compact_image_open
    {M Z : Type*} [MetricSpace M] [TopologicalSpace Z]
    {S : Set M} (hS : IsCompact S) {F : M × ℝ → Z} (hF : Continuous F)
    {U : Set Z} (hU : IsOpen U) (hzero : ∀ p ∈ S, F (p, 0) ∈ U) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → ∀ p ∈ S, F (p, a) ∈ U := by
  let C : Set (M × ℝ) := (fun p : M => (p, (0 : ℝ))) '' S
  have hC : IsCompact C := hS.image (continuous_id.prodMk continuous_const)
  have hCU : C ⊆ F ⁻¹' U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hzero p hp
  obtain ⟨δ, hδ, hthick⟩ :=
    hC.exists_thickening_subset_open (hU.preimage hF) hCU
  refine ⟨δ, hδ, fun a ha p hp => ?_⟩
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(p, 0), ⟨p, hp, rfl⟩, ?_⟩
  simpa only [dist_prod_same_left, Real.dist_eq, sub_zero] using ha

/-- Compact localization supplies both global injection and inverse continuity.
The neighborhood U keeps the changed compact image away from all unchanged
points outside K, including possible ambient accumulation of the open ends. -/
theorem nativeSupportedEmbedding_of_compact_localization
    {M Z : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace Z] [T2Space Z]
    {X F : M → Z} (hX : Topology.IsEmbedding X) (hF : Continuous F)
    {S K : Set M} (hS : IsCompact S) (hK : IsCompact K) (hSK : S ⊆ K)
    (hfixed : ∀ p ∉ S, F p = X p) (hinjK : InjOn F K)
    {U : Set Z} (hU : IsOpen U) (hmoved : F '' S ⊆ U)
    (hlocalize : X ⁻¹' U ⊆ K) : Topology.IsEmbedding F := by
  have hinj : Function.Injective F := by
    intro p q he
    by_cases hpK : p ∈ K
    · by_cases hqK : q ∈ K
      · exact hinjK hpK hqK he
      · have hqS : q ∉ S := fun h => hqK (hSK h)
        by_cases hpS : p ∈ S
        · have hqU : X q ∈ U := by
            rw [← hfixed q hqS, ← he]
            exact hmoved ⟨p, hpS, rfl⟩
          exact False.elim (hqK (hlocalize hqU))
        · apply hX.injective
          simpa only [hfixed p hpS, hfixed q hqS] using he
    · have hpS : p ∉ S := fun h => hpK (hSK h)
      by_cases hqS : q ∈ S
      · have hpU : X p ∈ U := by
          rw [← hfixed p hpS, he]
          exact hmoved ⟨q, hqS, rfl⟩
        exact False.elim (hpK (hlocalize hpU))
      · apply hX.injective
        simpa only [hfixed p hpS, hfixed q hqS] using he
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heK : Topology.IsEmbedding (fun p : K => F p) :=
    ((hF.comp continuous_subtype_val).isClosedEmbedding
      (fun p q h => Subtype.ext (hinjK p.property q.property h))).isEmbedding
  have hFSclosed : IsClosed (F '' S) := (hS.image hF).isClosed
  apply Topology.IsEmbedding.mk' F hinj
  intro p
  symm
  apply le_antisymm
  · intro A hA
    obtain ⟨V, hV, hVA⟩ := Filter.mem_comap.mp hA
    exact mem_of_superset (hF.continuousAt.preimage_mem_nhds hV) hVA
  · intro A hA
    apply Filter.mem_comap.mpr
    by_cases hpS : p ∈ S
    · let pK : K := ⟨p, hSK hpS⟩
      have hAK : (Subtype.val : K → M) ⁻¹' A ∈ 𝓝 pK :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds hA
      rw [heK.nhds_eq_comap pK] at hAK
      obtain ⟨V, hV, hVA⟩ := Filter.mem_comap.mp hAK
      have hpU : F p ∈ U := hmoved ⟨p, hpS, rfl⟩
      refine ⟨V ∩ U, inter_mem hV (hU.mem_nhds hpU), ?_⟩
      intro q hq
      have hqK : q ∈ K := by
        by_cases hqS : q ∈ S
        · exact hSK hqS
        · apply hlocalize
          change X q ∈ U
          simpa only [hfixed q hqS] using hq.2
      exact hVA (show F (⟨q, hqK⟩ : K) ∈ V from hq.1)
    · have hpnotimage : F p ∉ F '' S := by
        rintro ⟨q, hq, he⟩
        exact hpS (hinj he ▸ hq)
      have hAX : A ∈ comap X (𝓝 (X p)) := by
        rw [← hX.nhds_eq_comap p]
        exact hA
      obtain ⟨V, hV, hVA⟩ := Filter.mem_comap.mp hAX
      have hVp : V ∈ 𝓝 (F p) := by simpa only [hfixed p hpS] using hV
      refine ⟨V ∩ (F '' S)ᶜ,
        inter_mem hVp (hFSclosed.isOpen_compl.mem_nhds hpnotimage), ?_⟩
      intro q hq
      have hqS : q ∉ S := fun h => hq.2 ⟨q, h, rfl⟩
      apply hVA
      change X q ∈ V
      simpa only [hfixed q hqS] using hq.1

/-- Local injection of the actual parameter graph and compact support yield a
uniform embedding threshold even when the whole source is noncompact. -/
theorem nativeSupportedEmbedding_exists_parameter_threshold
    {M Z : Type*} [MetricSpace M] [WeaklyLocallyCompactSpace M]
    [TopologicalSpace Z] [T2Space Z]
    {X : M → Z} {F : M × ℝ → Z}
    (hX : Topology.IsEmbedding X) (hF : Continuous F)
    (hzero : ∀ p, F (p, 0) = X p)
    {S : Set M} (hS : IsCompact S)
    (hfixed : ∀ p ∉ S, ∀ a : ℝ, F (p, a) = X p)
    (hgraph : ∀ p : M, ∃ V ∈ 𝓝 (p, (0 : ℝ)),
      InjOn (fun z : M × ℝ => (z.2, F z)) V) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      Topology.IsEmbedding (fun p : M => F (p, a)) := by
  obtain ⟨K, hK, hSKi⟩ := exists_compact_superset hS
  have hSK : S ⊆ K := hSKi.trans interior_subset
  obtain ⟨U, hU, hUX⟩ := hX.isInducing.isOpen_iff.mp (isOpen_interior (s := K))
  have hXSU : ∀ p ∈ S, F (p, 0) ∈ U := by
    intro p hp
    rw [hzero p]
    change p ∈ X ⁻¹' U
    rw [hUX]
    exact hSKi hp
  obtain ⟨δ₁, hδ₁, hmove⟩ :=
    nativeSupportedEmbedding_compact_image_open hS hF hU hXSU
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let graph : K × ℝ → ℝ × Z := fun z => (z.2, F ((z.1 : M), z.2))
  have hc : Continuous graph :=
    continuous_snd.prodMk (hF.comp (continuous_subtype_val.prodMap continuous_id))
  have hcentral : Function.Injective (fun p : K => graph (p, 0)) := by
    intro p q he
    apply Subtype.ext
    apply hX.injective
    simpa only [graph, hzero] using congrArg Prod.snd he
  have hl : ∀ p : K, ∃ V ∈ 𝓝 (p, (0 : ℝ)), InjOn graph V := by
    intro p
    obtain ⟨V, hV, hi⟩ := hgraph p
    let lift : K × ℝ → M × ℝ := fun z => ((z.1 : M), z.2)
    have hcl : Continuous lift := continuous_subtype_val.prodMap continuous_id
    refine ⟨lift ⁻¹' V, hcl.continuousAt.preimage_mem_nhds hV, ?_⟩
    intro q hq r hr he
    have he' : lift q = lift r := hi hq hr he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he')
    · simpa only [lift] using congrArg (fun z : M × ℝ => z.2) he'
  obtain ⟨δ₂, hδ₂, hi⟩ := exists_thinBand_injective hc hcentral hl
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun a ha => ?_⟩
  have ha₁ : |a| < δ₁ := lt_of_lt_of_le ha (min_le_left _ _)
  have ha₂ : |a| < δ₂ := lt_of_lt_of_le ha (min_le_right _ _)
  have hinjK : InjOn (fun p : M => F (p, a)) K := by
    intro p hp q hq he
    have hm : a ∈ Icc (-δ₂) δ₂ := abs_le.mp ha₂.le
    have hpa : ((⟨p, hp⟩ : K), a) ∈ (univ : Set K) ×ˢ Icc (-δ₂) δ₂ :=
      ⟨mem_univ _, hm⟩
    have hqa : ((⟨q, hq⟩ : K), a) ∈ (univ : Set K) ×ˢ Icc (-δ₂) δ₂ :=
      ⟨mem_univ _, hm⟩
    have hpair : (a, F (p, a)) = (a, F (q, a)) := Prod.ext rfl he
    have he' := hi hpa hqa hpair
    exact congrArg (fun z : K × ℝ => (z.1 : M)) he'
  apply nativeSupportedEmbedding_of_compact_localization hX
    (hF.comp (continuous_id.prodMk continuous_const)) hS hK hSK
    (fun p hp => hfixed p hp a) hinjK hU
  · rintro _ ⟨p, hp, rfl⟩
    exact hmove a ha₁ p hp
  · rw [hUX]
    exact interior_subset

end
end TightVer401
