import TightVer401.NativeCompactEmbeddingGraphDerivative
import TightVer401.NativeProductPlaneAtlas
import TightVer401.ThinBandChartTransport
import TightVer401.ThinBandTopology

/-! Small smooth perturbations of actual compact native immersions preserve
embedding. Local parameter-graph injection comes from the actual differential;
compactness reuses the retained thin-strip theorem. -/
open Manifold
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [MetricSpace M] [ChartedSpace (ModelProd ℝ ℝ) M]

/-- Actual smooth chart representatives for native product-model maps. -/
theorem nativeCompactEmbedding_chart_contDiffAt
    {X : M → Ambient} (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X) (p : M) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm z))
      (chartAt (ModelProd ℝ ℝ) p p) := by
  have h := (contMDiffAt_iff.mp (hX p)).2
  have hr : range nativeProductModel = univ := ModelWithCorners.range_eq_univ nativeProductModel
  rw [hr] at h
  convert! contDiffWithinAt_univ.mp h using 1 <;>
    simp [extChartAt, nativeProductModel, Function.comp_def]

/-- The chart differential is the actual native manifold differential. -/
theorem nativeCompactEmbedding_chart_fderiv
    {X : M → Ambient} (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X) (p : M) :
    fderiv ℝ (fun z : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm z))
      (chartAt (ModelProd ℝ ℝ) p p) = mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p := by
  have h := ((hX p).mdifferentiableAt (by simp)).hasMFDerivAt.2
  have hr : range nativeProductModel = univ := ModelWithCorners.range_eq_univ nativeProductModel
  rw [hr] at h
  have hd : HasFDerivAt (fun z : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm z))
      (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p) (chartAt (ModelProd ℝ ℝ) p p) := by
    convert! h.hasFDerivAt_of_univ using 1 <;>
      simp [writtenInExtChartAt, extChartAt, nativeProductModel, Function.comp_def]
  exact hd.fderiv

/-- Local injection of the actual parameter graph, derived in native charts. -/
theorem nativeCompactEmbedding_parameterGraph_locally_injective
    {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (p : M) (himm : Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) :
    ∃ U ∈ 𝓝 (p, (0 : ℝ)),
      InjOn (fun z : M × ℝ => (z.2, X z.1 + z.2 • Y z.1)) U := by
  let e : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) (M × ℝ) :=
    (chartAt (ModelProd ℝ ℝ) p).symm.prod (OpenPartialHomeomorph.refl ℝ)
  let z := chartAt (ModelProd ℝ ℝ) p p
  have hi : Function.Injective
      (fderiv ℝ (fun q : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm q)) z) := by
    rw [nativeCompactEmbedding_chart_fderiv hX p]
    exact himm
  have hlocal := nativeCompactEmbeddingGraph_exists_local_injOn
    (nativeCompactEmbedding_chart_contDiffAt hX p)
    (nativeCompactEmbedding_chart_contDiffAt hY p) hi
  have hx : (z, (0 : ℝ)) ∈ e.source :=
    ⟨(chartAt (ModelProd ℝ ℝ) p).map_source (mem_chart_source _ p), mem_univ _⟩
  have hmatch : ∀ q ∈ e.source,
      (fun r : M × ℝ => (r.2, X r.1 + r.2 • Y r.1)) (e q) =
      nativeCompactEmbeddingGraph
        (fun r : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm r))
        (fun r : ℝ × ℝ => Y ((chartAt (ModelProd ℝ ℝ) p).symm r)) q := by
    intro q _
    rfl
  have ht := local_injOn_transport_chart
    (e := e)
    (f := nativeCompactEmbeddingGraph
      (fun r : ℝ × ℝ => X ((chartAt (ModelProd ℝ ℝ) p).symm r))
      (fun r : ℝ × ℝ => Y ((chartAt (ModelProd ℝ ℝ) p).symm r)))
    (g := fun r : M × ℝ => (r.2, X r.1 + r.2 • Y r.1)) hx hmatch hlocal
  have he : e (z, (0 : ℝ)) = (p, 0) := by
    apply Prod.ext
    · exact (chartAt (ModelProd ℝ ℝ) p).left_inv (mem_chart_source _ p)
    · rfl
  rw [he] at ht
  exact ht

/-- Genuine smooth compact embeddings have a proved perturbation amplitude threshold. -/
theorem nativeCompactEmbedding_exists_amplitude_threshold [CompactSpace M]
    {X Y : M → Ambient}
    (hX : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ X)
    (hY : ContMDiff nativeProductModel 𝓘(ℝ, Ambient) ∞ Y)
    (hemb : Topology.IsEmbedding X)
    (himm : ∀ p, Function.Injective (mfderiv nativeProductModel 𝓘(ℝ, Ambient) X p)) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → Topology.IsEmbedding (fun p => X p + a • Y p) := by
  have hgraph : Continuous (fun z : M × ℝ => (z.2, X z.1 + z.2 • Y z.1)) :=
    continuous_snd.prodMk ((hX.continuous.comp continuous_fst).add
      (continuous_snd.smul (hY.continuous.comp continuous_fst)))
  have hcentral : Function.Injective (fun p : M => ((0 : ℝ), X p + (0 : ℝ) • Y p)) := by
    intro p q he
    apply hemb.injective
    simpa only [zero_smul, add_zero] using congrArg Prod.snd he
  obtain ⟨δ, hδ, hi⟩ := exists_thinBand_injective hgraph hcentral
    (fun p => nativeCompactEmbedding_parameterGraph_locally_injective hX hY p (himm p))
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hinj : Function.Injective (fun p => X p + a • Y p) := by
    intro p q he
    have hm : a ∈ Icc (-δ) δ := abs_le.mp ha.le
    have hpa : (p, a) ∈ (univ : Set M) ×ˢ Icc (-δ) δ := ⟨mem_univ p, hm⟩
    have hqa : (q, a) ∈ (univ : Set M) ×ˢ Icc (-δ) δ := ⟨mem_univ q, hm⟩
    have hpair : (a, X p + a • Y p) = (a, X q + a • Y q) := Prod.ext rfl he
    have hpq := hi hpa hqa hpair
    exact congrArg Prod.fst hpq
  exact ((hX.continuous.add
    ((continuous_const : Continuous (fun _ : M => a)).smul hY.continuous)).isClosedEmbedding hinj).isEmbedding

end
end TightVer401
