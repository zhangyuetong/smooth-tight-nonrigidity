import TightVer401.ThinBandRuledCharts
import TightVer401.ThinBandLocalCalculus
import TightVer401.ThinBandTopology

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem periodicRuledFrame_fullBandMap_continuous {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) : Continuous d.fullBandMap := by
  have hγ := (periodicLift_contMDiff d.smooth_γ d.period_γ).continuous
  have hE := (periodicLift_contMDiff d.smooth_E d.period_E).continuous
  exact (hγ.comp continuous_fst).add (continuous_snd.smul (hE.comp continuous_fst))

theorem periodicRuledFrame_fullBandMap_locally_injective {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (q : AddCircle L) :
    ∃ U ∈ 𝓝 (q, (0 : ℝ)), Set.InjOn d.fullBandMap U := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ U ∈ 𝓝 (periodProjection L r, (0 : ℝ)), Set.InjOn d.fullBandMap U
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hp : (![r, 0] : Coord) 0 = r := rfl
  have hi := ruled_differential_injective (d.deriv_γ ((![r, 0] : Coord) 0))
    (d.deriv_E ((![r, 0] : Coord) 0)) (d.orthonormal r) (d.torsion_ne_zero r)
  have hlocal := exists_local_injOn_of_injective_strictFDeriv
    (hX.hasStrictFDerivAt (x := (![r, 0] : Coord)) (by simp)) hi
  have hl := local_injOn_transport_chart (ruledCircleChart_center_source L r)
    (fun p _ => ruledCircleChart_fullBandMap d r p) hlocal
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hl

theorem periodicRuledFrame_exists_thin_embedded_strip {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hi : Function.Injective d.period_γ.lift) :
    ∃ δ > 0, Set.InjOn d.fullBandMap (univ ×ˢ Icc (-δ) δ) ∧
      Topology.IsEmbedding
        (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-δ) δ) => d.fullBandMap p) := by
  apply exists_thinBand_embedding (periodicRuledFrame_fullBandMap_continuous d) ?_
    (periodicRuledFrame_fullBandMap_locally_injective d)
  intro x y he
  apply hi
  simpa only [PeriodicRuledFrame.fullBandMap, zero_smul, add_zero] using he

theorem periodicRuledFrame_exists_thin_band_embedding {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hi : Function.Injective d.period_γ.lift) :
    ∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) := by
  obtain ⟨δ, hδ, _, hemb⟩ := periodicRuledFrame_exists_thin_embedded_strip d hi
  let S : Set (AddCircle L × ℝ) := univ ×ˢ Ioo (-δ) δ
  let ι : AddCircle L × Ioo (0 : ℝ) δ → AddCircle L × ℝ := fun p => (p.1, p.2)
  have hι : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have hmem (p : AddCircle L × Ioo (0 : ℝ) δ) : ι p ∈ S :=
    ⟨mem_univ _, ⟨by linarith [p.2.property.1], p.2.property.2⟩⟩
  have hembι := hι.codRestrict S hmem
  exact ⟨δ, hδ, hemb.comp hembι⟩

end
end TightVer401
