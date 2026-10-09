import TightVer401.SeamNormalChart
import TightVer401.ThinBandTopology
import TightVer401.ThinBandRuledCharts
import TightVer401.PeriodicCircleFunctions

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Manifold

local instance seamNormalTubeChart (L : ℝ) [Fact (0 < L)] : ChartedSpace ℝ (AddCircle L) :=
  periodCircleChartedSpace L

theorem seam_complex_deriv_periodic {γ : ℝ → ℂ} {L : ℝ}
    (hL : Function.Periodic γ L) : Function.Periodic (deriv γ) L := by
  intro s
  have he : (fun t => γ (t+L))=γ := funext hL
  have hd := congrArg (fun f : ℝ → ℂ => deriv f s) he
  simpa only [deriv_comp_add_const] using hd

def seamNormalNative {L : ℝ} (γ : ℝ → ℂ) (hL : Function.Periodic γ L)
    (p : AddCircle L × ℝ) : Coord :=
  seamComplexCoord (hL.lift p.1 + p.2 • (Complex.I*(seam_complex_deriv_periodic hL).lift p.1))

theorem seamNormalNative_chart {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) (s : ℝ) (p : Coord) :
    seamNormalNative γ hL (ruledCircleChart L s p)=seamNormalCoordinates γ p := by
  simp only [seamNormalNative,ruledCircleChart_apply,periodicLift_coe]
  rfl

theorem seamNormalNative_continuous {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) :
    Continuous (seamNormalNative γ hL) := by
  have hγ' : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hc : Continuous (fun p : AddCircle L × ℝ => hL.lift p.1) :=
    (periodicLift_contMDiff hγ hL).continuous.comp continuous_fst
  have hd : Continuous (fun p : AddCircle L × ℝ => (seam_complex_deriv_periodic hL).lift p.1) :=
    (periodicLift_contMDiff hγ' (seam_complex_deriv_periodic hL)).continuous.comp continuous_fst
  exact seamComplexCoord.continuous.comp (hc.add (continuous_snd.smul (continuous_const.mul hd)))

theorem seamNormalNative_locally_injective {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (q : AddCircle L) :
    ∃ U ∈ 𝓝 (q,(0 : ℝ)), InjOn (seamNormalNative γ hL) U := by
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ U ∈ 𝓝 (periodProjection L s,(0 : ℝ)), InjOn (seamNormalNative γ hL) U
  obtain ⟨e,heS,he,_,_⟩ := seamNormalCoordinates_exists_chart hγ s (hreg s)
  have hlocal : ∃ U ∈ 𝓝 (![s,0] : Coord), InjOn (seamNormalCoordinates γ) U := by
    refine ⟨e.source,e.open_source.mem_nhds heS,?_⟩
    intro p hp z hz hpz
    apply e.injOn hp hz
    simpa only [he] using hpz
  have hl := local_injOn_transport_chart (ruledCircleChart_center_source L s)
    (fun p _ => seamNormalNative_chart hL s p) hlocal
  simpa only [ruledCircleChart_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons] using hl

/-- An actual uniform embedded normal tube around the actual quotient seam. -/
theorem seamNormalNative_exists_embedded_strip {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L)
    (hreg : ∀ s, deriv γ s ≠ 0) (hi : Function.Injective hL.lift) :
    ∃ r > 0, InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r) ∧
      Topology.IsEmbedding (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-r) r) =>
        seamNormalNative γ hL p) := by
  apply exists_thinBand_embedding (seamNormalNative_continuous hγ hL) ?_
    (seamNormalNative_locally_injective hγ hL hreg)
  intro p q hpq
  apply hi
  apply seamComplexCoord.injective
  simpa only [seamNormalNative,zero_smul,add_zero] using hpq

end
end TightVer401
