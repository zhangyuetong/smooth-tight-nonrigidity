import TightVer401.FermiNormalGeometry
import TightVer401.ThinBandRuledCharts
import TightVer401.ThinBandLocalCalculus
import TightVer401.ThinBandTopology

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

def fermiNativeMap {L : ℝ} (ζ : ℝ → Ambient) (hζ : ContDiff ℝ ∞ ζ)
    (hζL : Function.Periodic ζ L) (p : AddCircle L × ℝ) : Ambient :=
  Real.cos p.2 • hζL.lift p.1 +
    Real.sin p.2 • (normalLoop_actual_periodic hζ hζL).1.lift p.1

theorem fermiNativeMap_chart {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (r : ℝ) (p : Coord) :
    fermiNativeMap ζ hζ hζL (ruledCircleChart L r p) = fermiNormalMap ζ p := by
  simp only [fermiNativeMap, ruledCircleChart_apply, periodicLift_coe, fermiNormalMap]

theorem fermiNativeMap_contMDiff {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
      (fermiNativeMap ζ hζ hζL) := by
  have hc := Real.contDiff_cos.contMDiff.comp
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : AddCircle L × ℝ → ℝ))
  have hs := Real.contDiff_sin.contMDiff.comp
    (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.snd : AddCircle L × ℝ → ℝ))
  have hz := (periodicLift_contMDiff hζ hζL).comp
    (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : AddCircle L × ℝ → AddCircle L))
  have hP := (periodicLift_contMDiff (normalLoop_actual_smooth hζ).1
    (normalLoop_actual_periodic hζ hζL).1).comp
      (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (Prod.fst : AddCircle L × ℝ → AddCircle L))
  exact (hc.smul hz).add (hs.smul hP)

theorem fermiNormalMap_central_differential_injective {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (r : ℝ) :
    Function.Injective (fderiv ℝ (fermiNormalMap ζ) (![r, 0] : Coord)) := by
  intro v w hvw
  have hz : fderiv ℝ (fermiNormalMap ζ) (![r, 0] : Coord) (v - w) = 0 := by
    simp [map_sub, hvw]
  have he := inducedMetric_bilinear (fermiNormalMap ζ) (![r, 0] : Coord) (v - w) (v - w)
  rw [hz, inner_zero_left, fermiNormalMap_metric hζ hunit hspeed] at he
  simp only [fermiNormalScale, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Real.cos_zero, Real.sin_zero, mul_zero, add_zero, one_pow,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two, zero_mul, one_mul, zero_add] at he
  norm_num at he
  have h0 : (v - w) 0 = 0 := by
    change v 0 - w 0 = 0
    nlinarith [sq_nonneg (v 1 - w 1)]
  have h1 : (v - w) 1 = 0 := by
    change v 1 - w 1 = 0
    nlinarith [sq_nonneg (v 0 - w 0)]
  apply sub_eq_zero.mp
  ext i
  fin_cases i <;> assumption

theorem fermiNativeMap_locally_injective {L : ℝ} [Fact (0 < L)] {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (q : AddCircle L) :
    ∃ U ∈ 𝓝 (q, (0 : ℝ)), InjOn (fermiNativeMap ζ hζ hζL) U := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ U ∈ 𝓝 (periodProjection L r, (0 : ℝ)), InjOn (fermiNativeMap ζ hζ hζL) U
  have hlocal := exists_local_injOn_of_injective_strictFDeriv
    ((fermiNormalMap_contDiff hζ).hasStrictFDerivAt (x := (![r, 0] : Coord)) (by simp))
    (fermiNormalMap_central_differential_injective hζ hunit hspeed r)
  have hl := local_injOn_transport_chart (ruledCircleChart_center_source L r)
    (fun p _ => fermiNativeMap_chart hζ hζL r p) hlocal
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hl

theorem fermiNativeMap_exists_thin_embedded_strip {L : ℝ} [Fact (0 < L)]
    {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζL.lift) :
    ∃ ε > 0, InjOn (fermiNativeMap ζ hζ hζL) (univ ×ˢ Icc (-ε) ε) ∧
      Topology.IsEmbedding (fun p : ↥((univ : Set (AddCircle L)) ×ˢ Ioo (-ε) ε) =>
        fermiNativeMap ζ hζ hζL p) := by
  apply exists_thinBand_embedding (fermiNativeMap_contMDiff hζ hζL).continuous ?_
    (fermiNativeMap_locally_injective hζ hζL hunit hspeed)
  intro x y he
  apply hi
  simpa only [fermiNativeMap, Real.cos_zero, Real.sin_zero, one_smul,
    zero_smul, add_zero] using he

end
end TightVer401
