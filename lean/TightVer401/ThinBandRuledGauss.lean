import TightVer401.ThinBandRuledCharts
import TightVer401.ThinBandLocalCalculus
import TightVer401.ThinBandTopology
import TightVer401.GaussMapDifferential

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def PeriodicRuledFrame.rawGaussMap {L : ℝ} (d : PeriodicRuledFrame L) (p : Coord) : Ambient :=
  ruledNormal (d.T (p 0)) (d.n (p 0)) (d.k (p 0)) (d.τ (p 0)) (p 1)

def PeriodicRuledFrame.fullGaussMap {L : ℝ} (d : PeriodicRuledFrame L)
    (p : AddCircle L × ℝ) : Ambient :=
  ruledNormal (d.period_T.lift p.1) (d.period_n.lift p.1)
    (d.period_k.lift p.1) (d.period_τ.lift p.1) p.2

theorem periodicRuledFrame_rawGaussMap_contDiff {L : ℝ} (d : PeriodicRuledFrame L) :
    ContDiff ℝ ∞ d.rawGaussMap := by
  have hk := d.smooth_k.comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hτ := d.smooth_τ.comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hu : ContDiff ℝ ∞ (fun p : Coord => p 1) := contDiff_apply ℝ ℝ (1 : Fin 2)
  have henergy : ContDiff ℝ ∞ (fun p : Coord => ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) := by
    unfold ruledEnergy
    fun_prop
  have hroot := henergy.sqrt (fun p => (ruledEnergy_pos (d.torsion_ne_zero (p 0))).ne')
  have hrootne (p : Coord) : Real.sqrt (ruledEnergy (d.k (p 0)) (d.τ (p 0)) (p 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (ruledEnergy_pos (d.torsion_ne_zero (p 0)))).ne'
  exact (((hτ.neg.mul hu).div hroot hrootne).smul
    (d.smooth_T.comp (contDiff_apply ℝ ℝ 0))).add
    (((contDiff_const.sub (hk.mul hu)).div hroot hrootne).smul
      (d.smooth_n.comp (contDiff_apply ℝ ℝ 0)))

theorem periodicRuledFrame_fullGaussMap_continuous {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) : Continuous d.fullGaussMap := by
  have hT : Continuous (fun p : AddCircle L × ℝ => d.period_T.lift p.1) :=
    (periodicLift_contMDiff d.smooth_T d.period_T).continuous.comp continuous_fst
  have hn : Continuous (fun p : AddCircle L × ℝ => d.period_n.lift p.1) :=
    (periodicLift_contMDiff d.smooth_n d.period_n).continuous.comp continuous_fst
  have hk : Continuous (fun p : AddCircle L × ℝ => d.period_k.lift p.1) :=
    (periodicLift_contMDiff d.smooth_k d.period_k).continuous.comp continuous_fst
  have hτ : Continuous (fun p : AddCircle L × ℝ => d.period_τ.lift p.1) :=
    (periodicLift_contMDiff d.smooth_τ d.period_τ).continuous.comp continuous_fst
  have hτne (q : AddCircle L) : d.period_τ.lift q ≠ 0 := by
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa only [Function.Periodic.lift_coe] using d.torsion_ne_zero r
  have henergy : Continuous (fun p : AddCircle L × ℝ =>
      ruledEnergy (d.period_k.lift p.1) (d.period_τ.lift p.1) p.2) := by
    unfold ruledEnergy
    fun_prop
  have hroot := henergy.sqrt
  have hrootne (p : AddCircle L × ℝ) :
      Real.sqrt (ruledEnergy (d.period_k.lift p.1) (d.period_τ.lift p.1) p.2) ≠ 0 :=
    (Real.sqrt_pos.mpr (ruledEnergy_pos (hτne p.1))).ne'
  exact (((hτ.neg.mul continuous_snd).div hroot hrootne).smul hT).add
    (((continuous_const.sub (hk.mul continuous_snd)).div hroot hrootne).smul hn)

theorem ruledCircleChart_fullGaussMap {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (r : ℝ) (p : Coord) :
    d.fullGaussMap (ruledCircleChart L r p) = d.rawGaussMap p := by
  rw [ruledCircleChart_apply]
  simp only [PeriodicRuledFrame.fullGaussMap, PeriodicRuledFrame.rawGaussMap, periodicLift_coe]

theorem periodicRuledFrame_rawGaussMap_differential_injective {L : ℝ}
    (d : PeriodicRuledFrame L) (p : Coord) : Function.Injective (fderiv ℝ d.rawGaussMap p) := by
  have hX : ContDiff ℝ ∞ (ruledMap d.γ d.E) :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  apply gaussMap_differential_injective_of_second_form hX.contDiffOn
    (periodicRuledFrame_rawGaussMap_contDiff d).contDiffOn isOpen_univ
    (fun q _ => ruled_isUnitNormal (d.deriv_γ (q 0)) (d.deriv_E (q 0))
      (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))) (mem_univ p)
  unfold PeriodicRuledFrame.rawGaussMap
  rw [ruled_second_form_det d.deriv_γ d.deriv_E hX.contDiffOn isOpen_univ
    (mem_univ p) (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (d.torsion_ne_zero (p 0))))
    (ruledEnergy_pos (d.torsion_ne_zero (p 0))).ne'

theorem periodicRuledFrame_fullGaussMap_locally_injective {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (q : AddCircle L) :
    ∃ U ∈ 𝓝 (q, (0 : ℝ)), Set.InjOn d.fullGaussMap U := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ∃ U ∈ 𝓝 (periodProjection L r, (0 : ℝ)), Set.InjOn d.fullGaussMap U
  have hlocal := exists_local_injOn_of_injective_strictFDeriv
    ((periodicRuledFrame_rawGaussMap_contDiff d).hasStrictFDerivAt
      (x := (![r, 0] : Coord)) (by simp))
    (periodicRuledFrame_rawGaussMap_differential_injective d (![r, 0]))
  have hl := local_injOn_transport_chart (ruledCircleChart_center_source L r)
    (fun p _ => ruledCircleChart_fullGaussMap d r p) hlocal
  simpa only [ruledCircleChart_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hl

theorem periodicRuledFrame_exists_thin_Gauss_injective {L : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hi : Function.Injective d.period_n.lift) :
    ∃ δ > 0, Set.InjOn d.fullGaussMap (univ ×ˢ Icc (-δ) δ) := by
  apply exists_thinBand_injective (periodicRuledFrame_fullGaussMap_continuous d) ?_
    (periodicRuledFrame_fullGaussMap_locally_injective d)
  intro x y he
  apply hi
  simpa only [PeriodicRuledFrame.fullGaussMap, ruledNormal, ruledEnergy, mul_zero,
    sub_zero, zero_pow (by decide : 2 ≠ 0), one_pow, zero_mul, add_zero, Real.sqrt_one,
    zero_div, zero_smul, one_div, inv_one, one_smul, zero_add] using he

end
end TightVer401
