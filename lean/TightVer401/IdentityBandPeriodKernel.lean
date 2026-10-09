import TightVer401.NormalLoopCriterionGeometry
import TightVer401.RuledBandSufficiency
import TightVer401.RuledBandClassification

/-! Actual identity return forces the characteristic period to vanish, and
therefore supplies the nonzero localized bending and its profile classification. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem periodicRuledFrame_identity_band_period_zero {T : ℝ}
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d) :
    (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0 := by
  obtain ⟨δ₀, hδ₀, hf₀⟩ := hidentity.2.2.2.2 0
  obtain ⟨δ₁, hδ₁, hf₁⟩ := ruled_flow_over_period (s := (0 : ℝ))
    d.smooth_k d.smooth_τ d.torsion_ne_zero d.period_k d.period_τ
  let v := min δ₀ δ₁ / 2
  have hv : 0 < v := half_pos (lt_min hδ₀ hδ₁)
  have hv₀ : |v| < δ₀ := by
    rw [abs_of_pos hv]
    exact (half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_left _ _)
  have hv₁ : |v| < δ₁ := by
    rw [abs_of_pos hv]
    exact (half_lt_self (lt_min hδ₀ hδ₁)).trans_le (min_le_right _ _)
  have hr₀ := (hf₀ v hv₀).2.2.2
  have hr₁ := (hf₁ v hv₁).2.2
  have hfixed : projectiveReturn
      (ruledRho d.τ 0 * (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s)) v = v :=
    hr₁.symm.trans hr₀
  have hden : 1 + (ruledRho d.τ 0 *
      (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s)) * v ≠ 0 := by
    intro hz
    have hh := hfixed
    simp only [projectiveReturn, hz, div_zero] at hh
    exact hv.ne' hh.symm
  have hz := (projectiveReturn_fixed_iff _ v hv.ne' hden).mp hfixed
  exact (mul_eq_zero.mp hz).resolve_left (ruledRho_pos (d.torsion_ne_zero 0)).ne'

theorem periodicRuledFrame_identity_band_iff_period_zero {T : ℝ}
    (d : PeriodicRuledFrame T) :
    PrincipalNormalIdentityBand d ↔
      (∫ s in 0..T, ruledPeriodCoefficient d.k d.τ s) = 0 :=
  ⟨periodicRuledFrame_identity_band_period_zero d, periodicRuledFrame_identity_band d⟩

theorem periodicRuledFrame_identity_band_localized_bending {T b : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d) (hb : 0 < b) :
    ∃ Y : AddCircle T × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0 :=
  ruled_band_period_zero_suffices d hb (periodicRuledFrame_identity_band_period_zero d hidentity)

theorem periodicRuledFrame_identity_band_omega {T : ℝ}
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d) :
    ContDiff ℝ ∞ (ruledOmega d.k d.τ) ∧ Function.Periodic (ruledOmega d.k d.τ) T ∧
      ruledOmega d.k d.τ 0 = 0 := by
  refine ⟨rawPrimitive_contDiff
    (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero), ?_, ?_⟩
  · intro s
    have h := ruledOmega_increment d.smooth_k d.smooth_τ d.torsion_ne_zero
      d.period_k d.period_τ s
    rw [periodicRuledFrame_identity_band_period_zero d hidentity] at h
    exact sub_eq_zero.mp h
  · simp [ruledOmega, rawPrimitive]

/-- An attained cutoff and the full unique supported-profile description for
the same actual band; nonzero bending existence is a conclusion. -/
theorem periodicRuledFrame_identity_band_supported_kernel {T b : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d) (hb : 0 < b) :
    ∃ hWL : Function.Periodic (ruledOmega d.k d.τ) T,
      ∃ cb : ℝ,
        (∀ s, 1 / (ruledRho d.τ s * b) - ruledOmega d.k d.τ s ≤ cb) ∧
        (∃ s, 1 / (ruledRho d.τ s * b) - ruledOmega d.k d.τ s = cb) ∧
        (∃ Y : AddCircle T × Ioo (0 : ℝ) b → Ambient,
          IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0) ∧
        ∀ Y : AddCircle T × Ioo (0 : ℝ) b → Ambient,
          (IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y) ↔
          ∃! F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ioi cb ∧
            Y = d.profile (F := F) hWL := by
  obtain ⟨hWs, hWL, hW0⟩ := periodicRuledFrame_identity_band_omega d hidentity
  obtain ⟨cb, hmax, hattained⟩ := periodic_ruled_cutoff d hWs hWL hb
  refine ⟨hWL, cb, hmax, hattained,
    periodicRuledFrame_identity_band_localized_bending d hidentity hb, fun Y => ?_⟩
  constructor
  · intro hY
    exact ruled_band_supported_kernel_classification d hWL
      (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero) hW0
      hb hmax hattained hY.1 hY.2
  · rintro ⟨F, hFs, _hunique⟩
    rw [hFs.2.2.2]
    exact ruled_band_profile_supported d hWs hWL
      (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero)
      hb hmax hFs.1 hFs.2.1 hFs.2.2.1

end
end TightVer401
