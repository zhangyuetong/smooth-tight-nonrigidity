import TightVer401.ProfileTranslation

/-! The complete supported-kernel statement on the actual periodic band.
The frame hypotheses contain only ordinary smooth periodic curve data,
orthonormality and the displayed frame derivative equations. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem ruled_supported_kernel {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hb : 0 < b) :
    ((∃ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0) ↔
      (∫ s in 0..L, ruledPeriodCoefficient d.k d.τ s) = 0) ∧
    ((∫ s in 0..L, ruledPeriodCoefficient d.k d.τ s) = 0 →
      ∃ (W : ℝ → ℝ) (hWL : Function.Periodic W L) (cb : ℝ),
        ContDiff ℝ ∞ W ∧
        (∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s) ∧
        (∀ s, 1 / (ruledRho d.τ s * b) - W s ≤ cb) ∧
        (∃ s, 1 / (ruledRho d.τ s * b) - W s = cb) ∧
        ∀ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
          (IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y) ↔
            ∃! F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
              tsupport F ⊆ Ioi cb ∧ Y = d.profile (F := F) hWL) := by
  refine ⟨ruled_band_supported_bending_iff_period_zero d hb, ?_⟩
  intro hperiod
  obtain ⟨W, hWs, hWL, hW⟩ :=
    (ruled_period_zero_iff_periodic_primitive d.smooth_k d.smooth_τ
      d.torsion_ne_zero d.period_k d.period_τ).mp hperiod
  obtain ⟨cb, hmax, hattained⟩ := periodic_ruled_cutoff d hWs hWL hb
  refine ⟨W, hWL, cb, hWs, hW, hmax, hattained, fun Y => ?_⟩
  constructor
  · rintro ⟨hY, hcompact⟩
    exact ruled_band_supported_kernel_classification_any_primitive
      d hWL hW hb hmax hattained hY hcompact
  · rintro ⟨F, ⟨hFs, hFc, hsupport, hY⟩, _⟩
    rw [hY]
    exact ruled_band_profile_supported d hWs hWL hW hb hmax hFs hFc hsupport

end
end TightVer401
