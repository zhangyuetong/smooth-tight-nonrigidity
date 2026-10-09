import TightVer401.PeriodicRuledBending
import TightVer401.PeriodicBandInjectivity

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold

theorem ruled_band_period_zero_suffices {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hb : 0 < b)
    (hperiod : (∫ s in 0..L, ruledPeriodCoefficient d.k d.τ s) = 0) :
    ∃ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0 := by
  obtain ⟨W, hWs, hWL, hW⟩ :=
    (ruled_period_zero_iff_periodic_primitive d.smooth_k d.smooth_τ d.torsion_ne_zero
      d.period_k d.period_τ).mp hperiod
  let hρL := ruledRho_periodic d.period_τ
  have hρs := ruledRho_contDiff d.smooth_τ d.torsion_ne_zero
  have hρpos : ∀ s, 0 < ruledRho d.τ s := fun s => ruledRho_pos (d.torsion_ne_zero s)
  have hρlift : ∀ a : AddCircle L, 0 < hρL.lift a := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact hρpos s
  obtain ⟨cb, hmax, _⟩ := exists_band_cutoff (periodicLift_contMDiff hρs hρL).continuous
    (periodicLift_contMDiff hWs hWL).continuous hρlift hb
  have hmaxReal (s : ℝ) : 1 / (ruledRho d.τ s * b) - W s ≤ cb :=
    hmax (periodProjection L s)
  obtain ⟨F, hFs, hFc, hFsupport, hFvalue⟩ := exists_nonzero_compact_profile_above cb
  refine ⟨d.profile (F := F) hWL,
    periodic_ruled_profile_isBandBending d hWL hWs hW hFs, ?_, ?_⟩
  · apply periodic_bandProfile_hasCompactSupport hρs hWs d.period_k d.period_τ hρL hWL
      d.period_T d.period_n hρpos hb hFc
    intro s c hc
    exact (hmaxReal s).trans_lt (hFsupport hc)
  · apply periodic_bandProfile_nonzero d.period_k d.period_τ hρL hWL d.period_T d.period_n
      (d.orthonormal 0) (d.torsion_ne_zero 0) (hρpos 0) hb (hmaxReal 0)
      (show cb < cb + 2 by linarith)
    rw [hFvalue]
    norm_num

end
end TightVer401
