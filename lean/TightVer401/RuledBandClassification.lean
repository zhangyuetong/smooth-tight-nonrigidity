import TightVer401.RuledBandNecessity
import TightVer401.RuledVectorClassification

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold

theorem bandCoordinateLift_real_value {L b : ℝ}
    (Y : AddCircle L × Ioo (0 : ℝ) b → Ambient) (s : ℝ) (u : Ioo (0 : ℝ) b) :
    bandCoordinateLift Y (![s, (u : ℝ)] : Coord) = Y (periodProjection L s, u) := by
  have hu : (![s, (u : ℝ)] : Coord) 1 ∈ Ioo 0 b := u.property
  rw [bandCoordinateLift, dif_pos hu]
  rfl

theorem periodic_ruled_cutoff {L b : ℝ} [Fact (0 < L)] (d : PeriodicRuledFrame L)
    {W : ℝ → ℝ} (hWs : ContDiff ℝ ∞ W) (hWL : Function.Periodic W L) (hb : 0 < b) :
    ∃ cb : ℝ, (∀ s, 1 / (ruledRho d.τ s * b) - W s ≤ cb) ∧
      ∃ s, 1 / (ruledRho d.τ s * b) - W s = cb := by
  let hρL := ruledRho_periodic d.period_τ
  have hρpos : ∀ a : AddCircle L, 0 < hρL.lift a := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    exact ruledRho_pos (d.torsion_ne_zero s)
  obtain ⟨cb, hmax, a, ha⟩ := exists_band_cutoff
    (periodicLift_contMDiff (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) hρL).continuous
    (periodicLift_contMDiff hWs hWL).continuous hρpos hb
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact ⟨cb, fun t => hmax (periodProjection L t), s, ha⟩

theorem ruled_band_supported_kernel_classification {L b cb : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) {W : ℝ → ℝ} (hWL : Function.Periodic W L)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s) (hW0 : W 0 = 0)
    (hb : 0 < b) (hmax : ∀ s, 1 / (ruledRho d.τ s * b) - W s ≤ cb)
    (hattained : ∃ s, 1 / (ruledRho d.τ s * b) - W s = cb)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hcompact : HasCompactSupport Y) :
    ∃! F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ioi cb ∧
      Y = d.profile (F := F) hWL := by
  obtain ⟨lower, upper, hlower, hlu, hub, hsupport⟩ := compact_band_support_uniform_bounds hb hcompact
  have hYs := bandCoordinateLift_contDiff hY.1 hlower hub hsupport
  have hstrain := bandCoordinateLift_zero_strain d hY hlower hub hsupport
  obtain ⟨F, hFs, hFc, hFsupport, hrep⟩ := supported_ruled_vector_has_profile d hYs hlower
    (hlower.trans hlu) hub (fun p _ => hstrain p)
    (fun p hp => bandCoordinateLift_support_bounds hsupport hp) hW hW0 hattained
  have hYe : Y = d.profile (F := F) hWL := by
    funext p
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
    have h := hrep (![s, (p.2 : ℝ)] : Coord) p.2.property.1
    rw [bandCoordinateLift_real_value] at h
    have hvalue := periodic_bandProfile_real_lift d.period_k d.period_τ
      (ruledRho_periodic d.period_τ) hWL d.period_T d.period_n s p.2 (F := F)
    have hs' : periodProjection L s = p.1 := hs
    rw [hs'] at h hvalue
    exact h.trans hvalue.symm
  refine ⟨F, ⟨hFs, hFc, hFsupport, hYe⟩, ?_⟩
  intro G hG
  exact periodic_bandProfile_injective d.period_k d.period_τ (ruledRho_periodic d.period_τ)
    hWL d.period_T d.period_n (d.orthonormal 0) (d.torsion_ne_zero 0)
    (ruledRho_pos (d.torsion_ne_zero 0)) hb (hmax 0) hG.2.2.1 hFsupport
    (hG.2.2.2.symm.trans hYe)

theorem ruled_band_profile_supported {L b cb : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) {W F : ℝ → ℝ}
    (hWs : ContDiff ℝ ∞ W) (hWL : Function.Periodic W L)
    (hW : ∀ s, HasDerivAt W (ruledPeriodCoefficient d.k d.τ s) s)
    (hb : 0 < b) (hmax : ∀ s, 1 / (ruledRho d.τ s * b) - W s ≤ cb)
    (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hFsupport : tsupport F ⊆ Ioi cb) :
    IsBandBending (d.bandMap (b := b)) (d.profile (F := F) hWL) ∧
      HasCompactSupport (d.profile (b := b) (F := F) hWL) := by
  refine ⟨periodic_ruled_profile_isBandBending d hWL hWs hW hFs, ?_⟩
  apply periodic_bandProfile_hasCompactSupport
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) hWs d.period_k d.period_τ
    (ruledRho_periodic d.period_τ) hWL d.period_T d.period_n
    (fun s => ruledRho_pos (d.torsion_ne_zero s)) hb hFc
  intro s c hc
  exact (hmax s).trans_lt (hFsupport hc)

end
end TightVer401
