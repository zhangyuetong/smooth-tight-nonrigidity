import TightVer401.BandLiftStrain
import TightVer401.RuledVectorNecessity
import TightVer401.RuledBandSufficiency

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff

theorem ruled_band_period_zero_necessary {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hb : 0 < b)
    {Y : AddCircle L × Ioo (0 : ℝ) b → Ambient}
    (hY : IsBandBending (d.bandMap (b := b)) Y) (hcompact : HasCompactSupport Y)
    (hne : ∃ p, Y p ≠ 0) : (∫ r in 0..L, ruledPeriodCoefficient d.k d.τ r) = 0 := by
  obtain ⟨lower, upper, hlower, hlu, hub, hsupport⟩ := compact_band_support_uniform_bounds hb hcompact
  have hYs := bandCoordinateLift_contDiff hY.1 hlower hub hsupport
  have hstrain := bandCoordinateLift_zero_strain d hY hlower hub hsupport
  obtain ⟨p, hp⟩ := hne
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let q : Coord := ![s, (p.2 : ℝ)]
  have hqb : q 1 ∈ Ioo 0 b := p.2.property
  have hq : bandCoordinateLift Y q = Y p := by
    rw [bandCoordinateLift, dif_pos hqb]
    change Y (periodProjection L s, p.2) = Y p
    have hs' : periodProjection L s = p.1 := hs
    rw [hs']
  apply supported_ruled_vector_period_zero d hYs hlower (hlower.trans hlu)
    (bandCoordinateLift_periodic Y) (fun r _ => hstrain r)
    (fun r hr => bandCoordinateLift_support_bounds hsupport hr) hqb.1
  rw [hq]
  exact hp

theorem ruled_band_supported_bending_iff_period_zero {L b : ℝ} [Fact (0 < L)]
    (d : PeriodicRuledFrame L) (hb : 0 < b) :
    (∃ Y : AddCircle L × Ioo (0 : ℝ) b → Ambient,
      IsBandBending (d.bandMap (b := b)) Y ∧ HasCompactSupport Y ∧ ∃ p, Y p ≠ 0) ↔
      (∫ r in 0..L, ruledPeriodCoefficient d.k d.τ r) = 0 := by
  constructor
  · rintro ⟨Y, hY, hc, hn⟩
    exact ruled_band_period_zero_necessary d hb hY hc hn
  · exact ruled_band_period_zero_suffices d hb

end
end TightVer401
