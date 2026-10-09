import TightVer401.BandProfileSmooth
import TightVer401.BandCutoff

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

theorem periodic_bandProfile_real_lift {L b : ℝ}
    {k τ ρ W : ℝ → ℝ} {T n : ℝ → Ambient} {F : ℝ → ℝ}
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hρL : Function.Periodic ρ L) (hWL : Function.Periodic W L)
    (hTL : Function.Periodic T L) (hnL : Function.Periodic n L)
    (s : ℝ) (u : Ioo (0 : ℝ) b) :
    bandProfile hkL.lift hτL.lift hρL.lift hWL.lift F hTL.lift hnL.lift
      (periodProjection L s, u) = ruledProfileField k τ ρ W F T n (![s, (u : ℝ)] : Coord) := by
  rfl

theorem periodic_bandProfile_contMDiff {L b : ℝ} [Fact (0 < L)]
    {k τ ρ W : ℝ → ℝ} {T n : ℝ → Ambient} {F : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hτ : ContDiff ℝ ∞ τ) (hρ : ContDiff ℝ ∞ ρ)
    (hW : ContDiff ℝ ∞ W) (hT : ContDiff ℝ ∞ T) (hn : ContDiff ℝ ∞ n)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hρL : Function.Periodic ρ L) (hWL : Function.Periodic W L)
    (hTL : Function.Periodic T L) (hnL : Function.Periodic n L)
    (hρ0 : ∀ s, ρ s ≠ 0) (hF : ContDiff ℝ ∞ F) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
      (bandProfile hkL.lift hτL.lift hρL.lift hWL.lift F hTL.lift hnL.lift (b := b)) := by
  apply bandProfile_contMDiff (periodicLift_contMDiff hk hkL)
    (periodicLift_contMDiff hτ hτL) (periodicLift_contMDiff hρ hρL)
    (periodicLift_contMDiff hW hWL) (periodicLift_contMDiff hT hTL)
    (periodicLift_contMDiff hn hnL) _ hF
  intro a
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  simpa only [hρL.lift_coe] using hρ0 s

theorem periodic_bandProfile_hasCompactSupport {L b : ℝ} [Fact (0 < L)]
    {k τ ρ W : ℝ → ℝ} {T n : ℝ → Ambient} {F : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hW : ContDiff ℝ ∞ W)
    (hkL : Function.Periodic k L) (hτL : Function.Periodic τ L)
    (hρL : Function.Periodic ρ L) (hWL : Function.Periodic W L)
    (hTL : Function.Periodic T L) (hnL : Function.Periodic n L)
    (hρpos : ∀ s, 0 < ρ s) (hb : 0 < b) (hF : HasCompactSupport F)
    (hlevels : ∀ s, ∀ c ∈ tsupport F, 1 / (ρ s * b) - W s < c) :
    HasCompactSupport
      (bandProfile hkL.lift hτL.lift hρL.lift hWL.lift F hTL.lift hnL.lift (b := b)) := by
  have hpos : ∀ a : AddCircle L, 0 < hρL.lift a := by
    intro a
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    simpa only [hρL.lift_coe] using hρpos s
  apply bandProfile_hasCompactSupport (periodicLift_contMDiff hρ hρL).continuous
    (periodicLift_contMDiff hW hWL).continuous hpos hb hF
  intro a c hc
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  simpa only [hρL.lift_coe, hWL.lift_coe] using hlevels s c hc

end
end TightVer401
