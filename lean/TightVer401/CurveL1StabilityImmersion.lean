import TightVer401.CurveL1StabilityCircle
import TightVer401.PeriodProjectionDifferential

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem speedCurve_fderiv_injective {a : ℝ → ℝ} {P : ℝ → E}
    (ha : Continuous a) (hP : Continuous P) (hapos : ∀ x, 0 < a x)
    (hne : ∀ x, P x ≠ 0) (s : ℝ) : Function.Injective (fderiv ℝ (speedCurve a P) s) := by
  have hd := rawPrimitive_hasDerivAt (ha.smul hP) s
  have hfd : fderiv ℝ (speedCurve a P) s =
      ContinuousLinearMap.toSpanSingleton ℝ (a s • P s) := hd.hasFDerivAt.fderiv
  have hnonzero : a s • P s ≠ 0 := smul_ne_zero (hapos s).ne' (hne s)
  intro v z hvz
  rw [hfd] at hvz
  change v • (a s • P s) = z • (a s • P s) at hvz
  have he : v • (a s • P s) = z • (a s • P s) := hvz
  have hz : (v - z) • (a s • P s) = 0 := by rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp hz with hv | hp
  · exact sub_eq_zero.mp hv
  · exact False.elim (hnonzero hp)

theorem speedCurve_circle_mfderiv_injective {L : ℝ} [Fact (0 < L)]
    {a : ℝ → ℝ} {P : ℝ → E} (ha : ContDiff ℝ ∞ a) (hP : ContDiff ℝ ∞ P)
    (hapos : ∀ x, 0 < a x) (hne : ∀ x, P x ≠ 0)
    (hp : Function.Periodic (speedCurve a P) L) (q : AddCircle L) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift q) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hraw : ContDiff ℝ ∞ (speedCurve a P) := rawPrimitive_contDiff (ha.smul hP)
  have hC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := periodicLift_contMDiff hraw hp
  have hc : hp.lift ∘ periodProjection L = speedCurve a P := by
    funext s
    exact hp.lift_coe s
  have hchain := mfderiv_comp s (hC.mdifferentiableAt (by simp))
    ((periodProjection_contMDiff L s).mdifferentiableAt (by simp))
  rw [hc, mfderiv_eq_fderiv] at hchain
  have hsurj := periodProjection_mfderiv_surjective L s
  have hinj := speedCurve_fderiv_injective ha.continuous hP.continuous hapos hne s
  intro v z hvz
  obtain ⟨v₀, hv₀⟩ := hsurj v
  obtain ⟨z₀, hz₀⟩ := hsurj z
  have hvchain : fderiv ℝ (speedCurve a P) s v₀ =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s) v := by
    have h := congrArg (fun A : ℝ →L[ℝ] E => A v₀) hchain
    change fderiv ℝ (speedCurve a P) s v₀ =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s v₀) at h
    exact h.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)) hv₀)
  have hzchain : fderiv ℝ (speedCurve a P) s z₀ =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s) z := by
    have h := congrArg (fun A : ℝ →L[ℝ] E => A z₀) hchain
    change fderiv ℝ (speedCurve a P) s z₀ =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s z₀) at h
    exact h.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)) hz₀)
  have he : v₀ = z₀ := hinj (hvchain.trans (hvz.trans hzchain.symm))
  rw [← hv₀, ← hz₀, he]

end
end TightVer401
