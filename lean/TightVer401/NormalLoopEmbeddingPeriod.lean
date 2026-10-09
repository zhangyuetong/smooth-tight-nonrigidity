import TightVer401.CurveL1StabilityImmersion

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem periodicCurve_lift_injective {L : ℝ} [Fact (0 < L)] {f : ℝ → E}
    (hp : Function.Periodic f L) (hi : Set.InjOn f (Ico 0 L)) : Function.Injective hp.lift := by
  intro q r he
  let x := AddCircle.equivIco L 0 q
  let y := AddCircle.equivIco L 0 r
  have hx : (x : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using x.property
  have hy : (y : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using y.property
  have hxq : periodProjection L (x : ℝ) = q := AddCircle.coe_equivIco
  have hyr : periodProjection L (y : ℝ) = r := AddCircle.coe_equivIco
  have hqx : hp.lift q = f (x : ℝ) := by rw [← hxq]; exact hp.lift_coe _
  have hry : hp.lift r = f (y : ℝ) := by rw [← hyr]; exact hp.lift_coe _
  have hxy := hi hx hy (hqx.symm.trans (he.trans hry))
  rw [← hxq, ← hyr, hxy]

theorem periodicCurve_lift_embedding {L : ℝ} [Fact (0 < L)] {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) (hi : Set.InjOn f (Ico 0 L)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift ∧ Topology.IsEmbedding hp.lift := by
  have hC := periodicLift_contMDiff hf hp
  exact ⟨hC, (hC.continuous.isClosedEmbedding (periodicCurve_lift_injective hp hi)).isEmbedding⟩

theorem periodicCurve_lift_mfderiv_injective {L : ℝ} [Fact (0 < L)] {f : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (hderiv : ∀ s, deriv f s ≠ 0) (q : AddCircle L) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift q) := by
  have hinj (s : ℝ) : Function.Injective (fderiv ℝ f s) := by
    have hd := (hf.differentiable (by simp) s).hasDerivAt.hasFDerivAt.fderiv
    intro v z he
    rw [hd] at he
    change v • deriv f s = z • deriv f s at he
    have hz : (v - z) • deriv f s = 0 := by rw [sub_smul, he, sub_self]
    rcases smul_eq_zero.mp hz with hv | hv
    · exact sub_eq_zero.mp hv
    · exact False.elim (hderiv s hv)
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ hp.lift := periodicLift_contMDiff hf hp
  have hc : hp.lift ∘ periodProjection L = f := funext hp.lift_coe
  have hchain := mfderiv_comp s (hC.mdifferentiableAt (by simp))
    ((periodProjection_contMDiff L s).mdifferentiableAt (by simp))
  rw [hc, mfderiv_eq_fderiv] at hchain
  intro v z hvz
  obtain ⟨v₀, hv₀⟩ := periodProjection_mfderiv_surjective L s v
  obtain ⟨z₀, hz₀⟩ := periodProjection_mfderiv_surjective L s z
  have hvchain : fderiv ℝ f s v₀ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s) v := by
    have h := congrArg (fun A : ℝ →L[ℝ] E => A v₀) hchain
    change fderiv ℝ f s v₀ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s v₀) at h
    exact h.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)) hv₀)
  have hzchain : fderiv ℝ f s z₀ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s) z := by
    have h := congrArg (fun A : ℝ →L[ℝ] E => A z₀) hchain
    change fderiv ℝ f s z₀ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (periodProjection L) s z₀) at h
    exact h.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) hp.lift (periodProjection L s)) hz₀)
  have he : v₀ = z₀ := hinj s (hvchain.trans (hvz.trans hzchain.symm))
  rw [← hv₀, ← hz₀, he]

end
end TightVer401
