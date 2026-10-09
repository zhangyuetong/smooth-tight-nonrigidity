import TightVer401.MomentPrescription
import TightVer401.PeriodCircleInstances

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_periodic {m : ℕ} {L : ℝ} [Fact (0 < L)]
    {f : ℝ → EuclideanSpace ℝ (Fin m)} {g b : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hb : ContDiff ℝ ∞ b)
    (hfL : Function.Periodic f L) (hgL : Function.Periodic g L)
    (hbL : Function.Periodic b L) (hbpos : ∀ r, 0 < b r)
    (hgpos : ∃ r, 0 < g r) (hgneg : ∃ r, g r < 0) (B : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧
      momentPathMoment L f a = momentPathMoment L f b ∧ momentNonlinearPeriod a g L = B := by
  let fCircle := hfL.lift
  let gCircle := hgL.lift
  let bCircle := hbL.lift
  have hfRep : fCircle ∘ periodProjection L = f := funext hfL.lift_coe
  have hgRep : gCircle ∘ periodProjection L = g := funext hgL.lift_coe
  have hbRep : bCircle ∘ periodProjection L = b := funext hbL.lift_coe
  have hfEq (r) : fCircle (periodProjection L r) = f r := congrFun hfRep r
  have hgEq (r) : gCircle (periodProjection L r) = g r := congrFun hgRep r
  have hbEq (r) : bCircle (periodProjection L r) = b r := congrFun hbRep r
  have hbCircle : ∀ q, 0 < bCircle q := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hbpos r
  have hgCirclePos : ∃ q, 0 < gCircle q := by
    obtain ⟨r, hr⟩ := hgpos
    exact ⟨periodProjection L r, by simpa only [hgEq] using hr⟩
  have hgCircleNeg : ∃ q, gCircle q < 0 := by
    obtain ⟨r, hr⟩ := hgneg
    exact ⟨periodProjection L r, by simpa only [hgEq] using hr⟩
  obtain ⟨A, hA, hApos, hsmall, hmoment, htarget, _harcs⟩ :=
    finite_moment_period_prescription L fCircle gCircle bCircle
      (periodicLift_contMDiff hf hfL).continuous (hfRep.symm ▸ hf)
      (periodicLift_contMDiff hg hgL).continuous (hbRep.symm ▸ hb)
      hbCircle hgCirclePos hgCircleNeg B hη (show 0 < (1 : ℝ) by norm_num)
  let a := A ∘ periodProjection L
  refine ⟨a, (hA.comp (periodProjection_contMDiff L)).contDiff, ?_,
    fun r => hApos _, ?_, ?_, ?_⟩
  · intro r
    change A ((r + L : ℝ) : AddCircle L) = A (r : AddCircle L)
    rw [AddCircle.coe_add_period]
  · simpa only [a, Function.comp_apply, hbEq] using hsmall
  · simpa only [momentPathMoment, a, Function.comp_apply, hfEq, hbEq]
      using hmoment
  · simpa only [momentNonlinearPeriod, a, Function.comp_apply, hgEq] using htarget

end
end TightVer401
