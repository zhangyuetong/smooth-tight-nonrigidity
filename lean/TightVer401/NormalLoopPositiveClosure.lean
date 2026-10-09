import TightVer401.NormalLoopPositiveSpeed
import TightVer401.NormalLoopActual

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Set MeasureTheory
open scoped ContDiff Topology Manifold

theorem exists_positive_periodic_closing_speed_of_real_origin_interior {m : ℕ}
    {L : ℝ} (hL : 0 < L) {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hf : ContDiff ℝ ∞ f) (hperiod : Function.Periodic f L)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range f))) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
      (∀ s, 0 < b s) ∧ momentPathMoment L f b = 0 := by
  letI : Fact (0 < L) := ⟨hL⟩
  letI := periodCircleChartedSpace L
  let F := hperiod.lift
  have hF : Continuous F := (periodicLift_contMDiff hf hperiod).continuous
  have he : F ∘ periodProjection L = f := funext (periodicLift_coe hperiod)
  have hrange : Set.range F = Set.range f := by
    apply Subset.antisymm
    · rintro _ ⟨q, rfl⟩
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
      exact ⟨s, (periodicLift_coe hperiod s).symm⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨periodProjection L s, periodicLift_coe hperiod s⟩
  have hFsmooth : ContDiff ℝ ∞ (F ∘ periodProjection L) := he.symm ▸ hf
  have h0F : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (convexHull ℝ (Set.range F)) :=
    hrange.symm ▸ h0
  obtain ⟨b, hb, hbp, hpos, hm⟩ :=
    exists_positive_periodic_closing_speed_of_origin_interior L hF hFsmooth h0F
  exact ⟨b, hb, hbp, hpos, he ▸ hm⟩

theorem normalLoop_origin_interior_positive_closing_speed {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (h0 : (0 : Ambient) ∈ interior (convexHull ℝ (Set.range (normalLoopTangent ζ)))) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
      (∀ r, 0 < b r) ∧ normalLoopMoment b ζ (deriv ζ) L = 0 := by
  obtain ⟨b, hb, hbp, hpos, hm⟩ :=
    exists_positive_periodic_closing_speed_of_real_origin_interior hL
      (normalLoop_actual_smooth hζ).1 (normalLoop_actual_periodic hζ hζL).1 h0
  refine ⟨b, hb, hbp, hpos, ?_⟩
  simpa only [momentPathMoment, normalLoopMoment, normalLoopTangent] using hm

theorem normalLoop_origin_interior_closed_curve {ζ : ℝ → Ambient}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (h0 : (0 : Ambient) ∈ interior (convexHull ℝ (Set.range (normalLoopTangent ζ)))) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ Function.Periodic b L ∧
      (∀ r, 0 < b r) ∧ Function.Periodic (normalLoopCurve b ζ (deriv ζ)) L := by
  obtain ⟨b, hb, hbp, hpos, hm⟩ :=
    normalLoop_origin_interior_positive_closing_speed hζ hζL hL h0
  refine ⟨b, hb, hbp, hpos, ?_⟩
  exact (normalLoopCurve_periodic_iff hb.continuous hζ (contDiff_infty_iff_deriv.mp hζ).2
    hbp hζL (normalLoop_derivative_periodic hζL
      (fun r => ((contDiff_infty_iff_deriv.mp hζ).1 r).hasDerivAt))).mpr hm

end
end TightVer401
