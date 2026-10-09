import TightVer401.NormalLoopCriterion
import TightVer401.NormalLoopCriterionImmersion

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive Set MeasureTheory
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- A prescribed immersed band, expressed by actual maps, derivatives and flow.
No moment closure or period cancellation is included as an input field. -/
def NormalLoopPrescribedIdentityBand (ζ : ℝ → Ambient) (L : ℝ) : Prop :=
  ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
    ∃ hT : 0 < rawPrimitive a L,
      ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
        ∃ d : PeriodicRuledFrame (rawPrimitive a L),
          d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
          d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
          d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
          d.τ = normalLoopPhysicalTau a e.symm ∧ PrincipalNormalIdentityBand d ∧
          (letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
           ∀ w : ℝ,
             ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ (d.bandMap (b := w)) ∧
             ∀ p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) w,
               Function.Injective (bandDifferential (d.bandMap (b := w)) p))

theorem normalLoop_closing_speed_identity_band {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hclosing : NormalLoopClosingSpeed ζ L) : NormalLoopPrescribedIdentityBand ζ L := by
  obtain ⟨b, hb, hbL, hbpos, hM⟩ := hclosing
  obtain ⟨a, ha, haL, hapos, _hsmall, _hMa, e, he, hesmooth, d,
    hγ, hT, hE, hn, hk, hτ, hperiod⟩ :=
    normalLoop_construct_balanced_frame hζ hb hunit hspeed hbpos hζL hbL hL hM
      (show 0 < (1 : ℝ) by norm_num)
  have hTpos := normalLoop_arclength_period_pos ha.continuous hapos hL
  refine ⟨a, ha, haL, hapos, hTpos, e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ,
    periodicRuledFrame_identity_band d hperiod, ?_⟩
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  intro w
  exact ⟨d.bandMap_contMDiff, fun p => periodicRuledFrame_bandMap_immersion d p⟩

theorem normalLoop_prescribed_identity_band_closing_speed {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L)
    (hband : NormalLoopPrescribedIdentityBand ζ L) : NormalLoopClosingSpeed ζ L := by
  obtain ⟨a, ha, haL, hapos, _hTpos, e, he, _hesmooth, d,
    hγ, _hT, _hE, _hn, _hk, _hτ, _hgeometry, _hnative⟩ := hband
  have hγpoint (r) : d.γ (e r) = normalLoopCurve a ζ (deriv ζ) r := by
    rw [hγ]
    simp only [Function.comp_apply, e.symm_apply_apply]
  have hshift (r) : e (r + L) = e r + rawPrimitive a L := by
    simpa only [he] using normalLoop_arclength_shift ha.continuous haL r
  have hcurveperiod : Function.Periodic (normalLoopCurve a ζ (deriv ζ)) L := by
    intro r
    calc
      normalLoopCurve a ζ (deriv ζ) (r + L) = d.γ (e (r + L)) := (hγpoint _).symm
      _ = d.γ (e r + rawPrimitive a L) := by rw [hshift]
      _ = d.γ (e r) := d.period_γ _
      _ = normalLoopCurve a ζ (deriv ζ) r := hγpoint r
  refine ⟨a, ha, haL, hapos, ?_⟩
  exact (normalLoopCurve_periodic_iff ha.continuous hζ (contDiff_infty_iff_deriv.mp hζ).2
    haL hζL (normalLoop_derivative_periodic hζL
      (fun r => ((contDiff_infty_iff_deriv.mp hζ).1 r).hasDerivAt))).mp hcurveperiod

theorem normalLoop_prescribed_identity_band_criterion {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) (hL : 0 < L)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) :
    ((0 : Ambient) ∈ interior (convexHull ℝ (range (normalLoopTangent ζ))) ↔
      NormalLoopPrescribedIdentityBand ζ L) ∧
    (NormalLoopClosingSpeed ζ L ↔ NormalLoopPrescribedIdentityBand ζ L) ∧
    (NormalLoopBalancedSpeed ζ L ↔ NormalLoopPrescribedIdentityBand ζ L) := by
  have h₂₄ : NormalLoopClosingSpeed ζ L ↔ NormalLoopPrescribedIdentityBand ζ L :=
    ⟨normalLoop_closing_speed_identity_band hζ hζL hL hunit hspeed,
      normalLoop_prescribed_identity_band_closing_speed hζ hζL⟩
  have hcriteria := normalLoop_existence_criterion hζ hζL hL hunit hspeed
  exact ⟨hcriteria.1.trans h₂₄, h₂₄, hcriteria.2.1.symm.trans h₂₄⟩

end
end TightVer401
