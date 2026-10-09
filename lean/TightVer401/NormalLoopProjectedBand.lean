import TightVer401.NormalLoopRelativeFrame
import TightVer401.ThinBandRuledHorizontalProtected

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- An actual northern embedded normal and an actual embedded horizontal
closing primitive produce one width on which the band, its horizontal
projection, and its Gauss map are all injective. -/
theorem normalLoop_northern_embedded_balanced_band {ζ : ℝ → Ambient} {a : ℝ → ℝ} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : ContDiff ℝ ∞ a)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hapos : ∀ r, 0 < a r) (hζL : Function.Periodic ζ L) (haL : Function.Periodic a L)
    (hL : 0 < L) (hM : normalLoopMoment a ζ (deriv ζ) L = 0)
    (hB : (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0)
    (hζinj : Set.InjOn ζ (Ico 0 L)) (hnorth : ∀ r, 0 < ζ r 2)
    (hπinj : Set.InjOn (corrugatedAmbientHorizontalCLM ∘ normalLoopCurve a ζ (deriv ζ)) (Ico 0 L)) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
      ∃ d : PeriodicRuledFrame (rawPrimitive a L),
        d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
        d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
        d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
        d.τ = normalLoopPhysicalTau a e.symm ∧ PrincipalNormalIdentityBand d ∧
        ∃ hT : 0 < rawPrimitive a L,
          letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
          ∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ)) ∧
            Topology.IsEmbedding (corrugatedAmbientHorizontalCLM ∘ d.bandMap (b := δ)) ∧
            Function.Injective (fun p : AddCircle (rawPrimitive a L) × Ioo (0 : ℝ) δ =>
              d.fullGaussMap (p.1, (p.2 : ℝ))) := by
  have hi : Set.InjOn (normalLoopCurve a ζ (deriv ζ)) (Ico 0 L) := by
    intro r hr s hs he
    exact hπinj hr hs (congrArg corrugatedAmbientHorizontalCLM he)
  obtain ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity,
    hTpos, hembγ, _, _⟩ := normalLoop_embedded_balanced_speed_band
      hζ ha hunit hspeed hapos hζL haL hL hM hB hi
  letI : Fact (0 < rawPrimitive a L) := ⟨hTpos⟩
  have hnorthd : ∀ s, 0 < d.n s 2 := by
    intro s
    rw [hn]
    exact hnorth (e.symm s)
  have hin : Set.InjOn d.n (Ico 0 (rawPrimitive a L)) := by
    rw [hn]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he hζinj
  have hip : Set.InjOn (corrugatedAmbientHorizontalCLM ∘ d.γ) (Ico 0 (rawPrimitive a L)) := by
    rw [hγ]
    exact normalLoop_arclength_reparameterized_injective ha.continuous hapos e he hπinj
  have hp : Function.Periodic (corrugatedAmbientHorizontalCLM ∘ d.γ) (rawPrimitive a L) := by
    intro r
    change corrugatedAmbientHorizontalCLM (d.γ (r + rawPrimitive a L)) = corrugatedAmbientHorizontalCLM (d.γ r)
    rw [d.period_γ r]
  have hlift : hp.lift = corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift := by
    funext q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [Function.comp_apply, Function.Periodic.lift_coe]
  have hipnative : Function.Injective (corrugatedAmbientHorizontalCLM ∘ d.period_γ.lift) := by
    rw [← hlift]
    exact periodicCurve_lift_injective hp hip
  have hwidth := periodicRuledFrame_exists_embedded_projected_Gauss_band d hembγ.injective
    (periodicCurve_lift_injective d.period_n hin) (fun s => (hnorthd s).ne') hipnative
  exact ⟨e, he, hesmooth, d, hγ, hT, hE, hn, hk, hτ, hidentity, hTpos, hwidth⟩

end
end TightVer401
