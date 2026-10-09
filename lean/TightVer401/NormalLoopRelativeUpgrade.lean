import TightVer401.NormalLoopRelativePath
import TightVer401.NormalLoopRelativeFrame

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Relative holonomy upgrade, including the actual smooth path, any specified
regular embedded linear projection, physical frame, and thin Gauss injectivity. -/
theorem normalLoop_relative_holonomy_upgrade
    {ζ : ℝ → Ambient} {b : ℝ → ℝ} {L η : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hb : ContDiff ℝ ∞ b)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hbpos : ∀ r, 0 < b r) (hζL : Function.Periodic ζ L) (hbL : Function.Periodic b L)
    (hL : 0 < L) (hmoment : normalLoopMoment b ζ (deriv ζ) L = 0)
    (hbinj : Set.InjOn (normalLoopCurve b ζ (deriv ζ)) (Ico 0 L))
    (π : Ambient →L[ℝ] F) (hπregular : ∀ r, π (normalLoopTangent ζ r) ≠ 0)
    (hπinj : Set.InjOn (π ∘ normalLoopCurve b ζ (deriv ζ)) (Ico 0 L)) (hη : 0 < η) :
    letI : Fact (0 < L) := ⟨hL⟩
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧ (∀ r, 0 < a r) ∧
      (∫ r in 0..L, ‖a r - b r‖) < η ∧ normalLoopMoment a ζ (deriv ζ) L = 0 ∧
      (∫ r in 0..L, deriv (normalLoopCurvature ζ) r / Real.sqrt (a r)) = 0 ∧
      ∃ H : ℝ × AddCircle L → Ambient,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ H ∧
        (∀ t r, H (t, periodProjection L r) =
          normalLoopCurve (speedLinearInterpolation b a t) ζ (deriv ζ) r) ∧
        (∀ r, H (0, periodProjection L r) = normalLoopCurve b ζ (deriv ζ) r) ∧
        (∀ r, H (1, periodProjection L r) = normalLoopCurve a ζ (deriv ζ) r) ∧
        (∀ t ∈ Icc 0 1, Topology.IsEmbedding (fun q => H (t, q)) ∧
          Topology.IsEmbedding (π ∘ (fun q => H (t, q))) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Ambient) (fun q => H (t, q)) q)) ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (π ∘ (fun q => H (t, q))) q))) ∧
        (∀ t ∈ Icc 0 1, ∀ q, ‖H (t, q) - H (0, q)‖ < η) ∧
        (∀ t ∈ Icc 0 1, ∀ r,
          0 < speedLinearInterpolation b a t r ∧
          HasDerivAt (normalLoopCurve (speedLinearInterpolation b a t) ζ (deriv ζ))
            (speedLinearInterpolation b a t r • normalLoopTangent ζ r) r ∧
          inner ℝ (normalLoopTangent ζ r) (ζ r) = 0) ∧
        ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = rawPrimitive a ∧ ContDiff ℝ ∞ e.symm ∧
          ∃ d : PeriodicRuledFrame (rawPrimitive a L),
            d.γ = normalLoopCurve a ζ (deriv ζ) ∘ e.symm ∧
            d.T = normalLoopTangent ζ ∘ e.symm ∧ d.E = deriv ζ ∘ e.symm ∧
            d.n = ζ ∘ e.symm ∧ d.k = normalLoopPhysicalK a (normalLoopCurvature ζ) e.symm ∧
            d.τ = normalLoopPhysicalTau a e.symm ∧
            PrincipalNormalIdentityBand d ∧
            ∃ hT : 0 < rawPrimitive a L,
              letI : Fact (0 < rawPrimitive a L) := ⟨hT⟩
              Topology.IsEmbedding d.period_γ.lift ∧
              (∃ δ > 0, Topology.IsEmbedding (d.bandMap (b := δ))) ∧
              (Set.InjOn ζ (Ico 0 L) →
                ∃ δ > 0, Set.InjOn d.fullGaussMap (univ ×ˢ Icc (-δ) δ)) := by
  letI : Fact (0 < L) := ⟨hL⟩
  obtain ⟨a, ha, haL, hapos, hsmall, hM, hB, H, hH, hrep, hzero, hone, hemb, hclose, hdir⟩ :=
    normalLoop_relative_embedded_balanced_path hζ hb hunit hspeed hbpos hζL hbL hL
      hmoment hbinj π hπregular hπinj hη
  have hfinal := (hemb 1 ⟨by norm_num, by norm_num⟩).1.injective
  have hi := periodicPullback_representative_injective hfinal hone
  have hband := normalLoop_embedded_balanced_speed_band hζ ha hunit hspeed hapos hζL haL hL hM hB hi
  exact ⟨a, ha, haL, hapos, hsmall, hM, hB, H, hH, hrep, hzero, hone, hemb, hclose, hdir, hband⟩

end
end TightVer401
