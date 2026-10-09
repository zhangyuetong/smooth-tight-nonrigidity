import TightVer401.IdentityBandFlowEmbedding
import TightVer401.IdentityBandFlowImmersion
import TightVer401.IdentityBandPeriodKernel

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

/-- Identity holonomy yields an actual embedded smooth annulus foliated by
complete closed asymptotic leaves inside any selected embedded positive band.
The annulus image, rather than the original rectangular band, is saturated. -/
theorem periodicRuledFrame_exists_embedded_flow_annulus {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    (s : ℝ) (hw : 0 < w) (hband : Topology.IsEmbedding (d.bandMap (b := w))) :
    let hbalance := periodicRuledFrame_identity_band_period_zero d hidentity
    ∃ δ > 0, δ < w ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞
        (identityFlowSurface (δ := δ) d hbalance s) ∧
      Topology.IsEmbedding (identityFlowSurface (δ := δ) d hbalance s) ∧
      (∀ p : AddCircle T × Ioo (0 : ℝ) δ,
        Function.Injective (bandDifferential (identityFlowSurface (δ := δ) d hbalance s) p)) ∧
      ∀ v : Ioo (0 : ℝ) δ,
        let U := principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v
        U s = v ∧ Function.Periodic U T ∧ ContDiff ℝ ∞ U ∧
        (∀ t : ℝ, U t ∈ Ioo 0 w) ∧
        (∀ t : ℝ, HasDerivAt U
          (-(U t / 2) * (ruledLambda d.τ t + U t * ruledD d.k d.τ t)) t) ∧
        (∀ t : ℝ,
          let p : Coord := ![t, U t]
          let tangent := deriv (fun r => (![r, U r] : Coord)) t
          dotProduct tangent
            ((secondFundamental (ruledMap d.γ d.E)
              (ruledNormal (d.T t) (d.n t) (d.k t) (d.τ t) (U t)) p).mulVec tangent) = 0) := by
  let hbalance := periodicRuledFrame_identity_band_period_zero d hidentity
  obtain ⟨δ₀, hδ₀, hδ₀w, hleaves⟩ :=
    periodicRuledFrame_closed_asymptotic_leaves d hbalance s w hw
  obtain ⟨δ₁, hδ₁, hglobal⟩ := periodicRuledFrame_global_denominator d hbalance s
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0 := by
    intro v hv t
    have hv₁ : |v| < δ₁ := by
      simpa only [abs_of_pos hv.1] using hv.2.trans_le (min_le_right δ₀ δ₁)
    exact ne_of_gt ((show (0 : ℝ) < 1 / 2 by norm_num).trans (hglobal v hv₁ t))
  have hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w := by
    intro v hv
    exact (hleaves v hv.1 (hv.2.trans_le (min_le_left δ₀ δ₁))).2.2.2.1
  refine ⟨δ, hδ, (min_le_left _ _).trans_lt hδ₀w,
    identityFlowSurface_contMDiff d hbalance s hden,
    identityFlowSurface_isEmbedding d hbalance s hden hinside hband,
    identityFlowSurface_immersion d hbalance s hden hinside, ?_⟩
  intro v
  exact hleaves v v.property.1 (v.property.2.trans_le (min_le_left δ₀ δ₁))

end
end TightVer401
