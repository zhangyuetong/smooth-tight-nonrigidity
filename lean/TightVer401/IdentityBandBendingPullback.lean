import TightVer401.IdentityBandFlowEmbedding

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Zero actual strain is preserved under smooth reparametrization, by the
actual manifold derivative chain rule. -/
theorem isBandBending_pullback {T δ w : ℝ} [Fact (0 < T)]
    {X Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    {f : AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × Ioo (0 : ℝ) w}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Ambient) ∞ X)
    (hY : IsBandBending X Y)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ f) :
    IsBandBending (X ∘ f) (Y ∘ f) := by
  refine ⟨hY.1.comp hf, ?_⟩
  intro p v z
  have hx : bandDifferential (X ∘ f) p =
      (bandDifferential X (f p)).comp
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) f p) :=
    mfderiv_comp p ((hX (f p)).mdifferentiableAt (by simp)) ((hf p).mdifferentiableAt (by simp))
  have hy : bandDifferential (Y ∘ f) p =
      (bandDifferential Y (f p)).comp
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) f p) :=
    mfderiv_comp p ((hY.1 (f p)).mdifferentiableAt (by simp)) ((hf p).mdifferentiableAt (by simp))
  rw [hx, hy]
  exact hY.2 (f p) _ _

/-- A compact support contained in an embedding's image remains compact under
pullback; closedness of the entire image is unnecessary. -/
theorem hasCompactSupport_pullback_of_embedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [R1Space A]
    {f : A → B} {Y : B → Ambient} (hf : Topology.IsEmbedding f)
    (hY : HasCompactSupport Y) (hsupport : tsupport Y ⊆ range f) :
    HasCompactSupport (Y ∘ f) := by
  have hc : IsCompact (f ⁻¹' tsupport Y) :=
    hf.isInducing.isCompact_preimage' hY hsupport
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro p hp
  exact subset_tsupport Y hp

theorem nonzero_pullback_of_support_in_range {A B : Type*}
    [TopologicalSpace B] {f : A → B} {Y : B → Ambient}
    (hsupport : tsupport Y ⊆ range f) (hnonzero : ∃ p, Y p ≠ 0) :
    ∃ p, (Y ∘ f) p ≠ 0 := by
  obtain ⟨p, hp⟩ := hnonzero
  obtain ⟨q, hq⟩ := hsupport (subset_tsupport Y hp)
  exact ⟨q, by simpa only [Function.comp_apply, hq] using hp⟩

/-- The actual characteristic coordinates regarded as a map into the original
positive width-w band. The containment proof is an actual trajectory bound. -/
def identityFlowBandInclusion {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × Ioo (0 : ℝ) w := fun p =>
  (p.1, ⟨identityFlowHeight d hbalance s p, by
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
    have hp : (periodProjection T t, p.2) = p := Prod.ext ht rfl
    rw [← hp]
    exact hinside _ p.2.property t⟩)

theorem identityFlowBandInclusion_contMDiff {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (identityFlowBandInclusion d hbalance s hinside) := by
  apply contMDiff_fst.prodMk
  exact (ContMDiff.subtypeVal_comp_iff (bandOpen w) _).mp
    (identityFlowHeight_contMDiff d hbalance s hden)

theorem identityFlowBandInclusion_isEmbedding {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    Topology.IsEmbedding (identityFlowBandInclusion d hbalance s hinside) := by
  let ι : AddCircle T × Ioo (0 : ℝ) w → AddCircle T × ℝ := fun p => (p.1, p.2)
  have hi : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  exact hi.of_comp_iff.mp (identityFlowCoordinates_isEmbedding d hbalance s hden)

theorem identityFlowBandInclusion_surface {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    d.bandMap ∘ identityFlowBandInclusion d hbalance s hinside =
      identityFlowSurface d hbalance s := rfl

/-- The full protected support condition, in the ordinary circle-height
coordinates used by the protected bending construction. -/
theorem identityFlowBandInclusion_support_in_range {T δ w : ℝ}
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hsupport : ∀ p ∈ tsupport Y,
      (p.1, (p.2 : ℝ)) ∈ range (identityFlowCoordinates (δ := δ) d hbalance s)) :
    tsupport Y ⊆ range (identityFlowBandInclusion d hbalance s hinside) := by
  intro p hp
  obtain ⟨q, hq⟩ := hsupport p hp
  refine ⟨q, ?_⟩
  have hfirst : q.1 = p.1 := congrArg Prod.fst hq
  have hheight : identityFlowHeight d hbalance s q = (p.2 : ℝ) := congrArg Prod.snd hq
  exact Prod.ext hfirst (Subtype.ext hheight)

/-- Actual nonzero compact bending on the protected region pulls back to actual
nonzero compact bending of the smooth identity-flow annulus. -/
theorem identityFlowSurface_compact_nonzero_bending {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hY : IsBandBending d.bandMap Y) (hcompact : HasCompactSupport Y)
    (hnonzero : ∃ p, Y p ≠ 0)
    (hsupport : (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) '' tsupport Y ⊆
      range (identityFlowCoordinates (δ := δ) d hbalance s)) :
    let Yflow := Y ∘ identityFlowBandInclusion d hbalance s hinside
    IsBandBending (identityFlowSurface (δ := δ) d hbalance s) Yflow ∧
      HasCompactSupport Yflow ∧ ∃ p, Yflow p ≠ 0 := by
  have hs := identityFlowBandInclusion_support_in_range d hbalance s hinside
    (fun p hp => hsupport ⟨p, hp, rfl⟩)
  refine ⟨?_, hasCompactSupport_pullback_of_embedding
    (identityFlowBandInclusion_isEmbedding d hbalance s hden hinside) hcompact hs,
    nonzero_pullback_of_support_in_range hs hnonzero⟩
  exact isBandBending_pullback d.bandMap_contMDiff hY
    (identityFlowBandInclusion_contMDiff d hbalance s hden hinside)

end
end TightVer401
