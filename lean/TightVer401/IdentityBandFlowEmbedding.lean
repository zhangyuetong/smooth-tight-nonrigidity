import TightVer401.IdentityBandFlowAnnulus
import TightVer401.ThinBandRuledEmbedding

namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

private theorem identityFlow_inverse_denominator {a b c v : ℝ} (hb : b ≠ 0)
    (hd : 1 + a * v * c ≠ 0) :
    1 - b * (a * v / (b * (1 + a * v * c))) * c = 1 / (1 + a * v * c) := by
  field_simp
  <;> ring

private theorem identityFlow_inverse_formula {a b c v : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : 1 + a * v * c ≠ 0) :
    b * (a * v / (b * (1 + a * v * c))) /
      (a * (1 - b * (a * v / (b * (1 + a * v * c))) * c)) = v := by
  rw [identityFlow_inverse_denominator hb hd]
  field_simp

/-- The actual characteristic-coordinate map has a continuous explicit inverse
on an open set containing its image, hence is a native topological embedding. -/
theorem identityFlowCoordinates_isEmbedding {T δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0) :
    Topology.IsEmbedding (identityFlowCoordinates (δ := δ) d hbalance s) := by
  let ρ := (ruledRho_periodic d.period_τ).lift
  let W := (periodicRuledFrame_omega_periodic d hbalance).lift
  let a := ruledRho d.τ s
  let c := fun q => W q - ruledOmega d.k d.τ s
  have hρ : Continuous ρ := (periodicLift_contMDiff
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero) (ruledRho_periodic d.period_τ)).continuous
  have hW : Continuous W := (periodicLift_contMDiff
    (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
    (periodicRuledFrame_omega_periodic d hbalance)).continuous
  have hc : Continuous c := hW.sub continuous_const
  have hρ0 (q) : ρ q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ne_of_gt (ruledRho_pos (d.torsion_ne_zero t))
  have hd (q : AddCircle T) (v : Ioo (0 : ℝ) δ) : 1 + a * (v : ℝ) * c q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hden _ v.property t
  let D : Set (AddCircle T × ℝ) := {p | 1 - ρ p.1 * p.2 * c p.1 ≠ 0}
  let F := identityFlowCoordinates (δ := δ) d hbalance s
  have hmem (p : AddCircle T × Ioo (0 : ℝ) δ) : F p ∈ D := by
    change 1 - ρ p.1 * (a * (p.2 : ℝ) / (ρ p.1 *
      (1 + a * (p.2 : ℝ) * c p.1))) * c p.1 ≠ 0
    rw [identityFlow_inverse_denominator (hρ0 _) (hd _ _)]
    exact one_div_ne_zero (hd _ _)
  let f : AddCircle T × Ioo (0 : ℝ) δ → D := fun p => ⟨F p, hmem p⟩
  let g : D → AddCircle T × ℝ := fun p =>
    (p.val.1, ρ p.val.1 * p.val.2 / (a * (1 - ρ p.val.1 * p.val.2 * c p.val.1)))
  have hF : Continuous F := continuous_fst.prodMk
    (identityFlowHeight_contMDiff d hbalance s hden).continuous
  have hf : Continuous f := hF.subtype_mk _
  have hg : Continuous g := by
    have hfst : Continuous (fun p : D => p.val.1) := continuous_fst.comp continuous_subtype_val
    have hsnd : Continuous (fun p : D => p.val.2) := continuous_snd.comp continuous_subtype_val
    apply hfst.prodMk
    exact ((hρ.comp hfst).mul hsnd).div
      (continuous_const.mul (continuous_const.sub
        (((hρ.comp hfst).mul hsnd).mul (hc.comp hfst))))
      (fun p => mul_ne_zero (ne_of_gt (ruledRho_pos (d.torsion_ne_zero s))) p.property)
  let ι : AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × ℝ := fun p => (p.1, p.2)
  have hi : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have he : g ∘ f = ι := by
    funext p
    apply Prod.ext
    · rfl
    · exact identityFlow_inverse_formula
        (ne_of_gt (ruledRho_pos (d.torsion_ne_zero s))) (hρ0 _) (hd _ _)
  have hemb : Topology.IsEmbedding f := Topology.IsEmbedding.of_comp hf hg (he.symm ▸ hi)
  exact Topology.IsEmbedding.subtypeVal.comp hemb

/-- Restricting the original embedded band to the annulus swept by the periodic
asymptotic trajectories preserves the native embedding. -/
theorem identityFlowSurface_isEmbedding {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s * v * (ruledOmega d.k d.τ t - ruledOmega d.k d.τ s) ≠ 0)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    (hband : Topology.IsEmbedding (d.bandMap (b := w))) :
    Topology.IsEmbedding (identityFlowSurface (δ := δ) d hbalance s) := by
  have hheight (p : AddCircle T × Ioo (0 : ℝ) δ) :
      identityFlowHeight d hbalance s p ∈ Ioo 0 w := by
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
    have hp : (periodProjection T t, p.2) = p := Prod.ext ht rfl
    rw [← hp]
    exact hinside _ p.2.property t
  let f : AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × Ioo (0 : ℝ) w :=
    fun p => (p.1, ⟨identityFlowHeight d hbalance s p, hheight p⟩)
  let ι : AddCircle T × Ioo (0 : ℝ) w → AddCircle T × ℝ := fun p => (p.1, p.2)
  have hi : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  have hf : Topology.IsEmbedding f := hi.of_comp_iff.mp
    (identityFlowCoordinates_isEmbedding d hbalance s hden)
  exact hband.comp hf

end
end TightVer401


