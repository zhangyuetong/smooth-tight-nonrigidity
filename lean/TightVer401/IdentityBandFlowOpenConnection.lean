import TightVer401.IdentityBandBendingPullback
import Mathlib.Topology.Separation.Regular

/-! Openness of the actual characteristic-coordinate image and the actual
protected compact neighborhood. The rational inverse is the same inverse as
in IdentityBandFlowEmbedding. No openness or local-inversion grant is used. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

private theorem flowOpen_inverse_denominator {a b c v : ℝ} (hb : b ≠ 0)
    (hd : 1 + a*v*c ≠ 0) :
    1-b*(a*v/(b*(1+a*v*c)))*c = 1/(1+a*v*c) := by
  field_simp [hb, hd]
  <;> ring

private theorem flowOpen_inverse_value {a b c v : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : 1+a*v*c ≠ 0) :
    b*(a*v/(b*(1+a*v*c))) /
      (a*(1-b*(a*v/(b*(1+a*v*c)))*c)) = v := by
  rw [flowOpen_inverse_denominator hb hd]
  field_simp [ha, hb, hd]
  <;> ring

private theorem flowOpen_forward_denominator {a b c u : ℝ} (ha : a ≠ 0)
    (hd : 1-b*u*c ≠ 0) :
    1+a*(b*u/(a*(1-b*u*c)))*c = 1/(1-b*u*c) := by
  field_simp [ha, hd]
  <;> ring

private theorem flowOpen_forward_value {a b c u : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : 1-b*u*c ≠ 0) :
    a*(b*u/(a*(1-b*u*c))) /
      (b*(1+a*(b*u/(a*(1-b*u*c)))*c)) = u := by
  rw [flowOpen_forward_denominator ha hd]
  field_simp [ha, hb, hd]
  <;> ring

/-- Actual periodic characteristic coordinates have an open image, as the
inverse height lies in the original open initial-height interval. -/
theorem identityFlowCoordinates_isOpen_range {T δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hden : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1 + ruledRho d.τ s*v*(ruledOmega d.k d.τ t-ruledOmega d.k d.τ s) ≠ 0) :
    IsOpen (range (identityFlowCoordinates (δ := δ) d hbalance s)) := by
  let ρ := (ruledRho_periodic d.period_τ).lift
  let W := (periodicRuledFrame_omega_periodic d hbalance).lift
  let a := ruledRho d.τ s
  let c : AddCircle T → ℝ := fun q => W q-ruledOmega d.k d.τ s
  let D : AddCircle T × ℝ → ℝ := fun z => 1-ρ z.1*z.2*c z.1
  let H : AddCircle T × ℝ → ℝ := fun z => ρ z.1*z.2/(a*D z)
  let V : Set (AddCircle T × ℝ) := {z | D z ≠ 0}
  have hρ : Continuous ρ := (periodicLift_contMDiff
    (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero)
    (ruledRho_periodic d.period_τ)).continuous
  have hW : Continuous W := (periodicLift_contMDiff
    (OAI.ClosedSurfaceR4.PeriodicPrimitive.rawPrimitive_contDiff
      (ruledPeriodCoefficient_contDiff d.smooth_k d.smooth_τ d.torsion_ne_zero))
    (periodicRuledFrame_omega_periodic d hbalance)).continuous
  have hc : Continuous c := hW.sub continuous_const
  have hD : Continuous D := continuous_const.sub
    (((hρ.comp continuous_fst).mul continuous_snd).mul (hc.comp continuous_fst))
  have hV : IsOpen V :=
    (isOpen_compl_singleton : IsOpen (({0} : Set ℝ)ᶜ)).preimage hD
  have ha : a ≠ 0 := ne_of_gt (ruledRho_pos (d.torsion_ne_zero s))
  have hb (q : AddCircle T) : ρ q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ne_of_gt (ruledRho_pos (d.torsion_ne_zero t))
  have hd (q : AddCircle T) (v : Ioo (0 : ℝ) δ) : 1+a*(v : ℝ)*c q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hden _ v.property t
  have hH : ContinuousOn H V :=
    ((hρ.comp continuous_fst).mul continuous_snd).continuousOn.div
      (continuous_const.mul hD).continuousOn (fun z hz => mul_ne_zero ha hz)
  have hOpen : IsOpen (V ∩ H ⁻¹' Ioo (0 : ℝ) δ) :=
    hH.isOpen_inter_preimage hV isOpen_Ioo
  have hRange : range (identityFlowCoordinates (δ := δ) d hbalance s) =
      V ∩ H ⁻¹' Ioo (0 : ℝ) δ := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      have hi : D (identityFlowCoordinates d hbalance s p) =
          1/(1+a*(p.2 : ℝ)*c p.1) :=
        flowOpen_inverse_denominator (hb p.1) (hd p.1 p.2)
      refine ⟨?_, ?_⟩
      · change D (identityFlowCoordinates d hbalance s p) ≠ 0
        rw [hi]
        exact one_div_ne_zero (hd p.1 p.2)
      · have he : H (identityFlowCoordinates d hbalance s p) = (p.2 : ℝ) :=
          flowOpen_inverse_value ha (hb p.1) (hd p.1 p.2)
        change H (identityFlowCoordinates d hbalance s p) ∈ Ioo (0 : ℝ) δ
        rw [he]
        exact p.2.property
    · rintro ⟨hz, hheight⟩
      let v : Ioo (0 : ℝ) δ := ⟨H z, hheight⟩
      refine ⟨(z.1, v), ?_⟩
      apply Prod.ext
      · rfl
      · change a*(ρ z.1*z.2/(a*(1-ρ z.1*z.2*c z.1))) /
          (ρ z.1*(1+a*(ρ z.1*z.2/(a*(1-ρ z.1*z.2*c z.1)))*c z.1)) = z.2
        exact flowOpen_forward_value ha (hb z.1) hz
  rw [hRange]
  exact hOpen

/-- Actual positive trajectory bounds already force the nonzero denominator;
this uses the SAME visible seed margin, with no further width restriction. -/
theorem identityFlowBandInclusion_denominator_ne_zero {T δ w : ℝ}
    (d : PeriodicRuledFrame T) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      1+ruledRho d.τ s*v*(ruledOmega d.k d.τ t-ruledOmega d.k d.τ s) ≠ 0 := by
  intro v hv t he
  have hp := (hinside v hv t).1
  simp only [principalTrajectory, he, mul_zero, div_zero] at hp
  exact (lt_irrefl 0) hp

/-- The actual flow inclusion has an open range in the original native band. -/
theorem identityFlowBandInclusion_isOpen_range {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w) :
    IsOpen (range (identityFlowBandInclusion d hbalance s hinside)) := by
  let ι : AddCircle T × Ioo (0 : ℝ) w → AddCircle T × ℝ := fun p => (p.1, p.2)
  have hi : Continuous ι := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he : range (identityFlowBandInclusion d hbalance s hinside) =
      ι ⁻¹' range (identityFlowCoordinates (δ := δ) d hbalance s) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have hf := congrArg (fun z : AddCircle T × ℝ => z.1) hq
      have hs := congrArg (fun z : AddCircle T × ℝ => z.2) hq
      exact Prod.ext hf (Subtype.ext hs)
  rw [he]
  exact (identityFlowCoordinates_isOpen_range d hbalance s
    (identityFlowBandInclusion_denominator_ne_zero d s hinside)).preimage hi

/-- The original native support chart sends the SAME flow range to an open
planar image. Only its already constructed full source is needed. -/
theorem identityFlowBandInclusion_planar_isOpen_range {T δ w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (hsource : c0.source = univ) :
    IsOpen (range (c0 ∘ identityFlowBandInclusion d hbalance s hinside)) := by
  rw [range_comp]
  exact c0.isOpen_image_of_subset_source
    (identityFlowBandInclusion_isOpen_range d hbalance s hinside)
    (by rw [hsource]; exact subset_univ _)

/-- Apply the retained compact-neighborhood theorem to the SAME later
visible-margin-selected field and original support chart. -/
theorem identityFlowBandInclusion_exists_protected_neighborhood
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (hinside : ∀ v ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) s v t ∈ Ioo 0 w)
    (c0 : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (hsource : c0.source = univ)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hcompact : HasCompactSupport Y)
    (hsupport : tsupport Y ⊆ range (identityFlowBandInclusion d hbalance s hinside)) :
    ∃ O : Set Coord, IsOpen O ∧ c0 '' tsupport Y ⊆ O ∧ IsCompact (closure O) ∧
      closure O ⊆ range (c0 ∘ identityFlowBandInclusion d hbalance s hinside) := by
  have hc : Continuous c0 := continuousOn_univ.mp (by
    simpa only [hsource] using c0.continuousOn)
  have hK : IsCompact (c0 '' tsupport Y) := hcompact.image hc
  have hKU : c0 '' tsupport Y ⊆
      range (c0 ∘ identityFlowBandInclusion d hbalance s hinside) := by
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨q, hq⟩ := hsupport hp
    exact ⟨q, congrArg c0 hq⟩
  obtain ⟨O, hO, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hK
    (identityFlowBandInclusion_planar_isOpen_range d hbalance s hinside c0 hsource) hKU
  exact ⟨O, hO, hKO, hOc, hOU⟩

end
end TightVer401
