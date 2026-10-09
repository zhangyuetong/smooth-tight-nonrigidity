import TightVer401.IdentityBandPeriodKernel
import TightVer401.IdentityBandFlowAnnulus

/-! A genuine nonzero compactly supported bending can be protected inside
any narrower annulus swept by the actual identity-return flow. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

private theorem identityFlow_point_of_high_level {a ρ δ u W Ws : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hδ : 0 < δ) (hu : 0 < u)
    (hc : 1 / (a * δ) - Ws < 1 / (ρ * u) - W) :
    ∃ v : ℝ, v ∈ Ioo 0 δ ∧ a * v / (ρ * (1 + a * v * (W - Ws))) = u := by
  let B := 1 / (ρ * u) - W + Ws
  have hB : 1 / (a * δ) < B := by dsimp [B]; linarith
  have hBpos : 0 < B := (one_div_pos.mpr (mul_pos ha hδ)).trans hB
  let v := 1 / (a * B)
  have hv : 0 < v := one_div_pos.mpr (mul_pos ha hBpos)
  have hvδ : v < δ := by
    have h := one_div_lt_one_div_of_lt
      (mul_pos ha (one_div_pos.mpr (mul_pos ha hδ)))
      (mul_lt_mul_of_pos_left hB ha)
    have he : 1 / (a * (1 / (a * δ))) = δ := by field_simp
    rw [he] at h
    exact h
  have he : 1 + a * v * (W - Ws) = (1 / (ρ * u)) / B := by
    have hab : a * (1 / (a * B)) = 1 / B := by field_simp
    dsimp only [v]
    rw [hab]
    calc
      1 + 1 / B * (W - Ws) = (B + W - Ws) / B := by field_simp; ring
      _ = (1 / (ρ * u)) / B := by congr 1; dsimp [B]; ring
  refine ⟨v, ⟨hv, hvδ⟩, ?_⟩
  rw [he]
  dsimp [v]
  field_simp

/-- The profile's entire topological support is controlled by the actual
invariant coordinate, including the derivative term in the vector profile. -/
theorem periodicRuledFrame_profile_tsupport_levels {T w : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) {W F : ℝ → ℝ} (hWL : Function.Periodic W T)
    (hWs : ContDiff ℝ ∞ W) :
    tsupport (d.profile (b := w) (F := F) hWL) ⊆
      {p | 1 / ((ruledRho_periodic d.period_τ).lift p.1 * (p.2 : ℝ)) -
        hWL.lift p.1 ∈ tsupport F} := by
  let V : AddCircle T × Ioo (0 : ℝ) w → ℝ := fun p =>
    1 / ((ruledRho_periodic d.period_τ).lift p.1 * (p.2 : ℝ)) - hWL.lift p.1
  have hρ : Continuous (ruledRho_periodic d.period_τ).lift :=
    (periodicLift_contMDiff (ruledRho_contDiff d.smooth_τ d.torsion_ne_zero)
      (ruledRho_periodic d.period_τ)).continuous
  have hρne (q : AddCircle T) : (ruledRho_periodic d.period_τ).lift q ≠ 0 := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (ruledRho_pos (d.torsion_ne_zero t)).ne'
  have hV : Continuous V :=
    (continuous_const.div ((hρ.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
      (fun p => mul_ne_zero (hρne _) p.2.property.1.ne')).sub
      ((periodicLift_contMDiff hWs hWL).continuous.comp continuous_fst)
  apply closure_minimal ?_ ((isClosed_tsupport F).preimage hV)
  intro p hp
  by_contra hn
  exact hp (bandProfile_zero_off_profile_support hn)

/-- The same band's bending is compactly supported strictly inside the actual
flow-annulus image. The annulus parameter δ may be chosen arbitrarily small. -/
theorem periodicRuledFrame_exists_protected_bending {T w δ : ℝ} [Fact (0 < T)]
    (d : PeriodicRuledFrame T) (hidentity : PrincipalNormalIdentityBand d)
    (s : ℝ) (hw : 0 < w) (hδ : 0 < δ) :
    let hbalance := periodicRuledFrame_identity_band_period_zero d hidentity
    ∃ Y : AddCircle T × Ioo (0 : ℝ) w → Ambient,
      IsBandBending (d.bandMap (b := w)) Y ∧ HasCompactSupport Y ∧
      (∃ p, Y p ≠ 0) ∧
      (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) '' tsupport Y ⊆
        range (identityFlowCoordinates (δ := δ) d hbalance s) ∧
      d.bandMap '' tsupport Y ⊆ range (identityFlowSurface (δ := δ) d hbalance s) := by
  let hbalance := periodicRuledFrame_identity_band_period_zero d hidentity
  obtain ⟨hWs, hWL, _hW0⟩ := periodicRuledFrame_identity_band_omega d hidentity
  obtain ⟨cb, hmax, _hattained⟩ := periodic_ruled_cutoff d hWs hWL hw
  let c := max cb (1 / (ruledRho d.τ s * δ) - ruledOmega d.k d.τ s)
  obtain ⟨F, hFs, hFc, hFsupport, hFvalue⟩ := exists_nonzero_compact_profile_above c
  let Y := d.profile (b := w) (F := F) hWL
  have hmaxc (t) : 1 / (ruledRho d.τ t * w) - ruledOmega d.k d.τ t ≤ c :=
    (hmax t).trans (le_max_left _ _)
  have hbending := ruled_band_profile_supported d hWs hWL
    (ruledOmega_hasDerivAt d.smooth_k d.smooth_τ d.torsion_ne_zero) hw hmaxc hFs hFc hFsupport
  have hnonzero : ∃ p, Y p ≠ 0 := by
    apply periodic_bandProfile_nonzero d.period_k d.period_τ
      (ruledRho_periodic d.period_τ) hWL d.period_T d.period_n
      (d.orthonormal 0) (d.torsion_ne_zero 0) (ruledRho_pos (d.torsion_ne_zero 0)) hw
      (hmaxc 0) (show c < c + 2 by linarith)
    rw [hFvalue]
    norm_num
  have hpoint (p : AddCircle T × Ioo (0 : ℝ) w) (hp : p ∈ tsupport Y) :
      ∃ q : AddCircle T × Ioo (0 : ℝ) δ,
        identityFlowCoordinates d hbalance s q = (p.1, (p.2 : ℝ)) ∧
        identityFlowSurface d hbalance s q = d.bandMap p := by
    have hlevel := periodicRuledFrame_profile_tsupport_levels d hWL hWs hp
    have hc := hFsupport hlevel
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective p.1
    have hthreshold : 1 / (ruledRho d.τ s * δ) - ruledOmega d.k d.τ s <
        1 / (ruledRho d.τ t * (p.2 : ℝ)) - ruledOmega d.k d.τ t := by
      have h := (le_max_right cb
        (1 / (ruledRho d.τ s * δ) - ruledOmega d.k d.τ s)).trans_lt hc
      rw [← ht] at h
      exact h
    obtain ⟨v, hv, hvformula⟩ := identityFlow_point_of_high_level
      (ruledRho_pos (d.torsion_ne_zero s)) (ruledRho_pos (d.torsion_ne_zero t))
      hδ p.2.property.1 hthreshold
    let q : AddCircle T × Ioo (0 : ℝ) δ := (p.1, ⟨v, hv⟩)
    have hheight : identityFlowHeight d hbalance s q = (p.2 : ℝ) := by
      dsimp [q, identityFlowHeight]
      rw [← ht]
      exact hvformula
    refine ⟨q, Prod.ext rfl hheight, ?_⟩
    change d.period_γ.lift p.1 + identityFlowHeight d hbalance s q • d.period_E.lift p.1 = _
    rw [hheight]
    rfl
  refine ⟨Y, hbending.1, hbending.2, hnonzero, ?_, ?_⟩
  · rintro z ⟨p, hp, rfl⟩
    obtain ⟨q, hq, _⟩ := hpoint p hp
    exact ⟨q, hq⟩
  · rintro z ⟨p, hp, rfl⟩
    obtain ⟨q, _, hq⟩ := hpoint p hp
    exact ⟨q, hq⟩

/-- Convert the full support inclusion in real-height coordinates to the same
inclusion in the original native band, for its actual flow inclusion. -/
theorem identityFlow_protected_support_in_band {T w δ : ℝ}
    (d : PeriodicRuledFrame T)
    (hbalance : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) (s : ℝ)
    (f : AddCircle T × Ioo (0 : ℝ) δ → AddCircle T × Ioo (0 : ℝ) w)
    (hf : ∀ q, ( (f q).1, ((f q).2 : ℝ)) = identityFlowCoordinates d hbalance s q)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hprotect : (fun p : AddCircle T × Ioo (0 : ℝ) w => (p.1, (p.2 : ℝ))) '' tsupport Y ⊆
      range (identityFlowCoordinates (δ := δ) d hbalance s)) :
    tsupport Y ⊆ range f := by
  intro p hp
  obtain ⟨q, hq⟩ := hprotect ⟨p, hp, rfl⟩
  refine ⟨q, ?_⟩
  have h := (hf q).trans hq
  exact Prod.ext (congrArg (fun z : AddCircle T × ℝ => z.1) h)
    (Subtype.ext (congrArg (fun z : AddCircle T × ℝ => z.2) h))

end
end TightVer401
