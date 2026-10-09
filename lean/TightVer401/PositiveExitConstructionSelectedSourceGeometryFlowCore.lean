import TightVer401.PositiveExitConstructionProtectedLeaves

/-! Actual protected-core placement between the SAME selected complete-flow
leaves. Strict Cartesian labels force strict bounds on the original initial
value, and the SAME protected field is transferred into that explicit image.
Identifying this flow image with the selected graph Jordan annulus remains a
separate topology obligation; no Jordan nesting or enclosure is assumed here. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original flow strip between the two selected initial values. -/
def positiveExit_selectedSourceGeometry_flowCore
    {T δ w : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (vin vout : Ioo (0 : ℝ) δ) : Set Coord :=
  e '' (identityFlowBandInclusion d hb 0 hinside ''
    {p : AddCircle T × Ioo (0 : ℝ) δ |
      (vin : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < (vout : ℝ)})

/-- Derive actual strict initial-value placement from the SAME original
flow-image containment and selected Cartesian label gaps. -/
theorem positiveExit_selectedSourceGeometry_core_in_flowCore
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ) (vin vout : Ioo (0 : ℝ) δ)
    {C : Set Coord}
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (hlabels : ∀ p ∈ C,
      1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
        positiveExitCartesianLabel d hb e p ∧
      positiveExitCartesianLabel d hb e p <
        1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) :
    C ⊆ positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout := by
  intro p hp
  obtain ⟨z, ⟨q, hq⟩, hzp⟩ := hprotect hp
  have hlabel : positiveExitCartesianLabel d hb e p =
      1 / (ruledRho d.τ 0 * (q.2 : ℝ)) - ruledOmega d.k d.τ 0 := by
    rw [← hzp, ← hq]
    change positiveExitLevel d hb
      (e.symm (e (identityFlowBandInclusion d hb 0 hinside q))) = _
    rw [e.left_inv (by rw [heS]; exact mem_univ _)]
    exact positiveExitLevel_identityFlowBandInclusion d hb hinside q
  have hbds := hlabels p hp
  rw [hlabel] at hbds
  have hρ : 0 < ruledRho d.τ 0 := ruledRho_pos (d.torsion_ne_zero 0)
  have hin : (vin : ℝ) < (q.2 : ℝ) := by
    by_contra hnot
    have hle : (q.2 : ℝ) ≤ (vin : ℝ) := le_of_not_gt hnot
    have hr := one_div_le_one_div_of_le (mul_pos hρ q.2.property.1)
      (mul_le_mul_of_nonneg_left hle hρ.le)
    have hh := sub_le_sub_right hr (ruledOmega d.k d.τ 0)
    exact (not_le_of_gt hbds.2) hh
  have hout : (q.2 : ℝ) < (vout : ℝ) := by
    by_contra hnot
    have hle : (vout : ℝ) ≤ (q.2 : ℝ) := le_of_not_gt hnot
    have hr := one_div_le_one_div_of_le (mul_pos hρ vout.property.1)
      (mul_le_mul_of_nonneg_left hle hρ.le)
    have hh := sub_le_sub_right hr (ruledOmega d.k d.τ 0)
    exact (not_le_of_gt hbds.1) hh
  exact ⟨z, ⟨q, ⟨hin, hout⟩, hq⟩, hzp⟩

/-- Retain the SAME protected field and original chart in the newly produced
strict flow-core image. No independent support or chart is selected. -/
theorem positiveExit_selectedSourceGeometry_support_in_flowCore
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heS : e.source = univ) (vin vout : Ioo (0 : ℝ) δ)
    {C : Set Coord}
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (hlabels : ∀ p ∈ C,
      1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
        positiveExitCartesianLabel d hb e p ∧
      positiveExitCartesianLabel d hb e p <
        1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient}
    (hsupport : e '' tsupport Y ⊆ C) :
    e '' tsupport Y ⊆ positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout :=
  hsupport.trans (positiveExit_selectedSourceGeometry_core_in_flowCore
    d hb hinside e heS vin vout hprotect hlabels)

end
end TightVer401
