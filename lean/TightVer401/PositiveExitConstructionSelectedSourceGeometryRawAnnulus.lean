import TightVer401.PositiveExitConstructionSelectedSourceGeometryRoundCartesian
import TightVer401.VisibleConnectorSourceOrderRound

/-! Signed order and exact raw source annulus for the SAME selected original
flow. Ordinary positive Jordan parametrizations and genuine boundary separation
and enclosure remain producer inputs. Nesting and protected placement are
outputs of the actual positive Cartesian source map. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem selectedRawAnnulus_circle_polar (r t : ℝ) :
    seamComplexCoord (unitCircleParam 0 r t) = saddlePolarChart ![r, 2 * Real.pi * t] := by
  ext i
  fin_cases i <;> simp [seamComplexCoord_apply, unitCircleParam, circleMap,
    saddlePolarChart, ← Complex.ofReal_mul]

private theorem selectedRawAnnulus_phase (T t : ℝ) :
    positiveExitSelected_roundFlowPhase T (2 * Real.pi * t) = T * t := by
  dsimp [positiveExitSelected_roundFlowPhase]
  field_simp [Real.pi_ne_zero]
  <;> ring

variable {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (vin vout : Ioo (0 : ℝ) δ)

/-- The actual radius-one boundary equals the normalized SAME raw loop. -/
theorem positiveExitSelected_rawAnnulus_trace_inner (t : ℝ) :
    annularComplexConjugate (positiveExitSelected_roundCartesianSource d vin vout)
      (unitCircleParam 0 1 t) =
      angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside vin (T * t))) := by
  change seamComplexCoord.symm (positiveExitSelected_roundCartesianSource d vin vout
    (seamComplexCoord (unitCircleParam 0 1 t))) = _
  rw [selectedRawAnnulus_circle_polar,
    positiveExitSelected_roundCartesianSource_boundary_one d hb hinside vin vout,
    selectedRawAnnulus_phase]
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply, quadraticRadialFillingCoord_complex]

/-- The actual radius-two boundary equals the normalized SAME raw loop. -/
theorem positiveExitSelected_rawAnnulus_trace_outer (t : ℝ) :
    annularComplexConjugate (positiveExitSelected_roundCartesianSource d vin vout)
      (unitCircleParam 0 2 t) =
      angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside vout (T * t))) := by
  change seamComplexCoord.symm (positiveExitSelected_roundCartesianSource d vin vout
    (seamComplexCoord (unitCircleParam 0 2 t))) = _
  rw [selectedRawAnnulus_circle_polar,
    positiveExitSelected_roundCartesianSource_boundary_two d hb hinside vin vout,
    selectedRawAnnulus_phase]
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply, quadraticRadialFillingCoord_complex]

variable (horder : (vin : ℝ) < (vout : ℝ))
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho
      (fun t => angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside vout (T * t)))))
    (hInner : PositiveJordanParametrization Hi
      (fun t => angularDescentComplex (gnomonicInverse (positiveExitRawLeaf d hb hinside vin (T * t)))))
    (hDisjoint : Disjoint (frontier (jordanInterior Ho)) (frontier (jordanInterior Hi)))
    (hcOuter : (0 : ℂ) ∈ jordanInterior Ho) (hcInner : (0 : ℂ) ∈ jordanInterior Hi)

include horder hnorth horient heF hOuter hInner hDisjoint hcOuter hcInner

/-- Produce strict nesting by signed degree, then identify the entire SAME
raw flow core with its Jordan annulus using the actual global source inverse. -/
theorem positiveExitSelected_rawAnnulus_order_and_image :
    closure (jordanInterior Hi) ⊆ jordanInterior Ho ∧
    positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout =
      annularCoordJordanInterior Ho Hi ∧
    ∃ e0 : OpenPartialHomeomorph Coord Coord,
      e0.source = {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} ∧
      e0.target = positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout ∧
      (e0 : Coord → Coord) = positiveExitSelected_roundCartesianSource d vin vout ∧
      ContDiffOn ℝ ∞ e0.symm e0.target := by
  have hO := positiveExitSelected_roundCartesianDomain_isOpen δ vin vout
  have hF := positiveExitSelected_roundCartesianSource_contDiffOn d vin vout hinside hnorth hb
  have hKO := positiveExitSelected_roundCartesianDomain_contains_closed_band vin vout horder
  have hJ : ∀ p : Coord, 1 ≤ planarRadius p → planarRadius p ≤ 2 →
      0 < annularJacobian (positiveExitSelected_roundCartesianSource d vin vout) p :=
    fun p hp1 hp2 => positiveExitSelected_roundCartesianSource_jacobian_pos
      d vin vout horder hinside hnorth horient hb hp1 hp2
  have hTi := positiveExitSelected_rawAnnulus_trace_inner d hb hinside vin vout
  have hTo := positiveExitSelected_rawAnnulus_trace_outer d hb hinside vin vout
  have hNested := visibleConnectorSourceOrder_round hO hF hKO hJ hOuter hInner
    hTo hTi hDisjoint hcOuter hcInner
  obtain ⟨e0, E, H, heS, heT, he0F, heI, _hrest⟩ :=
    visibleConnectorSourceInverse_global hO hF hKO hJ hOuter hInner hNested hTo hTi
  have hImage : positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout =
      annularCoordJordanInterior Ho Hi := by
    rw [← positiveExitSelected_roundCartesianSource_image_open_annulus d hb hinside e heF vin vout horder]
    rw [← he0F, ← heS, e0.image_source_eq_target, heT]
  exact ⟨hNested, hImage, e0, heS, heT.trans hImage.symm, he0F, heI⟩

/-- The SAME protected compact set is inside the actual raw Jordan annulus,
by its already proved label-based placement in the original flow image. -/
theorem positiveExitSelected_rawAnnulus_protected_core
    (heS : e.source = univ) {C : Set Coord}
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (hlabels : ∀ p ∈ C,
      1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
        positiveExitCartesianLabel d hb e p ∧
      positiveExitCartesianLabel d hb e p <
        1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0) :
    C ⊆ annularCoordJordanInterior Ho Hi := by
  have hImage := (positiveExitSelected_rawAnnulus_order_and_image d hb hinside vin vout horder
    hnorth horient e heF hOuter hInner hDisjoint hcOuter hcInner).2.1
  rw [← hImage]
  exact positiveExit_selectedSourceGeometry_core_in_flowCore d hb hinside e heS vin vout hprotect hlabels

/-- Retain the SAME protected field in the raw annulus; selected graph
transport remains a separate producer obligation. -/
theorem positiveExitSelected_rawAnnulus_protected_support
    (heS : e.source = univ) {C : Set Coord}
    (hprotect : C ⊆ e '' range (identityFlowBandInclusion d hb 0 hinside))
    (hlabels : ∀ p ∈ C,
      1 / (ruledRho d.τ 0 * (vout : ℝ)) - ruledOmega d.k d.τ 0 <
        positiveExitCartesianLabel d hb e p ∧
      positiveExitCartesianLabel d hb e p <
        1 / (ruledRho d.τ 0 * (vin : ℝ)) - ruledOmega d.k d.τ 0)
    {Y : AddCircle T × Ioo (0 : ℝ) w → Ambient} (hsupport : e '' tsupport Y ⊆ C) :
    e '' tsupport Y ⊆ annularCoordJordanInterior Ho Hi :=
  hsupport.trans (positiveExitSelected_rawAnnulus_protected_core d hb hinside vin vout horder
    hnorth horient e heF hOuter hInner hDisjoint hcOuter hcInner heS hprotect hlabels)

end
end TightVer401

