import TightVer401.PositiveExitConstructionSelectedSourceGeometryRoundImage
import TightVer401.PositiveExitConstructionSelectedSourceGeometryAnnularJacobian
import TightVer401.VisibleConnectorSourceInverseCartesianJacobian

/-! Actual SAME Cartesian source on the full round annulus, constructed by
angular descent of the original complete flow. Smoothness, positive Jacobian,
boundaries and the entire strict flow-core image are produced without nesting
or a Jordan enclosure premise. -/
namespace TightVer401
noncomputable section
open Set MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def positiveExitSelected_roundCartesianRadialDomain (δ vin vout : ℝ) : Set ℝ :=
  {r | positiveExitSelected_roundFlowInitial vin vout r ∈ Ioo (0 : ℝ) δ}

def positiveExitSelected_roundCartesianSource {T : ℝ} (d : PeriodicRuledFrame T)
    (vin vout : ℝ) : Coord → Coord :=
  positiveExitSelectedAnnularDescent (positiveExitSelected_roundFlowSource d vin vout)

def positiveExitSelected_roundCartesianDomain (δ vin vout : ℝ) : Set Coord :=
  positiveExitSelectedAnnularDescentDomain (positiveExitSelected_roundCartesianRadialDomain δ vin vout)

theorem positiveExitSelected_roundCartesianRadialDomain_isOpen (δ vin vout : ℝ) :
    IsOpen (positiveExitSelected_roundCartesianRadialDomain δ vin vout) :=
  isOpen_Ioo.preimage (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const))

theorem positiveExitSelected_roundCartesianDomain_isOpen (δ vin vout : ℝ) :
    IsOpen (positiveExitSelected_roundCartesianDomain δ vin vout) :=
  positiveExitSelectedAnnularDescentDomain_isOpen
    (positiveExitSelected_roundCartesianRadialDomain_isOpen δ vin vout)

theorem positiveExitSelected_roundCartesianSource_contDiffOn
    {T δ w : ℝ} (d : PeriodicRuledFrame T) (vin vout : ℝ)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0) :
    ContDiffOn ℝ ∞ (positiveExitSelected_roundCartesianSource d vin vout)
      (positiveExitSelected_roundCartesianDomain δ vin vout) :=
  positiveExitSelectedAnnularDescent_contDiffOn
    (positiveExitSelected_roundCartesianRadialDomain_isOpen δ vin vout)
    (positiveExitSelected_roundFlowSource_contDiffOn d vin vout hinside hnorth)
    (positiveExitSelected_roundFlowSource_periodic d hb vin vout)

theorem positiveExitSelected_roundCartesianDomain_contains_closed_band
    {δ : ℝ} (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ)) :
    {p : Coord | 1 ≤ planarRadius p ∧ planarRadius p ≤ 2} ⊆
      positiveExitSelected_roundCartesianDomain δ vin vout := by
  apply positiveExitSelectedAnnularDescentDomain_closed_band
  intro r hr
  have hm : (![r, 0] : Coord) ∈ positiveExitSelected_roundFlowDomain δ vin vout :=
    positiveExitSelected_roundFlowDomain_contains_closed_band vin vout horder hr
  exact hm

theorem positiveExitSelected_roundCartesianSource_jacobian_pos
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ))
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (hnorth : ∀ p : AddCircle T × Ioo (0 : ℝ) w, 0 < d.bandGaussMap p 2)
    (horient : ∀ s, ambientCross (d.T s) (d.E s) = d.n s)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    {p : Coord} (hp1 : 1 ≤ planarRadius p) (hp2 : planarRadius p ≤ 2) :
    0 < annularJacobian (positiveExitSelected_roundCartesianSource d vin vout) p := by
  let q : Coord := ![planarRadius p, Complex.arg (angularDescentComplex p)]
  have hq : 0 < q 0 := lt_of_lt_of_le zero_lt_one hp1
  have hqD : q ∈ positiveExitSelected_roundFlowDomain δ vin vout :=
    positiveExitSelected_roundFlowDomain_contains_closed_band vin vout horder ⟨hp1, hp2⟩
  have heq : saddlePolarChart q = p := visibleConnectorSourceInverse_polar_representative p
  rw [← heq]
  exact positiveExitSelectedAnnularDescent_jacobian_pos
    (positiveExitSelected_roundCartesianRadialDomain_isOpen δ vin vout)
    (positiveExitSelected_roundFlowSource_contDiffOn d vin vout hinside hnorth)
    (positiveExitSelected_roundFlowSource_periodic d hb vin vout) hq hqD
    (positiveExitSelected_roundFlowSource_jacobian_pos d vin vout horder hinside hnorth horient hqD)

/-- Literal equality on every positive-radius polar representative. -/
theorem positiveExitSelected_roundCartesianSource_polar
    {T : ℝ} (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (vin vout : ℝ) {q : Coord} (hq : 0 < q 0) :
    positiveExitSelected_roundCartesianSource d vin vout (saddlePolarChart q) =
      positiveExitSelected_roundFlowSource d vin vout q :=
  positiveExitSelectedAnnularDescent_polar
    (positiveExitSelected_roundFlowSource_periodic d hb vin vout) hq

/-- The radius-one trace is the SAME original selected incoming leaf. -/
theorem positiveExitSelected_roundCartesianSource_boundary_one
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (vin vout : Ioo (0 : ℝ) δ) (theta : ℝ) :
    positiveExitSelected_roundCartesianSource d vin vout (saddlePolarChart ![1, theta]) =
      gnomonicInverse (positiveExitRawLeaf d hb hinside vin
        (positiveExitSelected_roundFlowPhase T theta)) := by
  rw [positiveExitSelected_roundCartesianSource_polar d hb vin vout (by simp)]
  rw [positiveExitRawLeaf_eq_raw]
  have hi : positiveExitSelected_roundFlowInitial vin vout 1 = (vin : ℝ) := by
    simp [positiveExitSelected_roundFlowInitial]
  simp only [positiveExitSelected_roundFlowSource, Function.comp_apply,
    positiveExitSelected_roundFlowRaw, Matrix.cons_val_zero, Matrix.cons_val_one, hi]
  rfl

/-- The radius-two trace is the SAME original selected outgoing leaf. -/
theorem positiveExitSelected_roundCartesianSource_boundary_two
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (vin vout : Ioo (0 : ℝ) δ) (theta : ℝ) :
    positiveExitSelected_roundCartesianSource d vin vout (saddlePolarChart ![2, theta]) =
      gnomonicInverse (positiveExitRawLeaf d hb hinside vout
        (positiveExitSelected_roundFlowPhase T theta)) := by
  rw [positiveExitSelected_roundCartesianSource_polar d hb vin vout (by simp)]
  rw [positiveExitRawLeaf_eq_raw]
  have hi : positiveExitSelected_roundFlowInitial vin vout 2 = (vout : ℝ) := by
    dsimp [positiveExitSelected_roundFlowInitial]
    ring
  simp only [positiveExitSelected_roundFlowSource, Function.comp_apply,
    positiveExitSelected_roundFlowRaw, Matrix.cons_val_zero, Matrix.cons_val_one, hi]
  rfl

/-- The full actual open Cartesian annulus has the exact strict flow-core image. -/
theorem positiveExitSelected_roundCartesianSource_image_open_annulus
    {T δ w : ℝ} [Fact (0 < T)] (d : PeriodicRuledFrame T)
    (hb : (∫ r in 0..T, ruledPeriodCoefficient d.k d.τ r) = 0)
    (hinside : ∀ u ∈ Ioo (0 : ℝ) δ, ∀ t : ℝ,
      principalTrajectory (ruledRho d.τ) (ruledOmega d.k d.τ) 0 u t ∈ Ioo 0 w)
    (e : OpenPartialHomeomorph (AddCircle T × Ioo (0 : ℝ) w) Coord)
    (heF : ∀ p, e p = gnomonicInverse (d.bandGaussMap p))
    (vin vout : Ioo (0 : ℝ) δ) (horder : (vin : ℝ) < (vout : ℝ)) :
    positiveExitSelected_roundCartesianSource d vin vout ''
        {p : Coord | 1 < planarRadius p ∧ planarRadius p < 2} =
      positiveExit_selectedSourceGeometry_flowCore d hb hinside e vin vout := by
  rw [← positiveExitSelected_roundFlowSource_image_open_band d hb hinside e heF vin vout horder]
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    let q : Coord := ![planarRadius p, Complex.arg (angularDescentComplex p)]
    have hq : 0 < q 0 := lt_of_lt_of_le zero_lt_one hp.1.le
    refine ⟨q, hp, ?_⟩
    have heq : saddlePolarChart q = p := visibleConnectorSourceInverse_polar_representative p
    exact (positiveExitSelected_roundCartesianSource_polar d hb vin vout hq).symm.trans
      (congrArg (positiveExitSelected_roundCartesianSource d vin vout) heq)
  · rintro x ⟨q, hq, rfl⟩
    have hr : 0 < q 0 := lt_of_lt_of_le zero_lt_one hq.1.le
    refine ⟨saddlePolarChart q, ?_, positiveExitSelected_roundCartesianSource_polar d hb vin vout hr⟩
    change 1 < planarRadius (saddlePolarChart q) ∧ planarRadius (saddlePolarChart q) < 2
    rw [angularDescent_radius_polar hr]
    exact hq

end
end TightVer401


