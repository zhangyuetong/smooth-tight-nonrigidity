import TightVer401.VisibleConnectorSourceInverseCartesianJacobian
import TightVer401.VisibleConnectorSourceInverseGlobal

/-! The literal raw Cartesian source supplies the actual circle boundary
maps and actual positive Jacobian for the ordinary annular-degree consumer.
No source inverse, completed potential or Jacobian conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

private theorem sourceInverseApplication_physical_clock (L t : ℝ) :
    visibleConnectorPhysicalParameter L (2 * Real.pi * t) = L * t := by
  unfold visibleConnectorPhysicalParameter
  calc
    L * (2 * Real.pi * t) / (2 * Real.pi) =
        (L * t) * ((2 * Real.pi) / (2 * Real.pi)) := by ring
    _ = L * t := by rw [div_self Real.two_pi_pos.ne', mul_one]

/-- Actual once-traversed circle image under the SAME descended source. -/
theorem visibleConnectorSourceInverseApplication_circle
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    annularComplexConjugate (visibleConnectorCartesianSource L p w h)
      (unitCircleParam 0 r t) =
      seamComplexCoord.symm (p (L * t) + ((r - 1) * h (L * t)) • w (L * t)) := by
  change seamComplexCoord.symm (visibleConnectorCartesianSource L p w h
    (seamComplexCoord (unitCircleParam 0 r t))) = _
  rw [show unitCircleParam 0 r t = quadraticRadialFillingCircle r (2 * Real.pi * t) from rfl,
    quadraticRadialFillingCircle_coord,
    visibleConnectorCartesianSource_polar hpL hwL hhL
      (by simpa only [Matrix.cons_val_zero] using hr)]
  simp only [visibleConnectorPolarSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    sourceInverseApplication_physical_clock]

theorem visibleConnectorSourceInverseApplication_inner
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L) (t : ℝ) :
    annularComplexConjugate (visibleConnectorCartesianSource L p w h)
      (unitCircleParam 0 1 t) = seamComplexCoord.symm (p (L * t)) := by
  simpa only [sub_self, zero_mul, zero_smul, add_zero] using
    visibleConnectorSourceInverseApplication_circle hpL hwL hhL zero_lt_one t

theorem visibleConnectorSourceInverseApplication_outer
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L) (t : ℝ) :
    annularComplexConjugate (visibleConnectorCartesianSource L p w h)
      (unitCircleParam 0 2 t) =
      seamComplexCoord.symm (p (L * t) + h (L * t) • w (L * t)) := by
  have hTwo : (2 : ℝ) - 1 = 1 := by norm_num
  simpa only [hTwo, one_mul] using
    visibleConnectorSourceInverseApplication_circle hpL hwL hhL (r := 2) (by norm_num) t

/-- The actual raw source, ordinary Delta positivity and ordinary literal
Jordan boundaries construct the full source inverse and open collar. -/
theorem visibleConnectorSourceInverseApplication_global
    {L : ℝ} {p w : ℝ → Coord} {h : ℝ → ℝ} {Ho Hi : ℂ ≃ₜ ℂ}
    (hL : 0 < L) (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (hpos : ∀ s, 0 < h s) (gamma : ℝ → Coord)
    (hDelta : ∀ q : Coord, 0 ≤ q 1 → q 1 ≤ h (q 0) →
      0 < visibleConnectorDelta p gamma w q)
    (hOuter : PositiveJordanParametrization Ho
      (fun t => seamComplexCoord.symm (p (L * t) + h (L * t) • w (L * t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm (p (L * t))))
    (hNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho) :
    ∃ (e0 E : OpenPartialHomeomorph Coord Coord)
      (H : ↥{z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ≃ₜ
        annularCoordJordanClosure Ho Hi),
      e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2} ∧
      e0.target = annularCoordJordanInterior Ho Hi ∧
      (e0 : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ e0.symm e0.target ∧
      (∀ z, (H z : Coord) = visibleConnectorCartesianSource L p w h z) ∧
      visibleConnectorCartesianSource L p w h ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
        annularCoordJordanClosure Ho Hi ∧
      {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source ∧
      E.source ⊆ {z : Coord | 0 < planarRadius z} ∧
      ContDiffOn ℝ ∞ (visibleConnectorCartesianSource L p w h) E.source ∧
      (∀ z ∈ E.source, 0 < annularJacobian (visibleConnectorCartesianSource L p w h) z) ∧
      (E : Coord → Coord) = visibleConnectorCartesianSource L p w h ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      annularCoordJordanClosure Ho Hi ⊆ E.target ∧
      EqOn E.symm e0.symm (annularCoordJordanInterior Ho Hi) := by
  have hO : IsOpen {z : Coord | 0 < planarRadius z} :=
    isOpen_lt continuous_const quadraticRadialFilling_radius_continuous
  have hKO : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆
      {z : Coord | 0 < planarRadius z} := fun _ hz => lt_of_lt_of_le zero_lt_one hz.1
  exact visibleConnectorSourceInverse_global hO
    (visibleConnectorSourceInverse_cartesian_smooth hp hw hh hpL hwL hhL) hKO
    (visibleConnectorSourceInverse_cartesian_positive_closed hL hp hw hh hpL hwL hhL
      hpos gamma hDelta) hOuter hInner hNested
    (visibleConnectorSourceInverseApplication_outer hpL hwL hhL)
    (visibleConnectorSourceInverseApplication_inner hpL hwL hhL)

end
end TightVer401
