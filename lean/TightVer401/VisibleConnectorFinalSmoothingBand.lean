import TightVer401.VisibleConnectorFinalSmoothingCarrier
import TightVer401.VisibleConnectorSourceInverseApplication
import TightVer401.VisibleConnectorWitnessAssemblyTopology

/-! Literal whole-band identification for the SAME rebased source used by the
ordinary family. The Cartesian source image, closed radial parameter band and
physical closed ruling band are identified, including both endpoint curves.
No carrier coverage or closure-to-band containment is assumed in the image
identity. This removes that independent smoothing input once the checked
source-degree image and physical Jordan topology are available. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix

private theorem finalSmoothing_physical_clock {L : ℝ} (hL : 0 < L) (s : ℝ) :
    visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
  unfold visibleConnectorPhysicalParameter
  field_simp [hL.ne', Real.two_pi_pos.ne']

/-- The actual Cartesian source maps the ENTIRE closed round band onto the
literal closed rebased ruling band, with both boundary heights retained. -/
theorem visibleConnectorFinalSmoothing_cartesian_image_rebased_band
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : Periodic (visibleConnectorRebasedSource p w a b) L)
    (hw : Periodic (visibleConnectorRebasedRuling w a d) L) :
    visibleConnectorCartesianSource L (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (fun _ => 1) ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} =
      visibleConnectorFinalSmoothingClosedRebasedBand p w a b d := by
  have hh : Periodic (fun _ : ℝ => (1 : ℝ)) L := fun _ => rfl
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    let r := planarRadius z
    let theta := Complex.arg (angularDescentComplex z)
    let s := visibleConnectorPhysicalParameter L theta
    refine ⟨s, r - 1, ?_, ?_⟩
    · exact ⟨sub_nonneg.mpr hz.1, by dsimp [r]; linarith [hz.2]⟩
    · have hr : 0 < r := lt_of_lt_of_le zero_lt_one hz.1
      rw [← visibleConnectorSourceInverse_polar_representative z,
        visibleConnectorCartesianSource_polar hp hw hh (by simpa only [Matrix.cons_val_zero] using hr)]
      simp only [visibleConnectorPolarSource, visibleConnectorSource,
        Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
      rfl
  · rintro x ⟨s, u, hu, rfl⟩
    let q : Coord := ![1 + u, 2 * Real.pi * s / L]
    have hr : 0 < q 0 := by change 0 < 1 + u; linarith [hu.1]
    refine ⟨saddlePolarChart q, ?_, ?_⟩
    · change 1 ≤ planarRadius (saddlePolarChart q) ∧ planarRadius (saddlePolarChart q) ≤ 2
      rw [angularDescent_radius_polar hr]
      change 1 ≤ 1 + u ∧ 1 + u ≤ 2
      constructor <;> linarith [hu.1, hu.2]
    · rw [visibleConnectorCartesianSource_polar hp hw hh hr]
      simp [visibleConnectorPolarSource, visibleConnectorSource, q,
        finalSmoothing_physical_clock hL]

/-- The exact source-degree image output supplies the physical closed-annulus
identity for the SAME rebased incoming and terminal traces. This is the
OrdinaryData closure, rather than an arbitrary closed set coverage premise. -/
theorem visibleConnectorFinalSmoothing_physical_closure_rebased_band
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : Periodic (visibleConnectorRebasedSource p w a b) L)
    (hw : Periodic (visibleConnectorRebasedRuling w a d) L)
    {Ho Hi : ℂ ≃ₜ ℂ}
    (hOuter : PositiveJordanParametrization Ho (fun t => seamComplexCoord.symm
      (visibleConnectorRebasedSource p w a b (L*t) + visibleConnectorRebasedRuling w a d (L*t))))
    (hInner : PositiveJordanParametrization Hi (fun t => seamComplexCoord.symm
      (visibleConnectorRebasedSource p w a b (L*t))))
    (hOuterJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange
      (fun s => visibleConnectorRebasedSource p w a b s + visibleConnectorRebasedRuling w a d s)))
    (hInnerJordan : Schoenflies.IsJordanCurve (positiveExitJordanRange
      (visibleConnectorRebasedSource p w a b)))
    (hNested : closure (positiveExitInside (visibleConnectorRebasedSource p w a b)) ⊆
      positiveExitInside (fun s => visibleConnectorRebasedSource p w a b s + visibleConnectorRebasedRuling w a d s))
    (hImage : visibleConnectorCartesianSource L (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) (fun _ => 1) ''
        {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} = annularCoordJordanClosure Ho Hi) :
    closure (positiveExitInside (fun s => visibleConnectorRebasedSource p w a b s +
      visibleConnectorRebasedRuling w a d s) \
        closure (positiveExitInside (visibleConnectorRebasedSource p w a b))) =
      visibleConnectorFinalSmoothingClosedRebasedBand p w a b d := by
  obtain ⟨_, _, _, _, hClosed, _, _⟩ :=
    visibleConnectorWitnessAssemblyTopology_annulus_geometry hL hOuter hInner
      hOuterJordan hInnerJordan hNested
  exact hClosed.trans (hImage.symm.trans
    (visibleConnectorFinalSmoothing_cartesian_image_rebased_band hL hp hw))

end
end TightVer401

