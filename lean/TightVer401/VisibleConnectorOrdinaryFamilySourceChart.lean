import TightVer401.VisibleConnectorSourceInverseCartesianJacobian
import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! The SAME literal ruling constructs the ordinary F/O fields from two
physical boundary determinant signs. Affineness in ruling height supplies
all intermediate signs, including the closed round band. No nesting,
global inverse, or Cartesian Jacobian conclusion is assumed. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- The ruling determinant is affine in height, so its two boundary signs
control the whole closed interval. -/
theorem visibleConnectorOrdinaryFamilySourceChart_delta_closed
    {p gamma w : ℝ → Coord} {h : ℝ → ℝ}
    (hInner : ∀ s, visibleConnectorDet (deriv p s) (w s) < 0)
    (hTerminal : ∀ s,
      visibleConnectorDet (deriv p s + h s • deriv w s) (w s) < 0)
    (q : Coord) (hu : 0 ≤ q 1) (huh : q 1 ≤ h (q 0)) :
    0 < visibleConnectorDelta p gamma w q := by
  have h0 := hInner (q 0)
  have hh := hTerminal (q 0)
  rw [visibleConnectorDet_add_smul] at hh
  have heq : visibleConnectorDelta p gamma w q =
      -visibleConnectorDet (deriv p (q 0)) (w (q 0)) -
        q 1 * visibleConnectorDet (deriv w (q 0)) (w (q 0)) := by
    simp only [visibleConnectorDelta, visibleConnectorA, visibleConnectorC]
    ring
  rw [heq]
  by_cases hd : 0 ≤ visibleConnectorDet (deriv w (q 0)) (w (q 0))
  · have hm := mul_nonneg (sub_nonneg.mpr huh) hd
    nlinarith
  · have hm := mul_nonpos_of_nonneg_of_nonpos hu (le_of_not_ge hd)
    linarith

/-- Exact physical traces of the descended SAME source; the phase is the
physical clock rather than an independently selected angular parametrization. -/
theorem visibleConnectorOrdinaryFamilySourceChart_physical
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    visibleConnectorCartesianSource L p w h
      (saddlePolarChart ![r, 2 * Real.pi * s / L]) =
      p s + ((r - 1) * h s) • w s := by
  have hClock : visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
    unfold visibleConnectorPhysicalParameter
    field_simp [hL.ne', Real.two_pi_pos.ne']
  rw [visibleConnectorCartesianSource_polar hpL hwL hhL
    (by simpa only [Matrix.cons_val_zero] using hr)]
  simp only [visibleConnectorPolarSource, Matrix.cons_val_zero,
    Matrix.cons_val_one, hClock]

/-- Produce every ordinary Cartesian source field on the punctured plane
from actual smooth periodic ruling data and its two physical endpoint signs.
The outgoing trace is literally p+h*w, so callers must retain their SAME
terminal curve when applying this producer. -/
theorem visibleConnectorOrdinaryFamilySourceChart_fields
    {L : ℝ} (hL : 0 < L) {p w : ℝ → Coord} {h : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (hpL : Periodic p L) (hwL : Periodic w L) (hhL : Periodic h L)
    (hpos : ∀ s, 0 < h s)
    (hInner : ∀ s, visibleConnectorDet (deriv p s) (w s) < 0)
    (hTerminal : ∀ s,
      visibleConnectorDet (deriv p s + h s • deriv w s) (w s) < 0) :
    let F := visibleConnectorCartesianSource L p w h
    let O : Set Coord := {q | 0 < planarRadius q}
    IsOpen O ∧ ContDiffOn ℝ ∞ F O ∧
    ({q : Coord | 1 ≤ planarRadius q ∧ planarRadius q ≤ 2} ⊆ O) ∧
    (∀ q : Coord, 1 ≤ planarRadius q → planarRadius q ≤ 2 →
      0 < annularJacobian F q) ∧
    (∀ s, F (saddlePolarChart ![1, 2 * Real.pi * s / L]) = p s) ∧
    (∀ s, F (saddlePolarChart ![2, 2 * Real.pi * s / L]) = p s + h s • w s) := by
  dsimp only
  refine ⟨isOpen_lt continuous_const (by unfold planarRadius; fun_prop),
    visibleConnectorSourceInverse_cartesian_smooth hp hw hh hpL hwL hhL,
    (fun q hq => lt_of_lt_of_le zero_lt_one hq.1), ?_, ?_, ?_⟩
  · exact visibleConnectorSourceInverse_cartesian_positive_closed hL hp hw hh
      hpL hwL hhL hpos p
      (fun q hu huh => visibleConnectorOrdinaryFamilySourceChart_delta_closed
        hInner hTerminal q hu huh)
  · intro s
    simpa only [sub_self, zero_mul, zero_smul, add_zero] using
      visibleConnectorOrdinaryFamilySourceChart_physical hL hpL hwL hhL zero_lt_one s
  · intro s
    convert visibleConnectorOrdinaryFamilySourceChart_physical hL hpL hwL hhL
      (r := 2) (by norm_num) s using 1 <;> norm_num

/-- The SAME inverse phase/height and remaining ruling length transport the
old two endpoint signs to the original incoming parametrization. In particular,
negative lower inverse heights b are allowed; positivity there is an explicit
remaining geometric obligation. No replacement inverse is selected. -/
theorem visibleConnectorOrdinaryFamilySourceChart_rebased_endpoint_signs
    {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hap : ∀ s, 0 < deriv a s) (hdp : ∀ s, 0 < d s)
    (hLower : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s])
    (hUpper : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s + d s]) :
    ∀ s,
      visibleConnectorDet (deriv (visibleConnectorRebasedSource p w a b) s)
        (visibleConnectorRebasedRuling w a d s) < 0 ∧
      visibleConnectorDet
        (deriv (visibleConnectorRebasedSource p w a b) s +
          deriv (visibleConnectorRebasedRuling w a d) s)
        (visibleConnectorRebasedRuling w a d s) < 0 := by
  intro s
  obtain ⟨hA, hDelta⟩ :=
    visibleConnector_rebase_determinants (gamma := gamma) hp hw ha hb hd s 1
  have hApos : 0 < visibleConnectorA (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedRuling w a d) s := by
    rw [hA]
    exact mul_pos (mul_pos (hap s) (hdp s)) (hLower s)
  have hDpos : 0 < visibleConnectorDelta (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) ![s, 1] := by
    rw [hDelta]
    simpa only [one_mul] using mul_pos (mul_pos (hap s) (hdp s)) (hUpper s)
  have hdet := visibleConnector_source_determinant
    (visibleConnectorRebasedSource p w a b)
    (visibleConnectorRebasedGradient p gamma w a b)
    (visibleConnectorRebasedRuling w a d) (![s, 1] : Coord)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] at hdet
  constructor
  · exact neg_pos.mp hApos
  · rw [hdet]
    exact neg_lt_zero.mpr hDpos

/-- Only the two actual old endpoint Delta facts are needed to fill the
whole SAME rebased closed strip. The source endpoint at u=1 is the old point
(a,b+d), not a new independently chosen terminal curve. -/
theorem visibleConnectorOrdinaryFamilySourceChart_rebased_delta_closed
    {p gamma w : ℝ → Coord} {a b d : ℝ → ℝ}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hap : ∀ s, 0 < deriv a s) (hdp : ∀ s, 0 < d s)
    (hLower : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s])
    (hUpper : ∀ s, 0 < visibleConnectorDelta p gamma w ![a s, b s + d s])
    (q : Coord) (hu : 0 ≤ q 1) (hu1 : q 1 ≤ 1) :
    0 < visibleConnectorDelta (visibleConnectorRebasedSource p w a b)
      (visibleConnectorRebasedGradient p gamma w a b)
      (visibleConnectorRebasedRuling w a d) q := by
  have hs := visibleConnectorOrdinaryFamilySourceChart_rebased_endpoint_signs
    hp hw ha hb hd hap hdp hLower hUpper
  exact visibleConnectorOrdinaryFamilySourceChart_delta_closed
    (h := fun _ => 1) (fun s => (hs s).1)
    (fun s => by simpa only [one_smul] using (hs s).2) q hu hu1

end
end TightVer401



