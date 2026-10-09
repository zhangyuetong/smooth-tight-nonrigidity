import TightVer401.VisibleConnectorCartesianDescent
import TightVer401.VisibleConnectorDisplacedSeamRebase
import TightVer401.VisibleConnectorSourceInverseCartesianJacobian

/-! A concrete height on the SAME actual Cartesian source carrier.  The only
inverse used here is the ordinary source inverse constructed by the degree
application.  The height is descended by AngularDescent; neither a side
classifier nor a smoothing or incoming-potential package is an input.

The fixed-carrier negative sublevel need not lie in the incoming potential's
domain merely from these hypotheses.  The later caller must prove that
containment by a compact small-displacement/height-strip estimate before
invoking relative smoothing. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def visibleConnectorFinalSmoothingPolarHeight (L : ℝ) (b d : ℝ → ℝ)
    (q : Coord) : ℝ :=
  b (visibleConnectorPhysicalParameter L (q 1)) +
    (q 0 - 1) * d (visibleConnectorPhysicalParameter L (q 1))

/-- Actual scalar on the whole target of the SAME Cartesian source inverse. -/
def visibleConnectorFinalSmoothingHeight (L : ℝ) (b d : ℝ → ℝ)
    (E : OpenPartialHomeomorph Coord Coord) (y : Coord) : ℝ :=
  angularDescentPotential (visibleConnectorFinalSmoothingPolarHeight L b d) (E.symm y)

theorem visibleConnectorFinalSmoothingPolarHeight_contDiff {L : ℝ} {b d : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d) :
    ContDiff ℝ ∞ (visibleConnectorFinalSmoothingPolarHeight L b d) := by
  have hs : ContDiff ℝ ∞ (fun q : Coord => visibleConnectorPhysicalParameter L (q 1)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const _
  exact (hb.comp hs).add
    (((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul (hd.comp hs))

theorem visibleConnectorFinalSmoothingPolarHeight_periodic {L : ℝ} {b d : ℝ → ℝ}
    (hb : Periodic b L) (hd : Periodic d L) (r theta : ℝ) :
    visibleConnectorFinalSmoothingPolarHeight L b d ![r, theta + 2 * Real.pi] =
      visibleConnectorFinalSmoothingPolarHeight L b d ![r, theta] := by
  simp only [visibleConnectorFinalSmoothingPolarHeight,
    Matrix.cons_val_zero, Matrix.cons_val_one, visibleConnectorPhysicalParameter_shift]
  rw [hb (visibleConnectorPhysicalParameter L theta), hd (visibleConnectorPhysicalParameter L theta)]

theorem visibleConnectorFinalSmoothingHeight_contDiffOn {L : ℝ} {b d : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hd : ContDiff ℝ ∞ d)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (E : OpenPartialHomeomorph Coord Coord)
    (hsource : E.source ⊆ {z | 0 < planarRadius z})
    (hi : ContDiffOn ℝ ∞ E.symm E.target) :
    ContDiffOn ℝ ∞ (visibleConnectorFinalSmoothingHeight L b d E) E.target := by
  exact (angularDescentPotential_contDiffOn
    (visibleConnectorFinalSmoothingPolarHeight_contDiff hb hd)
    (visibleConnectorFinalSmoothingPolarHeight_periodic hbL hdL)).comp hi
    (fun y hy => hsource (E.map_target hy))

/-- Literal inverse coordinates; no local branch of the angle is chosen. -/
theorem visibleConnectorFinalSmoothingHeight_inverse_formula (L : ℝ) (b d : ℝ → ℝ)
    (E : OpenPartialHomeomorph Coord Coord) (y : Coord) :
    visibleConnectorFinalSmoothingHeight L b d E y =
      b (visibleConnectorPhysicalParameter L (Complex.arg (angularDescentComplex (E.symm y)))) +
        (planarRadius (E.symm y) - 1) *
          d (visibleConnectorPhysicalParameter L (Complex.arg (angularDescentComplex (E.symm y)))) := by
  simp only [visibleConnectorFinalSmoothingHeight, angularDescentPotential,
    visibleConnectorFinalSmoothingPolarHeight, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem visibleConnectorFinalSmoothingHeight_clock {L : ℝ} (hL : 0 < L) (s : ℝ) :
    visibleConnectorPhysicalParameter L (2 * Real.pi * s / L) = s := by
  unfold visibleConnectorPhysicalParameter
  field_simp [hL.ne', Real.two_pi_pos.ne']

/-- Physical source and height at a point of the actual inverse's source. -/
theorem visibleConnectorFinalSmoothingHeight_pullback {L : ℝ} (hL : 0 < L)
    {p w : ℝ → Coord} {b d : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L p w (fun _ => 1))
    (s u : ℝ) (hu : 0 < 1 + u)
    (hq : saddlePolarChart (![1 + u, 2 * Real.pi * s / L] : Coord) ∈ E.source) :
    visibleConnectorSource p w ![s, u] ∈ E.target ∧
      visibleConnectorFinalSmoothingHeight L b d E (visibleConnectorSource p w ![s, u]) =
        b s + u * d s := by
  have hr : 0 < (![1 + u, 2 * Real.pi * s / L] : Coord) 0 := hu
  have hsrc : E (saddlePolarChart (![1 + u, 2 * Real.pi * s / L] : Coord)) =
      visibleConnectorSource p w ![s, u] := by
    rw [hE, visibleConnectorCartesianSource_polar hpL hwL (fun _ => rfl) hr]
    have hrad : 1 + u - 1 = u := by ring
    simp only [visibleConnectorPolarSource, visibleConnectorFinalSmoothingHeight_clock hL,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, visibleConnectorSource, hrad]
  refine ⟨hsrc ▸ E.map_source hq, ?_⟩
  change angularDescentPotential (visibleConnectorFinalSmoothingPolarHeight L b d)
    (E.symm (visibleConnectorSource p w ![s, u])) = _
  rw [← hsrc, E.left_inv hq,
    angularDescentPotential_polar
      (visibleConnectorFinalSmoothingPolarHeight_periodic hbL hdL) hr]
  simp only [visibleConnectorFinalSmoothingPolarHeight, visibleConnectorFinalSmoothingHeight_clock hL,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The actual fixed inverse domain covers every point of the closed band. -/
theorem visibleConnectorFinalSmoothingHeight_closed_band {L : ℝ} (hL : 0 < L)
    {p w : ℝ → Coord} {b d : ℝ → ℝ}
    (hpL : Periodic p L) (hwL : Periodic w L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L p w (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source)
    (s u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    visibleConnectorSource p w ![s, u] ∈ E.target ∧
      visibleConnectorFinalSmoothingHeight L b d E (visibleConnectorSource p w ![s, u]) =
        b s + u * d s := by
  have hu : 0 < 1 + u := by linarith
  apply visibleConnectorFinalSmoothingHeight_pullback hL hpL hwL hbL hdL E hE s u hu
  apply hclosed
  change 1 ≤ planarRadius (saddlePolarChart (![1 + u, 2 * Real.pi * s / L] : Coord)) ∧
    planarRadius (saddlePolarChart (![1 + u, 2 * Real.pi * s / L] : Coord)) ≤ 2
  rw [angularDescent_radius_polar (show 0 < (![1 + u, 2 * Real.pi * s / L] : Coord) 0 from hu)]
  change 1 ≤ 1 + u ∧ 1 + u ≤ 2
  exact ⟨by linarith, by linarith⟩

/-- Every target point has its literal real source representative.  This is
read from E.right_inv, rather than assuming a global angular inverse. -/
theorem visibleConnectorFinalSmoothingHeight_target_representation {L : ℝ}
    {p w : ℝ → Coord} (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L p w (fun _ => 1))
    {y : Coord} (hy : y ∈ E.target) :
    y = visibleConnectorSource p w
      ![visibleConnectorPhysicalParameter L (Complex.arg (angularDescentComplex (E.symm y))),
        planarRadius (E.symm y) - 1] := by
  have he := E.right_inv hy
  rw [hE] at he
  calc
    y = visibleConnectorCartesianSource L p w (fun _ => 1) (E.symm y) := he.symm
    _ = _ := by
      ext i
      simp only [visibleConnectorCartesianSource, angularDescentPotential,
        visibleConnectorPolarSource, visibleConnectorSource,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, mul_one]

/-- The negative original graph, positive terminal graph, and intermediate
zero graph are all in the SAME fixed target. -/
theorem visibleConnectorFinalSmoothingHeight_rebased_band {L : ℝ} (hL : 0 < L)
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (hpL : Periodic (visibleConnectorRebasedSource pc wc a b) L)
    (hwL : Periodic (visibleConnectorRebasedRuling wc a d) L)
    (hbL : Periodic b L) (hdL : Periodic d L)
    (hb : ∀ s, b s < 0) (hd : ∀ s, 0 < d s) (ht : ∀ s, 0 < b s + d s)
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    (hclosed : {z | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ E.source) (s : ℝ) :
    visibleConnectorRebasedSource pc wc a b s ∈ E.target ∧
      visibleConnectorFinalSmoothingHeight L b d E (visibleConnectorRebasedSource pc wc a b s) = b s ∧
      visibleConnectorSource pc wc ![a s, b s + d s] ∈ E.target ∧
      visibleConnectorFinalSmoothingHeight L b d E
        (visibleConnectorSource pc wc ![a s, b s + d s]) = b s + d s ∧
      pc (a s) ∈ E.target ∧ visibleConnectorFinalSmoothingHeight L b d E (pc (a s)) = 0 ∧
      0 < -b s / d s ∧ -b s / d s < 1 := by
  have hu0 : 0 < -b s / d s := div_pos (neg_pos.mpr (hb s)) (hd s)
  have hu1 : -b s / d s < 1 := (div_lt_one (hd s)).mpr (by linarith [ht s])
  have hz : b s + (-b s / d s) * d s = 0 := by field_simp [(hd s).ne']; ring
  have h0 := visibleConnectorFinalSmoothingHeight_closed_band hL hpL hwL hbL hdL E hE
    hclosed s 0 (by norm_num) (by norm_num)
  have h1 := visibleConnectorFinalSmoothingHeight_closed_band hL hpL hwL hbL hdL E hE
    hclosed s 1 (by norm_num) (by norm_num)
  have hmid := visibleConnectorFinalSmoothingHeight_closed_band hL hpL hwL hbL hdL E hE
    hclosed s (-b s / d s) hu0.le hu1.le
  simp only [visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, add_zero, zero_mul] at h0
  rw [visibleConnector_rebase_source] at h1 hmid
  simp only [one_mul] at h1
  simp only [hz, visibleConnectorSource, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, add_zero] at hmid
  exact ⟨h0.1, h0.2, h1.1, h1.2, hmid.1, hmid.2, hu0, hu1⟩

/-- On the ENTIRE target, zero height can occur only on the actual displaced
seam.  There is no restriction to the tiny local normal-coordinate carrier. -/
theorem visibleConnectorFinalSmoothingHeight_zero_range {L : ℝ}
    {pc wc : ℝ → Coord} {a b d : ℝ → ℝ}
    (E : OpenPartialHomeomorph Coord Coord)
    (hE : (E : Coord → Coord) = visibleConnectorCartesianSource L
      (visibleConnectorRebasedSource pc wc a b) (visibleConnectorRebasedRuling wc a d) (fun _ => 1))
    {y : Coord} (hy : y ∈ E.target)
    (hz : visibleConnectorFinalSmoothingHeight L b d E y = 0) :
    y ∈ range (pc ∘ a) := by
  let s := visibleConnectorPhysicalParameter L (Complex.arg (angularDescentComplex (E.symm y)))
  let u := planarRadius (E.symm y) - 1
  have hheight : b s + u * d s = 0 := by
    simpa only [s, u, visibleConnectorFinalSmoothingHeight_inverse_formula] using hz
  have hrep := visibleConnectorFinalSmoothingHeight_target_representation E hE hy
  change y = visibleConnectorSource (visibleConnectorRebasedSource pc wc a b)
    (visibleConnectorRebasedRuling wc a d) ![s, u] at hrep
  rw [visibleConnector_rebase_source, hheight] at hrep
  refine ⟨s, ?_⟩
  simpa only [Function.comp_apply, visibleConnectorSource, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_smul, add_zero] using hrep.symm


end
end TightVer401



