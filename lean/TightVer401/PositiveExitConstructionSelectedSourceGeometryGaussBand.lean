import TightVer401.PositiveExitConstructionSelectedSourceGeometryProjection
import TightVer401.ThinBandRuledGauss
import TightVer401.GaussMapDifferential
import TightVer401.NormalLoopCross

/-! Actual full-band Gauss orientation from the SAME ruled second form and
oriented tangent cross. No smaller band, replacement seed, or desired
Cartesian orientation is assumed. The full raw-flow annulus still requires
composition with the produced transverse flow derivative and polar map. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem selectedGaussBand_cross_swap (a b : Ambient) :
    ambientCross a b = -ambientCross b a := by
  ext i
  fin_cases i <;> simp [ambientCross, cross_apply] <;> ring

private theorem selectedGaussBand_cross_pairing (a b c d : Ambient) :
    inner ℝ (ambientCross a b) (ambientCross c d) =
      inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp only [ambient_inner_dot]
  exact cross_dot_cross (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i)

/-- Actual signed Gauss area paired with the original tangent orientation is
exactly the actual second-form determinant. The four pairings are derived
from the unit-normal equation rather than assumed as an orientation grant. -/
theorem positiveExit_selectedSourceGeometry_gauss_cross_pairing_det
    {X N : Coord → Ambient} {U : Set Coord}
    (hX : ContDiffOn ℝ ∞ X U) (hN : ContDiffOn ℝ ∞ N U) (hU : IsOpen U)
    (hnormal : ∀ p ∈ U, IsUnitNormalAt X (N p) p) {q : Coord} (hq : q ∈ U) :
    inner ℝ (ambientCross (coordPartial 0 N q) (coordPartial 1 N q))
      (ambientCross (coordPartial 0 X q) (coordPartial 1 X q)) =
        (secondFundamental X (N q) q).det := by
  rw [selectedGaussBand_cross_pairing,
    gaussMap_partial_pairing hX hN hU hnormal hq 0 0,
    gaussMap_partial_pairing hX hN hU hnormal hq 1 1,
    gaussMap_partial_pairing hX hN hU hnormal hq 0 1,
    gaussMap_partial_pairing hX hN hU hnormal hq 1 0,
    Matrix.det_fin_two]
  ring
/-- The actual tangent cross is the positive ruled area factor times the
SAME original Gauss normal, throughout the unshrunk raw band. -/
theorem positiveExit_selectedSourceGeometry_ruled_tangent_cross
    {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord)
    (horient : ambientCross (d.T (q 0)) (d.E (q 0)) = d.n (q 0)) :
    ambientCross (coordPartial 0 (ruledMap d.γ d.E) q)
      (coordPartial 1 (ruledMap d.γ d.E) q) =
        Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) • d.rawGaussMap q := by
  have hNE : ambientCross (d.n (q 0)) (d.E (q 0)) = -d.T (q 0) := by
    have hh := normalLoopCross_double (d.E (q 0)) (d.T (q 0)) (d.E (q 0))
    rw [horient, (d.orthonormal (q 0)).2.1,
      (d.orthonormal (q 0)).2.2.2.1, one_smul, zero_smul, sub_zero] at hh
    rw [selectedGaussBand_cross_swap, hh]
  have hr : Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (ruledEnergy_pos (d.torsion_ne_zero (q 0)))).ne'
  have ha : Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) *
      (-d.τ (q 0) * q 1 / Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1))) =
        -d.τ (q 0) * q 1 := by field_simp [hr]
  have hb : Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) *
      ((1 - d.k (q 0) * q 1) /
        Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1))) =
        1 - d.k (q 0) * q 1 := by field_simp [hr]
  rw [ruled_partial_s (d.deriv_γ (q 0)) (d.deriv_E (q 0)),
    ruled_partial_u (d.deriv_γ (q 0)) (d.deriv_E (q 0)),
    ambientCross_add_left, ambientCross_smul_left, ambientCross_smul_left,
    horient, hNE]
  simp only [PeriodicRuledFrame.rawGaussMap, ruledNormal, smul_add, smul_smul, ha, hb]
  module

/-- Full-band signed Gauss area is strictly negative. The actual second-form
determinant is converted using the positive original ruled tangent area. -/
theorem positiveExit_selectedSourceGeometry_raw_gauss_signed_area_neg
    {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord)
    (horient : ambientCross (d.T (q 0)) (d.E (q 0)) = d.n (q 0)) :
    inner ℝ (d.rawGaussMap q)
      (ambientCross (coordPartial 0 d.rawGaussMap q) (coordPartial 1 d.rawGaussMap q)) < 0 := by
  let X := ruledMap d.γ d.E
  let N := d.rawGaussMap
  have hX : ContDiff ℝ ∞ X :=
    (d.smooth_γ.comp (contDiff_apply ℝ ℝ 0)).add
      ((contDiff_apply ℝ ℝ 1).smul (d.smooth_E.comp (contDiff_apply ℝ ℝ 0)))
  have hN : ContDiff ℝ ∞ N := periodicRuledFrame_rawGaussMap_contDiff d
  have hnormal : ∀ p ∈ (univ : Set Coord), IsUnitNormalAt X (N p) p := by
    intro p _
    exact ruled_isUnitNormal (d.deriv_γ (p 0)) (d.deriv_E (p 0))
      (d.orthonormal (p 0)) (d.torsion_ne_zero (p 0))
  have hcross : inner ℝ
      (ambientCross (coordPartial 0 N q) (coordPartial 1 N q))
      (ambientCross (coordPartial 0 X q) (coordPartial 1 X q)) =
        (secondFundamental X (N q) q).det := by
    rw [selectedGaussBand_cross_pairing,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hnormal (mem_univ q) 0 0,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hnormal (mem_univ q) 1 1,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hnormal (mem_univ q) 0 1,
      gaussMap_partial_pairing hX.contDiffOn hN.contDiffOn isOpen_univ hnormal (mem_univ q) 1 0,
      Matrix.det_fin_two]
    ring
  have hdet : (secondFundamental X (N q) q).det =
      -(d.τ (q 0))^2 / ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1) :=
    ruled_second_form_det d.deriv_γ d.deriv_E hX.contDiffOn isOpen_univ
      (mem_univ q) (d.orthonormal (q 0)) (d.torsion_ne_zero (q 0))
  have hscale : Real.sqrt (ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1)) *
      inner ℝ (N q) (ambientCross (coordPartial 0 N q) (coordPartial 1 N q)) =
        -(d.τ (q 0))^2 / ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1) := by
    rw [← hdet, ← hcross, positiveExit_selectedSourceGeometry_ruled_tangent_cross d q horient,
      real_inner_smul_right, real_inner_comm]
  have henergy := ruledEnergy_pos (k := d.k (q 0)) (u := q 1) (d.torsion_ne_zero (q 0))
  have hneg : -(d.τ (q 0))^2 / ruledEnergy (d.k (q 0)) (d.τ (q 0)) (q 1) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (d.torsion_ne_zero (q 0)))) henergy
  have hroot := Real.sqrt_pos.mpr henergy
  change inner ℝ (N q) (ambientCross (coordPartial 0 N q) (coordPartial 1 N q)) < 0
  by_contra hnot
  have hnonneg := mul_nonneg hroot.le (le_of_not_gt hnot)
  rw [hscale] at hnonneg
  exact (not_le_of_gt hneg) hnonneg

/-- Actual gnomonic Cartesian source orientation on every northern point
of the SAME full original raw Gauss band. -/
theorem positiveExit_selectedSourceGeometry_raw_gnomonic_jacobian_neg
    {T : ℝ} (d : PeriodicRuledFrame T) (q : Coord)
    (horient : ambientCross (d.T (q 0)) (d.E (q 0)) = d.n (q 0))
    (hnorth : 0 < d.rawGaussMap q 2) :
    annularJacobian (gnomonicInverse ∘ d.rawGaussMap) q < 0 :=
  positiveExitSelected_gnomonic_annular_jacobian_neg
    ((periodicRuledFrame_rawGaussMap_contDiff d).differentiable (by simp) q)
    hnorth (positiveExit_selectedSourceGeometry_raw_gauss_signed_area_neg d q horient)

end
end TightVer401

