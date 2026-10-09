import TightVer401.PositiveExitConstructionCoordinates
import TightVer401.PositiveExitConstructionFermi
import TightVer401.IdentityBandCentralSupportCartesian
import TightVer401.IdentityBandPlanarSupportCoordinates
import TightVer401.FermiSupportSpatialGeometry
import TightVer401.SeamFrameJet
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The actual Fermi support height and tensor of the SAME Cartesian potential.
North and scale conditions come from the constructed Fermi collar. No support
reconstruction, tensor correspondence or seam/exit package is an input. -/
open scoped Manifold
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def positiveExitFermiHeight (G : Coord → ℝ) (ζ : ℝ → Ambient) (q : Coord) : ℝ :=
  G (positiveExitFermiSource ζ q) / planarWeight (positiveExitFermiSource ζ q)

theorem positiveExitFermiSource_contDiffOn {ζ : ℝ → Ambient} {V : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ) (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2) :
    ContDiffOn ℝ ∞ (positiveExitFermiSource ζ) V := by
  intro q hq
  exact (gnomonicInverse_contDiffAt (hnorth q hq).ne').comp_contDiffWithinAt q
    (fermiNormalMap_contDiff hζ).contDiffWithinAt

theorem positiveExitFermiSource_periodic {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) :
    ∀ q : Coord, positiveExitFermiSource ζ (q + Pi.single 0 L) = positiveExitFermiSource ζ q := by
  have hPL := (normalLoop_actual_periodic hζ hζL).1
  intro q
  have hQ : fermiNormalMap ζ (q + Pi.single 0 L) = fermiNormalMap ζ q := by
    simp only [fermiNormalMap, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, hζL (q 0), hPL (q 0)]
  exact congrArg gnomonicInverse hQ

theorem positiveExitFermiHeight_periodic {ζ : ℝ → Ambient} {L : ℝ} (G : Coord → ℝ)
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) :
    FermiPeriodic L (positiveExitFermiHeight G ζ) := by
  intro q
  simp only [positiveExitFermiHeight, positiveExitFermiSource_periodic hζ hζL q]

theorem positiveExitFermiHeight_contDiffOn {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ) (hG : ContDiffOn ℝ ∞ G U)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) :
    ContDiffOn ℝ ∞ (positiveExitFermiHeight G ζ) V := by
  have hP := positiveExitFermiSource_contDiffOn hζ hnorth
  exact (hG.comp hP hmap).div (gnomonicWeight_contDiff.comp_contDiffOn hP)
    (fun q _ => (planarWeight_pos (positiveExitFermiSource ζ q)).ne')

theorem positiveExitFermi_normal_eq {ζ : ℝ → Ambient} {V : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2) :
    EqOn (planarUnitNormal ∘ positiveExitFermiSource ζ) (fermiNormalMap ζ) V := by
  intro q hq
  exact identityBand_gnomonic_unitNormal (fermiNormalMap_unit hζ hunit hspeed q) (hnorth q hq)

private theorem positiveExitFermi_metric_positive {ζ : ℝ → Ambient} {V : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0) :
    SmoothPositiveOn (inducedMetric (fermiNormalMap ζ)) V := by
  rw [fermiNormalMap_inducedMetric hζ hunit hspeed]
  exact fermiMetric_smoothPositiveOn
    (fermiNormalScale_contDiff (normalLoop_actual_smooth hζ).2) hscale

/-- The actual sphere support in Fermi coordinates reconstructs the same
Cartesian support surface, by its actual unit normal and actual height. -/
theorem positiveExitFermi_support_reconstruction {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) :
    EqOn (sphereSupportMap (inducedMetric (fermiNormalMap ζ)) (fermiNormalMap ζ)
      (positiveExitFermiHeight G ζ)) (planarSupportMap G ∘ positiveExitFermiSource ζ) V := by
  let Q := fermiNormalMap ζ
  let P := positiveExitFermiSource ζ
  let X := planarSupportMap G ∘ P
  have hP : ContDiffOn ℝ ∞ P V := positiveExitFermiSource_contDiffOn hζ hnorth
  have hX : ContDiffOn ℝ ∞ X V := (planarSupportMap_contDiffOn hG hU).comp hP hmap
  have hg := positiveExitFermi_metric_positive hζ hunit hspeed hscale
  have hi := inducedMetric_isometricOn (fermiNormalMap_contDiff hζ).contDiffOn (U := V)
  have hnEq : EqOn (planarUnitNormal ∘ P) Q V := positiveExitFermi_normal_eq hζ hunit hspeed hnorth
  have hn (q : Coord) (hq : q ∈ V) : IsUnitNormalAt X (Q q) q := by
    have hdP := ((hP q hq).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
    have hdX := (((planarSupportMap_contDiffOn hG hU) (P q) (hmap hq)).contDiffAt
      (hU.mem_nhds (hmap hq))).differentiableAt (by simp)
    refine ⟨fermiNormalMap_unit hζ hunit hspeed q, fun v => ?_⟩
    rw [show fderiv ℝ X q = (fderiv ℝ (planarSupportMap G) (P q)).comp (fderiv ℝ P q) from
      fderiv_comp q hdX hdP]
    change inner ℝ (fderiv ℝ (planarSupportMap G) (P q) (fderiv ℝ P q v)) (Q q) = 0
    rw [← hnEq hq]
    exact (planarSupportMap_isUnitNormal hG hU (hmap hq)).2 _
  have hh : EqOn (fun q => inner ℝ (X q) (Q q)) (positiveExitFermiHeight G ζ) V := by
    intro q hq
    change inner ℝ (planarSupportMap G (P q)) (Q q) = G (P q) / planarWeight (P q)
    rw [← hnEq hq]
    exact planarSupportMap_height G (P q)
  have hconverse := sphereSupportMap_converse_local hg hi hX hV hn
  intro q hq
  have he := sphereSupportMap_congr_of_eventuallyEq (g := inducedMetric Q) (Q := Q)
    (hh.eventuallyEq_of_mem (hV.mem_nhds hq))
  exact he.symm.trans (hconverse hq).symm

/-- Actual Fermi tensor/Cartesian Hessian correspondence on arbitrary tangent
vectors. Both derivative chains follow from actual reconstruction germs. -/
theorem positiveExitFermi_tensor_pairing {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) {q : Coord} (hq : q ∈ V) (v w : Coord) :
    v ⬝ᵥ (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ) q *ᵥ w) =
      dotProduct (fderiv ℝ (positiveExitFermiSource ζ) q v)
        (planarHessian G (positiveExitFermiSource ζ q) *ᵥ
          fderiv ℝ (positiveExitFermiSource ζ) q w) / planarWeight (positiveExitFermiSource ζ q) := by
  let Q := fermiNormalMap ζ
  let H := positiveExitFermiHeight G ζ
  let X := sphereSupportMap (inducedMetric Q) Q H
  have hg := positiveExitFermi_metric_positive hζ hunit hspeed hscale
  have hi := inducedMetric_isometricOn (fermiNormalMap_contDiff hζ).contDiffOn (U := V)
  have hH : ContDiffOn ℝ ∞ H V := positiveExitFermiHeight_contDiffOn hζ hG hnorth hmap
  have hQu : ∀ p ∈ V, inner ℝ (Q p) (Q p) = 1 :=
    fun p _ => fermiNormalMap_unit hζ hunit hspeed p
  have hpair (i j : Fin 2) : inner ℝ (coordPartial i X q) (coordPartial j Q q) =
      sphereSupportTensor (inducedMetric Q) H q i j :=
    (sphereSupportMap_differential_pairings hg hi hH hV hq hQu i j).2
  have hbilinear : inner ℝ (fderiv ℝ X q v) (fderiv ℝ Q q w) =
      v ⬝ᵥ (sphereSupportTensor (inducedMetric Q) H q *ᵥ w) := by
    rw [fderiv_two_coordinates X q v, fderiv_two_coordinates Q q w]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hpair, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hrec : EqOn (planarSupportMap G ∘ positiveExitFermiSource ζ) X V :=
    fun p hp => (positiveExitFermi_support_reconstruction hζ hunit hspeed hG hU hV
      hnorth hscale hmap hp).symm
  have hnorm := positiveExitFermi_normal_eq hζ hunit hspeed hnorth
  exact hbilinear.symm.trans (identityBand_cartesian_pullback_pairing hG hU hV
    (positiveExitFermiSource_contDiffOn hζ hnorth) hmap hrec hnorm hq v w)

theorem positiveExitFermi_tensor_entry {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) {q : Coord} (hq : q ∈ V) (i j : Fin 2) :
    sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ) q i j =
      dotProduct (fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single i 1 : Coord))
        (planarHessian G (positiveExitFermiSource ζ q) *ᵥ
          fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single j 1 : Coord)) /
        planarWeight (positiveExitFermiSource ζ q) := by
  have he := positiveExitFermi_tensor_pairing hζ hunit hspeed hG hU hV hnorth hscale hmap hq
    (Pi.single i 1 : Coord) (Pi.single j 1 : Coord)
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he

theorem positiveExitFermi_tensor_matrix {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) {q : Coord} (hq : q ∈ V) :
    sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ) q =
      (planarWeight (positiveExitFermiSource ζ q))⁻¹ •
        seamFramedHessian G (positiveExitFermiSource ζ q)
          (fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single 0 1 : Coord))
          (fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single 1 1 : Coord)) := by
  ext i j
  rw [positiveExitFermi_tensor_entry hζ hunit hspeed hG hU hV hnorth hscale hmap hq i j]
  fin_cases i <;> fin_cases j <;>
    simp [seamFramedHessian, seamFrame, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_eq_mul_inv] <;> ring

/-- An actual determinant formula, including the true Cartesian coordinate
Jacobian and positive weight; no curvature transformation is assumed. -/
theorem positiveExitFermi_tensor_det {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) {q : Coord} (hq : q ∈ V) :
    (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ) q).det =
      (positiveExitJacobian (positiveExitFermiSource ζ) q).det^2 *
        (planarHessian G (positiveExitFermiSource ζ q)).det /
        (planarWeight (positiveExitFermiSource ζ q))^2 := by
  have hframe : seamFrame
      (fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single 0 1 : Coord))
      (fderiv ℝ (positiveExitFermiSource ζ) q (Pi.single 1 1 : Coord)) =
      positiveExitJacobian (positiveExitFermiSource ζ) q := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [positiveExitFermi_tensor_matrix hζ hunit hspeed hG hU hV hnorth hscale hmap hq,
    Matrix.det_smul, seamFramedHessian_det, hframe]
  simp only [Fintype.card_fin, div_eq_mul_inv, inv_pow]
  ring

/-- The actual Fermi and north-coordinate differentials force a nonzero
Cartesian Jacobian, by differentiating their true normal identity. -/
theorem positiveExitFermi_jacobian_ne_zero {ζ : ℝ → Ambient} {V : Set Coord}
    (hζ : ContDiff ℝ ∞ ζ) (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hV : IsOpen V) (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    {q : Coord} (hq : q ∈ V) : (positiveExitJacobian (positiveExitFermiSource ζ) q).det ≠ 0 := by
  let P := positiveExitFermiSource ζ
  have hP : ContDiffOn ℝ ∞ P V := positiveExitFermiSource_contDiffOn hζ hnorth
  have hdP := ((hP q hq).contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
  have hnEq := positiveExitFermi_normal_eq hζ hunit hspeed hnorth
  have he := (hnEq.eventuallyEq_of_mem (hV.mem_nhds hq)).fderiv_eq (𝕜 := ℝ)
  have hD : fderiv ℝ (fermiNormalMap ζ) q =
      (fderiv ℝ planarUnitNormal (P q)).comp (fderiv ℝ P q) := by
    rw [← he]
    exact fderiv_comp q (gnomonicNormal_contDiff.differentiable (by simp) (P q)) hdP
  have hiQ := positiveExitFermi_raw_differential_injective hζ hunit hspeed q (hscale q hq)
  have hiP : Function.Injective (fderiv ℝ P q) := by
    intro v w hvw
    apply hiQ
    rw [hD]
    simp only [ContinuousLinearMap.comp_apply, hvw]
  have hmul (v : Coord) : positiveExitJacobian P q *ᵥ v = fderiv ℝ P q v := by
    have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
      ext i
      fin_cases i <;> simp
    conv_rhs => rw [hv]
    ext i
    simp [positiveExitJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two, coordPartial,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    <;> ring
  intro hz
  obtain ⟨v, hv, hzero⟩ := (Matrix.exists_mulVec_eq_zero_iff
    (M := positiveExitJacobian P q)).mpr hz
  apply hv
  apply hiP
  simpa only [hmul, map_zero] using hzero

theorem positiveExitFermi_tensor_det_neg {ζ : ℝ → Ambient} {G : Coord → ℝ}
    {U V : Set Coord} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ s, inner ℝ (ζ s) (ζ s) = 1)
    (hspeed : ∀ s, inner ℝ (deriv ζ s) (deriv ζ s) = 1)
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) (hV : IsOpen V)
    (hnorth : ∀ q ∈ V, 0 < fermiNormalMap ζ q 2)
    (hscale : ∀ q ∈ V, fermiNormalScale (normalLoopCurvature ζ) q ≠ 0)
    (hmap : MapsTo (positiveExitFermiSource ζ) V U) {q : Coord} (hq : q ∈ V)
    (hdet : (planarHessian G (positiveExitFermiSource ζ q)).det < 0) :
    (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) (positiveExitFermiHeight G ζ) q).det < 0 := by
  rw [positiveExitFermi_tensor_det hζ hunit hspeed hG hU hV hnorth hscale hmap hq]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero
      (positiveExitFermi_jacobian_ne_zero hζ hunit hspeed hV hnorth hscale hq)) hdet)
    (sq_pos_of_pos (planarWeight_pos (positiveExitFermiSource ζ q)))

end
end TightVer401
