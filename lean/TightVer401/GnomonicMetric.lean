import TightVer401.GnomonicCoordinates
import TightVer401.PlanarSupportSecondForm
import TightVer401.ScalarCoordinateCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace

theorem gnomonicWeight_coordPartial (p : Coord) (i : Fin 2) :
    coordPartial i planarWeight p = p i / planarWeight p := by
  let P₀ : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)
  let P₁ : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)
  have hf := ((hasFDerivAt_const (c := (1 : ℝ)) p).add (P₀.hasFDerivAt.pow 2)).add
    (P₁.hasFDerivAt.pow 2)
  have hpos : 0 < 1 + p 0 ^ 2 + p 1 ^ 2 := by positivity
  have hs := hf.sqrt (ne_of_gt hpos)
  change HasFDerivAt planarWeight _ p at hs
  unfold coordPartial
  rw [hs.fderiv]
  simp only [smul_apply, add_apply, zero_apply, smul_eq_mul,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, nsmul_eq_mul]
  simp only [Pi.add_apply, P₀, P₁, ContinuousLinearMap.proj_apply]
  change (1 / (2 * planarWeight p)) *
    (0 + 2 * p 0 * (Pi.single i (1 : ℝ) : Coord) 0 +
      2 * p 1 * (Pi.single i (1 : ℝ) : Coord) 1) = p i / planarWeight p
  fin_cases i <;> simp <;> ring

theorem gnomonicNormal_coordPartial (p : Coord) (i : Fin 2) :
    coordPartial i planarUnitNormal p =
      (planarWeight p)⁻¹ • coordPartial i planarNormalNumerator p -
        (p i / planarWeight p ^ 3) • planarNormalNumerator p := by
  have hw : planarWeight p ≠ 0 := ne_of_gt (planarWeight_pos p)
  have hdw : DifferentiableAt ℝ planarWeight p :=
    gnomonicWeight_contDiff.contDiffAt.differentiableAt (by simp)
  have hdi : DifferentiableAt ℝ (fun q => (planarWeight q)⁻¹) p := hdw.inv hw
  have hdP : DifferentiableAt ℝ planarNormalNumerator p :=
    planarNormalNumerator_contDiff.contDiffAt.differentiableAt (by simp)
  have he : planarUnitNormal = fun q => (planarWeight q)⁻¹ • planarNormalNumerator q :=
    funext planarUnitNormal_eq_smul
  rw [he]
  unfold coordPartial
  have hderiv := hdi.hasFDerivAt.smul hdP.hasFDerivAt
  change HasFDerivAt (fun q => (planarWeight q)⁻¹ • planarNormalNumerator q) _ p at hderiv
  rw [hderiv.fderiv]
  change (planarWeight p)⁻¹ • coordPartial i planarNormalNumerator p +
    coordPartial i (fun q => (planarWeight q)⁻¹) p • planarNormalNumerator p = _
  rw [coordPartial_scalar_inv hdw hw, gnomonicWeight_coordPartial]
  have hcoef : -(p i / planarWeight p) / planarWeight p ^ 2 =
      -(p i / planarWeight p ^ 3) := by field_simp [hw]
  rw [hcoef, neg_smul, sub_eq_add_neg]
  rfl

theorem gnomonicNumerator_partial_inner (p : Coord) (i j : Fin 2) :
    inner ℝ (coordPartial i planarNormalNumerator p) (coordPartial j planarNormalNumerator p) =
      if i = j then 1 else 0 := by
  rw [planarNormalNumerator_coordPartial, planarNormalNumerator_coordPartial]
  simp only [EuclideanSpace.inner_toLp_toLp]
  fin_cases i <;> fin_cases j <;> simp [dotProduct, Fin.sum_univ_succ]

theorem gnomonicNumerator_partial_pairing (p : Coord) (i : Fin 2) :
    inner ℝ (coordPartial i planarNormalNumerator p) (planarNormalNumerator p) = p i := by
  rw [planarNormalNumerator_coordPartial]
  simp only [planarNormalNumerator, EuclideanSpace.inner_toLp_toLp]
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_succ]

theorem gnomonicNumerator_inner_self (p : Coord) :
    inner ℝ (planarNormalNumerator p) (planarNormalNumerator p) = planarWeight p ^ 2 := by
  rw [planarWeight_sq]
  simp only [planarNormalNumerator, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_succ]
  ring

theorem gnomonic_inducedMetric (p : Coord) (i j : Fin 2) :
    inducedMetric planarUnitNormal p i j =
      (if i = j then 1 else 0) / planarWeight p ^ 2 - p i * p j / planarWeight p ^ 4 := by
  change inner ℝ (coordPartial i planarUnitNormal p) (coordPartial j planarUnitNormal p) = _
  rw [gnomonicNormal_coordPartial, gnomonicNormal_coordPartial]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    gnomonicNumerator_partial_inner, gnomonicNumerator_partial_pairing,
    gnomonicNumerator_inner_self]
  rw [real_inner_comm (coordPartial j planarNormalNumerator p) (planarNormalNumerator p),
    gnomonicNumerator_partial_pairing]
  field_simp [ne_of_gt (planarWeight_pos p)]
  ring

theorem gnomonic_inducedMetric_det (p : Coord) :
    (inducedMetric planarUnitNormal p).det = (planarWeight p)⁻¹ ^ 6 := by
  rw [Matrix.det_fin_two]
  simp [gnomonic_inducedMetric]
  have hw : planarWeight p ≠ 0 := ne_of_gt (planarWeight_pos p)
  field_simp [hw]
  linear_combination (planarWeight p ^ 2) * planarWeight_sq p

theorem gnomonic_metric :
    SmoothPositiveOn (inducedMetric planarUnitNormal) univ ∧
    IsometricOn (inducedMetric planarUnitNormal) planarUnitNormal univ := by
  have hQ : ContDiffOn ℝ ∞ planarUnitNormal univ := gnomonicNormal_contDiff.contDiffOn
  exact ⟨inducedMetric_smoothPositiveOn hQ isOpen_univ
    (fun p _ => gnomonicNormal_differential_injective p), inducedMetric_isometricOn hQ⟩

end
end TightVer401
