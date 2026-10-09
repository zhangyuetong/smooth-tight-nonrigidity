import TightVer401.VisibleConnectorSourceInverseNativeChartsComposition
import TightVer401.VisibleConnectorSourceInverseCartesianJacobian
import TightVer401.AnnularDegreeGradient
import TightVer401.PositiveExitConstructionContract
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

/-! Actual orientation of the SAME positive-phase native raw source. The
(angle,radius) order reverses orientation; no physical parameter is reversed. -/
namespace TightVer401
noncomputable section
open Set Filter Function OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology Matrix

/-- The contract's matrix is the standard-basis matrix of the actual derivative. -/
theorem visibleConnectorWitnessAssembly_positiveExitJacobian_det
    (P : Coord → Coord) (q : Coord) :
    (positiveExitJacobian P q).det = annularJacobian P q := by
  have hm : positiveExitJacobian P q = LinearMap.toMatrix' (fderiv ℝ P q).toLinearMap := by
    ext i j
    simp only [positiveExitJacobian,LinearMap.toMatrix'_apply,ContinuousLinearMap.coe_coe]
  rw [hm,LinearMap.det_toMatrix']
  rfl

private def witnessOrientationClock (L : ℝ) (q : Coord) : Coord :=
  ![1+q 1,2*Real.pi*q 0/L]

private theorem witnessOrientationClock_differential (L : ℝ) (q : Coord) :
    ∃ A : Coord →L[ℝ] Coord, HasFDerivAt (witnessOrientationClock L) A q ∧
      A (Pi.single 0 1) = ![0,2*Real.pi/L] ∧ A (Pi.single 1 1) = ![1,0] := by
  let A : Coord →L[ℝ] Coord := ContinuousLinearMap.pi
    (![ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2),
      (2*Real.pi/L) • ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)] :
      Fin 2 → Coord →L[ℝ] ℝ)
  have heq : witnessOrientationClock L = fun z => ![1,0] + A z := by
    funext z
    ext i
    fin_cases i <;> simp [witnessOrientationClock,A] <;> ring
  refine ⟨A,?_,?_,?_⟩
  · rw [heq]
    exact A.hasFDerivAt.const_add _
  · ext i
    fin_cases i <;> simp [A]
  · ext i
    fin_cases i <;> simp [A]

private theorem witnessOrientationClock_contDiff (L : ℝ) :
    ContDiff ℝ ∞ (witnessOrientationClock L) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const.add (contDiff_apply ℝ ℝ 1)
  · exact (contDiff_const.mul (contDiff_apply ℝ ℝ 0)).div_const L

private theorem witnessOrientationClock_jacobian (L : ℝ) (q : Coord) :
    annularJacobian (witnessOrientationClock L) q = -(2*Real.pi/L) := by
  obtain ⟨A,hd,h0,h1⟩ := witnessOrientationClock_differential L q
  rw [visibleConnectorSourceInverseJacobian_columns,coordPartial,coordPartial,hd.fderiv,h0,h1]
  simp [visibleConnectorDet]

/-- Exact determinant of the literal native raw source for the SAME Cartesian `F`. -/
theorem visibleConnectorWitnessAssembly_native_raw_source_determinant
    (L : ℝ) {F : Coord → Coord} (q : Coord)
    (hF : DifferentiableAt ℝ F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L])) :
    (positiveExitJacobian (visibleConnectorSourceInverseNativeRawSource L F) q).det =
      annularJacobian F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) *
        (-(2*Real.pi/L)*(1+q 1)) := by
  rw [visibleConnectorWitnessAssembly_positiveExitJacobian_det]
  change annularJacobian (F ∘ (saddlePolarChart ∘ witnessOrientationClock L)) q = _
  have hFclock : DifferentiableAt ℝ F ((saddlePolarChart ∘ witnessOrientationClock L) q) := by
    change DifferentiableAt ℝ F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L])
    exact hF
  rw [visibleConnectorSourceInverseJacobian_comp (F := F)
      (H := saddlePolarChart ∘ witnessOrientationClock L) (q := q) hFclock
    ((saddlePolarChart_contDiff.comp (witnessOrientationClock_contDiff L)).differentiable (by simp) q),
    visibleConnectorSourceInverseJacobian_comp (F := saddlePolarChart)
      (H := witnessOrientationClock L) (q := q)
      (saddlePolarChart_contDiff.differentiable (by simp) _)
      ((witnessOrientationClock_contDiff L).differentiable (by simp) q),
    visibleConnectorSourceInverseJacobian_polar_chart,witnessOrientationClock_jacobian]
  simp only [Function.comp_apply,witnessOrientationClock,Matrix.cons_val_zero]
  ring

theorem visibleConnectorWitnessAssembly_native_raw_source_negative
    {L : ℝ} (hL : 0 < L) {F : Coord → Coord} (q : Coord) (hq : 0 < 1+q 1)
    (hF : DifferentiableAt ℝ F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]))
    (hJ : 0 < annularJacobian F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L])) :
    (positiveExitJacobian (visibleConnectorSourceInverseNativeRawSource L F) q).det < 0 := by
  rw [visibleConnectorWitnessAssembly_native_raw_source_determinant L q hF]
  exact mul_neg_of_pos_of_neg hJ (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (div_pos Real.two_pi_pos hL)) hq)

/-- Actual negative Hessian and actual negative raw-source determinant give the
positive gradient-composite determinant required by the canonical contract. -/
theorem visibleConnectorWitnessAssembly_native_raw_gradient_positive
    {L : ℝ} {F : Coord → Coord} {G : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (q : Coord)
    (hqU : visibleConnectorSourceInverseNativeRawSource L F q ∈ U)
    (hRaw : DifferentiableAt ℝ (visibleConnectorSourceInverseNativeRawSource L F) q)
    (hNeg : (planarHessian G (visibleConnectorSourceInverseNativeRawSource L F q)).det < 0)
    (hSource : (positiveExitJacobian (visibleConnectorSourceInverseNativeRawSource L F) q).det < 0) :
    (positiveExitJacobian (planarGradient G ∘ visibleConnectorSourceInverseNativeRawSource L F) q).det > 0 := by
  rw [visibleConnectorWitnessAssembly_positiveExitJacobian_det,
    visibleConnectorSourceInverseJacobian_comp
      ((planarGradient_contDiffOn hG hU).contDiffAt (hU.mem_nhds hqU) |>.differentiableAt (by simp)) hRaw,
    annularGradientJacobian_eq_hessian_det hG hU hqU]
  rw [visibleConnectorWitnessAssembly_positiveExitJacobian_det] at hSource
  exact mul_pos_of_neg_of_neg hNeg hSource

private theorem witnessOrientation_radius {L : ℝ} {q : Coord} (hq : 0 < 1+q 1) :
    planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) = 1+q 1 :=
  angularDescent_radius_polar (q := ![1+q 1,2*Real.pi*q 0/L]) hq

theorem visibleConnectorWitnessAssembly_native_raw_source_contDiffOn
    (L : ℝ) {F : Coord → Coord} {O : Set Coord}
    (hF : ContDiffOn ℝ ∞ F O)
    (hClosed : {z : Coord | 1 ≤ planarRadius z ∧ planarRadius z ≤ 2} ⊆ O) :
    ContDiffOn ℝ ∞ (visibleConnectorSourceInverseNativeRawSource L F)
      {q : Coord | q 1 ∈ Ioo (0 : ℝ) 1} := by
  apply hF.comp (saddlePolarChart_contDiff.comp (witnessOrientationClock_contDiff L)).contDiffOn
  intro q hq
  apply hClosed
  change 1 ≤ planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) ∧
    planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) ≤ 2
  rw [witnessOrientation_radius (by linarith [hq.1])]
  constructor <;> linarith [hq.1,hq.2]

theorem visibleConnectorWitnessAssembly_native_raw_source_periodic
    {L : ℝ} (hL : L ≠ 0) (F : Coord → Coord) (s t : ℝ) :
    visibleConnectorSourceInverseNativeRawSource L F ![s+L,t] =
      visibleConnectorSourceInverseNativeRawSource L F ![s,t] := by
  unfold visibleConnectorSourceInverseNativeRawSource
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hAngle : 2*Real.pi*(s+L)/L = 2*Real.pi*s/L+2*Real.pi := by
    field_simp [hL]
  rw [hAngle]
  congr 1
  simp [saddlePolarChart,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem visibleConnectorWitnessAssembly_native_raw_source_endpoints
    (L : ℝ) (F : Coord → Coord) (incoming terminal : ℝ → Coord)
    (hIncoming : ∀ s, F (saddlePolarChart ![1,2*Real.pi*s/L]) = incoming s)
    (hTerminal : ∀ s, F (saddlePolarChart ![2,2*Real.pi*s/L]) = terminal s) :
    (∀ s, visibleConnectorSourceInverseNativeRawSource L F ![s,0] = incoming s) ∧
      ∀ s, visibleConnectorSourceInverseNativeRawSource L F ![s,1] = terminal s := by
  constructor
  · intro s
    simpa only [visibleConnectorSourceInverseNativeRawSource,Matrix.cons_val_zero,
      Matrix.cons_val_one,add_zero] using hIncoming s
  · intro s
    simpa only [visibleConnectorSourceInverseNativeRawSource,Matrix.cons_val_zero,
      Matrix.cons_val_one,show (1:ℝ)+1=2 by norm_num] using hTerminal s

theorem visibleConnectorWitnessAssembly_native_raw_source_mapsTo
    (L : ℝ) {F : Coord → Coord} (e0 : OpenPartialHomeomorph Coord Coord)
    (he0S : e0.source = {z : Coord | 1 < planarRadius z ∧ planarRadius z < 2})
    (he0F : (e0 : Coord → Coord) = F) :
    MapsTo (visibleConnectorSourceInverseNativeRawSource L F)
      {q : Coord | q 1 ∈ Ioo (0 : ℝ) 1} e0.target := by
  intro q hq
  change F (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) ∈ e0.target
  rw [← he0F]
  apply e0.map_source
  rw [he0S]
  change 1 < planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) ∧
    planarRadius (saddlePolarChart ![1+q 1,2*Real.pi*q 0/L]) < 2
  rw [witnessOrientation_radius (by linarith [hq.1])]
  constructor <;> linarith [hq.1,hq.2]

private theorem witnessOrientation_complex_point (q : Coord) :
    seamComplexCoord.symm q = positiveExitComplexPoint q := by
  apply seamComplexCoord.injective
  rw [seamComplexCoord.apply_symm_apply,seamComplexCoord_apply]
  ext i
  fin_cases i <;> rfl

/-- Literal complex boundary trace, retaining the audited unit-circle parameter. -/
theorem visibleConnectorWitnessAssembly_complex_circle_trace
    (F : Coord → Coord) (r t : ℝ) :
    annularComplexConjugate F (unitCircleParam 0 r t) =
      positiveExitComplexPoint (F (saddlePolarChart ![r,2*Real.pi*t])) := by
  have hPolar : seamComplexCoord (unitCircleParam 0 r t) = saddlePolarChart ![r,2*Real.pi*t] := by
    ext i
    fin_cases i <;> simp [seamComplexCoord_apply,unitCircleParam,circleMap,
      saddlePolarChart,-Complex.ofReal_mul]
  simp only [annularComplexConjugate,comp_apply,hPolar,witnessOrientation_complex_point]

theorem visibleConnectorWitnessAssembly_complex_physical_boundary
    {L : ℝ} (hL : L ≠ 0) (F : Coord → Coord) (r : ℝ) (trace : ℝ → Coord)
    (hTrace : ∀ s, F (saddlePolarChart ![r,2*Real.pi*s/L]) = trace s) (t : ℝ) :
    annularComplexConjugate F (unitCircleParam 0 r t) = positiveExitComplexPoint (trace (L*t)) := by
  rw [visibleConnectorWitnessAssembly_complex_circle_trace]
  have hAngle : 2*Real.pi*(L*t)/L = 2*Real.pi*t := by
    field_simp [hL]
  rw [← hAngle,hTrace]

end
end TightVer401
