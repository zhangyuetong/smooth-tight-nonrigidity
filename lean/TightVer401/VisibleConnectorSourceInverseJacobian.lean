import TightVer401.VisibleConnectorLocalPotential
import TightVer401.PolarSaddleSignCalculus
import TightVer401.AnnularDegreeLocal

/-! Actual determinant calculus for the connector source. The two orientation
reversals (physical ruling and radial-to-physical clock) cancel. No source
injectivity or global scalar potential is assumed here. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Filter
open scoped ContDiff Matrix Topology

theorem visibleConnectorSourceInverseJacobian_columns (F : Coord → Coord) (q : Coord) :
    annularJacobian F q =
      visibleConnectorDet (coordPartial 0 F q) (coordPartial 1 F q) := by
  rw [annularJacobian, ← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply, visibleConnectorDet, coordPartial,
    ContinuousLinearMap.coe_coe]
  ring

theorem visibleConnectorSourceInverseJacobian_comp {F H : Coord → Coord} {q : Coord}
    (hF : DifferentiableAt ℝ F (H q)) (hH : DifferentiableAt ℝ H q) :
    annularJacobian (F ∘ H) q = annularJacobian F (H q) * annularJacobian H q := by
  unfold annularJacobian
  rw [fderiv_comp q hF hH]
  exact LinearMap.det_comp _ _

theorem visibleConnectorSourceInverseJacobian_ruled {p w : ℝ → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (gamma : ℝ → Coord) (q : Coord) :
    annularJacobian (visibleConnectorSource p w) q =
      -visibleConnectorDelta p gamma w q := by
  rw [visibleConnectorSourceInverseJacobian_columns]
  exact visibleConnectorSource_actual_determinant hp hw gamma q

/-- Radius-angle to the actual physical ruling parameters. -/
def visibleConnectorSourceInverseClock (L : ℝ) (h : ℝ → ℝ) (q : Coord) : Coord :=
  ![L * q 1 / (2 * Real.pi), (q 0 - 1) * h (L * q 1 / (2 * Real.pi))]

theorem visibleConnectorSourceInverseClock_contDiff (L : ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (visibleConnectorSourceInverseClock L h) := by
  have hs : ContDiff ℝ ∞ (fun q : Coord => L * q 1 / (2 * Real.pi)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const _
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hs
  · exact ((contDiff_apply ℝ ℝ 0).sub contDiff_const).mul (hh.comp hs)

theorem visibleConnectorSourceInverseClock_partials (L : ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (q : Coord) :
    coordPartial 0 (visibleConnectorSourceInverseClock L h) q =
        ![0, h (L * q 1 / (2 * Real.pi))] ∧
      coordPartial 1 (visibleConnectorSourceInverseClock L h) q =
        ![L / (2 * Real.pi),
          (q 0 - 1) * deriv h (L * q 1 / (2 * Real.pi)) * (L / (2 * Real.pi))] := by
  have hs : HasFDerivAt (fun q : Coord => L * q 1 / (2 * Real.pi))
      ((L / (2 * Real.pi)) • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)) q := by
    convert ((ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt
      (x := q)).const_mul (L / (2 * Real.pi)) using 1 <;> ext x <;> simp <;> ring
  have hh' := ((hh.differentiable (by simp) (L * q 1 / (2 * Real.pi))).hasDerivAt.hasFDerivAt).comp q hs
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := q)
  have hu := (hr.sub_const 1).mul hh'
  let ds : Coord →L[ℝ] ℝ := (L / (2 * Real.pi)) • ContinuousLinearMap.proj 1
  let du : Coord →L[ℝ] ℝ := (q 0 - 1) •
    ((ContinuousLinearMap.toSpanSingleton ℝ (deriv h (L * q 1 / (2 * Real.pi)))).comp ds) +
      h (L * q 1 / (2 * Real.pi)) • ContinuousLinearMap.proj 0
  have hd : HasFDerivAt (visibleConnectorSourceInverseClock L h)
      (ContinuousLinearMap.pi (![ds, du] : Fin 2 → Coord →L[ℝ] ℝ)) q := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hs
    · exact hu
  constructor <;> rw [coordPartial, hd.fderiv] <;>
    ext i <;> fin_cases i <;> simp [ds, du] <;> ring

theorem visibleConnectorSourceInverseClock_jacobian (L : ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (q : Coord) :
    annularJacobian (visibleConnectorSourceInverseClock L h) q =
      -(L / (2 * Real.pi)) * h (L * q 1 / (2 * Real.pi)) := by
  rw [visibleConnectorSourceInverseJacobian_columns,
    (visibleConnectorSourceInverseClock_partials L hh q).1,
    (visibleConnectorSourceInverseClock_partials L hh q).2]
  simp [visibleConnectorDet]
  ring

theorem visibleConnectorSourceInverseJacobian_polar (L : ℝ) {p w : ℝ → Coord}
    {h : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w)
    (hh : ContDiff ℝ ∞ h) (gamma : ℝ → Coord) (q : Coord) :
    annularJacobian (visibleConnectorSource p w ∘ visibleConnectorSourceInverseClock L h) q =
      (L / (2 * Real.pi)) * h (L * q 1 / (2 * Real.pi)) *
        visibleConnectorDelta p gamma w (visibleConnectorSourceInverseClock L h q) := by
  rw [visibleConnectorSourceInverseJacobian_comp
    ((visibleConnectorSource_contDiff hp hw).differentiable (by simp) _)
    ((visibleConnectorSourceInverseClock_contDiff L hh).differentiable (by simp) _),
    visibleConnectorSourceInverseJacobian_ruled hp hw gamma,
    visibleConnectorSourceInverseClock_jacobian L hh]
  ring

theorem visibleConnectorSourceInverseJacobian_polar_chart (q : Coord) :
    annularJacobian saddlePolarChart q = q 0 := by
  calc
    annularJacobian saddlePolarChart q = (seamCoordinateJacobian saddlePolarChart q).det := by
      rw [visibleConnectorSourceInverseJacobian_columns, Matrix.det_fin_two]
      simp only [seamCoordinateJacobian,
        seam_coordPartial_component saddlePolarChart_contDiff, visibleConnectorDet]
      ring
    _ = q 0 := saddlePolarChart_jacobian_det q

/-- A full open polar pullback germ identifies the actual Cartesian source
Jacobian. The conclusion is computed from the literal ruling, not granted. -/
theorem visibleConnectorSourceInverseJacobian_of_polar_germ
    (L : ℝ) {p w : ℝ → Coord} {h : ℝ → ℝ} {F : Coord → Coord}
    (hp : ContDiff ℝ ∞ p) (hw : ContDiff ℝ ∞ w) (hh : ContDiff ℝ ∞ h)
    (gamma : ℝ → Coord) (q : Coord) (hq : 0 < q 0)
    (hF : DifferentiableAt ℝ F (saddlePolarChart q))
    (hGerm : (F ∘ saddlePolarChart) =ᶠ[nhds q]
      (visibleConnectorSource p w ∘ visibleConnectorSourceInverseClock L h)) :
    annularJacobian F (saddlePolarChart q) =
      (L / (2 * Real.pi)) * h (L * q 1 / (2 * Real.pi)) *
        visibleConnectorDelta p gamma w (visibleConnectorSourceInverseClock L h q) / q 0 := by
  apply (eq_div_iff hq.ne').mpr
  rw [← visibleConnectorSourceInverseJacobian_polar_chart q,
    ← visibleConnectorSourceInverseJacobian_comp hF
      (saddlePolarChart_contDiff.differentiable (by simp) q)]
  change (fderiv ℝ (F ∘ saddlePolarChart) q).toLinearMap.det = _
  rw [hGerm.fderiv_eq]
  exact visibleConnectorSourceInverseJacobian_polar L hp hw hh gamma q

end
end TightVer401
