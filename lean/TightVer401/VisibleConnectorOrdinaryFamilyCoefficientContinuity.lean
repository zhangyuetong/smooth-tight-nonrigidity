import TightVer401.VisibleConnectorDisplacedSeamRebase

/-! Actual ruling coefficient continuity on the SAME open joint domain.
Longitudinal derivatives are computed from the joint derivative in direction
(0,1). These exports discharge the continuity inputs of LowerDelta without
selecting or assuming any inverse or determinant sign. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Actual longitudinal derivative of a joint displacement family. -/
theorem visibleConnectorOrdinaryFamilyCoefficientContinuity_longitudinal
    {P : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    deriv (fun s => P (z.1, s)) z.2 = fderiv ℝ P z (0, 1) := by
  have hf : DifferentiableAt ℝ P z :=
    ((hP z hz).contDiffAt (hOmega.mem_nhds hz)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hc := hf.hasFDerivAt.comp_hasDerivAt z.2 hpath
  simpa only [Function.comp_def] using hc.deriv

/-- Smooth joint data imply continuity of the actual slice derivative. -/
theorem visibleConnectorOrdinaryFamilyCoefficientContinuity_deriv
    {P : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega) :
    ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => P (z.1, s)) z.2) Omega := by
  have hconst : ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) Omega :=
    continuous_const.continuousOn
  exact (((hP.continuousOn_fderiv_of_isOpen hOmega (by simp)).clm_apply hconst).congr
    (fun z hz => visibleConnectorOrdinaryFamilyCoefficientContinuity_longitudinal
      hOmega hP hz))

private theorem coefficientContinuity_det
    {v w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hv : ContinuousOn v Omega) (hw : ContinuousOn w Omega) :
    ContinuousOn (fun z => visibleConnectorDet (v z) (w z)) Omega := by
  have hv0 : ContinuousOn (fun z => v z 0) Omega :=
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hv
  have hv1 : ContinuousOn (fun z => v z 1) Omega :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hv
  have hw0 : ContinuousOn (fun z => w z 0) Omega :=
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).continuous.comp_continuousOn hw
  have hw1 : ContinuousOn (fun z => w z 1) Omega :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).continuous.comp_continuousOn hw
  exact (hv0.mul hw1).sub (hv1.mul hw0)

/-- The two actual coefficient maps required by the SAME lower-Delta
producer are continuous on their given joint open domain. -/
theorem visibleConnectorOrdinaryFamilyCoefficientContinuity_actual
    {p w : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega)
    (hp : ContDiffOn ℝ ∞ p Omega) (hw : ContDiffOn ℝ ∞ w Omega) :
    ContinuousOn (fun z : ℝ × ℝ =>
      visibleConnectorA (fun s => p (z.1, s)) (fun s => w (z.1, s)) z.2) Omega ∧
    ContinuousOn (fun z : ℝ × ℝ =>
      visibleConnectorDet (deriv (fun s => w (z.1, s)) z.2) (w z)) Omega := by
  constructor
  · exact (coefficientContinuity_det
      (visibleConnectorOrdinaryFamilyCoefficientContinuity_deriv hOmega hp)
      hw.continuousOn).neg
  · exact coefficientContinuity_det
      (visibleConnectorOrdinaryFamilyCoefficientContinuity_deriv hOmega hw)
      hw.continuousOn

end
end TightVer401
