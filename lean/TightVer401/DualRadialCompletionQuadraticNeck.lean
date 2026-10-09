import TightVer401.DualRadialNeckGradientEscape
import TightVer401.QuadraticFillerCartesianConstruction

/-! An existing neck adapter attached inside the actual retained quadratic filler germ. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The existing neck attachment preserves a genuine open collar of the actual Cartesian filler. -/
theorem exists_dualRadialCompletion_quadratic_neck_adapter {R M a j : ℝ}
    (hR : 0 < R) (hM : 0 < M) (ha : 0 < a) (haj : a < j) (hjR : j < R / 2)
    (h bTrace : ℝ → ℝ) :
    let f := dualRadialQuadraticProfile R M (-M * R ^ 2 / 2)
    let B := dualRadialNeckCoefficient (deriv f j) j a
    let C := dualRadialNeckConstant (f j) (deriv f j) j a
    ∃ (bReturned c d : ℝ) (F : ℝ → ℝ),
      j < bReturned ∧ bReturned ∈ Ioo 0 (R / 2) ∧ c ∈ Ioo a j ∧ d ∈ Ioo j bReturned ∧
      Ioo d bReturned ⊆ Ioo 0 (R / 2) ∧
      ContDiffOn ℝ ∞ F (Ioo a bReturned) ∧
      (∀ r ∈ Ioo a bReturned, 0 < deriv F r ∧ deriv (deriv F) r < 0) ∧
      EqOn F (dualRadialNeck C B a) (Ioo a c) ∧ EqOn F f (Ioo d bReturned) ∧
      EqOn (radialPlanarPotential F) (quadraticFillerCartesianPotential R M h bTrace)
        (radialPlanarDomain (Ioo d bReturned)) ∧
      Tendsto (deriv F) (𝓝[>] a) atTop ∧ Tendsto F (𝓝[>] a) (𝓝 C) ∧
      (∀ p ∈ radialPlanarDomain (Ioo a bReturned),
        (planarHessian (radialPlanarPotential F) p).det < 0 ∧
        Function.Injective (fderiv ℝ (planarSupportMap (radialPlanarPotential F)) p) ∧
        gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential F))) p < 0) ∧
      ∀ theta : ℝ, Tendsto (fun r =>
        ‖(WithLp.toLp 2 (planarGradient (radialPlanarPotential F) (dualRadialPlanarRay theta r)) :
          EuclideanSpace ℝ (Fin 2))‖) (𝓝[>] a) atTop := by
  dsimp only
  let f := dualRadialQuadraticProfile R M (-M * R ^ 2 / 2)
  have hf : ContDiffOn ℝ ∞ f (Ioo 0 (R / 2)) :=
    (dualRadialQuadraticProfile_contDiff R M (-M * R ^ 2 / 2)).contDiffOn
  have hj : j ∈ Ioo 0 (R / 2) := ⟨ha.trans haj, hjR⟩
  have hpos : 0 < deriv f j :=
    (dualRadialQuadraticProfile_signs (R := R) (r := j) (d := -M * R ^ 2 / 2)
      hM (by linarith)).1
  have hneg : ∀ r ∈ Ioo 0 (R / 2), deriv (deriv f) r < 0 := by
    intro r hr
    exact (dualRadialQuadraticProfile_signs (R := R) (r := r) (d := -M * R ^ 2 / 2)
      hM (by linarith [hr.2])).2
  obtain ⟨bReturned, c, d, F, hjb, hbU, hc, hd, hcollar, hF, hsigns, hneck, hincoming,
      hescape, hvalue, hgeometry, hgradientEscape⟩ :=
    exists_dualRadialNeck_gradient_adapter isOpen_Ioo hf ha haj hj hpos hneg
  refine ⟨bReturned, c, d, F, hjb, hbU, hc, hd, hcollar, hF, hsigns, hneck, hincoming,
    ?_, hescape, hvalue, hgeometry, hgradientEscape⟩
  intro p hp
  calc
    radialPlanarPotential F p = radialPlanarPotential f p := hincoming hp.2
    _ = quadraticFillerCartesianPotential R M h bTrace p :=
      (quadraticFillerCartesianPotential_inner_germ hR M h bTrace (hcollar hp.2).2.le).symm

end
end TightVer401

