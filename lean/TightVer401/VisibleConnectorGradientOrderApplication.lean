import TightVer401.VisibleConnectorGradientOrder
import TightVer401.AnnularDegreeGradient

/-! Reversed gradient-disk order for the SAME supplied final potential. Actual
normalized positive boundary traces and Hessian sign discharge the signed-count
consumer; target nesting and an inverse are not inputs. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- Apply the actual negative-map order theorem to the SAME actual gradient.
Only interior Hessian negativity is needed for this order conclusion. -/
theorem visibleConnectorGradientOrder_planarGradient
    {Ho Hi To Ti : ℂ ≃ₜ ℂ} {gammaOuter gammaInner etaOuter etaInner : ℝ → ℂ}
    (hSourceOuter : PositiveJordanParametrization Ho gammaOuter)
    (hSourceInner : PositiveJordanParametrization Hi gammaInner)
    (hTargetInner : PositiveJordanParametrization Ti etaOuter)
    (hTargetOuter : PositiveJordanParametrization To etaInner)
    (hSourceNested : closure (jordanInterior Hi) ⊆ jordanInterior Ho)
    {G : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hKU : annularCoordJordanClosure Ho Hi ⊆ U)
    (hNeg : ∀ z ∈ annularCoordJordanInterior Ho Hi, (planarHessian G z).det < 0)
    (hTraceOuter : ∀ t, annularComplexConjugate (planarGradient G) (gammaOuter t) = etaOuter t)
    (hTraceInner : ∀ t, annularComplexConjugate (planarGradient G) (gammaInner t) = etaInner t)
    (hDisjoint : Disjoint (frontier (jordanInterior Ti)) (frontier (jordanInterior To)))
    {c : ℂ} (hcInner : c ∈ jordanInterior Ti) (hcOuter : c ∈ jordanInterior To) :
    closure (jordanInterior Ti) ⊆ jordanInterior To := by
  let Oc : Set ℂ := seamComplexCoord ⁻¹' U
  let Fc := annularComplexConjugate (planarGradient G)
  have hOc : IsOpen Oc := hU.preimage seamComplexCoord.continuous
  have hFc : ContDiffOn ℝ ∞ Fc Oc :=
    seamComplexCoord.symm.contDiff.comp_contDiffOn
      ((planarGradient_contDiffOn hG hU).comp seamComplexCoord.contDiff.contDiffOn
        (fun _ hz => hz))
  have hKOc : annularJordanClosure Ho Hi ⊆ Oc := by
    intro z hz
    exact hKU (mem_image_of_mem seamComplexCoord hz)
  have hNegative : ∀ z ∈ annularJordanInterior Ho Hi, (fderiv ℝ Fc z).det < 0 := by
    intro z hz
    have hzCoord : seamComplexCoord z ∈ annularCoordJordanInterior Ho Hi :=
      mem_image_of_mem seamComplexCoord hz
    have hzU : seamComplexCoord z ∈ U := hKU (mem_image_of_mem seamComplexCoord
      (annularJordanInterior_subset_closure Ho Hi hz))
    have hd : DifferentiableAt ℝ (planarGradient G) (seamComplexCoord z) :=
      (planarGradient_contDiffOn hG hU).contDiffAt (hU.mem_nhds hzU) |>.differentiableAt (by simp)
    have heq := annular_complex_conjugate_jacobian hd
    change annularJacobian (planarGradient G) (seamComplexCoord z) = (fderiv ℝ Fc z).det at heq
    rw [← heq,annularGradientJacobian_eq_hessian_det hG hU hzU]
    exact hNeg _ hzCoord
  have hOuterFun : Fc ∘ gammaOuter = etaOuter := funext hTraceOuter
  have hInnerFun : Fc ∘ gammaInner = etaInner := funext hTraceInner
  have hImageOuter : PositiveJordanParametrization Ti (Fc ∘ gammaOuter) := by
    rw [hOuterFun]
    exact hTargetInner
  have hImageInner : PositiveJordanParametrization To (Fc ∘ gammaInner) := by
    rw [hInnerFun]
    exact hTargetOuter
  exact visibleConnector_actual_negative_map_reverses_positive_jordan_order
    (Ho := Ho) (Hi := Hi) (To := Ti) (Ti := To)
    hSourceOuter.toRegular hSourceInner.toRegular hSourceNested
    (annular_positive_source_argument_integral hSourceOuter)
    (annular_positive_source_argument_integral hSourceInner)
    Fc Oc hOc hFc hKOc hNegative hImageOuter hImageInner hDisjoint hcInner hcOuter

end
end TightVer401
