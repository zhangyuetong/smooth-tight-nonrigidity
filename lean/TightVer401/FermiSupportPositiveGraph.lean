import TightVer401.FermiSeamCoefficient
import TightVer401.ExitPositiveGraphEmbeddedChoice
import TightVer401.ExitPositiveGraphFermiImmersion

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem fermiSupport_actual_matrix {κ : ℝ → ℝ} {H : Coord → ℝ} {U : Set Coord}
    (hκ : ContDiff ℝ ∞ κ) (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    {p : Coord} (hp : p ∈ U) (hscale : fermiNormalScale κ p ≠ 0) :
    sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p =
      !![fermiSupportL κ H p, fermiSupportM κ H p;
        fermiSupportM κ H p, fermiSupportN H p] := by
  have he := fermiSupport_actual_entries hκ H hscale
  have hc := fermiMetric_christoffel
    ((fermiNormalScale_contDiff hκ).differentiable (by simp) p) hscale
  have h10 : sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p 1 0 =
      fermiSupportM κ H p := by
    simp only [sphereSupportTensor, covHessian, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      hc.2.2.1, hc.2.2.2.2.2.2.1, fermiMetric, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_zero, add_zero, zero_mul, fermiSupportM]
    rw [coordPartial_comm hH hU hp 1 0]
  ext i j
  fin_cases i <;> fin_cases j
  · exact he.1
  · exact he.2.1
  · exact h10
  · exact he.2.2

theorem exists_fermiSupport_positive_embedded_graph {ζ : ℝ → Ambient}
    {H : Coord → ℝ} {U : Set Coord} {P η : ℝ}
    (hP : 0 < P) (hη : 0 < η)
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζP.lift)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (hHP : FermiPeriodic P H)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL (normalLoopCurvature ζ) H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed (normalLoopCurvature ζ) H r)
    (hm : exitGraphMean P (fermiSeamSlopeCoefficient
      (fermiSeamMixed (normalLoopCurvature ζ) H) (normalLoopCurvature ζ)
      (fermiSeamNormal H)) ≠ 0) :
    letI : Fact (0 < P) := ⟨hP⟩
    let b := fermiSeamSlopeCoefficient (fermiSeamMixed (normalLoopCurvature ζ) H)
      (normalLoopCurvature ζ) (fermiSeamNormal H)
    let v := exitPositiveGraphProfile P b
    let hvP := exitPositiveGraphProfile_periodic hP
      (fermiSeamSlopeCoefficient_contDiff
        (fermiSeam_coefficients_smooth (normalLoop_actual_smooth hζ).2 hU hH hscale hseam).1
        (normalLoop_actual_smooth hζ).2
        (fermiSeam_coefficients_smooth (normalLoop_actual_smooth hζ).2 hU hH hscale hseam).2 hpos)
      (fermiSeamSlopeCoefficient_periodic
        (fermiSeam_coefficients_smooth (normalLoop_actual_smooth hζ).2 hU hH hscale hseam).1
        (fermiSeam_coefficients_periodic (normalLoop_actual_periodic hζ hζP).2 hHP).1
        (normalLoop_actual_periodic hζ hζP).2
        (fermiSeam_coefficients_periodic (normalLoop_actual_periodic hζ hζP).2 hHP).2)
    ∃ δ : ℝ, 0 < |δ| ∧ |δ| < η ∧ δ * exitGraphMean P b < 0 ∧
      Topology.IsEmbedding (fermiNativeSphereGraph hζ hζP hunit hspeed hvP δ) ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fermiNativeSphereGraph hζ hζP hunit hspeed hvP δ) ∧
      (∀ q : AddCircle P, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
        (fermiNativeSphereGraph hζ hζP hunit hspeed hvP δ) q)) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U) ∧
      ∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) H (exitGraphCurve v δ r) *ᵥ
          deriv (exitGraphCurve v δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let a := fermiSeamMixed κ H
  let c := fermiSeamNormal H
  let b := fermiSeamSlopeCoefficient a κ c
  have hκ : ContDiff ℝ ∞ κ := (normalLoop_actual_smooth hζ).2
  have hκP : Function.Periodic κ P := (normalLoop_actual_periodic hζ hζP).2
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have hacP := fermiSeam_coefficients_periodic hκP hHP
  have hb : ContDiff ℝ ∞ b := fermiSeamSlopeCoefficient_contDiff hac.1 hκ hac.2 hpos
  have hbP : Function.Periodic b P :=
    fermiSeamSlopeCoefficient_periodic hac.1 hacP.1 hκP hacP.2
  have hLMN := fermiSupport_contDiffOn hκ hU hH hscale
  have hperiod := fermiSupport_periodic hκP hHP
  obtain ⟨δ, hd, hdη, hs, he, hsm, hreg, hdom, hquad⟩ :=
    exists_exitPositiveGraph_embedded hP hη hζ hζP hunit hspeed hi hb hbP
      hU hLMN.1 hLMN.2.1 hLMN.2.2
      ((fermiPeriodic_iff_slices P _).mp hperiod.1)
      ((fermiPeriodic_iff_slices P _).mp hperiod.2.1)
      ((fermiPeriodic_iff_slices P _).mp hperiod.2.2) hm
      (fun r _ => hseam r) (fun r _ => hzero r) (fun _ _ => rfl)
      (fun r _ => hpos r)
      (fun r _ => (fermiSupport_local_seam_slope_coefficient hκ hU hH hscale
        (hseam r) (hzero r) (hpos r)).1)
  refine ⟨δ, hd, hdη, hs, he, hsm, ?_, hdom, ?_⟩
  · exact fermiNativeSphereGraph_mfderiv_injective hζ hζP hunit hspeed
      (exitPositiveGraphProfile_contDiff hb) (exitPositiveGraphProfile_periodic hP hb hbP)
      δ hreg
  · intro r hr
    rw [fermiNormalMap_inducedMetric hζ hunit hspeed,
      fermiSupport_actual_matrix hκ hU hH (hdom r hr) (hscale _ (hdom r hr))]
    exact hquad r

end
end TightVer401
