import TightVer401.FermiSupportPositiveGraph
import TightVer401.FermiSupportPerturbedMean

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiPerturbedSupport_positive_embedded_graph {ζ : ℝ → Ambient}
    {H : Coord → ℝ} {U : Set Coord} {P η ε : ℝ} {χ : ℝ → ℝ}
    (hP : 0 < P) (hη : 0 < η) (hε : ε ≠ 0)
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζP.lift)
    {e : Ambient} (hhemisphere : ∀ r, 0 < inner ℝ (ζ r) e)
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (hHP : FermiPeriodic P H)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL (normalLoopCurvature ζ) H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed (normalLoopCurvature ζ) H r)
    (hm : exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ) H) = 0) :
    letI : Fact (0 < P) := ⟨hP⟩
    let κ := normalLoopCurvature ζ
    let Hε := fermiPerturbedSupport ε κ H χ
    let b := fermiSupportSeamSlope κ Hε
    let v := exitPositiveGraphProfile P b
    ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
      0 < |δ| ∧ |δ| < η ∧ 0 < δ * ε ∧
      Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
      (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U) ∧
      ∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
          deriv (exitGraphCurve v δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let Hε := fermiPerturbedSupport ε κ H χ
  let b := fermiSupportSeamSlope κ Hε
  have hκ := (normalLoop_actual_smooth hζ).2
  have hκP := (normalLoop_actual_periodic hζ hζP).2
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have haP := (fermiSeam_coefficients_periodic hκP hHP).1
  have hHε : ContDiffOn ℝ ∞ Hε U :=
    hH.add (fermiSeamPerturbation_contDiff ha hκ hχ ε).contDiffOn
  have hHεP : FermiPeriodic P Hε := by
    intro p
    exact congrArg₂ (· + ·) (hHP p) (fermiSeamPerturbation_periodic haP hκP ε p)
  have hj (r) := fermiSeamPerturbation_preserves_support_seam ha hκ hχ hχ0 hU hH ε (hseam r)
  have hzeroε (r) : fermiSupportL κ Hε ![r,0] = 0 := (hj r).1.trans (hzero r)
  have hposε (r) : 0 < fermiSeamMixed κ Hε r := by
    have heq : fermiSeamMixed κ Hε r = fermiSeamMixed κ H r := (hj r).2.1
    rw [heq]
    exact hpos r
  have hmε : exitGraphMean P b ≠ 0 :=
    fermiPerturbedSupport_mean_ne_zero hζ hP hζP hunit hspeed hhemisphere
      hχ hχ0 hU hH hscale hseam hpos hm hε
  have hacε := fermiSeam_coefficients_smooth hκ hU hHε hscale hseam
  have hacεP := fermiSeam_coefficients_periodic hκP hHεP
  have hb : ContDiff ℝ ∞ b := fermiSeamSlopeCoefficient_contDiff hacε.1 hκ hacε.2 hposε
  have hbP : Function.Periodic b P :=
    fermiSeamSlopeCoefficient_periodic hacε.1 hacεP.1 hκP hacεP.2
  let hvP := exitPositiveGraphProfile_periodic hP hb hbP
  obtain ⟨δ, hd, hdη, hsign, he, hsm, himm, hdom, hquad⟩ :=
    exists_fermiSupport_positive_embedded_graph hP hη hζ hζP hunit hspeed hi
      hU hHε hHεP hscale hseam hzeroε hposε hmε
  have hmass := normalLoop_hemisphere_curvature_sq_period_pos hζ hP hζP hunit hspeed hhemisphere
  have hmean : exitGraphMean P b =
      -(ε / 2 * ∫ r in 0..P, (κ r)^2) / P := by
    rw [fermiPerturbedSupport_mean hκ hχ hχ0 hU hH hscale hseam hpos P ε, hm]
    ring
  have hs : 0 < δ * ε := by
    change δ * exitGraphMean P b < 0 at hsign
    rw [hmean] at hsign
    have hp : 0 < (∫ r in 0..P, (κ r)^2) / (2 * P) :=
      div_pos hmass (mul_pos (by norm_num) hP)
    have heq : δ * (-(ε / 2 * ∫ r in 0..P, (κ r)^2) / P) =
        -(δ * ε * ((∫ r in 0..P, (κ r)^2) / (2 * P))) := by ring
    rw [heq] at hsign
    exact (mul_pos_iff_of_pos_right hp).mp (neg_lt_zero.mp hsign)
  refine ⟨δ, fermiNativeSphereGraph hζ hζP hunit hspeed hvP δ,
    hd, hdη, hs, he, hsm, himm, ?_, hdom, hquad⟩
  intro r
  change fermiNativeGraph hζ hζP hvP δ (periodProjection P r) = _
  exact fermiNativeGraph_coe hζ hζP hvP δ r

end
end TightVer401
