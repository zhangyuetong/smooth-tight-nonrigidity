import TightVer401.FermiSupportCloseGraph
import TightVer401.FermiSupportPerturbedGraph

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiPerturbedSupport_close_collar_graph {ζ : ℝ → Ambient}
    {H : Coord → ℝ} {U : Set Coord} {P η ε ρ : ℝ} {χ : ℝ → ℝ}
    (hP : 0 < P) (hη : 0 < η) (hρ : 0 < ρ) (hε : ε ≠ 0)
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
    let v := exitPositiveGraphProfile P (fermiSupportSeamSlope κ Hε)
    ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
      0 < |δ| ∧ |δ| < η ∧ 0 < δ * ε ∧
      Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
      (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
      (∀ q, ‖(C q : Ambient) - hζP.lift q‖ < η) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U ∧ |δ * v r| < ρ) ∧
      ∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
          deriv (exitGraphCurve v δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let Hε := fermiPerturbedSupport ε κ H χ
  let U' : Set Coord := U ∩ {p | |p 1| < ρ}
  have hU' : IsOpen U' := hU.inter (isOpen_lt (continuous_apply 1).abs continuous_const)
  have hseam' (r : ℝ) : (![r,0] : Coord) ∈ U' := ⟨hseam r,by simpa using hρ⟩
  have hκ := (normalLoop_actual_smooth hζ).2
  have hκP := (normalLoop_actual_periodic hζ hζP).2
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have haP := (fermiSeam_coefficients_periodic hκP hHP).1
  have hHε : ContDiffOn ℝ ∞ Hε U' :=
    (hH.add (fermiSeamPerturbation_contDiff ha hκ hχ ε).contDiffOn).mono inter_subset_left
  have hHεP : FermiPeriodic P Hε := by
    intro p
    exact congrArg₂ (· + ·) (hHP p) (fermiSeamPerturbation_periodic haP hκP ε p)
  have hj (r) := fermiSeamPerturbation_preserves_support_seam ha hκ hχ hχ0 hU hH ε (hseam r)
  have hz (r) : fermiSupportL κ Hε ![r,0] = 0 := (hj r).1.trans (hzero r)
  have hp (r) : 0 < fermiSeamMixed κ Hε r := by
    have he : fermiSeamMixed κ Hε r = fermiSeamMixed κ H r := (hj r).2.1
    rw [he]; exact hpos r
  have hmε := fermiPerturbedSupport_mean_ne_zero hζ hP hζP hunit hspeed hhemisphere
    hχ hχ0 hU hH hscale hseam hpos hm hε
  obtain ⟨δ,C,hd,hdη,hs,hC,hsm,himm,hco,hclose,hdom,hquad⟩ :=
    exists_fermiSupport_uniformly_close_positive_graph hP hη hζ hζP hunit hspeed hi
      hU' hHε hHεP (fun p hp => hscale p hp.1) hseam' hz hp hmε
  have hmval : exitGraphMean P (fermiSupportSeamSlope κ Hε) =
      -(ε / 2 * ∫ r in 0..P, (κ r)^2) / P := by
    rw [fermiPerturbedSupport_mean hκ hχ hχ0 hU hH hscale hseam hpos P ε,hm]
    ring
  have hmass := normalLoop_hemisphere_curvature_sq_period_pos hζ hP hζP hunit hspeed hhemisphere
  have hfactor : 0 < (∫ r in 0..P, (κ r)^2) / (2*P) :=
    div_pos hmass (mul_pos (by norm_num) hP)
  rw [hmval] at hs
  have hs' : 0 < δ * ε := by
    have he : δ * (-(ε / 2 * ∫ r in 0..P, (κ r)^2) / P) =
      -(δ * ε * ((∫ r in 0..P, (κ r)^2) / (2*P))) := by ring
    rw [he] at hs
    exact (mul_pos_iff_of_pos_right hfactor).mp (neg_lt_zero.mp hs)
  exact ⟨δ,C,hd,hdη,hs',hC,hsm,himm,hco,hclose,fun r hr => hdom r hr,hquad⟩

end
end TightVer401
