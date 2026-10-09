import TightVer401.FermiSupportPositiveGraph
import TightVer401.FermiSupportPerturbedMean
import TightVer401.FermiGraphCloseness

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiSupport_uniformly_close_positive_graph {ζ : ℝ → Ambient}
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
    (hm : exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ) H) ≠ 0) :
    letI : Fact (0 < P) := ⟨hP⟩
    let b := fermiSupportSeamSlope (normalLoopCurvature ζ) H
    let v := exitPositiveGraphProfile P b
    ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
      0 < |δ| ∧ |δ| < η ∧ δ * exitGraphMean P b < 0 ∧
      Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
      (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
      (∀ q, ‖(C q : Ambient) - hζP.lift q‖ < η) ∧
      (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U) ∧
      ∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) H (exitGraphCurve v δ r) *ᵥ
          deriv (exitGraphCurve v δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let b := fermiSupportSeamSlope κ H
  have hκ := (normalLoop_actual_smooth hζ).2
  have hκP := (normalLoop_actual_periodic hζ hζP).2
  have hac := fermiSeam_coefficients_smooth hκ hU hH hscale hseam
  have hacP := fermiSeam_coefficients_periodic hκP hHP
  have hb : ContDiff ℝ ∞ b := fermiSeamSlopeCoefficient_contDiff hac.1 hκ hac.2 hpos
  have hbP : Function.Periodic b P :=
    fermiSeamSlopeCoefficient_periodic hac.1 hacP.1 hκP hacP.2
  let hvP := exitPositiveGraphProfile_periodic hP hb hbP
  obtain ⟨e, he, hclose⟩ := fermiGraph_exists_uniform_closeness_radius hP hη hζ hζP
    (exitPositiveGraphProfile_contDiff hb) hvP
  obtain ⟨δ, hd, hdsmall, hs, hiC, hsm, himm, hdom, hquad⟩ :=
    exists_fermiSupport_positive_embedded_graph hP (lt_min hη he) hζ hζP
      hunit hspeed hi hU hH hHP hscale hseam hzero hpos hm
  have hdη : |δ| < η := hdsmall.trans_le (min_le_left _ _)
  have hde : |δ| < e := hdsmall.trans_le (min_le_right _ _)
  let C := fermiNativeSphereGraph hζ hζP hunit hspeed hvP δ
  have hco (r : ℝ) : (C (periodProjection P r) : Ambient) =
      fermiNormalMap ζ (exitGraphCurve (exitPositiveGraphProfile P b) δ r) :=
    fermiNativeGraph_coe hζ hζP hvP δ r
  refine ⟨δ, C, hd, hdη, hs, hiC, hsm, himm, hco, ?_, hdom, hquad⟩
  intro q
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  change ‖(C (periodProjection P r) : Ambient) - hζP.lift (periodProjection P r)‖ < η
  rw [hco, periodicLift_coe]
  exact hclose δ hde r

end
end TightVer401
