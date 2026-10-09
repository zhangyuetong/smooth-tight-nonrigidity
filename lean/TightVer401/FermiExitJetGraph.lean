import TightVer401.FermiExitSmoothConvergence
import TightVer401.FermiSupportPerturbedCloseGraph
import TightVer401.FermiExitSaddleGraph
import TightVer401.FermiGraphFiniteJetConvergence

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiExit_jet_close_positive_graph {ζ : ℝ → Ambient}
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
    (hm : exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ) H) = 0) (n : ℕ) :
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
      (∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
          deriv (exitGraphCurve v δ) r)) ∧
      (∀ r ∈ Icc (0 : ℝ) P,
        (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r)).det < 0) ∧
      ∀ j ≤ n, ∀ r ∈ Icc (0 : ℝ) P,
        ‖iteratedFDeriv ℝ j (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
          iteratedFDeriv ℝ j ζ r‖ < η := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let Hε := fermiPerturbedSupport ε κ H χ
  let v := exitPositiveGraphProfile P (fermiSupportSeamSlope κ Hε)
  have hκ := (normalLoop_actual_smooth hζ).2
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have hHε : ContDiffOn ℝ ∞ Hε U :=
    hH.add (fermiSeamPerturbation_contDiff ha hκ hχ ε).contDiffOn
  have hj (r) := fermiSeamPerturbation_preserves_support_seam ha hκ hχ hχ0 hU hH ε (hseam r)
  have hz (r) : fermiSupportL κ Hε ![r,0] = 0 := (hj r).1.trans (hzero r)
  have hp (r) : 0 < fermiSeamMixed κ Hε r := by
    have he : fermiSeamMixed κ Hε r = fermiSeamMixed κ H r := (hj r).2.1
    rw [he]; exact hpos r
  have hv : ContDiff ℝ ∞ v :=
    fermiPerturbedSupport_profile_contDiff hκ hχ hχ0 hU hH hscale hseam hpos ε P
  obtain ⟨eJ,heJ,hjet⟩ := fermiGraph_uniform_finite_jet_convergence hζ hv n (P := P) hη
  obtain ⟨eS,heS,hsaddle⟩ := exists_fermiSupport_graph_saddle_radius (P := P)
    hκ hv hU hHε hscale hseam hz hp
  let ν := min η (min eJ eS)
  have hν : 0 < ν := lt_min hη (lt_min heJ heS)
  obtain ⟨δ,C,hd,hdν,hs,hC,hsm,himm,hco,hclose,hdom,hquad⟩ :=
    exists_fermiPerturbedSupport_close_collar_graph hP hν hρ hε hζ hζP hunit hspeed hi
      hhemisphere hχ hχ0 hU hH hHP hscale hseam hzero hpos hm
  have hdη : |δ| < η := hdν.trans_le (min_le_left _ _)
  have hdJ : |δ| < eJ := hdν.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdS : |δ| < eS := hdν.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,C,hd,hdη,hs,hC,hsm,himm,hco,
    fun q => (hclose q).trans_le (min_le_left _ _),hdom,hquad,?_,hjet δ hdJ⟩
  intro r hr
  rw [fermiNormalMap_inducedMetric hζ hunit hspeed]
  exact (hsaddle δ hdS r hr).2

end
end TightVer401
