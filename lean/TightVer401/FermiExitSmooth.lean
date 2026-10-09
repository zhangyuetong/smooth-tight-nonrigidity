import TightVer401.FermiExitJetGraph
import TightVer401.FermiExitPositivePerturbation
import TightVer401.FermiSupportIdentityMean
import TightVer401.FermiSupportPerturbedFlow
import TightVer401.FermiSupportPerturbedCloseGraph

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Manifold Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual exit perturbation: the baseline identity is a return germ of a smooth
solution family, and the perturbed nonlinear return family is constructed. -/
theorem exists_fermiExit_smooth_perturbation {ζ : ℝ → Ambient}
    {H u₀ : Coord → ℝ} {U V₀ K : Set Coord} {P ρ η ξ σ : ℝ}
    (hP : 0 < P) (hρ : 0 < ρ) (hη : 0 < η) (hξ : 0 < ξ) (hσ : σ ≠ 0)
    (hζ : ContDiff ℝ ∞ ζ) (hζP : Function.Periodic ζ P)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1)
    (hi : Function.Injective hζP.lift)
    {e : Ambient} (hhemisphere : ∀ r, 0 < inner ℝ (ζ r) e)
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) (hHP : FermiPeriodic P H)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hscale : ∀ p ∈ U, fermiNormalScale (normalLoopCurvature ζ) p ≠ 0)
    (hseam : ∀ r, (![r,0] : Coord) ∈ U)
    (hzero : ∀ r, fermiSupportL (normalLoopCurvature ζ) H ![r,0] = 0)
    (hpos : ∀ r, 0 < fermiSeamMixed (normalLoopCurvature ζ) H r)
    (hV₀ : IsOpen V₀) (hu₀ : ContDiffOn ℝ ∞ u₀ V₀)
    (hode₀ : ∀ q ∈ V₀, coordPartial 0 u₀ q =
      fermiSupportAsymptoticSlope (normalLoopCurvature ζ) H ![q 0,u₀ q])
    (hvs₀ : ∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V₀)
    (huzero₀ : ∀ r ∈ Icc (0 : ℝ) P, u₀ ![r,0] = 0)
    (hinitial₀ : (fun x : ℝ => u₀ ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hreturn₀ : (fun x : ℝ => u₀ ![P,x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hdet : ∀ p ∈ K,
      (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) H p).det < 0) :
    letI : Fact (0 < P) := ⟨hP⟩
    ∃ ε : ℝ, 0 < ε * σ ∧ |ε| < ξ ∧
      let κ := normalLoopCurvature ζ
      let Hε := fermiPerturbedSupport ε κ H (fermiExitCutoff ρ hρ)
      let v := exitPositiveGraphProfile P (fermiSupportSeamSlope κ Hε)
      ContDiffOn ℝ ∞ Hε U ∧ FermiPeriodic P Hε ∧
      (∀ p, ρ ≤ |p 1| → Hε p = H p) ∧
      (∀ r, Hε ![r,0] = H ![r,0] ∧
        coordPartial 0 Hε ![r,0] = coordPartial 0 H ![r,0] ∧
        coordPartial 1 Hε ![r,0] = coordPartial 1 H ![r,0]) ∧
      (∀ p ∈ K, fermiCoordinateC2Size (fun q => Hε q - H q) p < η) ∧
      (∀ p ∈ K, (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε p).det < 0) ∧
      ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
        (∀ q ∈ V, (![q 0,u q] : Coord) ∈ U) ∧
        (∀ q ∈ V, coordPartial 0 u q = fermiSupportAsymptoticSlope κ Hε ![q 0,u q]) ∧
        (∀ r ∈ Icc (0 : ℝ) P, (![r,0] : Coord) ∈ V ∧ u ![r,0] = 0) ∧
        ((fun x : ℝ => u ![0,x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
        HasDerivAt (fun x : ℝ => u ![P,x])
          (Real.exp (-(ε / 2 * ∫ r in 0..P, (κ r)^2))) 0 ∧
        (0 < ε → ∃ d > 0, ∀ x : ℝ, |x| < d →
          (∀ n : ℕ, |((fun y : ℝ => u ![P,y])^[n]) x| < d) ∧
          Tendsto (fun n : ℕ => ((fun y : ℝ => u ![P,y])^[n]) x) atTop (𝓝 0)) ∧
        (ε < 0 → ∃ d > 0, ∀ x : ℝ, x ≠ 0 → |x| < d →
          ∃ n : ℕ, d ≤ |((fun y : ℝ => u ![P,y])^[n]) x|) ∧
        ∀ n : ℕ, ∀ ν : ℝ, 0 < ν → ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
          0 < |δ| ∧ |δ| < ν ∧ 0 < δ * ε ∧
          Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
          (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
          (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
          (∀ q, ‖(C q : Ambient) - hζP.lift q‖ < ν) ∧
          (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U ∧ |δ * v r| < ρ) ∧
          (∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
            (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
              deriv (exitGraphCurve v δ) r)) ∧
          (∀ r ∈ Icc (0 : ℝ) P,
            (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r)).det < 0) ∧
          ∀ j ≤ n, ∀ r ∈ Icc (0 : ℝ) P,
            ‖iteratedFDeriv ℝ j (fun s : ℝ => fermiNormalMap ζ (exitGraphCurve v δ s)) r -
              iteratedFDeriv ℝ j ζ r‖ < ν := by
  letI : Fact (0 < P) := ⟨hP⟩
  have hκ := (normalLoop_actual_smooth hζ).2
  have hm := fermiSupport_actual_identity_return_mean_zero hP.le hκ hU hH hscale
    hseam hzero hpos hV₀ hu₀ hode₀ hvs₀ huzero₀ hinitial₀ hreturn₀
  obtain ⟨ε,hεσ,hεξ,hHε,hHεP,houtside,hjets,hC2,hdetε,hgraphs⟩ :=
    exists_fermiExit_positive_perturbation hP hρ hη hξ hσ hζ hζP hunit hspeed hi
      hhemisphere hU hH hHP hK hKU hscale hseam hzero hpos hm hdet
  have hε : ε ≠ 0 := by intro hz; rw [hz,zero_mul] at hεσ; exact (lt_irrefl _) hεσ
  have hχ := fermiExitCutoff_contDiff ρ hρ
  have hχ0 := fermiExitCutoff_zero ρ hρ
  have hmass := normalLoop_hemisphere_curvature_sq_period_pos hζ hP hζP hunit hspeed hhemisphere
  obtain ⟨V,u,hV,hu,himage,hode,hvs,hiu,hd,hattract,hrepel⟩ :=
    exists_fermiPerturbedSupport_hyperbolic_flow hP hκ hχ hχ0 hU hH hscale hseam
      hzero hpos hm hmass ε
  exact ⟨ε,hεσ,hεξ,hHε,hHεP,houtside,hjets,hC2,hdetε,V,u,hV,hu,himage,hode,
    hvs,hiu,hd,hattract,hrepel,fun n ν hν =>
      exists_fermiExit_jet_close_positive_graph hP hν hρ hε hζ hζP hunit hspeed hi
        hhemisphere hχ hχ0 hU hH hHP hscale hseam hzero hpos hm n⟩

end
end TightVer401
