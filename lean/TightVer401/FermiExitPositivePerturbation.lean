import TightVer401.FermiSupportPerturbedGraph
import TightVer401.FermiPerturbationSaddle

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold Matrix
set_option backward.isDefEq.respectTransparency false

theorem exists_fermiExit_positive_perturbation {ζ : ℝ → Ambient}
    {H : Coord → ℝ} {U K : Set Coord} {P ρ η ξ σ : ℝ}
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
    (hm : exitGraphMean P (fermiSupportSeamSlope (normalLoopCurvature ζ) H) = 0)
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
      ∀ ν : ℝ, 0 < ν → ∃ (δ : ℝ) (C : AddCircle P → RoundSphere),
        0 < |δ| ∧ |δ| < ν ∧ 0 < δ * ε ∧
        Topology.IsEmbedding C ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ C ∧
        (∀ q, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) C q)) ∧
        (∀ r, (C (periodProjection P r) : Ambient) = fermiNormalMap ζ (exitGraphCurve v δ r)) ∧
        (∀ r ∈ Icc (0 : ℝ) P, exitGraphCurve v δ r ∈ U) ∧
        ∀ r ∈ Icc (0 : ℝ) P, 0 < dotProduct (deriv (exitGraphCurve v δ) r)
          (sphereSupportTensor (inducedMetric (fermiNormalMap ζ)) Hε (exitGraphCurve v δ r) *ᵥ
            deriv (exitGraphCurve v δ) r) := by
  letI : Fact (0 < P) := ⟨hP⟩
  let κ := normalLoopCurvature ζ
  let a := fermiSeamMixed κ H
  let χ := fermiExitCutoff ρ hρ
  have hκ := (normalLoop_actual_smooth hζ).2
  have hκP := (normalLoop_actual_periodic hζ hζP).2
  have ha := (fermiSeam_coefficients_smooth hκ hU hH hscale hseam).1
  have haP := (fermiSeam_coefficients_periodic hκP hHP).1
  have hχ : ContDiff ℝ ∞ χ := fermiExitCutoff_contDiff ρ hρ
  have hχ0 : χ 0 = 1 := fermiExitCutoff_zero ρ hρ
  obtain ⟨eC, heC, hC⟩ := exists_fermiSeamPerturbation_C2_threshold ha hκ ρ hρ hK hη
  have hdetF : ∀ p ∈ K,
      (sphereSupportTensor (fermiMetric (fermiNormalScale κ)) H p).det < 0 := by
    simpa only [fermiNormalMap_inducedMetric hζ hunit hspeed] using hdet
  obtain ⟨eS, heS, hS⟩ := exists_fermiSeamPerturbation_saddle_threshold
    hκ hU hH hK hKU hscale hdetF ha hχ
  let D := min ξ (min eC eS)
  have hD : 0 < D := lt_min hξ (lt_min heC heS)
  let ε := if 0 < σ then D / 2 else -(D / 2)
  have hεabs : |ε| = D / 2 := by
    dsimp only [ε]
    split <;> simp [abs_of_pos (half_pos hD)]
  have hεσ : 0 < ε * σ := by
    dsimp only [ε]
    split
    · exact mul_pos (half_pos hD) ‹0 < σ›
    · exact mul_pos_of_neg_of_neg (neg_neg_of_pos (half_pos hD))
        (lt_of_le_of_ne (le_of_not_gt ‹¬0 < σ›) hσ)
  have hεD : |ε| < D := by rw [hεabs]; exact half_lt_self hD
  have hεC : |ε| < eC := hεD.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεS : |ε| < eS := hεD.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hεξ : |ε| < ξ := hεD.trans_le (min_le_left _ _)
  have hε : ε ≠ 0 := by intro he; rw [he, zero_mul] at hεσ; exact (lt_irrefl _) hεσ
  let Hε := fermiPerturbedSupport ε κ H χ
  let J := fermiSeamPerturbation ε a κ χ
  have hJ : ContDiff ℝ ∞ J := fermiSeamPerturbation_contDiff ha hκ hχ ε
  have hHε : ContDiffOn ℝ ∞ Hε U := hH.add hJ.contDiffOn
  have hHεP : FermiPeriodic P Hε := by
    intro p
    exact congrArg₂ (· + ·) (hHP p) (fermiSeamPerturbation_periodic haP hκP ε p)
  refine ⟨ε, hεσ, hεξ, hHε, hHεP, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have he : J p = 0 := fermiSeamPerturbation_outside_collar a κ ε ρ hρ hp
    change H p + J p = H p
    rw [he, add_zero]
  · intro r
    have hj := fermiSeamPerturbation_jets ha hκ hχ hχ0 ε r
    have dh := ((hH _ (hseam r)).contDiffAt (hU.mem_nhds (hseam r))).differentiableAt (by simp)
    have dj := hJ.differentiable (by simp) (![r,0] : Coord)
    refine ⟨?_, ?_, ?_⟩
    · change H ![r,0] + J ![r,0] = _
      rw [show J ![r,0] = 0 from hj.1, add_zero]
    · change coordPartial 0 (fun q => H q + J q) ![r,0] = _
      rw [coordPartial_scalar_add dh dj, show coordPartial 0 J ![r,0] = 0 from hj.2.1, add_zero]
    · change coordPartial 1 (fun q => H q + J q) ![r,0] = _
      rw [coordPartial_scalar_add dh dj, show coordPartial 1 J ![r,0] = 0 from hj.2.2.1, add_zero]
  · intro p hp
    have he : (fun q => Hε q - H q) = J := by funext q; change H q + J q - H q = _; ring
    rw [he]
    exact hC ε hεC p hp
  · intro p hp
    rw [fermiNormalMap_inducedMetric hζ hunit hspeed]
    exact hS ε hεS p hp
  · intro ν hν
    exact exists_fermiPerturbedSupport_positive_embedded_graph hP hν hε hζ hζP
      hunit hspeed hi hhemisphere hχ hχ0 hU hH hHP hscale hseam hzero hpos hm

end
end TightVer401
