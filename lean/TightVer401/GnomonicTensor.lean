import TightVer401.GnomonicSupport

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Manifold Matrix

theorem secondFundamental_eq_of_eventuallyEq {X Y : Coord → Ambient} {p : Coord}
    (he : X =ᶠ[𝓝 p] Y) (n : Ambient) :
    secondFundamental X n p = secondFundamental Y n p := by
  ext i j
  have hp : coordPartial j X =ᶠ[𝓝 p] coordPartial j Y := by
    filter_upwards [he.eventuallyEq_nhds] with z hz
    unfold coordPartial
    rw [hz.fderiv_eq]
  change inner ℝ (fderiv ℝ (coordPartial j X) p (Pi.single i 1)) n =
    inner ℝ (fderiv ℝ (coordPartial j Y) p (Pi.single i 1)) n
  rw [hp.fderiv_eq]

theorem gnomonic_round_metric :
    SmoothPositiveOn (inducedMetric planarUnitNormal) (univ : Set Coord) ∧
      IsometricOn (inducedMetric planarUnitNormal) planarUnitNormal univ :=
  ⟨inducedMetric_smoothPositiveOn gnomonicNormal_contDiff.contDiffOn isOpen_univ
    (fun p _ => gnomonicNormal_differential_injective p),
    inducedMetric_isometricOn gnomonicNormal_contDiff.contDiffOn⟩

theorem gnomonicSupport_local_formula {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω) :
    EqOn (planarSupportMap (gnomonicPotential H))
      (sphereSupportMap (inducedMetric planarUnitNormal) planarUnitNormal
        (fun p => H (gnomonicPoint p))) (gnomonicPoint ⁻¹' Ω) := by
  let V := gnomonicPoint ⁻¹' Ω
  have hV : IsOpen V := hΩ.preimage gnomonicPoint_contMDiff.continuous
  have hG := gnomonicPotential_contDiffOn hH
  have hg : SmoothPositiveOn (inducedMetric planarUnitNormal) V :=
    ⟨fun i j => (gnomonic_round_metric.1.1 i j).mono (subset_univ _),
      fun p _ => gnomonic_round_metric.1.2 p (mem_univ p)⟩
  have hQ : IsometricOn (inducedMetric planarUnitNormal) planarUnitNormal V :=
    ⟨gnomonic_round_metric.2.1.mono (subset_univ _),
      fun p _ => gnomonic_round_metric.2.2 p (mem_univ p)⟩
  have he := sphereSupportMap_converse_local hg hQ (planarSupportMap_contDiffOn hG hV) hV
    (fun _ hp => planarSupportMap_isUnitNormal hG hV hp)
  have hh : (fun p => inner ℝ (planarSupportMap (gnomonicPotential H) p) (planarUnitNormal p)) =
      (fun p => H (gnomonicPoint p)) := by
    funext p
    rw [planarSupportMap_height]
    unfold gnomonicPotential
    exact mul_div_cancel_left₀ _ (ne_of_gt (planarWeight_pos p))
  rwa [hh] at he

theorem gnomonicSupport_tensor {H : RoundSphere → ℝ} {Ω : Set RoundSphere}
    (hH : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H Ω) (hΩ : IsOpen Ω)
    {p : Coord} (hp : gnomonicPoint p ∈ Ω) :
    sphereSupportTensor (inducedMetric planarUnitNormal) (fun p => H (gnomonicPoint p)) p =
      (planarWeight p)⁻¹ • planarHessian (gnomonicPotential H) p := by
  let V := gnomonicPoint ⁻¹' Ω
  have hV : IsOpen V := hΩ.preimage gnomonicPoint_contMDiff.continuous
  have hg : SmoothPositiveOn (inducedMetric planarUnitNormal) V :=
    ⟨fun i j => (gnomonic_round_metric.1.1 i j).mono (subset_univ _),
      fun p _ => gnomonic_round_metric.1.2 p (mem_univ p)⟩
  have hQ : IsometricOn (inducedMetric planarUnitNormal) planarUnitNormal V :=
    ⟨gnomonic_round_metric.2.1.mono (subset_univ _),
      fun p _ => gnomonic_round_metric.2.2 p (mem_univ p)⟩
  have hheight : ContDiffOn ℝ ∞ (fun p => H (gnomonicPoint p)) V :=
    (hH.comp gnomonicPoint_contMDiff.contMDiffOn (fun _ hx => hx)).contDiffOn
  have he : planarSupportMap (gnomonicPotential H) =ᶠ[𝓝 p]
      sphereSupportMap (inducedMetric planarUnitNormal) planarUnitNormal
        (fun p => H (gnomonicPoint p)) := by
    filter_upwards [hV.mem_nhds hp] with z hz
    exact gnomonicSupport_local_formula hH hΩ hz
  have hII := secondFundamental_eq_of_eventuallyEq he (planarUnitNormal p)
  rw [planarSupportMap_secondFundamental (gnomonicPotential_contDiffOn hH) hV hp,
    sphereSupportMap_secondFundamental hg hQ hheight hV hp
      (fun q _ => planarUnitNormal_unit q)] at hII
  apply neg_injective
  simpa only [neg_smul] using hII.symm

end
end TightVer401
