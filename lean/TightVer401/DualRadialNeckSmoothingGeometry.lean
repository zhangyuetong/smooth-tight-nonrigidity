import TightVer401.DualRadialNeckSmoothing

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The constructed germ-preserving radial adapter is a genuine saddle
support immersion with the actual induced metric and intrinsic curvature. -/
theorem exists_dualRadialNeck_saddle_adapter {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) {j a : ℝ}
    (ha : 0 < a) (haj : a < j) (hjU : j ∈ U)
    (hpos : 0 < deriv f j) (hneg : ∀ x ∈ U, deriv (deriv f) x < 0) :
    let B := dualRadialNeckCoefficient (deriv f j) j a
    let C := dualRadialNeckConstant (f j) (deriv f j) j a
    ∃ (b c d : ℝ) (F : ℝ → ℝ), j < b ∧ b ∈ U ∧ c ∈ Ioo a j ∧ d ∈ Ioo j b ∧
      Ioo d b ⊆ U ∧ ContDiffOn ℝ ∞ F (Ioo a b) ∧
      (∀ r ∈ Ioo a b, 0 < deriv F r ∧ deriv (deriv F) r < 0) ∧
      EqOn F (dualRadialNeck C B a) (Ioo a c) ∧ EqOn F f (Ioo d b) ∧
      Tendsto (deriv F) (𝓝[>] a) atTop ∧ Tendsto F (𝓝[>] a) (𝓝 C) ∧
      ∀ p ∈ radialPlanarDomain (Ioo a b),
        (planarHessian (radialPlanarPotential F) p).det < 0 ∧
        Function.Injective (fderiv ℝ (planarSupportMap (radialPlanarPotential F)) p) ∧
        gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential F))) p < 0 := by
  dsimp only
  let B := dualRadialNeckCoefficient (deriv f j) j a
  let C := dualRadialNeckConstant (f j) (deriv f j) j a
  obtain ⟨b, c, d, F, hjb, hbU, hc, hd, hcollarU, hF, hsigns, hneck, hincoming, hescape⟩ :=
    exists_dualRadialNeck_adapter hU hf ha haj hjU hpos hneg
  have hnear : F =ᶠ[𝓝[>] a] dualRadialNeck C B a := by
    have hupper : ∀ᶠ x in 𝓝[>] a, x < c :=
      (eventually_lt_nhds hc.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hupper] with x hx hxupper
    exact hneck ⟨hx, hxupper⟩
  refine ⟨b, c, d, F, hjb, hbU, hc, hd, hcollarU, hF, hsigns, hneck, hincoming,
    hescape, (dualRadialNeck_tendsto_endpoint C B a).congr' hnear.symm, ?_⟩
  intro p hp
  have hprod : deriv F (planarRadius p) * deriv (deriv F) (planarRadius p) < 0 :=
    mul_neg_of_pos_of_neg (hsigns _ hp.2).1 (hsigns _ hp.2).2
  have hdet := radialPlanarPotential_hessian_det_neg hF isOpen_Ioo hp hprod
  exact ⟨hdet, planarSupportMap_differential_injective
    (radialPlanarPotential_contDiffOn hF) (radialPlanarDomain_isOpen isOpen_Ioo) hp hdet.ne,
    radialPlanarPotential_gaussianCurvature_neg hF isOpen_Ioo hp hprod⟩

end
end TightVer401
