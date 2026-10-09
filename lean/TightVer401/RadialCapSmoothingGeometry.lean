import TightVer401.RadialCapSmoothingFinite
import TightVer401.RadialPlanarCurvature

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem radialCapSmoothing_actual_curvature {k : ℝ → ℝ} {u R e : ℝ}
    (he : 0 < e) (hk : ContDiffOn ℝ ∞ k (Ioo u (R + e)))
    (hpos : ∀ x ∈ Ioo u R, 0 < deriv k x)
    (hneg : ∀ x ∈ Ioo u (R + e), deriv (deriv k) x < 0) :
    ∀ p ∈ radialPlanarDomain (Ioo u R),
      (planarHessian (radialPlanarPotential k) p).det < 0 ∧
      gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential k))) p < 0 := by
  have hsub : Ioo u R ⊆ Ioo u (R + e) := fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  intro p hp
  have hprod : deriv k (planarRadius p) * deriv (deriv k) (planarRadius p) < 0 :=
    mul_neg_of_pos_of_neg (hpos _ hp.2) (hneg _ (hsub hp.2))
  exact ⟨radialPlanarPotential_hessian_det_neg (hk.mono hsub) isOpen_Ioo hp hprod,
    radialPlanarPotential_gaussianCurvature_neg (hk.mono hsub) isOpen_Ioo hp hprod⟩

/-- The constructed cap preserves the actual radial saddle geometry. -/
theorem exists_finite_radial_cap_surface {U : Set ℝ} (hU : IsOpen U)
    {k₀ : ℝ → ℝ} (hk₀ : ContDiffOn ℝ ∞ k₀ U) {j : ℝ}
    (hj : 0 < j) (hjU : j ∈ U) (hs : 0 < deriv k₀ j)
    (hneg : ∀ x ∈ U, deriv (deriv k₀) x < 0) :
    ∃ ε > 0, ∀ d : ℝ, 0 < d → d < ε →
      ∃ (u e : ℝ) (k : ℝ → ℝ), 0 < u ∧ u < j ∧ 0 < e ∧
        ContDiffOn ℝ ∞ k (Ioo u (j + d + e)) ∧
        (∀ x ∈ Ioo u (j + d + e), deriv (deriv k) x < 0) ∧
        (∀ x ∈ Ioo u (j + d), 0 < deriv k x) ∧
        (∀ p ∈ radialPlanarDomain (Ioo u (j + d)),
          (planarHessian (radialPlanarPotential k) p).det < 0 ∧
          gaussianCurvature (inducedMetric (planarSupportMap (radialPlanarPotential k))) p < 0) := by
  obtain ⟨ε, hε, hcap⟩ := exists_finite_radial_cap hU hk₀ hj hjU hs hneg
  refine ⟨ε, hε, fun d hd hsmall => ?_⟩
  obtain ⟨_, _, _, u, e, k, hu, huj, he, hk, hkneg, hkpos, _⟩ := hcap d hd hsmall
  exact ⟨u, e, k, hu, huj, he, hk, hkneg, hkpos,
    radialCapSmoothing_actual_curvature he hk hkpos hkneg⟩

end
end TightVer401
