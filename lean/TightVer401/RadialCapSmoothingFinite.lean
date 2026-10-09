import TightVer401.RadialCapSmoothing

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology

/-- Every sufficiently short displayed finite cap admits the relative radial
smoothing, with the incoming and terminal germs retained exactly. -/
theorem exists_finite_radial_cap {U : Set ℝ} (hU : IsOpen U)
    {k₀ : ℝ → ℝ} (hk₀ : ContDiffOn ℝ ∞ k₀ U) {j : ℝ}
    (hj : 0 < j) (hjU : j ∈ U) (hs : 0 < deriv k₀ j)
    (hneg : ∀ x ∈ U, deriv (deriv k₀) x < 0) :
    ∃ ε > 0, ∀ d : ℝ, 0 < d → d < ε →
      let a := radialCapRadius d (deriv k₀ j)
      let C := k₀ j - d / deriv k₀ j
      let R := j + d
      a < R ∧ radialCap C R a j = k₀ j ∧ deriv (radialCap C R a) j = deriv k₀ j ∧
      ∃ (u e : ℝ) (k : ℝ → ℝ), 0 < u ∧ u < j ∧ 0 < e ∧
        ContDiffOn ℝ ∞ k (Ioo u (R + e)) ∧
        (∀ x ∈ Ioo u (R + e), deriv (deriv k) x < 0) ∧
        (∀ x ∈ Ioo u R, 0 < deriv k x) ∧
        deriv k R = 0 ∧ deriv (deriv k) R = -1 / a ∧
        (∃ v ∈ Ioo u j, EqOn k k₀ (Ioo u v)) ∧
        k =ᶠ[𝓝 R] radialCap C R a := by
  obtain ⟨ε, hε, hwidth⟩ := exists_radialCap_small_width hj hs
  refine ⟨ε, hε, fun d hd hsmall => ?_⟩
  have hjet := radialCap_matches_first_jet (j := j) (value := k₀ j) hd hs
  exact ⟨hwidth d hd hsmall, hjet.1, hjet.2,
    exists_radialCap_smoothing hU hk₀ hj hjU hd hs hneg⟩

end
end TightVer401
