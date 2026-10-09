import TightVer401.ConcaveJetJoinPrimitive

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Reconstruction uses only local smoothness of the original representative. -/
theorem concaveJetReconstruction_eqOn_of_second_deriv {U : Set ℝ} {q h : ℝ → ℝ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) {c : ℝ} (hc : c ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hh : ContDiff ℝ ∞ h)
    (hsecond : ∀ r ∈ U, deriv (deriv q) r = -h r) :
    EqOn q (concaveJetReconstruction c (q c) (deriv q c) h) U := by
  let Q := concaveJetReconstruction c (q c) (deriv q c) h
  have hQ : ContDiff ℝ ∞ Q := concaveJetReconstruction_contDiff hh c (q c) (deriv q c)
  have hq₁ : ContDiffOn ℝ ∞ (deriv q) U :=
    (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hq |>.2
  have hQ₁ : ContDiff ℝ ∞ (deriv Q) := (contDiff_infty_iff_deriv.mp hQ).2
  have hderiv : EqOn (deriv q) (deriv Q) U := by
    apply hU.eqOn_of_deriv_eq hconnected (hq₁.differentiableOn (by simp))
      ((hQ₁.differentiable (by simp)).differentiableOn) _ hc
      (concaveJetReconstruction_first_jet hh c (q c) (deriv q c)).2.symm
    intro r hr
    exact (hsecond r hr).trans (concaveJetReconstruction_second_deriv hh c (q c) (deriv q c) r).symm
  exact hU.eqOn_of_deriv_eq hconnected (hq.differentiableOn (by simp))
    ((hQ.differentiable (by simp)).differentiableOn) hderiv hc
    (concaveJetReconstruction_first_jet hh c (q c) (deriv q c)).1.symm

theorem concaveJetReconstruction_strict_concavity {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (c value slope : ℝ) {U : Set ℝ}
    (hpositive : ∀ r ∈ U, 0 < h r) :
    ∀ r ∈ U, deriv (deriv (concaveJetReconstruction c value slope h)) r < 0 := by
  intro r hr
  rw [concaveJetReconstruction_second_deriv hh]
  exact neg_neg_of_pos (hpositive r hr)

end
end TightVer401
