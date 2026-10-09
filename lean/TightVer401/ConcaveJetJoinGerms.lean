import TightVer401.ConcaveJetJoinReconstruction

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem concaveJetJoin_eqOn_of_second_deriv {U : Set ℝ} {q Q : ℝ → ℝ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) {c : ℝ} (hc : c ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hQ : ContDiffOn ℝ ∞ Q U)
    (hsecond : EqOn (deriv (deriv q)) (deriv (deriv Q)) U)
    (hvalue : q c = Q c) (hslope : deriv q c = deriv Q c) : EqOn q Q U := by
  have hq₁ := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hq |>.2
  have hQ₁ := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hQ |>.2
  have hderiv : EqOn (deriv q) (deriv Q) U := hU.eqOn_of_deriv_eq hconnected
    (hq₁.differentiableOn (by simp)) (hQ₁.differentiableOn (by simp)) hsecond hc hslope
  exact hU.eqOn_of_deriv_eq hconnected (hq.differentiableOn (by simp))
    (hQ.differentiableOn (by simp)) hderiv hc hvalue

theorem concaveJetJoin_germ_from_acceleration {U : Set ℝ} {q h : ℝ → ℝ}
    (hU : IsOpen U) (hconnected : IsPreconnected U) {r : ℝ} (hr : r ∈ U)
    (hq : ContDiffOn ℝ ∞ q U) (hh : ContDiff ℝ ∞ h) (c value slope : ℝ)
    (hsecond : ∀ x ∈ U, deriv (deriv q) x = -h x)
    (hvalue : q r = concaveJetReconstruction c value slope h r)
    (hslope : deriv q r = deriv (concaveJetReconstruction c value slope h) r) :
    EqOn q (concaveJetReconstruction c value slope h) U := by
  apply concaveJetJoin_eqOn_of_second_deriv hU hconnected hr hq
    (concaveJetReconstruction_contDiff hh c value slope).contDiffOn _ hvalue hslope
  intro x hx
  exact (hsecond x hx).trans (concaveJetReconstruction_second_deriv hh c value slope x).symm

theorem concaveJetReconstruction_deriv_pos_on_interval {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (c value slope A B : ℝ)
    (hpositive : ∀ x ∈ Icc A B, 0 ≤ h x)
    (hend : 0 < deriv (concaveJetReconstruction c value slope h) B) :
    ∀ r ∈ Icc A B, 0 < deriv (concaveJetReconstruction c value slope h) r := by
  intro r hr
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hh.continuous.intervalIntegrable (μ := volume) c r)
    (hh.continuous.intervalIntegrable (μ := volume) r B)
  have hnonneg : 0 ≤ ∫ x in r..B, h x := intervalIntegral.integral_nonneg hr.2
    (fun x hx => hpositive x ⟨hr.1.trans hx.1, hx.2⟩)
  rw [concaveJetReconstruction_deriv hh, jetPrimitive_eq_interval hh.continuous] at hend ⊢
  linarith

end
end TightVer401
