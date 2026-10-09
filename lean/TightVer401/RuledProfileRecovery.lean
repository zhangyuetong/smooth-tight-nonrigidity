import TightVer401.RuledPotentialRecovery
import TightVer401.RuledProfileUniqueness
import TightVer401.RuledTransverse

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem ruled_profile_recovery_from_potential
    {k τ ρ W F : ℝ → ℝ} {α β : Coord → ℝ} {T n : ℝ → Ambient} {p : Coord} {ks τs : ℝ}
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0)) (hτ0 : τ (p 0) ≠ 0)
    (hρ0 : ρ (p 0) ≠ 0) (hp : 0 < p 1) (hF : ContDiff ℝ ∞ F)
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p)
    (hmix : (1 - k (p 0) * p 1) * coordPartial 1 α p +
      τ (p 0) * p 1 * coordPartial 1 β p + k (p 0) * α p - τ (p 0) * β p = 0)
    (hrep : ∀ q : Coord, 0 < q 1 → ruledPotential k τ α β q =
      τ (q 0) * (q 1)^2 * F (ruledFirstIntegral ρ W q)) :
    ruledBending α β T n p = ruledProfileField k τ ρ W F T n p := by
  have hP := ruledPotential_differentiableAt hk.differentiableAt hτ.differentiableAt hα hβ
  have hpoint : (![p 0, p 1] : Coord) = p := by ext i; fin_cases i <;> simp
  have hP' : DifferentiableAt ℝ (ruledPotential k τ α β) (![p 0, p 1] : Coord) := by
    rw [hpoint]
    exact hP
  have hd : HasDerivAt (fun u => ruledPotential k τ α β (![p 0, u] : Coord))
      (coordPartial 1 (ruledPotential k τ α β) p) (p 1) := by
    have hx := transverse_slice_hasDerivAt hP'
    rw [hpoint] at hx
    exact hx
  have he : (fun u => ruledPotential k τ α β (![p 0, u] : Coord)) =ᶠ[𝓝 (p 1)]
      (fun u => τ (p 0) * u^2 * F (1 / (ρ (p 0) * u) - W (p 0))) := by
    have hu : ∀ᶠ u : ℝ in 𝓝 (p 1), 0 < u :=
      continuousAt_const.eventually_lt continuousAt_id hp
    filter_upwards [hu] with u hu
    simpa [ruledFirstIntegral] using hrep (![p 0, u] : Coord) hu
  have hFd := (hF.differentiable (by simp) (ruledFirstIntegral ρ W p)).hasDerivAt
  have hform := ruled_profile_potential_hasDerivAt (τ := τ (p 0)) hρ0 (ne_of_gt hp) hFd
  have hPu := hd.unique (hform.congr_of_eventuallyEq he)
  obtain ⟨ha, hb⟩ := ruledPotential_reconstruction hk hτ hτ0 hα hβ hmix
  rw [hrep p hp, hPu] at ha hb
  obtain ⟨haF, hbF⟩ := ruled_profile_reconstruction (k := k (p 0)) (u := p 1)
    (f := F (ruledFirstIntegral ρ W p)) (f' := deriv F (ruledFirstIntegral ρ W p)) hτ0 hρ0
  have ha' : α p = ruledProfileAlpha τ ρ W F p := ha.trans haF
  have hb' : β p = ruledProfileBeta k ρ W F p := hb.trans hbF
  simp only [ruledProfileField, ruledBending, ha', hb']

end
end TightVer401
