import TightVer401.MomentControlBump

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def jetLocalExtension {c : ℝ} (β : ContDiffBump c) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun r => β r * f r

theorem jetLocalExtension_contDiff {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {c : ℝ} (β : ContDiffBump c)
    (hβ : tsupport (β : ℝ → ℝ) ⊆ U) : ContDiff ℝ ∞ (jetLocalExtension β f) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r ∈ U
  · exact β.contDiff.contDiffAt.mul ((hf r hr).contDiffAt (hU.mem_nhds hr))
  · have hout : r ∉ tsupport (β : ℝ → ℝ) := fun h => hr (hβ h)
    have hn : (tsupport (β : ℝ → ℝ))ᶜ ∈ 𝓝 r := isClosed_closure.isOpen_compl.mem_nhds hout
    have he : jetLocalExtension β f =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
      filter_upwards [hn] with x hx
      simp only [jetLocalExtension, image_eq_zero_of_notMem_tsupport hx, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem jetLocalExtension_eqOn {c : ℝ} (β : ContDiffBump c) (f : ℝ → ℝ) :
    EqOn (jetLocalExtension β f) f (closedBall c β.rIn) := by
  intro r hr
  simp only [jetLocalExtension, β.one_of_mem_closedBall hr, one_mul]

theorem jetLocalExtension_hasCompactSupport {c : ℝ} (β : ContDiffBump c) (f : ℝ → ℝ) :
    HasCompactSupport (jetLocalExtension β f) :=
  β.hasCompactSupport.mul_right

theorem jetLocalExtension_second_acceleration {U : Set ℝ} (hU : IsOpen U)
    {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q U) {c : ℝ} (β : ContDiffBump c)
    (hβ : tsupport (β : ℝ → ℝ) ⊆ U) :
    ContDiff ℝ ∞ (jetLocalExtension β (fun r => -deriv (deriv q) r)) ∧
    EqOn (jetLocalExtension β (fun r => -deriv (deriv q) r))
      (fun r => -deriv (deriv q) r) (closedBall c β.rIn) := by
  have hq₁ := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hq |>.2
  have hq₂ := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hq₁ |>.2
  exact ⟨jetLocalExtension_contDiff hU hq₂.neg β hβ, jetLocalExtension_eqOn β _⟩

end
end TightVer401
