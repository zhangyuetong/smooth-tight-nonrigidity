import TightVer401.SmoothingTubeTransfer

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem seamNormalTubePotential_germ {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    (H F : Coord → ℝ) (hPH : ∀ p, H (smoothingSeamShift L p)=H p)
    (hPF : ∀ p, F (smoothingSeamShift L p)=F p)
    {p : Coord} (hp : |p 1| < r) (hGerm : H =ᶠ[𝓝 p] F) :
    seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)]
      seamNormalTubePotential γ hL r F hPF := by
  obtain ⟨e,heS,hS,he,_⟩ := seamNormalCoordinates_tube_chart hγ hJ hp
  have ht : seamNormalCoordinates γ p ∈ e.target := by rw [← he]; exact e.map_source heS
  have hGH : seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)]
      smoothingChartPotential e H := by
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact seamNormalTubePotential_chart_eq hL H hPH hi e he hS hy
  have hGF : seamNormalTubePotential γ hL r F hPF =ᶠ[𝓝 (seamNormalCoordinates γ p)]
      smoothingChartPotential e F := by
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact seamNormalTubePotential_chart_eq hL F hPF hi e he hS hy
  have hMiddle := smoothingChartPotential_side_germ e heS hGerm
  rw [he] at hMiddle
  exact hGH.trans (hMiddle.trans hGF.symm)

end
end TightVer401
