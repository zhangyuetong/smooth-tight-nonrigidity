import TightVer401.SeamTubeBoundary
import TightVer401.SmoothingTubeGerms
import TightVer401.SmoothingTubeC1

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothingFlatOriginal_old_germ (F G : Coord → ℝ) {p : Coord} (hp : p 1 < 0) :
    smoothingFlatOriginal F G =ᶠ[𝓝 p] G := by
  filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
  change q 1 < 0 at hq
  simp only [smoothingFlatOriginal,if_pos hq.le]

theorem smoothingFlatOriginal_new_germ (F G : Coord → ℝ) {p : Coord} (hp : 0 < p 1) :
    smoothingFlatOriginal F G =ᶠ[𝓝 p] F := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp] with q hq
  change 0 < q 1 at hq
  simp only [smoothingFlatOriginal,if_neg (not_le.mpr hq)]

/-- The physical interpolation agrees with the physical original on full
neighborhoods of the boundary of any intermediate tube outside its transition. -/
theorem smoothing_tube_boundary_germ {L : ℝ} [Fact (0 < L)] {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r ρ w : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hwρ : w < ρ)
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    (hOpen : IsOpen (seamNormalOpenTube γ hL ρ)) (H F G : Coord → ℝ)
    (hPH : ∀ p, H (smoothingSeamShift L p)=H p)
    (hPF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hPG : ∀ p, G (smoothingSeamShift L p)=G p)
    (hOld : ∀ p : Coord, |p 1| < r → p 1 ≤ -w →
      seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)] seamNormalTubePotential γ hL r G hPG)
    (hNew : ∀ p : Coord, |p 1| < r → w ≤ p 1 →
      seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 (seamNormalCoordinates γ p)] seamNormalTubePotential γ hL r F hPF)
    {x : Coord} (hx : x ∈ frontier (seamNormalOpenTube γ hL ρ)) :
    seamNormalTubePotential γ hL r H hPH =ᶠ[𝓝 x]
      seamNormalTubePotential γ hL r (smoothingFlatOriginal F G) (smoothingFlatOriginal_periodic L hPF hPG) := by
  obtain ⟨s,t,ht,hxEq⟩ := seamNormalOpenTube_frontier_representative hγ hL hOpen hx
  have htr : |t| < r := by rw [ht]; exact hρr
  rw [hxEq]
  have hp : |(![s,t] : Coord) 1| < r := by simpa using htr
  by_cases hn : t ≤ 0
  · have he : -t=ρ := by simpa only [abs_of_nonpos hn] using ht
    have htneg : t < 0 := by linarith
    have hOld' := hOld (![s,t]) hp (by change t ≤ -w; linarith)
    have hOrig := seamNormalTubePotential_germ hγ hL hi hJ (smoothingFlatOriginal F G) G
      (smoothingFlatOriginal_periodic L hPF hPG) hPG hp
      (smoothingFlatOriginal_old_germ F G (by simpa using htneg))
    exact hOld'.trans hOrig.symm
  · have htpos : 0 < t := lt_of_not_ge hn
    have he : t=ρ := by simpa only [abs_of_pos htpos] using ht
    have hNew' := hNew (![s,t]) hp (by change w ≤ t; linarith)
    have hOrig := seamNormalTubePotential_germ hγ hL hi hJ (smoothingFlatOriginal F G) F
      (smoothingFlatOriginal_periodic L hPF hPG) hPF hp
      (smoothingFlatOriginal_new_germ F G (by simpa using htpos))
    exact hNew'.trans hOrig.symm

end
end TightVer401
