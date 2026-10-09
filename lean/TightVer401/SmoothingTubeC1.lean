import TightVer401.SmoothingTubeTransfer
import TightVer401.SmoothingPositiveSquare

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothingChartPotential_contDiffOn_one (e : OpenPartialHomeomorph Coord Coord)
    {H : Coord → ℝ} (hH : ContDiff ℝ 1 H)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ 1 (smoothingChartPotential e H) e.target := by
  intro x hx
  exact hH.contDiffAt.comp_contDiffWithinAt x ((hInv.of_le (by simp)) x hx)

theorem seamNormalTubePotential_contDiffOn_one {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {H : Coord → ℝ} (hH : ContDiff ℝ 1 H)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p) :
    ContDiffOn ℝ 1 (seamNormalTubePotential γ hL r H hPeriod) (seamNormalOpenTube γ hL r) := by
  rintro x ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change ContDiffWithinAt ℝ 1 (seamNormalTubePotential γ hL r H hPeriod)
    (seamNormalOpenTube γ hL r) (seamNormalNative γ hL (periodProjection L s,t))
  rw [seamNormalNative_coe]
  obtain ⟨e,hp,hS,he,hInv⟩ := seamNormalCoordinates_tube_chart (p := (![s,t] : Coord)) hγ hJ (by simpa using (abs_lt.mpr hq.2 : |t| < r))
  have ht : seamNormalCoordinates γ (![s,t]) ∈ e.target := by rw [← he]; exact e.map_source hp
  have hg : seamNormalTubePotential γ hL r H hPeriod =ᶠ[𝓝 (seamNormalCoordinates γ (![s,t]))]
      smoothingChartPotential e H := by
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact seamNormalTubePotential_chart_eq hL H hPeriod hi e he hS hy
  exact (((smoothingChartPotential_contDiffOn_one e hH hInv).contDiffAt (e.open_target.mem_nhds ht)).congr_of_eventuallyEq hg).contDiffWithinAt

theorem smoothingFlatOriginal_periodic {F G : Coord → ℝ} (L : ℝ)
    (hF : ∀ p, F (smoothingSeamShift L p)=F p)
    (hG : ∀ p, G (smoothingSeamShift L p)=G p) (p : Coord) :
    smoothingFlatOriginal F G (smoothingSeamShift L p)=smoothingFlatOriginal F G p := by
  change (if p 1 ≤ 0 then G (smoothingSeamShift L p) else F (smoothingSeamShift L p))=
    (if p 1 ≤ 0 then G p else F p)
  rw [hF,hG]

end
end TightVer401
