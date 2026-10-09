import TightVer401.SeamTubePotential
import TightVer401.SeamCoordinateInverse
import TightVer401.SmoothingChartTransfer

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

def seamNormalOpenTube {L : ℝ} (γ : ℝ → ℂ) (hL : Function.Periodic γ L) (r : ℝ) : Set Coord :=
  seamNormalNative γ hL '' ((univ : Set (AddCircle L)) ×ˢ Ioo (-r) r)

theorem seamNormalCoordinates_tube_chart {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) {r : ℝ}
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {p : Coord} (hp : |p 1| < r) :
    ∃ e : OpenPartialHomeomorph Coord Coord,
      p ∈ e.source ∧ e.source ⊆ {p : Coord | |p 1| < r} ∧
      (e : Coord → Coord)=seamNormalCoordinates γ ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hU : IsOpen {p : Coord | |p 1| < r} := isOpen_lt (continuous_apply 1 |>.abs) continuous_const
  apply seamCoordinateJacobian_exists_smooth_chart (seamNormalCoordinates_contDiff hγ) hU _ hp
  intro q hq
  have hqv : (![q 0,q 1] : Coord)=q := by ext i; fin_cases i <;> rfl
  have he := hJ (q 0) (q 1) hq.le
  rw [hqv] at he
  exact he

theorem seamNormalOpenTube_chart_target {L : ℝ} {γ : ℝ → ℂ}
    (hL : Function.Periodic γ L) {r : ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (he : (e : Coord → Coord)=seamNormalCoordinates γ)
    (hS : e.source ⊆ {p : Coord | |p 1| < r}) : e.target ⊆ seamNormalOpenTube γ hL r := by
  intro x hx
  let p := e.symm x
  have hp : |p 1| < r := hS (e.map_target hx)
  refine ⟨(periodProjection L (p 0),p 1),⟨mem_univ _,abs_lt.mp hp⟩,?_⟩
  rw [seamNormalNative_coe]
  have hpv : (![p 0,p 1] : Coord)=p := by ext i; fin_cases i <;> rfl
  rw [hpv,← he]
  exact e.right_inv hx

/-- The actual embedded tube image is an actual open planar domain. -/
theorem seamNormalOpenTube_isOpen {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0) :
    IsOpen (seamNormalOpenTube γ hL r) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change seamNormalOpenTube γ hL r ∈ 𝓝 (seamNormalNative γ hL (periodProjection L s,t))
  rw [seamNormalNative_coe]
  obtain ⟨e,hp,hS,he,_⟩ := seamNormalCoordinates_tube_chart (p := (![s,t] : Coord)) hγ hJ (by simpa using (abs_lt.mpr hq.2 : |t| < r))
  have ht : seamNormalCoordinates γ (![s,t]) ∈ e.target := by
    rw [← he]
    exact e.map_source hp
  exact Filter.mem_of_superset (e.open_target.mem_nhds ht) (seamNormalOpenTube_chart_target hL e he hS)

/-- Native periodic descent and the actual inverse charts produce a genuine
smooth planar potential throughout the actual normal tube. -/
theorem seamNormalTubePotential_contDiffOn {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {H : Coord → ℝ} (hH : ContDiff ℝ ∞ H)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p) :
    ContDiffOn ℝ ∞ (seamNormalTubePotential γ hL r H hPeriod) (seamNormalOpenTube γ hL r) := by
  rintro x ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change ContDiffWithinAt ℝ ∞ (seamNormalTubePotential γ hL r H hPeriod)
    (seamNormalOpenTube γ hL r) (seamNormalNative γ hL (periodProjection L s,t))
  rw [seamNormalNative_coe]
  obtain ⟨e,hp,hS,he,hInv⟩ := seamNormalCoordinates_tube_chart (p := (![s,t] : Coord)) hγ hJ (by simpa using (abs_lt.mpr hq.2 : |t| < r))
  have ht : seamNormalCoordinates γ (![s,t]) ∈ e.target := by rw [← he]; exact e.map_source hp
  have hg : seamNormalTubePotential γ hL r H hPeriod =ᶠ[𝓝 (seamNormalCoordinates γ (![s,t]))]
      smoothingChartPotential e H := by
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact seamNormalTubePotential_chart_eq hL H hPeriod hi e he hS hy
  exact (((smoothingChartPotential_contDiffOn e hH hInv).contDiffAt (e.open_target.mem_nhds ht)).congr_of_eventuallyEq hg).contDiffWithinAt

theorem seamNormalTubePotential_saddle {L : ℝ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (hL : Function.Periodic γ L) {r : ℝ}
    (hi : InjOn (seamNormalNative γ hL) (univ ×ˢ Icc (-r) r))
    (hJ : ∀ s t : ℝ, |t| ≤ r → (seamCoordinateJacobian (seamNormalCoordinates γ) (![s,t])).det ≠ 0)
    {H : Coord → ℝ} (hH : ContDiff ℝ ∞ H)
    (hPeriod : ∀ p, H (smoothingSeamShift L p)=H p)
    (hneg : ∀ s t : ℝ, |t| < r → (seamCorrectedHessian (seamNormalCoordinates γ) H (![s,t])).det < 0) :
    ∀ x ∈ seamNormalOpenTube γ hL r, (planarHessian (seamNormalTubePotential γ hL r H hPeriod) x).det < 0 := by
  rintro x ⟨⟨q,t⟩,hq,rfl⟩
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective q
  change (planarHessian (seamNormalTubePotential γ hL r H hPeriod)
    (seamNormalNative γ hL (periodProjection L s,t))).det < 0
  rw [seamNormalNative_coe]
  have htr : |t| < r := abs_lt.mpr hq.2
  obtain ⟨e,hp,hS,he,hInv⟩ := seamNormalCoordinates_tube_chart (p := (![s,t] : Coord)) hγ hJ (by simpa using htr)
  have hE : ContDiff ℝ ∞ (e : Coord → Coord) := by rw [he]; exact seamNormalCoordinates_contDiff hγ
  have hj : (seamCoordinateJacobian e (![s,t])).det ≠ 0 := by rw [he]; exact hJ s t htr.le
  have hn : (seamCorrectedHessian e H (![s,t])).det < 0 := by rw [he]; exact hneg s t htr
  have hs := smoothingChartPotential_saddle e hE hH hInv hp hj hn
  have ht : seamNormalCoordinates γ (![s,t]) ∈ e.target := by rw [← he]; exact e.map_source hp
  have hg : seamNormalTubePotential γ hL r H hPeriod =ᶠ[𝓝 (seamNormalCoordinates γ (![s,t]))]
      smoothingChartPotential e H := by
    filter_upwards [e.open_target.mem_nhds ht] with y hy
    exact seamNormalTubePotential_chart_eq hL H hPeriod hi e he hS hy
  rw [he] at hs
  rw [smoothing_planarHessian_germ hg]
  exact hs

end
end TightVer401
