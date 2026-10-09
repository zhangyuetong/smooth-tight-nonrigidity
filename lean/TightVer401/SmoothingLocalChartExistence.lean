import TightVer401.SmoothingNormalExtension
import TightVer401.SmoothingChartExistence

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothingFlatOriginal_germ {F G F' G' : Coord → ℝ} {p : Coord}
    (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    smoothingFlatOriginal F G =ᶠ[𝓝 p] smoothingFlatOriginal F' G' := by
  filter_upwards [hF,hG] with q hf hg
  unfold smoothingFlatOriginal
  split_ifs <;> assumption

theorem smoothing_planarGradient_germ {F G : Coord → ℝ} {p : Coord}
    (h : F =ᶠ[𝓝 p] G) : planarGradient F p=planarGradient G p := by
  ext i
  unfold planarGradient coordPartial
  rw [h.fderiv_eq]

/-- Local smooth branch data suffice: the global extensions and their exact
seam jets are constructed by OpenAI's collar cutoff. -/
theorem smoothing_local_chart_exists {r : ℝ} (hr : 0 < r)
    {Φ : Coord → Coord} {F G : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiffOn ℝ ∞ F {p : Coord | |p 1| < r})
    (hG : ContDiffOn ℝ ∞ G {p : Coord | |p 1| < r})
    (hzero : ∀ s : ℝ, (F-G) (![s,0])=0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0])=0)
    {K : Set ℝ} (hK : IsCompact K) {U S : Set Coord} (hS : IsCompact S)
    (hSU : S ⊆ U)
    (hUK : ∀ p ∈ U, p 0 ∈ K)
    (hUr : ∀ p ∈ U, |p 1| < r/4)
    (hseam : ∀ s ∈ K, (![s,0] : Coord) ∈ U)
    (hJ : ∀ s ∈ K, (seamCoordinateJacobian Φ (![s,0])).det ≠ 0)
    (hnegG : ∀ p ∈ U, (seamCorrectedHessian Φ G p).det < 0)
    (hnegF : ∀ p ∈ U, (seamCorrectedHessian Φ F p).det < 0)
    {w η : ℝ} (hw : 0 < w) (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiff ℝ ∞ H ∧
      (∀ p ∈ U, (seamCorrectedHessian Φ H p).det < 0) ∧
      (∀ p : Coord, |p 1| < r/4 → p 1 ≤ -w → H =ᶠ[𝓝 p] G) ∧
      (∀ p : Coord, |p 1| < r/4 → w ≤ p 1 → H =ᶠ[𝓝 p] F) ∧
      (∀ p ∈ S, |H p-smoothingFlatOriginal F G p| < η ∧
        ‖planarGradient H p-planarGradient (smoothingFlatOriginal F G) p‖ < η) := by
  let F' := smoothingNormalExtension r hr F
  let G' := smoothingNormalExtension r hr G
  have hF' : ContDiff ℝ ∞ F' := smoothingNormalExtension_contDiff r hr hF
  have hG' : ContDiff ℝ ∞ G' := smoothingNormalExtension_contDiff r hr hG
  have hgF (p : Coord) (hp : |p 1| < r/4) : F' =ᶠ[𝓝 p] F :=
    smoothingNormalExtension_germ r hr F hp
  have hgG (p : Coord) (hp : |p 1| < r/4) : G' =ᶠ[𝓝 p] G :=
    smoothingNormalExtension_germ r hr G hp
  have hgD (s : ℝ) : F'-G' =ᶠ[𝓝 (![s,0] : Coord)] F-G := by
    have ht : |(![s,0] : Coord) 1| < r/4 := by simp; positivity
    filter_upwards [hgF _ ht,hgG _ ht] with p hpF hpG
    change F' p-G' p=F p-G p
    rw [hpF,hpG]
  have hz' (s : ℝ) : (F'-G') (![s,0])=0 := by
    rw [(hgD s).eq_of_nhds]
    exact hzero s
  have hf' (s : ℝ) : coordPartial 1 (F'-G') (![s,0])=0 := by
    unfold coordPartial
    rw [(hgD s).fderiv_eq]
    exact hfirst s
  have hnG' (p : Coord) (hp : p ∈ U) : (seamCorrectedHessian Φ G' p).det < 0 := by
    rw [smoothing_correctedHessian_germ Φ (hgG p (hUr p hp))]
    exact hnegG p hp
  have hnF' (p : Coord) (hp : p ∈ U) : (seamCorrectedHessian Φ F' p).det < 0 := by
    rw [smoothing_correctedHessian_germ Φ (hgF p (hUr p hp))]
    exact hnegF p hp
  obtain ⟨H,hH,hn,hOld,hNew,hC1⟩ := smoothing_chart_exists hΦ hF' hG' hz' hf' hK hS
    hUK hseam hJ hnG' hnF' hw hη
  refine ⟨H,hH,hn,?_,?_,?_⟩
  · intro p hp hw'
    exact (hOld p hw').trans (hgG p hp)
  · intro p hp hw'
    exact (hNew p hw').trans (hgF p hp)
  · intro p hp
    have ho := smoothingFlatOriginal_germ (hgF p (hUr p (hSU hp))) (hgG p (hUr p (hSU hp)))
    have he := hC1 p hp
    rw [ho.eq_of_nhds,smoothing_planarGradient_germ ho] at he
    exact he

end
end TightVer401
