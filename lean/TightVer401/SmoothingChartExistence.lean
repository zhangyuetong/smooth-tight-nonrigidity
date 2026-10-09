import TightVer401.SmoothingChartCollar
import TightVer401.SmoothingFlatExistence

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothing_correctedHessian_germ (Φ : Coord → Coord) {F G : Coord → ℝ} {p : Coord}
    (h : F =ᶠ[𝓝 p] G) : seamCorrectedHessian Φ F p=seamCorrectedHessian Φ G p := by
  have hg (k : Fin 2) : coordPartial k F p=coordPartial k G p := by
    unfold coordPartial
    rw [h.fderiv_eq]
  ext i j
  unfold seamCorrectedHessian
  rw [smoothing_planarHessian_germ h]
  simp only [hg]

/-- Complete analytic smoothing in a genuine smooth chart, with its actual
Euclidean Hessian correction, arbitrary width, exact germs, and actual C¹ error. -/
theorem smoothing_chart_exists {Φ : Coord → Coord} {F G : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0])=0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0])=0)
    {K : Set ℝ} (hK : IsCompact K) {U S : Set Coord} (hS : IsCompact S)
    (hUK : ∀ p ∈ U, p 0 ∈ K) (hseam : ∀ s ∈ K, (![s,0] : Coord) ∈ U)
    (hJ : ∀ s ∈ K, (seamCoordinateJacobian Φ (![s,0])).det ≠ 0)
    (hnegG : ∀ p ∈ U, (seamCorrectedHessian Φ G p).det < 0)
    (hnegF : ∀ p ∈ U, (seamCorrectedHessian Φ F p).det < 0)
    {w η : ℝ} (hw : 0 < w) (hη : 0 < η) :
    ∃ H : Coord → ℝ, ContDiff ℝ ∞ H ∧
      (∀ p ∈ U, (seamCorrectedHessian Φ H p).det < 0) ∧
      (∀ p : Coord, p 1 ≤ -w → H =ᶠ[𝓝 p] G) ∧
      (∀ p : Coord, w ≤ p 1 → H =ᶠ[𝓝 p] F) ∧
      (∀ p ∈ S, |H p-smoothingFlatOriginal F G p| < η ∧
        ‖planarGradient H p-planarGradient (smoothingFlatOriginal F G) p‖ < η) := by
  obtain ⟨r₁,hr₁,hsaddle⟩ := smoothingFlatPatch_corrected_compact_saddle hΦ hF hG hzero hfirst hK hJ
    (fun s hs => hnegG _ (hseam s hs)) (fun s hs => hnegF _ (hseam s hs))
  obtain ⟨r₂,hr₂,hC1⟩ := smoothingFlatPatch_compact_C1 hF hG hzero hfirst hS hη
  let ρ := min 1 (min r₁ (min r₂ (w^2/4)))
  have hρ : 0 < ρ := lt_min zero_lt_one (lt_min hr₁ (lt_min hr₂ (by positivity)))
  let δ := ρ/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdρ : δ < ρ := by dsimp [δ]; linarith
  have hd₁ : δ < 1 := hdρ.trans_le (min_le_left _ _)
  have hd₂ : δ < r₁ := hdρ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd₃ : δ < r₂ := hdρ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdw : δ < w^2/4 := hdρ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hs₂ := Real.sq_sqrt hδ.le
  have hdhs : δ ≤ Real.sqrt δ := by nlinarith [sq_nonneg (Real.sqrt δ-δ)]
  have hsw : 2*Real.sqrt δ < w := by nlinarith [sq_nonneg (2*Real.sqrt δ+w)]
  let H := smoothingFlatPatch F G δ hδ (Real.sqrt δ)
  refine ⟨H,smoothingFlatPatch_contDiff hF hG δ hδ _,?_,?_,?_,?_⟩
  · intro p hp
    by_cases ht : |p 1| ≤ 2*Real.sqrt δ
    · have hc := hsaddle δ hδ hd₂ (p 0) (hUK p hp) (p 1) ht
      have he : (![p 0,p 1] : Coord)=p := by ext i; fin_cases i <;> rfl
      rw [he] at hc
      exact hc
    · by_cases htp : p 1 ≤ 0
      · have hg := smoothingFlatPatch_old_germ F G δ hδ hs (show p 1 < -δ by
          rw [abs_of_nonpos htp] at ht
          linarith)
        rw [smoothing_correctedHessian_germ Φ hg]
        exact hnegG p hp
      · have hf := smoothingFlatPatch_new_germ hF hG hzero hfirst δ hδ hs hdhs
          (show 2*Real.sqrt δ < p 1 by rw [abs_of_pos (lt_of_not_ge htp)] at ht; linarith)
        rw [smoothing_correctedHessian_germ Φ hf]
        exact hnegF p hp
  · intro p hp
    exact smoothingFlatPatch_old_germ F G δ hδ hs (by linarith)
  · intro p hp
    exact smoothingFlatPatch_new_germ hF hG hzero hfirst δ hδ hs hdhs (by linarith)
  · exact hC1 δ hδ hd₃

end
end TightVer401
