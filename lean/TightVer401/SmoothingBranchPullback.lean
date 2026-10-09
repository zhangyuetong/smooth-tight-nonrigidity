import TightVer401.SmoothingChartC1

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry OAI.CircleDomainRigidity.FiniteTransfer
open OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff Topology

theorem smoothing_branch_pullback_contDiffOn {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {U V : Set Coord} (hF : ContDiffOn ℝ ∞ F V)
    (hUV : MapsTo Φ U V) : ContDiffOn ℝ ∞ (fun p => F (Φ p)) U := by
  simpa only [Function.comp_def] using hF.comp hΦ.contDiffOn hUV

theorem smoothing_branch_pullback_matching {Φ : Coord → Coord} {F G : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ∀ s, DifferentiableAt ℝ F (Φ (![s,0])))
    (hG : ∀ s, DifferentiableAt ℝ G (Φ (![s,0])))
    (hvalue : ∀ s, F (Φ (![s,0]))=G (Φ (![s,0])))
    (hgrad : ∀ s, planarGradient F (Φ (![s,0]))=planarGradient G (Φ (![s,0]))) :
    (∀ s, ((fun p => F (Φ p))-(fun p => G (Φ p))) (![s,0])=0) ∧
      ∀ s, coordPartial 1 ((fun p => F (Φ p))-(fun p => G (Φ p))) (![s,0])=0 := by
  constructor
  · intro s
    change F (Φ (![s,0]))-G (Φ (![s,0]))=0
    rw [hvalue,sub_self]
  · intro s
    have hdF : DifferentiableAt ℝ (fun p => F (Φ p)) (![s,0]) := by
      simpa only [Function.comp_def] using (hF s).comp (![s,0] : Coord) (hΦ.differentiable (by simp) (![s,0]))
    have hdG : DifferentiableAt ℝ (fun p => G (Φ p)) (![s,0]) := by
      simpa only [Function.comp_def] using (hG s).comp (![s,0] : Coord) (hΦ.differentiable (by simp) (![s,0]))
    change coordPartial 1 (fun p => F (Φ p)-G (Φ p)) (![s,0])=0
    rw [coordPartial_sub_at hdF hdG,seam_coordPartial_comp_at (hF s)
      (hΦ.differentiable (by simp) (![s,0])),seam_coordPartial_comp_at (hG s)
      (hΦ.differentiable (by simp) (![s,0]))]
    have hg (a : Fin 2) : coordPartial a F (Φ (![s,0]))=coordPartial a G (Φ (![s,0])) :=
      congrFun (hgrad s) a
    simp only [hg,sub_self]

/-- The actual corrected pullback Hessian identity holds for branches smooth
only on their actual open planar domain. -/
theorem smoothing_branch_pullback_hessian_det {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {V : Set Coord} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) {p : Coord} (hp : Φ p ∈ V)
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) :
    (seamCorrectedHessian Φ (fun q => F (Φ q)) p).det=
      (seamCoordinateJacobian Φ p).det^2*(planarHessian F (Φ p)).det := by
  obtain ⟨F',hF',hg,_⟩ := exists_smooth_collar_extension hV
    (isClosed_singleton : IsClosed ({Φ p} : Set Coord)) (singleton_subset_iff.mpr hp) hF (0 : ℝ)
  have hg' : F' =ᶠ[𝓝 (Φ p)] F := by simpa only [nhdsSet_singleton] using hg
  have hc : (fun q => F' (Φ q)) =ᶠ[𝓝 p] (fun q => F (Φ q)) := hΦ.continuous.continuousAt.eventually hg'
  have he := seamCorrectedHessian_comp_det hF' hΦ hJ
  rw [smoothing_correctedHessian_germ Φ hc,smoothing_planarHessian_germ hg'] at he
  exact he

theorem smoothing_branch_pullback_saddle {Φ : Coord → Coord} {F : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {V : Set Coord} (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) {p : Coord} (hp : Φ p ∈ V)
    (hJ : (seamCoordinateJacobian Φ p).det ≠ 0) (hneg : (planarHessian F (Φ p)).det < 0) :
    (seamCorrectedHessian Φ (fun q => F (Φ q)) p).det < 0 := by
  rw [smoothing_branch_pullback_hessian_det hΦ hV hF hp hJ]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hJ) hneg

end
end TightVer401
