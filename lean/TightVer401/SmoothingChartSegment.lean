import TightVer401.SmoothingChartState
import TightVer401.SmoothingFlatJet

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.SmoothLocal.Geometry.HessianCalculus
open scoped ContDiff BigOperators Matrix Matrix.Norms.Elementwise

theorem smoothing_chart_endpoint_segment {Φ : Coord → Coord} {F G : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0])=0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0])=0)
    (s θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hnegG : (seamCorrectedHessian Φ G (![s,0])).det < 0)
    (hnegF : (seamCorrectedHessian Φ F (![s,0])).det < 0) :
    (smoothingChartHessianState Φ G (smoothingFlatRemainder (F-G)) (![s,0,θ,0,0])).det < 0 := by
  let p : Coord := (![s,0])
  let R := smoothingFlatRemainder (F-G)
  let a := seamCorrectedHessian Φ G p 0 0
  let b := seamCorrectedHessian Φ G p 1 0
  let c := seamCorrectedHessian Φ G p 1 1
  have hgrad (k : Fin 2) : coordPartial k F p=coordPartial k G p := by
    have hk := smoothing_flat_first_zero (hF.sub hG) hzero hfirst s k
    change coordPartial k (fun q => F q-G q) p=0 at hk
    rw [coordPartial_sub_at (hF.differentiable (by simp) p) (hG.differentiable (by simp) p)] at hk
    linarith
  have hD := smoothing_flat_difference_seam (hF.sub hG) hzero hfirst s
  have hcorr : seamCorrectedHessian Φ F p=seamCorrectedHessian Φ G p+seamSecondJet 0 0 (2*R p) := by
    ext i j
    have hi := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hD
    change planarHessian (fun q => F q-G q) p i j=seamSecondJet 0 0 (2*R p) i j at hi
    rw [smoothing_hessian_sub hF hG] at hi
    change planarHessian F p i j-(∑ k : Fin 2, seamChartConnection Φ k i j p*coordPartial k F p)=
      (planarHessian G p i j-(∑ k : Fin 2, seamChartConnection Φ k i j p*coordPartial k G p))+
        seamSecondJet 0 0 (2*R p) i j
    simp only [hgrad]
    linarith
  have hsym := seamCorrectedHessian_symm hΦ hG p 0 1
  have hGj : seamCorrectedHessian Φ G p=seamSecondJet a b c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet,a,b,c,hsym]
  have hFj : seamCorrectedHessian Φ F p=seamSecondJet a b (c+2*R p) := by
    rw [hcorr,hGj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> ring
  have hlead : smoothingChartHessianState Φ G R (![s,0,θ,0,0])=
      seamCorrectedHessian Φ G p+seamSecondJet 0 0 (2*θ*R p) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [smoothingChartHessianState,smoothingHessianState,seamCorrectedHessian,p,
        seamSecondJet,Fin.sum_univ_two] <;> ring
  have hstate : smoothingChartHessianState Φ G R (![s,0,θ,0,0])=
      seamSecondJet a b ((1-θ)*c+θ*(c+2*R p)) := by
    rw [hlead,hGj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> ring
  change (smoothingChartHessianState Φ G R (![s,0,θ,0,0])).det < 0
  rw [hstate]
  apply seamSecondJet_blend_saddle hθ
  · rw [← hGj]
    exact hnegG
  · rw [← hFj]
    exact hnegF

end
end TightVer401
