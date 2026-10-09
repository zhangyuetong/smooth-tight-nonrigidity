import TightVer401.SmoothingFlatCore

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

theorem smoothing_flat_endpoint_segment {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0)
    (s θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hnegG : (planarHessian G (![s,0])).det < 0)
    (hnegF : (planarHessian F (![s,0])).det < 0) :
    (smoothingHessianState G (smoothingFlatRemainder (F-G)) (![s,0,θ,0,0])).det < 0 := by
  let p : Coord := (![s,0])
  let R := smoothingFlatRemainder (F-G)
  let a := planarHessian G p 0 0
  let b := planarHessian G p 1 0
  let c := planarHessian G p 1 1
  have hsym := planarHessian_symm hG.contDiffOn isOpen_univ (mem_univ p) 0 1
  have hGj : planarHessian G p = seamSecondJet a b c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet,a,b,c,hsym]
  have hD := smoothing_flat_difference_seam (hF.sub hG) hzero hfirst s
  have hFj : planarHessian F p = seamSecondJet a b (c + 2*R p) := by
    have he : planarHessian F p = planarHessian G p + seamSecondJet 0 0 (2*R p) := by
      ext i j
      have hi := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hD
      change planarHessian (fun q => F q-G q) p i j = seamSecondJet 0 0 (2*R p) i j at hi
      rw [smoothing_hessian_sub hF hG] at hi
      change planarHessian F p i j = planarHessian G p i j + seamSecondJet 0 0 (2*R p) i j
      linarith
    rw [he,hGj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [seamSecondJet] <;> ring
  have hstate : smoothingHessianState G R (![s,0,θ,0,0]) =
      seamSecondJet a b ((1-θ)*c+θ*(c+2*R p)) := by
    ext i j
    have hgi := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hGj
    change planarHessian G p i j = seamSecondJet a b c i j at hgi
    fin_cases i <;> fin_cases j <;>
      simp [smoothingHessianState,p,seamSecondJet,a,b,c,hsym] <;> ring
  change (smoothingHessianState G R (![s,0,θ,0,0])).det < 0
  rw [hstate]
  apply seamSecondJet_blend_saddle hθ
  · rw [← hGj]
    exact hnegG
  · rw [← hFj]
    exact hnegF

/-- Compact matching flat jets and actual endpoint saddle Hessians produce a
uniform radius for the actual smooth interpolation, with no segment hypothesis. -/
theorem smoothing_flat_compact_core {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0)
    {K : Set ℝ} (hK : IsCompact K)
    (hnegG : ∀ s ∈ K, (planarHessian G (![s,0])).det < 0)
    (hnegF : ∀ s ∈ K, (planarHessian F (![s,0])).det < 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ s ∈ K, ∀ t : ℝ, |t| ≤ δ →
      (planarHessian (smoothingNormalModel (smoothingNormalProfile δ hδ) G
        (smoothingFlatRemainder (F-G))) (![s,t])).det < 0 :=
  smoothingNormalModel_compact_core hG (smoothingFlatRemainder_contDiff (hF.sub hG)) hK
    (fun s hs θ hθ => smoothing_flat_endpoint_segment hF hG hzero hfirst s θ hθ
      (hnegG s hs) (hnegF s hs))

end
end TightVer401
