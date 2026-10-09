import TightVer401.SmoothingChartSegment
import TightVer401.SmoothingCompactState
import TightVer401.SmoothingFlatPatch

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

/-- The constructed patch is saddle for the actual Euclidean chart correction.
Only the Jacobian along the seam is required to be regular. -/
theorem smoothingFlatPatch_corrected_compact_saddle {Φ : Coord → Coord} {F G : Coord → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0])=0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0])=0)
    {K : Set ℝ} (hK : IsCompact K)
    (hJ : ∀ s ∈ K, (seamCoordinateJacobian Φ (![s,0])).det ≠ 0)
    (hnegG : ∀ s ∈ K, (seamCorrectedHessian Φ G (![s,0])).det < 0)
    (hnegF : ∀ s ∈ K, (seamCorrectedHessian Φ F (![s,0])).det < 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ s ∈ K, ∀ t : ℝ,
      |t| ≤ 2*Real.sqrt δ →
      (seamCorrectedHessian Φ (smoothingFlatPatch F G δ hδ (Real.sqrt δ)) (![s,t])).det < 0 := by
  let R := smoothingFlatRemainder (F-G)
  have hR : ContDiff ℝ ∞ R := smoothingFlatRemainder_contDiff (hF.sub hG)
  have hAc (s : ℝ) (hs : s ∈ K) (θ : ℝ) (_hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContinuousAt (smoothingChartHessianState Φ G R) (![s,0,θ,0,0]) := by
    apply smoothingChartHessianState_continuousAt hΦ hG hR
    simpa using hJ s hs
  obtain ⟨δ₀,hδ₀,hstate⟩ := smoothing_patched_compact_state (A := smoothingChartHessianState Φ G R) hK hAc
    (fun s hs θ hθ => smoothing_chart_endpoint_segment hΦ hF hG hzero hfirst s θ hθ
      (hnegG s hs) (hnegF s hs))
  refine ⟨δ₀,hδ₀,fun δ hδ hd s hs t ht => ?_⟩
  have hneg := hstate δ hδ hd s hs t ht
  rw [smoothingChartHessianState_model (smoothingPatchedProfile_contDiff δ hδ (Real.sqrt δ)) hG hR] at hneg
  exact hneg

end
end TightVer401
