import TightVer401.SmoothingStateNeighborhood
import TightVer401.SmoothingFlatSegment
import TightVer401.SmoothingFlatPatch
import TightVer401.SmoothingPatchedStateBounds

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix.Norms.Elementwise

/-- The actual germ-preserving smooth interpolation has negative Hessian
determinant throughout its entire shrinking transition collar. -/
theorem smoothingFlatPatch_compact_saddle {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0)
    {K : Set ℝ} (hK : IsCompact K)
    (hnegG : ∀ s ∈ K, (planarHessian G (![s,0])).det < 0)
    (hnegF : ∀ s ∈ K, (planarHessian F (![s,0])).det < 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ s ∈ K, ∀ t : ℝ,
      |t| ≤ 2*Real.sqrt δ →
      (planarHessian (smoothingFlatPatch F G δ hδ (Real.sqrt δ)) (![s,t])).det < 0 := by
  let R := smoothingFlatRemainder (F-G)
  have hR : ContDiff ℝ ∞ R := smoothingFlatRemainder_contDiff (hF.sub hG)
  obtain ⟨ε,hε,hstate⟩ := smoothingHessianState_compact_segment_radius (G := G) (R := R) hG hR hK
    (fun s hs θ hθ => smoothing_flat_endpoint_segment hF hG hzero hfirst s θ hθ
      (hnegG s hs) (hnegF s hs))
  obtain ⟨B₁,hB₁,B₂,hB₂,hB⟩ := smoothingNormalStep_uniform_derivative_bounds
  let E : ℝ → ℝ := fun δ => 2*Real.sqrt δ+12*δ+
    (8+3*B₁*δ)*Real.sqrt δ+(3*B₂/2)*δ
  have hEc : Continuous E := by unfold E; fun_prop
  have hE₀ : E 0=0 := by simp [E]
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), E δ < ε :=
    hEc.continuousAt.eventually (gt_mem_nhds (by simpa only [hE₀] using hε))
  obtain ⟨ρ,hρ,hclose⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min 1 ρ,lt_min zero_lt_one hρ,fun δ hδ hd s hs t ht => ?_⟩
  have hd₁ : δ ≤ 1 := (hd.trans_le (min_le_left _ _)).le
  have hE : E δ < ε := hclose (by
    simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hd.trans_le (min_le_right _ _))
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hbounds := smoothingPatchedProfile_sqrt_state_bounds δ hδ hd₁ hB₁.le hB₂.le ht
    (hB (Real.sqrt δ) hsqrt t).1 (hB (Real.sqrt δ) hsqrt t).2
  let f := smoothingPatchedProfile δ hδ (Real.sqrt δ)
  let θ := smoothingNormalCDF δ hδ t
  let q : Fin 5 → ℝ := (![s,t,deriv (deriv f) t/2,f t,deriv f t])
  have hdist : ‖q-(![s,0,θ,0,0])‖ < ε := by
    apply (pi_norm_lt_iff hε).mpr
    intro i
    have hn₁ : 0 ≤ (8+3*B₁*δ)*Real.sqrt δ := by positivity
    have hn₂ : 0 ≤ (3*B₂/2)*δ := by positivity
    have hn₃ : 0 ≤ 2*Real.sqrt δ := by positivity
    change 2*Real.sqrt δ+12*δ+(8+3*B₁*δ)*Real.sqrt δ+(3*B₂/2)*δ < ε at hE
    fin_cases i
    · simpa [q] using hε
    · have : |t| < ε := by linarith
      simpa [q,Real.norm_eq_abs] using this
    · have : |deriv (deriv f) t/2-θ| < ε := by
        change |deriv (deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ))) t/2-
          smoothingNormalCDF δ hδ t| < ε
        linarith [hbounds.2.2]
      simpa [q] using this
    · have : |f t| < ε := by linarith [hbounds.1]
      simpa [q,Real.norm_eq_abs] using this
    · have : |deriv f t| < ε := by linarith [hbounds.2.1]
      simpa [q,Real.norm_eq_abs] using this
  have hneg := hstate s hs θ (smoothingNormalCDF_bounds δ hδ t) q hdist
  have hf : ContDiff ℝ ∞ f := smoothingPatchedProfile_contDiff δ hδ (Real.sqrt δ)
  have he : smoothingHessianState G R q = planarHessian (smoothingNormalModel f G R) (![s,t]) := by
    have htwo (x : ℝ) : 2*(x/2)=x := by ring
    ext i j
    rw [smoothingNormalModel_hessian (f := f) (G := G) (R := R) hf hG hR]
    simp [smoothingHessianState,q,htwo]
  change (smoothingHessianState G R q).det < 0 at hneg
  rw [he] at hneg
  exact hneg

end
end TightVer401
