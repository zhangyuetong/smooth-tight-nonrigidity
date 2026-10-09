import TightVer401.SmoothingStateNeighborhood
import TightVer401.SmoothingPatchedStateBounds

namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

/-- Continuity only at the compact center segment is sufficient. This allows
an actual chart connection whose inverse Jacobian is regular only near the seam. -/
theorem smoothing_compact_state_radius {A : (Fin 5 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {K : Set ℝ} (hK : IsCompact K)
    (hA : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, ContinuousAt A (![s,0,θ,0,0]))
    (hneg : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, (A (![s,0,θ,0,0])).det < 0) :
    ∃ ε > 0, ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ q : Fin 5 → ℝ,
      ‖q-(![s,0,θ,0,0])‖ < ε → (A q).det < 0 := by
  let center : ℝ × ℝ → (Fin 5 → ℝ) := fun z => (![z.1,0,z.2,0,0])
  have hc : Continuous center := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [center] <;> fun_prop
  let S := center '' (K ×ˢ Icc (0 : ℝ) 1)
  have hS : IsCompact S := (hK.prod isCompact_Icc).image hc
  let O := interior {q : Fin 5 → ℝ | (A q).det < 0}
  have hSO : S ⊆ O := by
    rintro q ⟨⟨s,θ⟩, hz, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    exact ((continuous_id.matrix_det).continuousAt.comp (hA s hz.1 θ hz.2)).preimage_mem_nhds
      (gt_mem_nhds (hneg s hz.1 θ hz.2))
  obtain ⟨ε,hε,hinc⟩ := hS.exists_thickening_subset_open isOpen_interior hSO
  refine ⟨ε,hε,fun s hs θ hθ q hq => ?_⟩
  change q ∈ {z : Fin 5 → ℝ | (A z).det < 0}
  apply interior_subset
  apply hinc
  apply Metric.mem_thickening_iff.mpr
  refine ⟨center (s,θ),⟨(s,θ),⟨hs,hθ⟩,rfl⟩,?_⟩
  simpa only [dist_eq_norm,center] using hq

theorem smoothing_patched_compact_state {A : (Fin 5 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {K : Set ℝ} (hK : IsCompact K)
    (hA : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, ContinuousAt A (![s,0,θ,0,0]))
    (hneg : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, (A (![s,0,θ,0,0])).det < 0) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ s ∈ K, ∀ t : ℝ,
      |t| ≤ 2*Real.sqrt δ →
      (A (![s,t,deriv (deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ))) t/2,
        smoothingPatchedProfile δ hδ (Real.sqrt δ) t,
        deriv (smoothingPatchedProfile δ hδ (Real.sqrt δ)) t])).det < 0 := by
  obtain ⟨ε,hε,hstate⟩ := smoothing_compact_state_radius hK hA hneg
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
  apply hstate s hs θ (smoothingNormalCDF_bounds δ hδ t) q
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

end
end TightVer401
