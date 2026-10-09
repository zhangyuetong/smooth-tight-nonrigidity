import TightVer401.SmoothingFlatCore

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix.Norms.Elementwise

theorem smoothingHessianState_compact_segment_radius {G R : Coord → ℝ}
    (hG : ContDiff ℝ ∞ G) (hR : ContDiff ℝ ∞ R) {K : Set ℝ} (hK : IsCompact K)
    (hsegment : ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1,
      (smoothingHessianState G R (![s,0,θ,0,0])).det < 0) :
    ∃ ε > 0, ∀ s ∈ K, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ q : Fin 5 → ℝ,
      ‖q-(![s,0,θ,0,0])‖ < ε → (smoothingHessianState G R q).det < 0 := by
  let center : ℝ × ℝ → (Fin 5 → ℝ) := fun z => (![z.1,0,z.2,0,0])
  have hc : Continuous center := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [center] <;> fun_prop
  let S := center '' (K ×ˢ Icc (0 : ℝ) 1)
  have hS : IsCompact S := (hK.prod isCompact_Icc).image hc
  let O : Set (Fin 5 → ℝ) := {q | (smoothingHessianState G R q).det < 0}
  have hO : IsOpen O := (smoothingHessianState_continuous hG hR).matrix_det.isOpen_preimage _ isOpen_Iio
  have hSO : S ⊆ O := by
    rintro q ⟨⟨s,θ⟩, hz, rfl⟩
    exact hsegment s hz.1 θ hz.2
  obtain ⟨ε,hε,hinc⟩ := hS.exists_thickening_subset_open hO hSO
  refine ⟨ε,hε,fun s hs θ hθ q hq => ?_⟩
  apply hinc
  apply Metric.mem_thickening_iff.mpr
  refine ⟨center (s,θ),⟨(s,θ),⟨hs,hθ⟩,rfl⟩,?_⟩
  simpa only [dist_eq_norm,center] using hq

end
end TightVer401
