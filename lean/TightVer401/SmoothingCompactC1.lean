import TightVer401.SmoothingFlatC1

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem smoothingFlatPatch_compact_C1 {F G : Coord → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ s : ℝ, (F-G) (![s,0]) = 0)
    (hfirst : ∀ s : ℝ, coordPartial 1 (F-G) (![s,0]) = 0)
    {S : Set Coord} (hS : IsCompact S) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < δ₀ → ∀ p ∈ S,
      |smoothingFlatPatch F G δ hδ (Real.sqrt δ) p-smoothingFlatOriginal F G p| < η ∧
      ‖planarGradient (smoothingFlatPatch F G δ hδ (Real.sqrt δ)) p-
        planarGradient (smoothingFlatOriginal F G) p‖ < η := by
  let R := smoothingFlatRemainder (F-G)
  have hR : ContDiff ℝ ∞ R := smoothingFlatRemainder_contDiff (hF.sub hG)
  have hgrad : ContDiff ℝ ∞ (planarGradient R) := contDiff_pi.mpr (fun i => smoothing_partial_contDiff hR i)
  obtain ⟨C₀,hC₀⟩ := hS.exists_bound_of_continuousOn hR.continuous.continuousOn
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn hgrad.continuous.continuousOn
  let M₀ := max 1 C₀
  let M₁ := max 1 C₁
  have hM₀ : 0 ≤ M₀ := le_trans zero_le_one (le_max_left _ _)
  have hM₁ : 0 ≤ M₁ := le_trans zero_le_one (le_max_left _ _)
  have hb₀ (p : Coord) (hp : p ∈ S) : |R p| ≤ M₀ := by
    simpa only [Real.norm_eq_abs] using (hC₀ p hp).trans (le_max_right 1 C₀)
  have hb₁ (p : Coord) (hp : p ∈ S) (i : Fin 2) : |coordPartial i R p| ≤ M₁ := by
    have hn : ‖planarGradient R p‖ ≤ M₁ := (hC₁ p hp).trans (le_max_right 1 C₁)
    have hi := (pi_norm_le_iff_of_nonneg hM₁).mp hn i
    simpa only [planarGradient,Real.norm_eq_abs] using hi
  obtain ⟨B,hB,B₂,hB₂,hζ⟩ := smoothingNormalStep_uniform_derivative_bounds
  let E : ℝ → ℝ := fun δ => 7*δ^2*M₀+(4*δ+3*B*δ*Real.sqrt δ)*M₀+7*δ^2*M₁
  have hEc : Continuous E := by unfold E; fun_prop
  have hE₀ : E 0=0 := by simp [E]
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), E δ < η :=
    hEc.continuousAt.eventually (gt_mem_nhds (by simpa only [hE₀] using hη))
  obtain ⟨δ₀,hδ₀,hclose⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ₀,hδ₀,fun δ hδ hd p hp => ?_⟩
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hE : E δ < η := hclose (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hd)
  have hv := smoothingFlatPatch_value_bound hF hG hzero hfirst δ hδ (Real.sqrt δ) (hb₀ p hp)
  have hr : δ/Real.sqrt δ=Real.sqrt δ :=
    (div_eq_iff (ne_of_gt hs)).mpr (by nlinarith [Real.sq_sqrt hδ.le])
  have hid : δ^2*(B/Real.sqrt δ)=B*δ*Real.sqrt δ := by
    calc
      _ = B*δ*(δ/Real.sqrt δ) := by ring
      _ = _ := by rw [hr]
  have hn₀ : 0 ≤ 7*δ^2*M₀ := by positivity
  have hn₁ : 0 ≤ (4*δ+3*B*δ*Real.sqrt δ)*M₀ := by positivity
  have hn₂ : 0 ≤ 7*δ^2*M₁ := by positivity
  change 7*δ^2*M₀+(4*δ+3*B*δ*Real.sqrt δ)*M₀+7*δ^2*M₁ < η at hE
  refine ⟨by linarith,?_⟩
  apply (pi_norm_lt_iff hη).mpr
  intro i
  have hg := smoothingFlatPatch_partial_bound hF hG hzero hfirst δ hδ hs hB.le
    (hζ (Real.sqrt δ) hs (p 1)).1 (hb₀ p hp) (hb₁ p hp) i
  rw [show 3*δ^2*(B/Real.sqrt δ)=3*(δ^2*(B/Real.sqrt δ)) by ring,hid] at hg
  change |coordPartial i (smoothingFlatPatch F G δ hδ (Real.sqrt δ)) p-
    coordPartial i (smoothingFlatOriginal F G) p| < η
  linarith

end
end TightVer401
