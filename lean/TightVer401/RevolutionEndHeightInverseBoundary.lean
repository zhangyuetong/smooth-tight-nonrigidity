import TightVer401.RevolutionEndHeightInverseSmooth

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem revolutionHeightInverse_boundary_extension {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    ∃ (g : ℝ → ℝ) (W : Set ℝ), IsOpen W ∧ revolutionNormalHeight q H ∈ W ∧
      ContDiffOn ℝ ∞ g W ∧ g (revolutionNormalHeight q H) = H ∧
      EqOn g (revolutionHeightInverse (H := H) hq hslope)
        (W ∩ Ico (revolutionNormalHeight q H) 1) := by
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have hqdd := (contDiff_infty_iff_deriv.mp hqd).2
  let U : Set ℝ := {z | 0 < deriv (deriv q) z}
  have hU : IsOpen U := hqdd.continuous.isOpen_preimage _ isOpen_Ioi
  have hHU : H ∈ U := hc H (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hHU)
  have hmono : StrictMonoOn (revolutionNormalHeight q) (Metric.ball H δ) := by
    apply strictMonoOn_of_deriv_pos (convex_ball H δ)
      (revolutionNormalHeight_contDiff hq).continuous.continuousOn
    intro z hz
    rw [(revolutionNormalHeight_hasDerivAt hq z).deriv]
    exact div_pos (hball (interior_subset hz)) (pow_pos (revolutionWeight_pos _) 3)
  obtain ⟨g, V, hV, hVH, hgH, hg, hright⟩ :=
    revolutionNormalHeight_smooth_local_inverse hq (hc H (by simp))
  let W := V ∩ g ⁻¹' Metric.ball H δ
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV Metric.isOpen_ball
  have hWH : revolutionNormalHeight q H ∈ W :=
    ⟨hVH, by simp [hgH, hδ]⟩
  refine ⟨g, W, hW, hWH, hg.mono inter_subset_left, hgH, ?_⟩
  intro y hy
  have hgy : H ≤ g y := by
    by_contra hle
    have hlt : g y < H := lt_of_not_ge hle
    have he := hmono hy.1.2 (Metric.mem_ball_self hδ) hlt
    rw [hright y hy.1.1] at he
    exact (not_lt_of_ge hy.2.1) he
  have hi := revolutionHeightInverse_spec hq hslope hy.2
  exact (revolutionNormalHeight_strictMonoOn hq hc).injOn hgy hi.1
    ((hright y hy.1.1).trans hi.2.symm)

theorem revolutionHeightInverse_contDiffWithinAt_boundary {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    ContDiffWithinAt ℝ ∞ (revolutionHeightInverse (H := H) hq hslope)
      (Ico (revolutionNormalHeight q H) 1) (revolutionNormalHeight q H) := by
  obtain ⟨g, W, hW, hWH, hg, hgH, he⟩ :=
    revolutionHeightInverse_boundary_extension hq hc hslope
  have hpoint : revolutionHeightInverse (H := H) hq hslope (revolutionNormalHeight q H) = g (revolutionNormalHeight q H) := by
    rw [hgH]
    exact revolutionHeightInverse_left hq hc hs hslope le_rfl
  have heq : revolutionHeightInverse (H := H) hq hslope =ᶠ[
      𝓝[Ico (revolutionNormalHeight q H) 1] (revolutionNormalHeight q H)] g := by
    filter_upwards [nhdsWithin_le_nhds (hW.mem_nhds hWH), self_mem_nhdsWithin] with y hy hys
    exact (he ⟨hy, hys⟩).symm
  exact ((hg _ hWH).contDiffAt (hW.mem_nhds hWH)).contDiffWithinAt.congr_of_eventuallyEq heq hpoint

theorem revolutionHeightInverse_contDiffOn_closed {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    ContDiffOn ℝ ∞ (revolutionHeightInverse (H := H) hq hslope)
      (Ico (revolutionNormalHeight q H) 1) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with he | he
  · rw [← he]
    exact revolutionHeightInverse_contDiffWithinAt_boundary hq hc hs hslope
  · exact (revolutionHeightInverse_contDiffAt hq hc hslope ⟨he, hy.2⟩).contDiffWithinAt

end
end TightVer401
