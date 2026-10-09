import TightVer401.CorrugatedSeedVisibility
import Mathlib.Topology.MetricSpace.Thickening

namespace TightVer401
noncomputable section
open Set Filter
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

theorem visibilityDirection_continuousAt (R : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (corrugatedVisibilityDirection R) z := by
  unfold corrugatedVisibilityDirection
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hd : ((‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  fun_prop

/-- The neighborhood is derived from the strict actual visibility margins
on the compact graph, rather than assumed as a stability package. -/
theorem exists_visibility_fixedDirection_threshold {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) {δ P Q : X → ℂ}
    (hδ : Continuous δ) (hP : Continuous P) (hQ : Continuous Q)
    (hvisible : ∀ t ∈ K, R < ‖δ t‖ ∧
      0 < inner ℝ (P t) (corrugatedVisibilityDirection R (δ t)) ∧
      0 < inner ℝ (Q t) (corrugatedVisibilityDirection R (δ t))) :
    ∃ ε > 0, ∀ t ∈ K, ∀ z : ℂ, ‖z - δ t‖ < ε →
      R < ‖z‖ ∧ 0 < inner ℝ (P t) (corrugatedVisibilityDirection R z) ∧
        0 < inner ℝ (Q t) (corrugatedVisibilityDirection R z) := by
  let O : Set (X × ℂ) := {x | R < ‖x.2‖ ∧
    0 < inner ℝ (P x.1) (corrugatedVisibilityDirection R x.2) ∧
    0 < inner ℝ (Q x.1) (corrugatedVisibilityDirection R x.2)}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hz : x.2 ≠ 0 := norm_pos_iff.mp (hR.trans_lt hx.1)
    have hv := (visibilityDirection_continuousAt R hz).comp continuous_snd.continuousAt
    have hp : ContinuousAt (fun y : X × ℂ => inner ℝ (P y.1)
        (corrugatedVisibilityDirection R y.2)) x :=
      (hP.continuousAt.comp continuous_fst.continuousAt).inner hv
    have hq : ContinuousAt (fun y : X × ℂ => inner ℝ (Q y.1)
        (corrugatedVisibilityDirection R y.2)) x :=
      (hQ.continuousAt.comp continuous_fst.continuousAt).inner hv
    have hr : ContinuousAt (fun y : X × ℂ => ‖y.2‖) x := continuous_snd.norm.continuousAt
    have h₁ := hr.preimage_mem_nhds (Ioi_mem_nhds hx.1)
    have h₂ := hp.preimage_mem_nhds (Ioi_mem_nhds hx.2.1)
    have h₃ := hq.preimage_mem_nhds (Ioi_mem_nhds hx.2.2)
    exact inter_mem h₁ (inter_mem h₂ h₃)
  let G : Set (X × ℂ) := (fun t => (t, δ t)) '' K
  have hG : IsCompact G := hK.image (continuous_id.prodMk hδ)
  have hGO : G ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact hvisible t ht
  obtain ⟨ε, hε, hεO⟩ := hG.exists_thickening_subset_open hO hGO
  refine ⟨ε, hε, fun t ht z hz => ?_⟩
  change (t, z) ∈ O
  apply hεO
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(t, δ t), ⟨t, ht, rfl⟩, ?_⟩
  simpa only [dist_prod_same_left, dist_eq_norm] using hz

end
end TightVer401
