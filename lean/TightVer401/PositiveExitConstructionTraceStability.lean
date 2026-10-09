import TightVer401.VisibilitySpeedStability
import TightVer401.CorrugatedSeedVisiblePairs
import Mathlib.Algebra.Order.ToIntervalMod

/-! Uniform stability of the full actual visibility tuple. Both tangent
vectors vary along with the direction-defining trace. This leaf consumes
literal first-jet bounds; it does not infer Cartesian jets from sphere jets. -/
namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Compact strict visibility is open in all three actual complex entries. -/
theorem positiveExit_exists_visibility_fullTuple_threshold
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) {z a b : X → ℂ}
    (hz : Continuous z) (ha : Continuous a) (hb : Continuous b)
    (hv : ∀ s ∈ K, R < ‖z s‖ ∧
      0 < inner ℝ (a s) (corrugatedVisibilityDirection R (z s)) ∧
      0 < inner ℝ (b s) (corrugatedVisibilityDirection R (z s))) :
    ∃ ε > 0, ∀ s ∈ K, ∀ z' a' b' : ℂ,
      ‖z' - z s‖ < ε → ‖a' - a s‖ < ε → ‖b' - b s‖ < ε →
      R < ‖z'‖ ∧ 0 < inner ℝ a' (corrugatedVisibilityDirection R z') ∧
        0 < inner ℝ b' (corrugatedVisibilityDirection R z') := by
  let O : Set (ℂ × (ℂ × ℂ)) := {u | R < ‖u.1‖ ∧
    0 < inner ℝ u.2.1 (corrugatedVisibilityDirection R u.1) ∧
    0 < inner ℝ u.2.2 (corrugatedVisibilityDirection R u.1)}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro u hu
    have hu0 : u.1 ≠ 0 := norm_pos_iff.mp (hR.trans_lt hu.1)
    have cd := (visibilityDirection_continuousAt R hu0).comp continuous_fst.continuousAt
    have ca : ContinuousAt (fun v : ℂ × (ℂ × ℂ) =>
        inner ℝ v.2.1 (corrugatedVisibilityDirection R v.1)) u :=
      (continuous_fst.comp continuous_snd).continuousAt.inner cd
    have cb : ContinuousAt (fun v : ℂ × (ℂ × ℂ) =>
        inner ℝ v.2.2 (corrugatedVisibilityDirection R v.1)) u :=
      (continuous_snd.comp continuous_snd).continuousAt.inner cd
    have h1 := continuous_fst.norm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hu.1)
    have h2 := ca.preimage_mem_nhds (Ioi_mem_nhds hu.2.1)
    have h3 := cb.preimage_mem_nhds (Ioi_mem_nhds hu.2.2)
    exact inter_mem h1 (inter_mem h2 h3)
  let T : Set (ℂ × (ℂ × ℂ)) := (fun s => (z s, (a s, b s))) '' K
  have hT : IsCompact T := hK.image (hz.prodMk (ha.prodMk hb))
  have hTO : T ⊆ O := by
    rintro _ ⟨s, hs, rfl⟩
    exact hv s hs
  obtain ⟨ε, hε, he⟩ := hT.exists_thickening_subset_open hO hTO
  refine ⟨ε, hε, fun s hs z' a' b' hz' ha' hb' => ?_⟩
  change (z', (a', b')) ∈ O
  apply he
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(z s, (a s, b s)), ⟨s, hs, rfl⟩, ?_⟩
  rw [Prod.dist_eq, Prod.dist_eq]
  simpa only [dist_eq_norm] using max_lt hz' (max_lt ha' hb')

private theorem exitTraceStability_deriv_periodic {f : ℝ → ℂ} {P : ℝ}
    (hf : ContDiff ℝ ∞ f) (hP : Function.Periodic f P) :
    Function.Periodic (deriv f) P := by
  have he : (f ∘ (fun s : ℝ => s + P)) = f := funext hP
  intro s
  have hd := ((hf.differentiable (by simp) (s + P)).hasDerivAt).scomp s
    ((hasDerivAt_id s).add_const P)
  change HasDerivAt (f ∘ (fun s : ℝ => s + P)) (1 • deriv f (s + P)) s at hd
  rw [he] at hd
  simpa only [one_smul] using hd.unique (hf.differentiable (by simp) s).hasDerivAt

/-- Genuine full-period first-jet bounds preserve the actual visible pair.
The periodic representative argument propagates the result to every real parameter. -/
theorem positiveExit_exists_visiblePair_C1_threshold {R P : ℝ}
    (hR : 0 ≤ R) (hP : 0 < P) {p δ : ℝ → ℂ}
    (hp : ContDiff ℝ ∞ p) (hδ : ContDiff ℝ ∞ δ)
    (hv : ComplexVisiblePair R p δ) :
    ∃ ε > 0, ∀ (p' δ' : ℝ → ℂ),
      ContDiff ℝ ∞ p' → ContDiff ℝ ∞ δ' →
      Function.Periodic p' P → Function.Periodic δ' P →
      (∀ s ∈ Icc (0 : ℝ) P, ‖δ' s - δ s‖ < ε ∧
        ‖deriv p' s - deriv p s‖ < ε ∧ ‖deriv δ' s - deriv δ s‖ < ε) →
      ComplexVisiblePair R p' δ' := by
  have hdp : Continuous (deriv p) := (contDiff_infty_iff_deriv.mp hp).2.continuous
  have hdδ : Continuous (deriv δ) := (contDiff_infty_iff_deriv.mp hδ).2.continuous
  obtain ⟨ε, hε, he⟩ := positiveExit_exists_visibility_fullTuple_threshold
    isCompact_Icc hR hδ.continuous hdp hdδ (fun s _ => hv s)
  refine ⟨ε, hε, fun p' δ' hp' hδ' hpP hδP hclose => ?_⟩
  have hdpP := exitTraceStability_deriv_periodic hp' hpP
  have hdδP := exitTraceStability_deriv_periodic hδ' hδP
  intro s
  let r := toIcoMod hP 0 s
  have hr : r ∈ Icc (0 : ℝ) P := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP s)
  have h := he r hr (δ' r) (deriv p' r) (deriv δ' r)
    (hclose r hr).1 (hclose r hr).2.1 (hclose r hr).2.2
  have hδeq := hδP.sub_zsmul_eq (x := s) (toIcoDiv hP 0 s)
  have hpeq := hdpP.sub_zsmul_eq (x := s) (toIcoDiv hP 0 s)
  have hdeq := hdδP.sub_zsmul_eq (x := s) (toIcoDiv hP 0 s)
  change δ' r = δ' s at hδeq
  change deriv p' r = deriv p' s at hpeq
  change deriv δ' r = deriv δ' s at hdeq
  rw [hδeq, hpeq, hdeq] at h
  exact h

end
end TightVer401
