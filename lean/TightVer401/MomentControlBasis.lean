import TightVer401.MomentControlSamples

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

theorem exists_independent_moment_samples_avoiding {m : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) {S : Set ℝ}
    (hS : IsOpen S) (a : ℝ) :
    ∃ c : Fin (Module.finrank ℝ (momentSampleSpan f S)) → ℝ,
      (∀ j, c j ∈ S) ∧ (∀ j, c j ≠ a) ∧ LinearIndependent ℝ (fun j => f (c j)) ∧
      Submodule.span ℝ (Set.range (fun j => f (c j))) = momentSampleSpan f S := by
  obtain ⟨c, hc, hLI, hspan⟩ := exists_independent_moment_samples f S
  have hT (j) : Tendsto (fun k => c j + momentControlRadius k) atTop (𝓝 (c j)) := by
    simpa only [add_zero] using tendsto_const_nhds.add momentControlRadius_tendsto
  have hmem : ∀ᶠ k in atTop, ∀ j, c j + momentControlRadius k ∈ S :=
    eventually_all.mpr (fun j => (hT j).eventually (hS.mem_nhds (hc j)))
  have hne : ∀ᶠ k in atTop, ∀ j, c j + momentControlRadius k ≠ a := by
    apply eventually_all.mpr
    intro j
    by_cases hja : c j = a
    · filter_upwards with k
      rw [hja]
      exact ne_of_gt (lt_add_of_pos_right a (momentControlRadius_pos k))
    · exact (hT j).eventually (eventually_ne_nhds hja)
  have hTf : Tendsto (fun k j => f (c j + momentControlRadius k)) atTop
      (𝓝 (fun j => f (c j))) :=
    tendsto_pi_nhds.mpr (fun j => (hf.tendsto (c j)).comp (hT j))
  obtain ⟨k, hkS, hka, hkLI⟩ := (hmem.and (hne.and (hTf.eventually hLI.eventually))).exists
  refine ⟨(fun j => c j + momentControlRadius k), hkS, hka, hkLI, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨_, hkS j, rfl⟩
  · simpa only [Fintype.card_fin] using finrank_span_eq_card hkLI

theorem exists_short_independent_interval_controls {m : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) {L a ε : ℝ}
    (ha : a ∈ Ioo 0 L) (hε : 0 < ε) :
    ∃ (r : ℝ) (ψ : Fin (Module.finrank ℝ (momentSampleSpan f (Ioo 0 L))) → ℝ → ℝ),
      0 < r ∧ r < ε ∧ 0 < a - r ∧ a + r < L ∧
      (∀ j, ContDiff ℝ ∞ (ψ j)) ∧ (∀ j x, 0 ≤ ψ j x) ∧
      (∀ j, ∫ x in 0..L, ψ j x = 1) ∧
      (∀ j, tsupport (ψ j) ⊆ Ioo 0 L) ∧
      (∀ j, ∃ c : ℝ, tsupport (ψ j) = Icc (c - r) (c + r)) ∧
      Pairwise (fun i j => Disjoint (tsupport (ψ i)) (tsupport (ψ j))) ∧
      (∀ j, Disjoint (tsupport (ψ j)) (closedBall a r)) ∧
      LinearIndependent ℝ (fun j => ∫ x in 0..L, ψ j x • f x) ∧
      Submodule.span ℝ (Set.range (fun j => ∫ x in 0..L, ψ j x • f x)) =
        momentSampleSpan f (Ioo 0 L) := by
  obtain ⟨c, hc, hca, hLI, hspan⟩ :=
    exists_independent_moment_samples_avoiding (S := Ioo 0 L) hf isOpen_Ioo a
  have hcI : Function.Injective c := by
    intro i j hij
    apply hLI.injective
    exact congrArg f hij
  have hεr : ∀ᶠ k in atTop, momentControlRadius k < ε :=
    momentControlRadius_tendsto.eventually (gt_mem_nhds hε)
  have har : ∀ᶠ k in atTop,
      momentControlRadius k < a ∧ momentControlRadius k < L - a :=
    (momentControlRadius_tendsto.eventually (gt_mem_nhds ha.1)).and
      (momentControlRadius_tendsto.eventually (gt_mem_nhds (sub_pos.mpr ha.2)))
  have hgood := (momentControlSequence_eventually_independent hf c hLI).and
    ((momentControlSequence_eventually_contained c L hc).and
      ((momentControlSequence_eventually_disjoint c hcI).and
        ((momentControlSequence_eventually_avoids c a hca).and (hεr.and har))))
  obtain ⟨k, hkLI, hkS, hkD, hka, hkε, hka0, hkaL⟩ := hgood.exists
  let r := momentControlRadius k
  let ψ := fun j => momentControlSequence (c j) k
  have hψS (j) : Function.support (ψ j) ⊆ Ioo 0 L :=
    subset_closure.trans (hkS j)
  have hedge (j) : 0 ≤ c j - r ∧ c j + r ≤ L := by
    have hEnds := hkS j
    rw [momentControlSequence, normalizedMomentControl_tsupport] at hEnds
    have hLo := hEnds (show c j - r ∈ Icc (c j - r) (c j + r) by
      constructor <;> linarith [momentControlRadius_pos k])
    have hHi := hEnds (show c j + r ∈ Icc (c j - r) (c j + r) by
      constructor <;> linarith [momentControlRadius_pos k])
    exact ⟨hLo.1.le, hHi.2.le⟩
  have hMoment (j) : (∫ x in 0..L, ψ j x • f x) = realControlMoment f (ψ j) :=
    normalizedMomentControl_intervalMoment f (c j) r L (momentControlRadius_pos k)
      (hedge j).1 (hedge j).2
  have hMass (j) : ∫ x in 0..L, ψ j x = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hψS j |>.trans Ioo_subset_Ioc_self)]
    exact normalizedMomentControl_integral (c j) r (momentControlRadius_pos k)
  refine ⟨r, ψ, momentControlRadius_pos k, hkε, by linarith, by linarith,
    (fun j => normalizedMomentControl_contDiff (c j) r (momentControlRadius_pos k)),
    (fun j x => normalizedMomentControl_nonneg (c j) r (momentControlRadius_pos k) x),
    hMass, hkS, (fun j => ⟨c j,
      normalizedMomentControl_tsupport (c j) r (momentControlRadius_pos k)⟩),
    hkD, hka, ?_, ?_⟩
  · simpa only [hMoment] using hkLI
  · simpa only [hMoment] using independent_control_moments_span ψ hψS hkLI

end
end TightVer401
