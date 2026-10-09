import TightVer401.MomentControlCircle
import TightVer401.MomentControlCoefficients
import TightVer401.MomentPath

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology BigOperators

def nonnegativeSmoothPeriodMoments {m : ℕ} (L : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {v | ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ Function.Periodic a L ∧
    (∀ s, 0 ≤ a s) ∧ momentPathMoment L f a = v}

theorem nonnegativeSmoothPeriodMoments_zero {m : ℕ} (L : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) :
    (0 : EuclideanSpace ℝ (Fin m)) ∈ nonnegativeSmoothPeriodMoments L f := by
  refine ⟨fun _ => 0, contDiff_const, fun _ => rfl, fun _ => le_rfl, ?_⟩
  simp [momentPathMoment]

theorem nonnegativeSmoothPeriodMoments_convex {m : ℕ} (L : ℝ)
    {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f) :
    Convex ℝ (nonnegativeSmoothPeriodMoments L f) := by
  rintro x ⟨u, hu, hpu, hnu, rfl⟩ y ⟨v, hv, hpv, hnv, rfl⟩ a b ha hb _
  refine ⟨fun s => a * u s + b * v s,
    (contDiff_const.mul hu).add (contDiff_const.mul hv), ?_, ?_, ?_⟩
  · intro s
    simp only [hpu s, hpv s]
  · intro s
    exact add_nonneg (mul_nonneg ha (hnu s)) (mul_nonneg hb (hnv s))
  · unfold momentPathMoment
    simp_rw [add_smul, mul_smul]
    have hiu : IntervalIntegrable (fun s => a • (u s • f s)) volume 0 L :=
      ((continuous_const (y := a)).smul (hu.continuous.smul hf)).intervalIntegrable 0 L
    have hiv : IntervalIntegrable (fun s => b • (v s • f s)) volume 0 L :=
      ((continuous_const (y := b)).smul (hv.continuous.smul hf)).intervalIntegrable 0 L
    rw [intervalIntegral.integral_add hiu hiv,
      intervalIntegral.integral_smul, intervalIntegral.integral_smul]

theorem nonnegativeSmoothPeriodMoments_smul {m : ℕ} (L : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) {v : EuclideanSpace ℝ (Fin m)}
    (hv : v ∈ nonnegativeSmoothPeriodMoments L f) {c : ℝ} (hc : 0 ≤ c) :
    c • v ∈ nonnegativeSmoothPeriodMoments L f := by
  obtain ⟨a, ha, hpa, hna, rfl⟩ := hv
  refine ⟨fun s => c * a s, contDiff_const.mul ha, ?_, ?_, ?_⟩
  · intro s
    simp only [hpa s]
  · intro s
    exact mul_nonneg hc (hna s)
  · simp only [momentPathMoment, mul_smul, intervalIntegral.integral_smul]

theorem sample_mem_closure_nonnegativeSmoothPeriodMoments {m : ℕ} (L : ℝ)
    [Fact (0 < L)] {f : ℝ → EuclideanSpace ℝ (Fin m)} (hf : Continuous f)
    {a : ℝ} (ha : a ∈ Ioo 0 L) :
    f a ∈ closure (nonnegativeSmoothPeriodMoments L f) := by
  have hins : ∀ᶠ k : ℕ in atTop, tsupport (momentControlSequence a k) ⊆ Ioo 0 L := by
    have hc := momentControlSequence_eventually_contained (fun _ : Fin 1 => a) L (fun _ => ha)
    exact hc.mono (fun k hk => hk 0)
  apply isClosed_closure.mem_of_tendsto (momentControlSequence_moment_tendsto hf a)
  filter_upwards [hins] with k hk
  apply subset_closure
  refine ⟨momentPeriodicRepresentative L (momentControlSequence a k),
    momentPeriodicRepresentative_contDiff L
      (normalizedMomentControl_contDiff a (momentControlRadius k) (momentControlRadius_pos k))
      ?_ hk,
    momentPeriodicRepresentative_periodic L _,
    momentPeriodicRepresentative_nonneg L
      (normalizedMomentControl_nonneg a (momentControlRadius k) (momentControlRadius_pos k)), ?_⟩
  · change IsCompact (tsupport (momentControlSequence a k))
    rw [momentControlSequence, normalizedMomentControl_tsupport]
    exact isCompact_Icc
  · change (∫ s in 0..L, momentPeriodicRepresentative L (momentControlSequence a k) s • f s) = _
    rw [momentPeriodicRepresentative_intervalMoment L hk f]
    exact controlMoment_interval_eq_real (fun _ hx => hk (subset_closure hx))

theorem circle_range_subset_closure_nonnegativeSmoothPeriodMoments {m : ℕ} (L : ℝ)
    [hL : Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) :
    Set.range f ⊆ closure (nonnegativeSmoothPeriodMoments L (f ∘ periodProjection L)) := by
  let g := f ∘ periodProjection L
  have hg : Continuous g := hf.comp (AddCircle.continuous_mk' L)
  have hz : g 0 ∈ closure (nonnegativeSmoothPeriodMoments L g) := by
    apply isClosed_closure.mem_of_tendsto ((hg.tendsto 0).comp momentControlRadius_tendsto)
    have hs : ∀ᶠ k in atTop, momentControlRadius k < L :=
      momentControlRadius_tendsto.eventually (gt_mem_nhds hL.out)
    filter_upwards [hs] with k hk
    exact sample_mem_closure_nonnegativeSmoothPeriodMoments L hg
      ⟨momentControlRadius_pos k, hk⟩
  rintro _ ⟨q, rfl⟩
  let r := AddCircle.equivIco L 0 q
  have hr : (r : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using r.property
  have hq : periodProjection L (r : ℝ) = q := AddCircle.coe_equivIco
  have he : f q = g (r : ℝ) := (congrArg f hq).symm
  rw [he]
  by_cases hpos : 0 < (r : ℝ)
  · exact sample_mem_closure_nonnegativeSmoothPeriodMoments L hg ⟨hpos, hr.2⟩
  · have hr0 : (r : ℝ) = 0 := le_antisymm (not_lt.mp hpos) hr.1
    rw [hr0]
    exact hz

theorem circle_convexHull_subset_closure_nonnegativeSmoothPeriodMoments {m : ℕ}
    (L : ℝ) [Fact (0 < L)] {f : AddCircle L → EuclideanSpace ℝ (Fin m)}
    (hf : Continuous f) :
    convexHull ℝ (Set.range f) ⊆
      closure (nonnegativeSmoothPeriodMoments L (f ∘ periodProjection L)) :=
  convexHull_min (circle_range_subset_closure_nonnegativeSmoothPeriodMoments L hf)
    (nonnegativeSmoothPeriodMoments_convex L (hf.comp (AddCircle.continuous_mk' L))).closure

end
end TightVer401
