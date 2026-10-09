import TightVer401.MomentControlCircleSpan

namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem momentPrescription_positive_center (L : ℝ) [hL : Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g) (hpos : ∃ q, 0 < g q) :
    ∃ a ∈ Ioo 0 L, 0 < g (periodProjection L a) := by
  obtain ⟨q, hq⟩ := hpos
  let r := AddCircle.equivIco L 0 q
  have hr : (r : ℝ) ∈ Ico 0 L := by simpa only [zero_add] using r.property
  have hqr : periodProjection L (r : ℝ) = q := AddCircle.coe_equivIco
  by_cases hrpos : 0 < (r : ℝ)
  · exact ⟨r, ⟨hrpos, hr.2⟩, hqr ▸ hq⟩
  · have hr0 : (r : ℝ) = 0 := le_antisymm (not_lt.mp hrpos) hr.1
    have hq0 : periodProjection L 0 = q := by simpa only [hr0] using hqr
    have hg0 : 0 < g (periodProjection L 0) := by rw [hq0]; exact hq
    have hreal : Continuous (g ∘ periodProjection L) := hg.comp (AddCircle.continuous_mk' L)
    have hT : Tendsto (fun k => g (periodProjection L (momentControlRadius k))) atTop
        (𝓝 (g (periodProjection L 0))) := (hreal.tendsto 0).comp momentControlRadius_tendsto
    have hpositive : ∀ᶠ k in atTop, 0 < g (periodProjection L (momentControlRadius k)) :=
      hT.eventually (lt_mem_nhds hg0)
    have hsmall : ∀ᶠ k in atTop, momentControlRadius k < L :=
      momentControlRadius_tendsto.eventually (gt_mem_nhds hL.out)
    obtain ⟨k, hkpos, hksmall⟩ := (hpositive.and hsmall).exists
    exact ⟨momentControlRadius k, ⟨momentControlRadius_pos k, hksmall⟩, hkpos⟩

theorem momentPrescription_negative_center (L : ℝ) [Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g) (hneg : ∃ q, g q < 0) :
    ∃ a ∈ Ioo 0 L, g (periodProjection L a) < 0 := by
  have hn : ∃ q, 0 < (-g) q := by
    obtain ⟨q, hq⟩ := hneg
    exact ⟨q, neg_pos.mpr hq⟩
  obtain ⟨a, ha, hapos⟩ := momentPrescription_positive_center L hg.neg hn
  exact ⟨a, ha, neg_pos.mp hapos⟩

theorem momentPrescription_positive_neighborhood (L : ℝ) [Fact (0 < L)]
    {g : AddCircle L → ℝ} (hg : Continuous g) {a : ℝ}
    (ha : a ∈ Ioo 0 L) (hga : 0 < g (periodProjection L a)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r ∈ closedBall a R, r ∈ Ioo 0 L ∧ 0 < g (periodProjection L r) := by
  have hreal : Continuous (g ∘ periodProjection L) := hg.comp (AddCircle.continuous_mk' L)
  have hU : IsOpen (Ioo (0 : ℝ) L ∩ {r | 0 < g (periodProjection L r)}) :=
    isOpen_Ioo.inter (isOpen_lt continuous_const hreal)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ⟨ha, hga⟩)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro r hr
  exact hball ((closedBall_subset_ball (half_lt_self hε)) hr)

end
end TightVer401
