import TightVer401.CorrugatedRootConcentration

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

theorem corrugated_small_zero_interval {u : ℝ → ℝ} (hu : Continuous u)
    {L c δ : ℝ} (hL : 0 < L) (hc : c ∈ Icc 0 L) (hzero : u c = 0) (hδ : 0 < δ) :
    ∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ L ∧ ∀ x ∈ Icc p q, u x ≤ δ / 2 := by
  have ht : ∀ᶠ x in 𝓝 c, u x < δ / 2 :=
    (hu.tendsto c).eventually (gt_mem_nhds (hzero ▸ half_pos hδ))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp ht
  by_cases hc0 : c = 0
  · let q := min (r / 2) (L / 2)
    have hq : 0 < q := lt_min (half_pos hr) (half_pos hL)
    have hqr : q < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    have hqL : q ≤ L := (min_le_right _ _).trans (half_le_self hL.le)
    refine ⟨0, q, le_rfl, hq, hqL, fun x hx => ?_⟩
    apply (hnear ?_).le
    rw [hc0, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact hx.2.trans_lt hqr
  · have hcp : 0 < c := hc.1.lt_of_ne' hc0
    let r' := min (r / 2) (c / 2)
    have hr' : 0 < r' := lt_min (half_pos hr) (half_pos hcp)
    have hr'r : r' < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    have hr'c : r' ≤ c := (min_le_right _ _).trans (half_le_self hc.1)
    refine ⟨c - r', c, sub_nonneg.mpr hr'c, sub_lt_self c hr', hc.2, fun x hx => ?_⟩
    apply (hnear ?_).le
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    linarith [hx.1]

theorem compactTiltFirst_eventually_ratio_lt {w u : ℝ → ℝ}
    (hw : Continuous w) (hu : Continuous u) {L A B c η : ℝ}
    (hL : 0 < L) (hA : 0 < A) (hB : 0 ≤ B)
    (hwu : ∀ x ∈ Icc 0 L, A ≤ w x ∧ w x ≤ B ∧ u x ∈ Icc 0 2)
    (hc : c ∈ Icc 0 L) (hzero : u c = 0) (hη : 0 < η) :
    ∀ᶠ k in atTop, compactTiltFirst L w u k / compactTiltMass L w u k < η := by
  let δ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hηδ : 0 < η - δ := by dsimp [δ]; linarith
  obtain ⟨p, q, hp, hpq, hq, hsmall⟩ := corrugated_small_zero_interval hu hL hc hzero hδ
  let α := (q - p) * A
  let β := L * (2 * B)
  have hα : 0 < α := mul_pos (sub_pos.mpr hpq) hA
  have hT : Tendsto (fun k : ℝ => β * Real.exp (-k * (δ / 2))) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (half_pos hδ))
    have ht' : Tendsto (fun k : ℝ => Real.exp (-k * (δ / 2))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, neg_mul] using ht
    simpa only [mul_zero] using ht'.const_mul β
  have he := hT.eventually (gt_mem_nhds (mul_pos hηδ hα))
  filter_upwards [he, eventually_ge_atTop (0 : ℝ)] with k hk hk0
  have hwpos (x : ℝ) (hx : x ∈ Icc 0 L) : 0 < w x := hA.trans_le (hwu x hx).1
  have hz := compactTiltMass_pos hw hu hL hwpos k
  have hl := compactTiltMass_lower hw hu hk0 hA.le hp hpq.le hq
    (fun x hx => (hwpos x hx).le) (fun x hx =>
      ⟨(hwu x ⟨hp.trans hx.1, hx.2.trans hq⟩).1, hsmall x hx⟩)
  have hupp := compactTiltFirst_upper hw hu hL.le hk0 hB hδ.le
    (fun x hx => ⟨⟨(hwpos x hx).le, (hwu x hx).2.1⟩, (hwu x hx).2.2⟩)
  have hex : Real.exp (-k * δ) = Real.exp (-k * (δ / 2)) * Real.exp (-k * (δ / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have herr : β * Real.exp (-k * δ) < (η - δ) * α * Real.exp (-k * (δ / 2)) := by
    rw [hex, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hk (Real.exp_pos _)
  have hl' : (η - δ) * α * Real.exp (-k * (δ / 2)) ≤
      (η - δ) * compactTiltMass L w u k := by
    simpa only [α, mul_assoc] using mul_le_mul_of_nonneg_left hl hηδ.le
  apply (div_lt_iff₀ hz).mpr
  have herr' := herr.trans_le hl'
  dsimp [β] at herr'
  nlinarith [hupp]

theorem compactTiltFirst_ratio_tendsto_zero {w u : ℝ → ℝ}
    (hw : Continuous w) (hu : Continuous u) {L A B c : ℝ}
    (hL : 0 < L) (hA : 0 < A) (hB : 0 ≤ B)
    (hwu : ∀ x ∈ Icc 0 L, A ≤ w x ∧ w x ≤ B ∧ u x ∈ Icc 0 2)
    (hc : c ∈ Icc 0 L) (hzero : u c = 0) :
    Tendsto (fun k => compactTiltFirst L w u k / compactTiltMass L w u k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have he := compactTiltFirst_eventually_ratio_lt hw hu hL hA hB hwu hc hzero hη
  filter_upwards [he] with k hk
  have hz := compactTiltMass_pos hw hu hL (fun x hx => hA.trans_le (hwu x hx).1) k
  have hn := compactTiltFirst_nonneg hL.le (fun x hx =>
    ⟨hA.le.trans (hwu x hx).1, (hwu x hx).2.2.1⟩) (k := k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hn hz.le)]
  exact hk

end
end TightVer401
