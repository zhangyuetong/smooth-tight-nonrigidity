import TightVer401.DualRadialNeckInverse

namespace TightVer401
noncomputable section
open Set Filter
open scoped Topology

/-- The actual slope of the square-root profile escapes to infinity at its
inner endpoint. No smoothing or geometric attachment is assumed. -/
theorem dualRadialNeck_deriv_tendsto_atTop (C a : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (deriv (dualRadialNeck C B a)) (𝓝[>] a) atTop := by
  apply tendsto_atTop.2
  intro m
  let q : ℝ := max m 0 + 1
  have hq : 0 < q := by dsimp [q]; linarith [le_max_right m 0]
  have hδ : 0 < B / q ^ 2 := div_pos hB (sq_pos_of_pos hq)
  have hnear : ∀ᶠ r in 𝓝[>] a, r < a + B / q ^ 2 :=
    (eventually_lt_nhds (lt_add_of_pos_right a hδ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with r hr hrδ
  rw [dualRadialNeck_deriv C a hB hr]
  have hdisc : 0 < B * (r - a) := mul_pos hB (sub_pos.mpr hr)
  have hs := Real.sqrt_pos.mpr hdisc
  have hbound : B * (r - a) < (B / q) ^ 2 := by
    have hsmall : r - a < B / q ^ 2 := by linarith
    have hmul := mul_lt_mul_of_pos_left hsmall hB
    have heq : B * (B / q ^ 2) = (B / q) ^ 2 := by field_simp
    rwa [heq] at hmul
  have hsbound := (Real.sqrt_lt' (div_pos hB hq)).mpr hbound
  have hsq : Real.sqrt (B * (r - a)) * q < B :=
    (lt_div_iff₀ hq).mp hsbound
  have hquot : q < B / Real.sqrt (B * (r - a)) :=
    (lt_div_iff₀ hs).mpr (by nlinarith [hsq])
  have hmq : m < q := by dsimp [q]; linarith [le_max_left m 0]
  exact (hmq.trans hquot).le

theorem dualRadialNeck_tendsto_endpoint (C B a : ℝ) :
    Tendsto (dualRadialNeck C B a) (𝓝[>] a) (𝓝 C) := by
  have hc : Continuous (dualRadialNeck C B a) :=
    continuous_const.add (continuous_const.mul
      ((continuous_const.mul (continuous_id.sub continuous_const)).sqrt))
  have ht : Tendsto (dualRadialNeck C B a) (𝓝 a)
      (𝓝 (dualRadialNeck C B a a)) := hc.continuousAt.tendsto
  simpa only [dualRadialNeck, sub_self, mul_zero, Real.sqrt_zero, add_zero]
    using ht.mono_left (nhdsWithin_le_nhds : 𝓝[>] a ≤ 𝓝 a)

theorem dualRadialNeck_inverse_radius_tendsto (a B : ℝ) :
    Tendsto (dualRadialNeckInverseRadius a B) atTop (𝓝 a) := by
  change Tendsto (fun p : ℝ => a + B / p ^ 2) atTop (𝓝 a)
  have hinv : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hterm : Tendsto (fun p : ℝ => B * (p⁻¹) ^ 2) atTop (𝓝 (B * 0 ^ 2)) :=
    tendsto_const_nhds.mul (hinv.pow 2)
  have hsum : Tendsto (fun p : ℝ => a + B * (p⁻¹) ^ 2) atTop
      (𝓝 (a + B * 0 ^ 2)) := tendsto_const_nhds.add hterm
  simpa only [dualRadialNeckInverseRadius, div_eq_mul_inv, inv_pow,
    zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] using hsum

end
end TightVer401
