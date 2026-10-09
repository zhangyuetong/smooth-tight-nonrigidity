import TightVer401.CorrugatedRootCalculus

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

def compactTiltMass (L : ℝ) (w u : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ x in 0..L, w x * Real.exp (-k * u x)

def compactTiltFirst (L : ℝ) (w u : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ x in 0..L, w x * Real.exp (-k * u x) * u x

theorem compactTilt_integrand_continuous {w u : ℝ → ℝ} (hw : Continuous w)
    (hu : Continuous u) (k : ℝ) : Continuous (fun x => w x * Real.exp (-k * u x)) :=
  hw.mul (Real.continuous_exp.comp ((continuous_const (y := -k)).mul hu))

theorem compactTiltMass_lower {w u : ℝ → ℝ} (hw : Continuous w) (hu : Continuous u)
    {L p q k A δ : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A) (hp : 0 ≤ p)
    (hpq : p ≤ q) (hq : q ≤ L) (hw0 : ∀ x ∈ Icc 0 L, 0 ≤ w x)
    (hsmall : ∀ x ∈ Icc p q, A ≤ w x ∧ u x ≤ δ / 2) :
    (q - p) * A * Real.exp (-k * (δ / 2)) ≤ compactTiltMass L w u k := by
  have hcont := compactTilt_integrand_continuous hw hu k
  have hpoint (x : ℝ) (hx : x ∈ Icc p q) :
      A * Real.exp (-k * (δ / 2)) ≤ w x * Real.exp (-k * u x) := by
    have he : Real.exp (-k * (δ / 2)) ≤ Real.exp (-k * u x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hsmall x hx).2 (neg_nonpos.mpr hk))
    exact mul_le_mul (hsmall x hx).1 he (Real.exp_pos _).le (hw0 x ⟨hp.trans hx.1, hx.2.trans hq⟩)
  have hi := intervalIntegral.integral_mono_on hpq
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => A * Real.exp (-k * (δ / 2))) volume p q)
    (hcont.intervalIntegrable p q) hpoint
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioc 0 L), 0 ≤ w x * Real.exp (-k * u x) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact mul_nonneg (hw0 x (Ioc_subset_Icc_self hx)) (Real.exp_pos _).le
  have hsub := intervalIntegral.integral_mono_interval hp hpq hq hnonneg
    (hcont.intervalIntegrable 0 L)
  have hconst : (∫ x in p..q, A * Real.exp (-k * (δ / 2))) =
      (q - p) * A * Real.exp (-k * (δ / 2)) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hi
  exact hi.trans hsub

theorem compactTiltFirst_upper {w u : ℝ → ℝ} (hw : Continuous w) (hu : Continuous u)
    {L k B δ : ℝ} (hL : 0 ≤ L) (hk : 0 ≤ k) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hwu : ∀ x ∈ Icc 0 L, w x ∈ Icc 0 B ∧ u x ∈ Icc 0 2) :
    compactTiltFirst L w u k ≤ δ * compactTiltMass L w u k +
      L * (2 * B * Real.exp (-k * δ)) := by
  have hc := compactTilt_integrand_continuous hw hu k
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 L) :
      w x * Real.exp (-k * u x) * u x ≤
        δ * (w x * Real.exp (-k * u x)) + 2 * B * Real.exp (-k * δ) := by
    have hwx := (hwu x hx).1
    have hux := (hwu x hx).2
    have hm : 0 ≤ w x * Real.exp (-k * u x) := mul_nonneg hwx.1 (Real.exp_pos _).le
    by_cases hle : u x ≤ δ
    · have h := mul_le_mul_of_nonneg_left hle hm
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
        (Real.exp_pos (-k * δ)).le]
    · have he : Real.exp (-k * u x) ≤ Real.exp (-k * δ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (not_le.mp hle).le (neg_nonpos.mpr hk))
      have hmB : w x * Real.exp (-k * u x) ≤ B * Real.exp (-k * δ) :=
        mul_le_mul hwx.2 he (Real.exp_pos _).le hB
      have h := (mul_le_mul_of_nonneg_right hmB hux.1).trans
        (mul_le_mul_of_nonneg_left hux.2 (mul_nonneg hB (Real.exp_pos _).le))
      have hδm := mul_nonneg hδ hm
      nlinarith
  have hir : IntervalIntegrable (fun x => δ * (w x * Real.exp (-k * u x)) +
      2 * B * Real.exp (-k * δ)) volume 0 L :=
    (((continuous_const (y := δ)).mul hc).add continuous_const).intervalIntegrable _ _
  have hif : IntervalIntegrable (fun x => w x * Real.exp (-k * u x) * u x) volume 0 L :=
    (hc.mul hu).intervalIntegrable 0 L
  have hiδ : IntervalIntegrable (fun x => δ * (w x * Real.exp (-k * u x))) volume 0 L :=
    ((continuous_const (y := δ)).mul hc).intervalIntegrable 0 L
  have hiconst : IntervalIntegrable (fun _ : ℝ => 2 * B * Real.exp (-k * δ)) volume 0 L :=
    intervalIntegrable_const
  have hi := intervalIntegral.integral_mono_on hL hif hir hpoint
  rw [intervalIntegral.integral_add hiδ hiconst, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simpa only [compactTiltFirst, compactTiltMass, sub_zero, smul_eq_mul] using hi

theorem compactTiltMass_pos {w u : ℝ → ℝ} (hw : Continuous w) (hu : Continuous u)
    {L : ℝ} (hL : 0 < L) (hwpos : ∀ x ∈ Icc 0 L, 0 < w x) (k : ℝ) :
    0 < compactTiltMass L w u k := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hL continuous_const.continuousOn (compactTilt_integrand_continuous hw hu k).continuousOn
    (fun x hx => (mul_pos (hwpos x (Ioc_subset_Icc_self hx)) (Real.exp_pos _)).le)
    ⟨0, ⟨le_rfl, hL.le⟩, mul_pos (hwpos 0 ⟨le_rfl, hL.le⟩) (Real.exp_pos _)⟩
  simpa only [compactTiltMass, intervalIntegral.integral_zero] using h

theorem compactTiltFirst_nonneg {w u : ℝ → ℝ} {L k : ℝ} (hL : 0 ≤ L)
    (hwu : ∀ x ∈ Icc 0 L, 0 ≤ w x ∧ 0 ≤ u x) : 0 ≤ compactTiltFirst L w u k := by
  apply intervalIntegral.integral_nonneg hL
  intro x hx
  exact mul_nonneg (mul_nonneg (hwu x hx).1 (Real.exp_pos _).le) (hwu x hx).2

end
end TightVer401
