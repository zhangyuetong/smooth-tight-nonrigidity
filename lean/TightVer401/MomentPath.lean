import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

def momentPathCorrection {n : ℕ} (c : Fin n → ℝ) (ψ : Fin n → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ j, c j * ψ j s

def momentPath {n : ℕ} (b χ : ℝ → ℝ) (c : Fin n → ℝ) (ψ : Fin n → ℝ → ℝ)
    (t s : ℝ) : ℝ := b s - t * χ s * b s + t * momentPathCorrection c ψ s

def momentPathMoment {m : ℕ} (L : ℝ) (f : ℝ → EuclideanSpace ℝ (Fin m)) (a : ℝ → ℝ) :
    EuclideanSpace ℝ (Fin m) := ∫ s in 0..L, a s • f s

theorem momentPathCorrection_contDiff {n : ℕ} (c : Fin n → ℝ) {ψ : Fin n → ℝ → ℝ}
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) : ContDiff ℝ ∞ (momentPathCorrection c ψ) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (hψ j))

theorem momentPath_contDiff {n : ℕ} {b χ : ℝ → ℝ} (c : Fin n → ℝ)
    {ψ : Fin n → ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) (t : ℝ) : ContDiff ℝ ∞ (momentPath b χ c ψ t) :=
  (hb.sub ((contDiff_const.mul hχ).mul hb)).add
    (contDiff_const.mul (momentPathCorrection_contDiff c hψ))

theorem momentPath_joint_contDiff {n : ℕ} {b χ : ℝ → ℝ} (c : Fin n → ℝ)
    {ψ : Fin n → ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ)
    (hψ : ∀ j, ContDiff ℝ ∞ (ψ j)) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => momentPath b χ c ψ x.1 x.2) :=
  ((hb.comp contDiff_snd).sub ((contDiff_fst.mul (hχ.comp contDiff_snd)).mul
    (hb.comp contDiff_snd))).add
    (contDiff_fst.mul ((momentPathCorrection_contDiff c hψ).comp contDiff_snd))

theorem momentPath_periodic {n : ℕ} {b χ : ℝ → ℝ} (c : Fin n → ℝ)
    {ψ : Fin n → ℝ → ℝ} {L : ℝ} (hb : Function.Periodic b L)
    (hχ : Function.Periodic χ L) (hψ : ∀ j, Function.Periodic (ψ j) L) (t : ℝ) :
    Function.Periodic (momentPath b χ c ψ t) L := by
  intro s
  simp [momentPath, momentPathCorrection, hb s, hχ s, fun j => hψ j s]

theorem momentPath_at_zero {n : ℕ} (b χ : ℝ → ℝ) (c : Fin n → ℝ)
    (ψ : Fin n → ℝ → ℝ) : momentPath b χ c ψ 0 = b := by
  ext s
  simp [momentPath]

theorem momentPath_zero_controls (b χ : ℝ → ℝ) (c : Fin 0 → ℝ)
    (ψ : Fin 0 → ℝ → ℝ) (t s : ℝ) : momentPath b χ c ψ t s = b s - t * χ s * b s := by
  simp [momentPath, momentPathCorrection]

theorem momentPathCorrection_abs_le {n : ℕ} (c : Fin n → ℝ) (ψ : Fin n → ℝ → ℝ) (s : ℝ) :
    |momentPathCorrection c ψ s| ≤ ∑ j, |c j| * |ψ j s| := by
  simpa [momentPathCorrection, abs_mul] using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => c j * ψ j s))

theorem momentPath_pos {n : ℕ} {b χ : ℝ → ℝ} {c : Fin n → ℝ}
    {ψ : Fin n → ℝ → ℝ} {t s : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hb : 0 < b s) (hχ : 0 ≤ χ s ∧ χ s ≤ 1)
    (hdisjoint : χ s ≠ 0 → ∀ j, ψ j s = 0)
    (hbound : χ s = 0 → (∑ j, |c j| * |ψ j s|) < b s) :
    0 < momentPath b χ c ψ t s := by
  by_cases hz : χ s = 0
  · have hc := (momentPathCorrection_abs_le c ψ s).trans_lt (hbound hz)
    have htc : |t * momentPathCorrection c ψ s| ≤ |momentPathCorrection c ψ s| := by
      rw [abs_mul, abs_of_nonneg ht]
      nlinarith [abs_nonneg (momentPathCorrection c ψ s)]
    have hlo := neg_abs_le (t * momentPathCorrection c ψ s)
    simp only [momentPath, hz, mul_zero, zero_mul, sub_zero]
    linarith
  · have hc : momentPathCorrection c ψ s = 0 := by
      simp [momentPathCorrection, hdisjoint hz]
    have hfac : 0 < 1 - t * χ s := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hχ.2)]
    have hprod := mul_pos hb hfac
    simp only [momentPath, hc, mul_zero, add_zero]
    nlinarith

theorem momentPathMoment_correction {n m : ℕ} (L : ℝ) (c : Fin n → ℝ)
    {ψ : Fin n → ℝ → ℝ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hψ : ∀ j, Continuous (ψ j)) (hf : Continuous f) :
    momentPathMoment L f (momentPathCorrection c ψ) =
      ∑ j, c j • momentPathMoment L f (ψ j) := by
  unfold momentPathMoment momentPathCorrection
  simp_rw [Finset.sum_smul, mul_smul]
  have hi : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun s => c j • (ψ j s • f s)) volume 0 L :=
    fun j _ => (continuous_const (y := c j) |>.smul ((hψ j).smul hf)).intervalIntegrable 0 L
  rw [intervalIntegral.integral_finsetSum hi]
  simp_rw [intervalIntegral.integral_smul]

theorem momentPathMoment_eq {n m : ℕ} (L : ℝ) {b χ : ℝ → ℝ} (c : Fin n → ℝ)
    {ψ : Fin n → ℝ → ℝ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    (hb : Continuous b) (hχ : Continuous χ) (hψ : ∀ j, Continuous (ψ j)) (hf : Continuous f)
    (hbalance : (∑ j, c j • momentPathMoment L f (ψ j)) =
      momentPathMoment L f (fun s => χ s * b s)) (t : ℝ) :
    momentPathMoment L f (momentPath b χ c ψ t) = momentPathMoment L f b := by
  have hcorr : Continuous (momentPathCorrection c ψ) :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (hψ j))
  have hi₀ : IntervalIntegrable (fun s => b s • f s) volume 0 L :=
    (hb.smul hf).intervalIntegrable 0 L
  have hi₁ : IntervalIntegrable (fun s => (χ s * b s) • f s) volume 0 L :=
    ((hχ.mul hb).smul hf).intervalIntegrable 0 L
  have hi₂ : IntervalIntegrable (fun s => momentPathCorrection c ψ s • f s) volume 0 L :=
    (hcorr.smul hf).intervalIntegrable 0 L
  have hit₁ : IntervalIntegrable (fun s => t • ((χ s * b s) • f s)) volume 0 L := hi₁.smul t
  have hit₂ : IntervalIntegrable (fun s => t • (momentPathCorrection c ψ s • f s)) volume 0 L := hi₂.smul t
  have he : (fun s => momentPath b χ c ψ t s • f s) =
      fun s => b s • f s - t • ((χ s * b s) • f s) +
        t • (momentPathCorrection c ψ s • f s) := by
    ext s
    simp [momentPath, add_smul, sub_smul, mul_smul]
  unfold momentPathMoment
  rw [he, intervalIntegral.integral_add (hi₀.sub hit₁) hit₂,
    intervalIntegral.integral_sub hi₀ hit₁,
    intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  change momentPathMoment L f b - t • momentPathMoment L f (fun s => χ s * b s) +
    t • momentPathMoment L f (momentPathCorrection c ψ) = momentPathMoment L f b
  rw [momentPathMoment_correction L c hψ hf, hbalance]
  abel

theorem momentPath_difference_abs_le {n : ℕ} (b χ : ℝ → ℝ) (c : Fin n → ℝ)
    (ψ : Fin n → ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    |momentPath b χ c ψ t s - b s| ≤
      t * (|χ s * b s| + ∑ j, |c j| * |ψ j s|) := by
  have he : momentPath b χ c ψ t s - b s =
      t * (momentPathCorrection c ψ s - χ s * b s) := by
    unfold momentPath
    ring
  rw [he, abs_mul, abs_of_nonneg ht]
  apply mul_le_mul_of_nonneg_left _ ht
  have hs := abs_sub (momentPathCorrection c ψ s) (χ s * b s)
  linarith [momentPathCorrection_abs_le c ψ s]

theorem momentPath_l1_le {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {b χ : ℝ → ℝ} (c : Fin n → ℝ) {ψ : Fin n → ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in 0..L, ‖momentPath b χ c ψ t s - b s‖) ≤
      (∫ s in 0..L, |χ s * b s|) +
        ∑ j, |c j| * (∫ s in 0..L, |ψ j s|) := by
  have hC : Continuous (fun s => ∑ j, |c j| * |ψ j s|) :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (hψ j).continuous.abs)
  have hS : Continuous (fun s => |χ s * b s|) := (hχ.continuous.mul hb.continuous).abs
  have hD := ((momentPath_contDiff c hb hχ hψ t).continuous.sub hb.continuous).norm
  have hmono : (∫ s in 0..L, ‖momentPath b χ c ψ t s - b s‖) ≤
      ∫ s in 0..L, |χ s * b s| + ∑ j, |c j| * |ψ j s| :=
    intervalIntegral.integral_mono hL (hD.intervalIntegrable 0 L)
    ((hS.add hC).intervalIntegrable 0 L) (fun s => by
      rw [Real.norm_eq_abs]
      apply (momentPath_difference_abs_le b χ c ψ ht s).trans
      have hnonneg : 0 ≤ |χ s * b s| + ∑ j, |c j| * |ψ j s| := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hnonneg)
  have hiψ : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun s => |c j| * |ψ j s|) volume 0 L :=
    fun j _ => ((continuous_const (y := |c j|)).mul (hψ j).continuous.abs).intervalIntegrable 0 L
  rw [intervalIntegral.integral_add (hS.intervalIntegrable 0 L) (hC.intervalIntegrable 0 L),
    intervalIntegral.integral_finsetSum hiψ] at hmono
  simpa only [intervalIntegral.integral_const_mul] using hmono

theorem momentPath_l1_lt {n : ℕ} {L η : ℝ} (hL : 0 ≤ L)
    {b χ : ℝ → ℝ} (c : Fin n → ℝ) {ψ : Fin n → ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hsmall : (∫ s in 0..L, |χ s * b s|) +
      (∑ j, |c j| * (∫ s in 0..L, |ψ j s|)) < η)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    (∫ s in 0..L, ‖momentPath b χ c ψ t s - b s‖) < η :=
  (momentPath_l1_le hL c hb hχ hψ ht ht1.le).trans_lt hsmall

end
end TightVer401
