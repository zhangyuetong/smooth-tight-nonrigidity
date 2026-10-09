import TightVer401.MomentSlowdownEstimates
import TightVer401.MomentPath

namespace TightVer401
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def jetAccelerationMoment {m : ℕ} (A B : ℝ) (f : ℝ → EuclideanSpace ℝ (Fin m))
    (h : ℝ → ℝ) := ∫ x in A..B, h x • f x

theorem jetAccelerationMoment_correction {m n : ℕ} (A B : ℝ)
    {f : ℝ → EuclideanSpace ℝ (Fin m)} {ψ : Fin n → ℝ → ℝ} (c : Fin n → ℝ)
    (hf : Continuous f) (hψ : ∀ j, Continuous (ψ j)) :
    jetAccelerationMoment A B f (momentPathCorrection c ψ) =
      ∑ j, c j • jetAccelerationMoment A B f (ψ j) := by
  unfold jetAccelerationMoment momentPathCorrection
  simp_rw [Finset.sum_smul, mul_smul]
  have hi : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      IntervalIntegrable (fun x => c j • (ψ j x • f x)) volume A B :=
    fun j _ => (continuous_const (y := c j) |>.smul ((hψ j).smul hf)).intervalIntegrable A B
  rw [intervalIntegral.integral_finsetSum hi]
  simp_rw [intervalIntegral.integral_smul]

/-- A threshold is derived from the actual fixed inverse and actual controls.
The target acceleration may have a jump: only its weighted integrability is needed. -/
theorem exists_jetAccelerationControl_threshold {m n : ℕ} (A B : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin m)) (hf : Continuous f)
    (ψ : Fin n → ℝ → ℝ) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin m))) (T : V ≃L[ℝ] (Fin n → ℝ))
    (hT : ∀ u : V, (∑ j, T u j • jetAccelerationMoment A B f (ψ j)) = (u : EuclideanSpace ℝ (Fin m)))
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ ε > 0, ∀ h h₀ : ℝ → ℝ, ContDiff ℝ ∞ h →
      IntervalIntegrable (fun x => h₀ x • f x) volume A B →
      (∀ x ∈ Icc A B, μ ≤ h x) →
      (jetAccelerationMoment A B f (fun x => h x - h₀ x) ∈ V) →
      ‖jetAccelerationMoment A B f (fun x => h x - h₀ x)‖ < ε →
      ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ (∀ x ∈ Icc A B, 0 < a x) ∧
        jetAccelerationMoment A B f a = jetAccelerationMoment A B f h₀ ∧
        Function.support (fun x => a x - h x) ⊆ ⋃ j, Function.support (ψ j) := by
  classical
  obtain ⟨C, hC, hCT⟩ := momentSlowdown_coordinate_bound V T
  have hψvec : Continuous (fun x => fun j => ψ j x) :=
    continuous_pi (fun j => (hψ j).continuous)
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hψvec.continuousOn
  let K := max K₀ 1
  have hK : 0 < K := zero_lt_one.trans_le (le_max_right _ _)
  have hKψ (j) (x) (hx : x ∈ Icc A B) : |ψ j x| ≤ K := by
    calc
      |ψ j x| = ‖ψ j x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fun j => ψ j x‖ := norm_le_pi_norm (fun j : Fin n => ψ j x) j
      _ ≤ K₀ := hK₀ x hx
      _ ≤ K := le_max_left _ _
  let ε := μ / (2 * K * C)
  have hε : 0 < ε := div_pos hμ (by positivity)
  refine ⟨ε, hε, fun h h₀ hh hi₀ hbaseline hmem hsmall => ?_⟩
  let u : V := ⟨jetAccelerationMoment A B f (fun x => h x - h₀ x), hmem⟩
  let c : Fin n → ℝ := fun j => -T u j
  let correction := momentPathCorrection c ψ
  let a : ℝ → ℝ := fun x => h x + correction x
  have hcorrection : ContDiff ℝ ∞ correction := momentPathCorrection_contDiff c hψ
  have hc : (∑ j, |c j|) ≤ C * ‖u‖ := by simpa only [c, abs_neg] using hCT u
  have hu : ‖u‖ < μ / (2 * K * C) := hsmall
  have hsmallerror : K * C * ‖u‖ < μ / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * K * C by positivity)).mp hu
    nlinarith
  have herror (x) (hx : x ∈ Icc A B) : |correction x| < μ / 2 := by
    calc
      |correction x| ≤ ∑ j, |c j| * |ψ j x| := momentPathCorrection_abs_le c ψ x
      _ ≤ K * ∑ j, |c j| := by
        calc
          _ ≤ ∑ j, |c j| * K := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left (hKψ j x hx) (abs_nonneg _))
          _ = _ := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ K * (C * ‖u‖) := mul_le_mul_of_nonneg_left hc hK.le
      _ < μ / 2 := by nlinarith [hsmallerror]
  have hi : IntervalIntegrable (fun x => h x • f x) volume A B :=
    (hh.continuous.smul hf).intervalIntegrable A B
  have hiCorr : IntervalIntegrable (fun x => correction x • f x) volume A B :=
    (hcorrection.continuous.smul hf).intervalIntegrable A B
  have hErr : jetAccelerationMoment A B f (fun x => h x - h₀ x) =
      jetAccelerationMoment A B f h - jetAccelerationMoment A B f h₀ := by
    unfold jetAccelerationMoment
    simp_rw [sub_smul]
    exact intervalIntegral.integral_sub hi hi₀
  have hCorrMoment : jetAccelerationMoment A B f correction = -(u : EuclideanSpace ℝ (Fin m)) := by
    rw [jetAccelerationMoment_correction A B c hf (fun j => (hψ j).continuous)]
    simp only [c, neg_smul, Finset.sum_neg_distrib, hT]
  refine ⟨a, hh.add hcorrection, ?_, ?_, ?_⟩
  · intro x hx
    have he := herror x hx
    have hb := hbaseline x hx
    have hlow := neg_abs_le (correction x)
    change 0 < h x + correction x
    linarith
  · change jetAccelerationMoment A B f (fun x => h x + correction x) = _
    unfold jetAccelerationMoment
    simp_rw [add_smul]
    rw [intervalIntegral.integral_add hi hiCorr]
    change jetAccelerationMoment A B f h + jetAccelerationMoment A B f correction = _
    rw [hCorrMoment]
    change jetAccelerationMoment A B f h -
      jetAccelerationMoment A B f (fun x => h x - h₀ x) = _
    rw [hErr]
    abel
  · intro x hx
    by_contra hout
    have hz (j) : ψ j x = 0 := by
      by_contra hj
      exact hout (mem_iUnion.mpr ⟨j, hj⟩)
    apply hx
    change h x + momentPathCorrection c ψ x - h x = 0
    simp [momentPathCorrection, hz]

end
end TightVer401
