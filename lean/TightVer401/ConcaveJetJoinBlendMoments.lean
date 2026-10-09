import TightVer401.ConcaveJetJoinBlend
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem concaveJetJoinBlendError_norm_le (c r : ℝ) (hL hR : ℝ → ℝ) (f : ℝ → E) (x : ℝ) :
    ‖concaveJetJoinBlendError c r hL hR x • f x‖ ≤ ‖(hR x - hL x) • f x‖ := by
  obtain ⟨h0, h1⟩ := concaveJetJoinBlendTransition_bound c r x
  by_cases hx : x ≤ c
  · have he : concaveJetJoinBlendError c r hL hR x =
        concaveJetJoinBlendTransition c r x * (hR x - hL x) := by
      simp only [concaveJetJoinBlendError, concaveJetJoinBlendAcceleration, concaveJetJoinBlendPiecewise, if_pos hx]
      ring
    rw [he, mul_smul, norm_smul, Real.norm_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans_eq (one_mul _)
  · have he : concaveJetJoinBlendError c r hL hR x =
        -(1 - concaveJetJoinBlendTransition c r x) * (hR x - hL x) := by
      simp only [concaveJetJoinBlendError, concaveJetJoinBlendAcceleration, concaveJetJoinBlendPiecewise, if_neg hx]
      ring
    rw [he, mul_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sub_nonneg.mpr h1)]
    exact (mul_le_mul_of_nonneg_right (by linarith : 1 - concaveJetJoinBlendTransition c r x ≤ 1)
      (norm_nonneg _)).trans_eq (one_mul _)

theorem concaveJetJoinBlendPiecewise_intervalIntegrable {c A B : ℝ} {hL hR : ℝ → ℝ} {f : ℝ → E}
    (hfL : Continuous hL) (hfR : Continuous hR) (hf : Continuous f) :
    IntervalIntegrable (fun x => concaveJetJoinBlendPiecewise c hL hR x • f x) volume A B := by
  have hiL : IntervalIntegrable (fun x => hL x • f x) volume A B := (hfL.smul hf).intervalIntegrable A B
  have hiR : IntervalIntegrable (fun x => hR x • f x) volume A B := (hfR.smul hf).intervalIntegrable A B
  rw [intervalIntegrable_iff]
  have hp : Integrable ((Iic c).piecewise (fun x => hL x • f x) (fun x => hR x • f x))
      (volume.restrict (uIoc A B)) :=
    Integrable.piecewise measurableSet_Iic hiL.def'.integrableOn hiR.def'.integrableOn
  have he : (fun x => concaveJetJoinBlendPiecewise c hL hR x • f x) =
      (Iic c).piecewise (fun x => hL x • f x) (fun x => hR x • f x) := by
    funext x
    by_cases hx : x ≤ c <;> simp [concaveJetJoinBlendPiecewise, Set.piecewise, hx]
  rw [he]
  exact hp

theorem concaveJetJoinBlendPiecewise_interval_split {c A B : ℝ} {hL hR : ℝ → ℝ} {f : ℝ → E}
    (hAc : A ≤ c) (hcB : c ≤ B) (hfL : Continuous hL) (hfR : Continuous hR) (hf : Continuous f) :
    (∫ x in A..B, concaveJetJoinBlendPiecewise c hL hR x • f x) =
      (∫ x in A..c, hL x • f x) + ∫ x in c..B, hR x • f x := by
  have hleft : (∫ x in A..c, concaveJetJoinBlendPiecewise c hL hR x • f x) = ∫ x in A..c, hL x • f x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hAc
    intro x hx
    simp [concaveJetJoinBlendPiecewise, hx.2.le]
  have hright : (∫ x in c..B, concaveJetJoinBlendPiecewise c hL hR x • f x) = ∫ x in c..B, hR x • f x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hcB
    intro x hx
    simp [concaveJetJoinBlendPiecewise, not_le.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (concaveJetJoinBlendPiecewise_intervalIntegrable hfL hfR hf)
    (concaveJetJoinBlendPiecewise_intervalIntegrable hfL hfR hf), hleft, hright]

theorem concaveJetJoinBlendError_intervalIntegrable {c r A B : ℝ} {hL hR : ℝ → ℝ} {f : ℝ → E}
    (hfL : ContDiff ℝ ∞ hL) (hfR : ContDiff ℝ ∞ hR) (hf : Continuous f) :
    IntervalIntegrable (fun x => concaveJetJoinBlendError c r hL hR x • f x) volume A B := by
  have hi : IntervalIntegrable (fun x => concaveJetJoinBlendAcceleration c r hL hR x • f x) volume A B :=
    (((concaveJetJoinBlendAcceleration_contDiff (c := c) (r := r) hfL hfR).continuous.smul hf).intervalIntegrable A B)
  have hi₀ : IntervalIntegrable (fun x => concaveJetJoinBlendPiecewise c hL hR x • f x) volume A B :=
    concaveJetJoinBlendPiecewise_intervalIntegrable hfL.continuous hfR.continuous hf
  have he : (fun x => concaveJetJoinBlendError c r hL hR x • f x) =
      (fun x => concaveJetJoinBlendAcceleration c r hL hR x • f x - concaveJetJoinBlendPiecewise c hL hR x • f x) := by
    funext x
    exact sub_smul _ _ _
  rw [he]
  exact hi.sub hi₀

theorem concaveJetJoinBlendError_integral_norm_le {c r A B M : ℝ} (hr : 0 < r)
    (hL hR : ℝ → ℝ) (f : ℝ → E) (hleft : A ≤ c - r) (hright : c + r ≤ B)
    (hbound : ∀ x ∈ Icc (c - r) (c + r), ‖(hR x - hL x) • f x‖ ≤ M) :
    ‖∫ x in A..B, concaveJetJoinBlendError c r hL hR x • f x‖ ≤ 2 * M * r := by
  let F : ℝ → E := fun x => concaveJetJoinBlendError c r hL hR x • f x
  have hsupport : Function.support F ⊆ Ioo (c - r) (c + r) := by
    intro x hx
    apply concaveJetJoinBlendError_support hr hL hR
    intro hz
    exact hx (by simp [F, hz])
  have heA : (∫ x in A..B, F x) = ∫ x : ℝ, F x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hs := hsupport hx
    exact ⟨hleft.trans_lt hs.1, hs.2.le.trans hright⟩
  have heR : (∫ x in (c - r)..(c + r), F x) = ∫ x : ℝ, F x :=
    intervalIntegral.integral_eq_integral_of_support_subset (hsupport.trans Ioo_subset_Ioc_self)
  change ‖∫ x in A..B, F x‖ ≤ _
  rw [heA, ← heR]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c - r) (b := c + r) (f := F) (C := M) (fun x hx => by
      rw [uIoc_of_le (by linarith : c - r ≤ c + r)] at hx
      exact (concaveJetJoinBlendError_norm_le c r hL hR f x).trans (hbound x (Ioc_subset_Icc_self hx)))
  have hlen : |(c + r) - (c - r)| = 2 * r := by rw [abs_of_pos (by linarith)]; ring
  rw [hlen] at hn
  nlinarith [hn]

theorem concaveJetJoinBlend_exists_moment_bound (A B : ℝ) {hL hR : ℝ → ℝ} {f : ℝ → E}
    (hfL : Continuous hL) (hfR : Continuous hR) (hf : Continuous f) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc A B, ‖(hR x - hL x) • f x‖ ≤ M := by
  let F : ℝ → E := fun x => (hR x - hL x) • f x
  have hc : Continuous (fun x => ‖F x‖) := ((hfR.sub hfL).smul hf).norm
  obtain ⟨x, hx, hmax⟩ := isCompact_uIcc.exists_isMaxOn ⟨A, left_mem_uIcc⟩ hc.continuousOn
  refine ⟨‖F x‖ + 1, by positivity, fun z hz => ?_⟩
  have hb := hmax (Icc_subset_uIcc hz)
  change ‖F z‖ ≤ ‖F x‖ at hb
  change ‖F z‖ ≤ ‖F x‖ + 1
  linarith

end
end TightVer401
