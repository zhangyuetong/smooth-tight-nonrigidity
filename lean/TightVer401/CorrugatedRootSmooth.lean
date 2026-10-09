import TightVer401.CorrugatedRootCalculus

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem corrugatedCosMoment_contDiff (ε : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (corrugatedCosMoment ε j) := by
  have hs : ∀ n : ℕ, ∀ j : ℕ, ContDiff ℝ n (corrugatedCosMoment ε j) := by
    intro n
    induction n with
    | zero =>
      intro j
      exact contDiff_zero.mpr (corrugatedCosMoment_continuous ε j)
    | succ n ih =>
      intro j
      rw [Nat.cast_add_one, contDiff_succ_iff_deriv]
      refine ⟨fun k => (corrugatedCosMoment_hasDerivAt ε j k).differentiableAt, by simp, ?_⟩
      have he : deriv (corrugatedCosMoment ε j) = -corrugatedCosMoment ε (j + 1) := by
        ext k
        exact (corrugatedCosMoment_hasDerivAt ε j k).deriv
      rw [he]
      exact (ih (j + 1)).neg
  exact contDiff_infty.mpr (fun n => hs n j)

theorem corrugatedRootIntegral_contDiff (ε : ℝ) : ContDiff ℝ ∞ (corrugatedRootIntegral ε) := by
  have he : corrugatedRootIntegral ε =
      (fun k => corrugatedCosMoment ε 0 k + 2 * corrugatedCosMoment ε 1 k) :=
    funext (corrugatedRootIntegral_eq ε)
  rw [he]
  exact (corrugatedCosMoment_contDiff ε 0).add
    (contDiff_const.mul (corrugatedCosMoment_contDiff ε 1))

theorem corrugatedCosExpectation_contDiff {ε : ℝ} (hε : |ε| < 1) :
    ContDiff ℝ ∞ (corrugatedCosExpectation ε) := by
  have he : corrugatedCosExpectation ε =
      (fun k => corrugatedCosMoment ε 1 k / corrugatedCosMoment ε 0 k) := rfl
  rw [he]
  exact (corrugatedCosMoment_contDiff ε 1).div (corrugatedCosMoment_contDiff ε 0)
    (fun k => (corrugatedCosMoment_zero_pos hε k).ne')

end
end TightVer401
