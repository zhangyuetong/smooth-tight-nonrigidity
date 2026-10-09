import TightVer401.CorrugatedRootSmooth

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem corrugatedCosMoment_interpolation (ε k : ℝ) (n : ℕ) :
    corrugatedCosMoment ε n k = (1 - ε ^ 2) * corrugatedCosMoment 0 n k +
      ((ε ^ 2 + ε) / 2) * corrugatedCosMoment 1 n k +
      ((ε ^ 2 - ε) / 2) * corrugatedCosMoment (-1) n k := by
  have hc (e : ℝ) : Continuous (fun x => corrugatedWeight e k x * Real.cos x ^ n) :=
    (corrugatedWeight_continuous e k).mul (Real.continuous_cos.pow n)
  have hi₀ : IntervalIntegrable (fun x => (1 - ε ^ 2) *
      (corrugatedWeight 0 k x * Real.cos x ^ n)) volume 0 (2 * Real.pi) :=
    ((continuous_const (y := 1 - ε ^ 2)).mul (hc 0)).intervalIntegrable _ _
  have hi₁ : IntervalIntegrable (fun x => ((ε ^ 2 + ε) / 2) *
      (corrugatedWeight 1 k x * Real.cos x ^ n)) volume 0 (2 * Real.pi) :=
    ((continuous_const (y := (ε ^ 2 + ε) / 2)).mul (hc 1)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun x => ((ε ^ 2 - ε) / 2) *
      (corrugatedWeight (-1) k x * Real.cos x ^ n)) volume 0 (2 * Real.pi) :=
    ((continuous_const (y := (ε ^ 2 - ε) / 2)).mul (hc (-1))).intervalIntegrable _ _
  have he : (fun x => corrugatedWeight ε k x * Real.cos x ^ n) =
      (fun x => (1 - ε ^ 2) * (corrugatedWeight 0 k x * Real.cos x ^ n) +
        ((ε ^ 2 + ε) / 2) * (corrugatedWeight 1 k x * Real.cos x ^ n) +
        ((ε ^ 2 - ε) / 2) * (corrugatedWeight (-1) k x * Real.cos x ^ n)) := by
    ext x
    simp only [corrugatedWeight]
    ring
  unfold corrugatedCosMoment
  rw [he, intervalIntegral.integral_add (hi₀.add hi₁) hi₂,
    intervalIntegral.integral_add hi₀ hi₁]
  simp only [intervalIntegral.integral_const_mul]

theorem corrugatedCosMoment_joint_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => corrugatedCosMoment p.1 n p.2) := by
  have he : (fun p : ℝ × ℝ => corrugatedCosMoment p.1 n p.2) =
      (fun p => (1 - p.1 ^ 2) * corrugatedCosMoment 0 n p.2 +
        ((p.1 ^ 2 + p.1) / 2) * corrugatedCosMoment 1 n p.2 +
        ((p.1 ^ 2 - p.1) / 2) * corrugatedCosMoment (-1) n p.2) :=
    funext (fun p => corrugatedCosMoment_interpolation p.1 p.2 n)
  rw [he]
  exact (((contDiff_const.sub (contDiff_fst.pow 2)).mul
    ((corrugatedCosMoment_contDiff 0 n).comp contDiff_snd)).add
    ((((contDiff_fst.pow 2).add contDiff_fst).div_const 2).mul
      ((corrugatedCosMoment_contDiff 1 n).comp contDiff_snd))).add
    ((((contDiff_fst.pow 2).sub contDiff_fst).div_const 2).mul
      ((corrugatedCosMoment_contDiff (-1) n).comp contDiff_snd))

theorem corrugatedRootIntegral_joint_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => corrugatedRootIntegral p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => corrugatedRootIntegral p.1 p.2) =
      (fun p => corrugatedCosMoment p.1 0 p.2 + 2 * corrugatedCosMoment p.1 1 p.2) :=
    funext (fun p => corrugatedRootIntegral_eq p.1 p.2)
  rw [he]
  exact (corrugatedCosMoment_joint_contDiff 0).add
    (contDiff_const.mul (corrugatedCosMoment_joint_contDiff 1))

end
end TightVer401
