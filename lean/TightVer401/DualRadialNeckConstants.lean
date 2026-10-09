import TightVer401.DualRadialNeckCalculus

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Topology

/-- Squared slope times the positive distance to the inner radial endpoint. -/
def dualRadialNeckCoefficient (s j a : ℝ) : ℝ := s ^ 2 * (j - a)

def dualRadialNeckConstant (value s j a : ℝ) : ℝ := value - 2 * s * (j - a)

theorem dualRadialNeckCoefficient_pos {s j a : ℝ} (hs : 0 < s) (ha : a < j) :
    0 < dualRadialNeckCoefficient s j a :=
  mul_pos (sq_pos_of_pos hs) (sub_pos.mpr ha)

theorem dualRadialNeck_incoming_sqrt {s j a : ℝ} (hs : 0 < s) (ha : a < j) :
    Real.sqrt (dualRadialNeckCoefficient s j a * (j - a)) = s * (j - a) := by
  have heq : dualRadialNeckCoefficient s j a * (j - a) = (s * (j - a)) ^ 2 := by
    dsimp [dualRadialNeckCoefficient]
    ring
  rw [heq, Real.sqrt_sq (mul_pos hs (sub_pos.mpr ha)).le]

theorem dualRadialNeck_matches_first_jet {value s j a : ℝ}
    (hs : 0 < s) (ha : a < j) :
    dualRadialNeck (dualRadialNeckConstant value s j a)
        (dualRadialNeckCoefficient s j a) a j = value ∧
      deriv (dualRadialNeck (dualRadialNeckConstant value s j a)
        (dualRadialNeckCoefficient s j a) a) j = s := by
  constructor
  · rw [dualRadialNeck, dualRadialNeck_incoming_sqrt hs ha]
    dsimp [dualRadialNeckConstant]
    ring
  · rw [dualRadialNeck_deriv _ _ (dualRadialNeckCoefficient_pos hs ha) ha,
      dualRadialNeck_incoming_sqrt hs ha]
    dsimp [dualRadialNeckCoefficient]
    have hsa : s * (j - a) ≠ 0 := (mul_pos hs (sub_pos.mpr ha)).ne'
    apply (div_eq_iff hsa).mpr
    ring

/-- A refinement of the ver500 neck adapter: the explicit profile matches
an actual incoming value and derivative. Relative radial smoothing remains separate. -/
theorem dualRadialNeck_actual_first_jet {f : ℝ → ℝ} {j a : ℝ}
    (ha : a < j) (hf : 0 < deriv f j) :
    let B := dualRadialNeckCoefficient (deriv f j) j a
    let C := dualRadialNeckConstant (f j) (deriv f j) j a
    0 < B ∧ ContDiffOn ℝ ∞ (dualRadialNeck C B a) (Ioi a) ∧
      dualRadialNeck C B a j = f j ∧ deriv (dualRadialNeck C B a) j = deriv f j ∧
      ∀ r ∈ Ioi a, 0 < deriv (dualRadialNeck C B a) r ∧
        deriv (deriv (dualRadialNeck C B a)) r < 0 := by
  dsimp only
  have hB := dualRadialNeckCoefficient_pos hf ha
  have hj := dualRadialNeck_matches_first_jet (value := f j) hf ha
  exact ⟨hB, dualRadialNeck_contDiffOn _ _ hB, hj.1, hj.2,
    fun r hr => dualRadialNeck_strict_derivative_signs _ _ hB hr⟩

end
end TightVer401
