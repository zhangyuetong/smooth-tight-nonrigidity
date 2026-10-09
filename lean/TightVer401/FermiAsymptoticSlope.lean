import TightVer401.FermiSupportSeam
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

def fermiAsymptoticSlope (L M N : Coord → ℝ) (p : Coord) : ℝ :=
  -L p / (M p + Real.sqrt (M p ^ 2 - L p * N p))

theorem fermiAsymptoticSlope_seam {L M N : Coord → ℝ} {p : Coord}
    (hL : DifferentiableAt ℝ L p) (hM : DifferentiableAt ℝ M p)
    (hN : DifferentiableAt ℝ N p) (hzero : L p = 0) (hpos : 0 < M p) (i : Fin 2) :
    fermiAsymptoticSlope L M N p = 0 ∧
    coordPartial i (fermiAsymptoticSlope L M N) p = -coordPartial i L p / (2 * M p) := by
  let D : Coord → ℝ := fun q => M q ^ 2 - L q * N q
  let den : Coord → ℝ := fun q => M q + Real.sqrt (D q)
  have dD : DifferentiableAt ℝ D p := (hM.pow 2).sub (hL.mul hN)
  have hD : D p ≠ 0 := by
    change M p ^ 2 - L p * N p ≠ 0
    rw [hzero]
    simpa using pow_ne_zero 2 hpos.ne'
  have ds := ((Real.hasDerivAt_sqrt hD).hasFDerivAt.comp p dD.hasFDerivAt).differentiableAt
  have dden : DifferentiableAt ℝ den p := hM.add ds
  have hv : den p = 2 * M p := by
    simp only [den, D, hzero, zero_mul, sub_zero, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
    ring
  have hn : den p ≠ 0 := by rw [hv]; exact mul_ne_zero (by norm_num) hpos.ne'
  have hneg : coordPartial i (fun q => -L q) p = -coordPartial i L p := by
    simp [coordPartial, fderiv_fun_neg]
  constructor
  · simp [fermiAsymptoticSlope, hzero]
  · change coordPartial i (fun q => -L q / den q) p = _
    rw [coordPartial_scalar_div (f := fun q => -L q) (g := den) hL.neg dden hn,
      hneg, hzero, neg_zero, zero_mul, sub_zero, hv]
    field_simp
    <;> ring

theorem fermiAsymptoticSlope_quadratic {L M N : Coord → ℝ} {p : Coord}
    (hD : 0 ≤ M p ^ 2 - L p * N p)
    (hden : M p + Real.sqrt (M p ^ 2 - L p * N p) ≠ 0) :
    L p + 2 * M p * fermiAsymptoticSlope L M N p +
      N p * (fermiAsymptoticSlope L M N p)^2 = 0 := by
  have hs := Real.sq_sqrt hD
  simp only [fermiAsymptoticSlope]
  field_simp [hden]
  nlinarith [congrArg (fun z : ℝ => L p * z) hs]

end
end TightVer401
