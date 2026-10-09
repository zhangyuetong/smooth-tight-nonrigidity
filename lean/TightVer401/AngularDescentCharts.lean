import TightVer401.PolarSupportGerm
import TightVer401.PolarSaddleSignCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Periodic scalar data on the cylinder, with actual local Cartesian angle lifts. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def angularDescentComplex (p : Coord) : ℂ := (p 0 : ℂ) + (p 1 : ℂ) * Complex.I

theorem angularDescentComplex_contDiff : ContDiff ℝ ∞ angularDescentComplex := by
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

theorem angularDescentComplex_norm (p : Coord) :
    ‖angularDescentComplex p‖ = planarRadius p := by
  simp [angularDescentComplex, Complex.norm_def, Complex.normSq, planarRadius, pow_two]

theorem angularDescent_radius_polar {q : Coord} (hq : 0 < q 0) :
    planarRadius (saddlePolarChart q) = q 0 := by
  have h : (q 0 * Real.cos (q 1))^2 + (q 0 * Real.sin (q 1))^2 = (q 0)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (q 1)]
  simp only [planarRadius, saddlePolarChart, Matrix.cons_val_zero, Matrix.cons_val_one,
    h]
  exact Real.sqrt_sq hq.le

/-- Periodicity identifies all real representatives of the same circle angle. -/
theorem angularDescent_value_eq_of_angle_eq {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    (r : ℝ) {a b : ℝ} (hab : (a : Real.Angle) = b) : W ![r, a] = W ![r, b] := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hab
  have hp : Function.Periodic (fun theta : ℝ => W ![r, theta]) (2 * Real.pi) := hperiod r
  have ha : a = b + k • (2 * Real.pi) := by
    simp only [zsmul_eq_mul] at *
    linarith
  rw [ha]
  exact hp.zsmul k b

/-- The principal angle of the polar image agrees in the real-circle quotient. -/
theorem angularDescent_angle_polar {q : Coord} (hq : 0 < q 0) :
    (Complex.arg (angularDescentComplex (saddlePolarChart q)) : Real.Angle) = q 1 := by
  have hn : ‖angularDescentComplex (saddlePolarChart q)‖ = q 0 :=
    (angularDescentComplex_norm _).trans (angularDescent_radius_polar hq)
  have hz : angularDescentComplex (saddlePolarChart q) ≠ 0 :=
    norm_pos_iff.mp (hn ▸ hq)
  apply Real.Angle.cos_sin_inj
  · rw [Complex.cos_arg hz, hn]
    simp [angularDescentComplex, saddlePolarChart, hq.ne']
    rw [← Complex.ofReal_cos]
    rfl
  · rw [Complex.sin_arg, hn]
    simp [angularDescentComplex, saddlePolarChart, hq.ne']
    rw [← Complex.ofReal_sin]
    rfl

def angularDescentPotential (W : Coord → ℝ) (p : Coord) : ℝ :=
  W ![planarRadius p, Complex.arg (angularDescentComplex p)]

theorem angularDescentPotential_polar {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {q : Coord} (hq : 0 < q 0) : angularDescentPotential W (saddlePolarChart q) = W q := by
  unfold angularDescentPotential
  rw [angularDescent_radius_polar hq,
    angularDescent_value_eq_of_angle_eq hperiod (q 0) (angularDescent_angle_polar hq)]
  congr 1
  ext i
  fin_cases i <;> simp

/-- On the second logarithm chart the angle is shifted by pi; periodicity
removes the branch discrepancy, including across the principal branch cut. -/
theorem angularDescentPotential_neg_chart {W : Coord → ℝ}
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {p : Coord} (hp : 0 < planarRadius p) :
    angularDescentPotential W p =
      W ![planarRadius p, Complex.arg (-angularDescentComplex p) - Real.pi] := by
  have hz : angularDescentComplex p ≠ 0 :=
    norm_pos_iff.mp ((angularDescentComplex_norm p).symm ▸ hp)
  apply angularDescent_value_eq_of_angle_eq hperiod
  rw [Real.Angle.coe_sub, Complex.arg_neg_coe_angle hz]
  simp

theorem angularDescent_arg_contDiffAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    Complex.imCLM.contDiff.contDiffAt.comp z hlog

/-- Every nonzero point has one of two genuine smooth Cartesian neighborhoods. -/
theorem angularDescentPotential_contDiffAt {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (hperiod : ∀ r theta : ℝ, W ![r, theta + 2 * Real.pi] = W ![r, theta])
    {p : Coord} (hp : 0 < planarRadius p) : ContDiffAt ℝ ∞ (angularDescentPotential W) p := by
  have hs : 0 < p 0^2 + p 1^2 := Real.sqrt_pos.mp hp
  have hrad : ContDiffAt ℝ ∞ planarRadius p :=
    planarRadius_contDiffOn.contDiffAt
      ((isOpen_lt continuous_const ((continuous_apply 0).pow 2 |>.add
        ((continuous_apply 1).pow 2))).mem_nhds hs)
  have hz : angularDescentComplex p ≠ 0 :=
    norm_pos_iff.mp ((angularDescentComplex_norm p).symm ▸ hp)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hpos | hneg
  · apply hW.contDiffAt.comp p
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact hrad
    · exact (angularDescent_arg_contDiffAt hpos).comp p
        angularDescentComplex_contDiff.contDiffAt
  · have hang : ContDiffAt ℝ ∞ (fun q => Complex.arg (-angularDescentComplex q) - Real.pi) p :=
      ((angularDescent_arg_contDiffAt hneg).comp p
        angularDescentComplex_contDiff.neg.contDiffAt).sub contDiffAt_const
    have hlocal : ContDiffAt ℝ ∞
        (fun q => W ![planarRadius q, Complex.arg (-angularDescentComplex q) - Real.pi]) p := by
      apply hW.contDiffAt.comp p
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact hrad
      · exact hang
    apply hlocal.congr_of_eventuallyEq
    have hc : Continuous planarRadius := by
      exact Real.continuous_sqrt.comp ((continuous_apply 0).pow 2 |>.add
        ((continuous_apply 1).pow 2))
    filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hp] with q hq
    exact angularDescentPotential_neg_chart hperiod hq

end
end TightVer401


