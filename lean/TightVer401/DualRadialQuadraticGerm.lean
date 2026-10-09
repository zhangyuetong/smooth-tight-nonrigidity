import TightVer401.RadialPlanarCurvature
import TightVer401.RevolutionEndCalculus

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact radial terminal germ in ver500, without an angular filling or smoothing assertion. -/
def dualRadialQuadraticProfile (R M d r : ℝ) : ℝ := M * R * r - M / 2 * r ^ 2 + d

def dualRadialQuadraticPotential (R M d : ℝ) : Coord → ℝ :=
  radialPlanarPotential (dualRadialQuadraticProfile R M d)

theorem dualRadialQuadraticProfile_contDiff (R M d : ℝ) :
    ContDiff ℝ ∞ (dualRadialQuadraticProfile R M d) := by
  exact ((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 2))).add contDiff_const

theorem dualRadialQuadraticProfile_hasDerivAt (R M d r : ℝ) :
    HasDerivAt (dualRadialQuadraticProfile R M d) (M * R - M * r) r := by
  convert! (((hasDerivAt_id r).const_mul (M * R)).sub
    (((hasDerivAt_id r).pow 2).const_mul (M / 2))).add_const d using 1 <;> simp only [id_eq] <;> ring

theorem dualRadialQuadraticProfile_deriv (R M d : ℝ) :
    deriv (dualRadialQuadraticProfile R M d) = fun r => M * R - M * r := by
  funext r
  exact (dualRadialQuadraticProfile_hasDerivAt R M d r).deriv

theorem dualRadialQuadraticProfile_second_deriv (R M d : ℝ) :
    deriv (deriv (dualRadialQuadraticProfile R M d)) = fun _ => -M := by
  rw [dualRadialQuadraticProfile_deriv]
  funext r
  simpa using ((hasDerivAt_const r (M * R)).sub ((hasDerivAt_id r).const_mul M)).deriv

theorem dualRadialQuadraticProfile_signs {R M d r : ℝ} (hM : 0 < M) (hr : r < R) :
    0 < deriv (dualRadialQuadraticProfile R M d) r ∧
      deriv (deriv (dualRadialQuadraticProfile R M d)) r < 0 := by
  rw [dualRadialQuadraticProfile_second_deriv, dualRadialQuadraticProfile_deriv]
  exact ⟨by nlinarith [mul_pos hM (sub_pos.mpr hr)], neg_neg_of_pos hM⟩

theorem dualRadialQuadraticPotential_contDiffOn (R M d : ℝ) :
    ContDiffOn ℝ ∞ (dualRadialQuadraticPotential R M d)
      (radialPlanarDomain (Ioo 0 R)) :=
  radialPlanarPotential_contDiffOn (dualRadialQuadraticProfile_contDiff R M d).contDiffOn

theorem dualRadialQuadraticPotential_hessian {R M d : ℝ} {p : Coord}
    (hp : p ∈ radialPlanarDomain (Ioo 0 R)) (i j : Fin 2) :
    planarHessian (dualRadialQuadraticPotential R M d) p i j =
      (M * R - M * planarRadius p) / planarRadius p * (if i = j then 1 else 0) +
      (-M / planarRadius p ^ 2 -
        (M * R - M * planarRadius p) / planarRadius p ^ 3) * p i * p j := by
  exact (radialPlanarPotential_hessian
    (dualRadialQuadraticProfile_contDiff R M d).contDiffOn isOpen_Ioo hp i j).trans
    (by rw [dualRadialQuadraticProfile_second_deriv, dualRadialQuadraticProfile_deriv])

theorem dualRadialQuadraticPotential_hessian_det {R M d : ℝ} {p : Coord}
    (hp : p ∈ radialPlanarDomain (Ioo 0 R)) :
    (planarHessian (dualRadialQuadraticPotential R M d) p).det =
      -(M ^ 2 * (R - planarRadius p)) / planarRadius p := by
  rw [dualRadialQuadraticPotential, radialPlanarPotential_hessian_det
    (dualRadialQuadraticProfile_contDiff R M d).contDiffOn isOpen_Ioo hp,
    dualRadialQuadraticProfile_second_deriv, dualRadialQuadraticProfile_deriv]
  ring

theorem dualRadialQuadraticPotential_hessian_det_neg {R M d : ℝ}
    (hM : 0 < M) {p : Coord} (hp : p ∈ radialPlanarDomain (Ioo 0 R)) :
    (planarHessian (dualRadialQuadraticPotential R M d) p).det < 0 := by
  rw [dualRadialQuadraticPotential_hessian_det hp]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (sq_pos_of_pos hM)
    (sub_pos.mpr hp.2.2))) hp.2.1

theorem dualRadialQuadraticPotential_gaussianCurvature_neg {R M d : ℝ}
    (hM : 0 < M) {p : Coord} (hp : p ∈ radialPlanarDomain (Ioo 0 R)) :
    gaussianCurvature (inducedMetric (planarSupportMap
      (dualRadialQuadraticPotential R M d))) p < 0 := by
  have hs := dualRadialQuadraticProfile_signs (d := d) hM hp.2.2
  exact radialPlanarPotential_gaussianCurvature_neg
    (dualRadialQuadraticProfile_contDiff R M d).contDiffOn isOpen_Ioo hp
    (mul_neg_of_pos_of_neg hs.1 hs.2)

theorem dualRadialQuadraticPotential_differential_injective {R M d : ℝ}
    (hM : 0 < M) {p : Coord} (hp : p ∈ radialPlanarDomain (Ioo 0 R)) :
    Function.Injective (fderiv ℝ (planarSupportMap (dualRadialQuadraticPotential R M d)) p) :=
  planarSupportMap_differential_injective (dualRadialQuadraticPotential_contDiffOn R M d)
    (radialPlanarDomain_isOpen isOpen_Ioo) hp
    (dualRadialQuadraticPotential_hessian_det_neg hM hp).ne

theorem dualRadialQuadraticPotential_gaussianCurvature {R M d : ℝ}
    (hM : 0 < M) {p : Coord} (hp : p ∈ radialPlanarDomain (Ioo 0 R)) :
    gaussianCurvature (inducedMetric (planarSupportMap (dualRadialQuadraticPotential R M d))) p =
      -planarRadius p / (planarWeight p ^ 4 * (M ^ 2 * (R - planarRadius p))) := by
  have hs := dualRadialQuadraticProfile_signs (d := d) hM hp.2.2
  have hprod := (mul_neg_of_pos_of_neg hs.1 hs.2).ne
  rw [dualRadialQuadraticPotential, radialPlanarPotential_gaussianCurvature
    (dualRadialQuadraticProfile_contDiff R M d).contDiffOn isOpen_Ioo hp hprod,
    dualRadialQuadraticProfile_second_deriv, dualRadialQuadraticProfile_deriv]
  change planarRadius p / (planarWeight p ^ 4 * ((M * R - M * planarRadius p) * -M)) = _
  rw [show (M * R - M * planarRadius p) * -M = -(M ^ 2 * (R - planarRadius p)) by ring]
  simp [mul_neg, div_neg, neg_div]

theorem dualRadialQuadraticPotential_supportMap {R M d : ℝ} {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) :
    planarSupportMap (dualRadialQuadraticPotential R M d) p =
      WithLp.toLp 2 ![(M * R - M * planarRadius p) * p 0 / planarRadius p,
        (M * R - M * planarRadius p) * p 1 / planarRadius p,
        d + M / 2 * planarRadius p ^ 2] := by
  have hm : p ∈ radialPlanarDomain univ := ⟨hp, mem_univ _⟩
  have hpartial (i : Fin 2) :
      coordPartial i (dualRadialQuadraticPotential R M d) p =
        (M * R - M * planarRadius p) * p i / planarRadius p := by
    rw [dualRadialQuadraticPotential, radialPlanarPotential_coordPartial
      (dualRadialQuadraticProfile_contDiff R M d).contDiffOn isOpen_univ hm,
      dualRadialQuadraticProfile_deriv]
  ext i
  fin_cases i
  · simp [planarSupportMap, hpartial]
  · simp [planarSupportMap, hpartial]
  · simp only [planarSupportMap, hpartial]
    change dualRadialQuadraticProfile R M d (planarRadius p) -
      p 0 * ((M * R - M * planarRadius p) * p 0 / planarRadius p) -
      p 1 * ((M * R - M * planarRadius p) * p 1 / planarRadius p) =
        d + M / 2 * planarRadius p ^ 2
    have hr : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hsq := planarRadius_sq p
    dsimp [dualRadialQuadraticProfile]
    field_simp [hr]
    linear_combination 2 * M * (R - planarRadius p) * hsq

end
end TightVer401
