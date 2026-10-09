import TightVer401.PolarSupportGerm

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem polarSupportPotential_contDiffOn (R a C : ℝ) :
    ContDiffOn ℝ ∞ (polarSupportPotential R a C) {p | 0 < p 0 ^ 2 + p 1 ^ 2} :=
  ((contDiffOn_const.mul planarRadius_contDiffOn).sub
    (contDiffOn_const.mul gnomonicWeight_contDiff.contDiffOn)).sub contDiffOn_const

theorem polarSupportPotential_hessian (R a C : ℝ) {p : Coord}
    (hp : 0 < p 0 ^ 2 + p 1 ^ 2) (i j : Fin 2) :
    planarHessian (polarSupportPotential R a C) p i j =
      R * ((if i = j then 1 else 0) / planarRadius p - p i * p j / planarRadius p ^ 3) -
      a * ((if i = j then 1 else 0) / planarWeight p - p i * p j / planarWeight p ^ 3) := by
  have hU : IsOpen {p : Coord | 0 < p 0 ^ 2 + p 1 ^ 2} :=
    isOpen_lt continuous_const (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))
  have hr : DifferentiableAt ℝ planarRadius p :=
    (planarRadius_contDiffOn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hw : DifferentiableAt ℝ planarWeight p := gnomonicWeight_contDiff.differentiable (by simp) p
  have hr0 : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hw0 : planarWeight p ≠ 0 := (planarWeight_pos p).ne'
  have heq : coordPartial j (polarSupportPotential R a C) =ᶠ[𝓝 p]
      (fun q => R * q j / planarRadius q - a * q j / planarWeight q) := by
    filter_upwards [hU.mem_nhds hp] with q hq using polarSupportPotential_coordPartial R a C hq j
  have hproj : DifferentiableAt ℝ (fun q : Coord => q j) p :=
    ((ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).hasFDerivAt (x := p)).differentiableAt
  have hconstR : DifferentiableAt ℝ (fun _ : Coord => R) p := differentiableAt_const R
  have hconsta : DifferentiableAt ℝ (fun _ : Coord => a) p := differentiableAt_const a
  have hRp : DifferentiableAt ℝ (fun q : Coord => R * q j) p := hconstR.mul hproj
  have hap : DifferentiableAt ℝ (fun q : Coord => a * q j) p := hconsta.mul hproj
  have hR : DifferentiableAt ℝ (fun q : Coord => R * q j / planarRadius q) p :=
    by
      convert! hRp.mul (hr.inv hr0) using 1
  have ha : DifferentiableAt ℝ (fun q : Coord => a * q j / planarWeight q) p :=
    by
      convert! hap.mul (hw.inv hw0) using 1
  change fderiv ℝ (coordPartial j (polarSupportPotential R a C)) p (Pi.single i 1) = _
  rw [heq.fderiv_eq]
  change coordPartial i (fun q => R * q j / planarRadius q - a * q j / planarWeight q) p = _
  rw [coordPartial_scalar_sub hR ha]
  rw [coordPartial_scalar_div hRp hr hr0, coordPartial_scalar_div hap hw hw0,
    coordPartial_scalar_mul (differentiableAt_const R) hproj,
    coordPartial_scalar_mul (differentiableAt_const a) hproj,
    coordPartial_scalar_const, coordPartial_scalar_const,
    coordPartial_proj, planarRadius_coordPartial hp, gnomonicWeight_coordPartial]
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp
  all_goals ring

end
end TightVer401
