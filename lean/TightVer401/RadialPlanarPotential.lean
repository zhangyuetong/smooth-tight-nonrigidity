import TightVer401.PolarSupportCurvature

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

def radialPlanarPotential (F : ℝ → ℝ) (p : Coord) : ℝ := F (planarRadius p)
def radialPlanarDomain (U : Set ℝ) : Set Coord :=
  {p | 0 < p 0 ^ 2 + p 1 ^ 2} ∩ planarRadius ⁻¹' U

theorem radialPlanarDomain_isOpen {U : Set ℝ} (hU : IsOpen U) :
    IsOpen (radialPlanarDomain U) := by
  have hr : Continuous planarRadius :=
    (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).sqrt
  exact (isOpen_lt continuous_const
    (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))).inter (hU.preimage hr)

theorem radialPlanarPotential_contDiffOn {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (radialPlanarPotential F) (radialPlanarDomain U) :=
  hF.comp (planarRadius_contDiffOn.mono inter_subset_left) (fun _ hp => hp.2)

theorem radialPlanarPotential_coordPartial {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U) (i : Fin 2) :
    coordPartial i (radialPlanarPotential F) p = deriv F (planarRadius p) * p i / planarRadius p := by
  have hf := (hF.contDiffAt (hU.mem_nhds hp.2)).differentiableAt (by simp)
  have hr : DifferentiableAt ℝ planarRadius p :=
    (planarRadius_contDiffOn.contDiffAt ((isOpen_lt continuous_const
      (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))).mem_nhds hp.1)).differentiableAt (by simp)
  change coordPartial i (fun q => F (planarRadius q)) p = _
  rw [coordPartial_scalar_comp hf.hasDerivAt hr,
    planarRadius_coordPartial hp.1]
  ring

theorem radialPlanarPotential_hessian {F : ℝ → ℝ} {U : Set ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ radialPlanarDomain U) (i j : Fin 2) :
    planarHessian (radialPlanarPotential F) p i j =
      deriv F (planarRadius p) / planarRadius p * (if i = j then 1 else 0) +
      (deriv (deriv F) (planarRadius p) / planarRadius p ^ 2 -
        deriv F (planarRadius p) / planarRadius p ^ 3) * p i * p j := by
  have hV := radialPlanarDomain_isOpen hU
  have hD : ContDiffOn ℝ ∞ (deriv F) U := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hF |>.2
  have hf : DifferentiableAt ℝ (fun q : Coord => deriv F (planarRadius q)) p :=
    ((radialPlanarPotential_contDiffOn hD).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hr : DifferentiableAt ℝ planarRadius p :=
    (planarRadius_contDiffOn.contDiffAt ((isOpen_lt continuous_const
      (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))).mem_nhds hp.1)).differentiableAt (by simp)
  have hproj : DifferentiableAt ℝ (fun q : Coord => q j) p :=
    ((ContinuousLinearMap.proj (R := ℝ) j : Coord →L[ℝ] ℝ).hasFDerivAt (x := p)).differentiableAt
  have hnum : DifferentiableAt ℝ (fun q : Coord => deriv F (planarRadius q) * q j) p := hf.mul hproj
  have hpartialD : coordPartial i (fun q : Coord => deriv F (planarRadius q)) p =
      deriv (deriv F) (planarRadius p) * p i / planarRadius p :=
    radialPlanarPotential_coordPartial hD hU hp i
  have heq : coordPartial j (radialPlanarPotential F) =ᶠ[𝓝 p]
      (fun q => deriv F (planarRadius q) * q j / planarRadius q) := by
    filter_upwards [hV.mem_nhds hp] with q hq using radialPlanarPotential_coordPartial hF hU hq j
  change fderiv ℝ (coordPartial j (radialPlanarPotential F)) p (Pi.single i 1) = _
  rw [heq.fderiv_eq]
  change coordPartial i (fun q => deriv F (planarRadius q) * q j / planarRadius q) p = _
  rw [coordPartial_scalar_div hnum hr (Real.sqrt_pos.mpr hp.1).ne',
    coordPartial_scalar_mul hf hproj, coordPartial_proj,
    hpartialD, planarRadius_coordPartial hp.1]
  have hr0 : planarRadius p ≠ 0 := (Real.sqrt_pos.mpr hp.1).ne'
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp [hr0] <;> ring

end
end TightVer401
