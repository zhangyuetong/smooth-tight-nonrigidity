import TightVer401.QuadraticFillerCartesianConstruction

/-! Actual mixed polar derivatives and exact Cartesian boundary Hessian determinant. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual mixed polar derivative, obtained from the proved angular first derivative. -/
theorem dualQuadraticFiller_radial_angular (R M : ℝ) {chi h b : ℝ → ℝ}
    (hchi : ContDiff ℝ ∞ chi) (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (p : Coord) :
    planarHessian (dualQuadraticFiller R M chi h b) p 0 1 =
      deriv chi (p 0) * (deriv h (p 1) + (p 0 - R) * deriv b (p 1)) +
        chi (p 0) * deriv b (p 1) := by
  have heq : coordPartial 1 (dualQuadraticFiller R M chi h b) = _ :=
    funext (fun q => dualQuadraticFiller_coordPartial R M hchi hh hb q 1)
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at heq
  change coordPartial 0 (coordPartial 1 (dualQuadraticFiller R M chi h b)) p = _
  rw [heq]
  have hr := (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).hasFDerivAt (x := p)
  have ht := (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)).hasFDerivAt (x := p)
  have hc := (hchi.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p hr
  have hd := ((contDiff_infty_iff_deriv.mp hh).2.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have he := ((contDiff_infty_iff_deriv.mp hb).2.differentiable (by simp)).differentiableAt.hasDerivAt.hasFDerivAt.comp p ht
  have hf := hc.mul (hd.add ((hr.sub_const R).mul he))
  change HasFDerivAt (fun q : Coord => chi (q 0) *
    (deriv h (q 1) + (q 0 - R) * deriv b (q 1))) _ p at hf
  change fderiv ℝ _ p (Pi.single 0 1) = _
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply]
  ring

/-- Actual boundary polar Hessian entries on the cutoff plateau. -/
theorem dualQuadraticFiller_boundary_polar_hessian {R : ℝ} (hR : 0 < R) (M : ℝ)
    {chi h b : ℝ → ℝ} (hchi : ContDiff ℝ ∞ chi)
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hchi1 : ∀ r, 3 * R / 4 ≤ r → chi r = 1) (theta : ℝ) :
    planarHessian (dualQuadraticFiller R M chi h b) ![R, theta] 0 0 = -M ∧
      planarHessian (dualQuadraticFiller R M chi h b) ![R, theta] 1 1 =
        deriv (deriv h) theta ∧
      planarHessian (dualQuadraticFiller R M chi h b) ![R, theta] 0 1 = deriv b theta := by
  have hc : chi R = 1 := hchi1 R (by linarith)
  obtain ⟨hc1, hc2⟩ := quadraticDomination_plateau_derivatives
    (fun r hr => hchi1 r hr.le) (by linarith : 3 * R / 4 < R)
  refine ⟨?_, ?_, ?_⟩
  · change coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M chi h b)) ![R, theta] = _
    rw [dualQuadraticFiller_radial_second R M hchi hh hb]
    simp [hc1, hc2]
  · change coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M chi h b)) ![R, theta] = _
    rw [dualQuadraticFiller_angular_second R M hchi hh hb]
    simp [hc]
  · rw [dualQuadraticFiller_radial_angular R M hchi hh hb]
    simp [hc, hc1]

/-- Exact actual Cartesian Hessian determinant at the outer circular seam. -/
theorem quadraticFillerCartesianPotential_boundary_hessian_det {R : ℝ} (hR : 0 < R)
    (M : ℝ) {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (theta : ℝ) :
    (planarHessian (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![R, theta])).det =
      (-M * (deriv (deriv h) theta + R * b theta) -
        (deriv b theta - deriv h theta / R) ^ 2) / R ^ 2 := by
  have hcutoff := quadraticDominationCutoff_properties hR
  have hperiod : ∀ r t : ℝ,
      dualQuadraticFiller R M (quadraticDominationCutoff R) h b ![r, t + 2 * Real.pi] =
        dualQuadraticFiller R M (quadraticDominationCutoff R) h b ![r, t] :=
    fun r t => dualQuadraticFiller_angular_periodic R M (2 * Real.pi) hhper hbper r t
  have hq : 0 < (![R, theta] : Coord) 0 := by simpa using hR
  obtain ⟨hrr, htt, hrt⟩ := dualQuadraticFiller_boundary_polar_hessian
    hR M hcutoff.1 hh hb hcutoff.2.2.1 theta
  obtain ⟨_, hr, ht⟩ := dualQuadraticFiller_boundary_first_jet
    hR M hcutoff.1 hh hb hcutoff.2.2.1 theta
  change (planarHessian
    (angularDescentPotential (dualQuadraticFiller R M (quadraticDominationCutoff R) h b))
    (saddlePolarChart ![R, theta])).det = _
  rw [angularDescentPotential_hessian_det
    (dualQuadraticFiller_contDiff R M hcutoff.1 hh hb) hperiod hq, hrr, htt, hrt, hr, ht]
  simp only [Matrix.cons_val_zero]

/-- A lower trace bound yields a quantitative actual Cartesian determinant bound. -/
theorem quadraticFillerCartesianPotential_boundary_hessian_det_bound {R M tau : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) {h b : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi)) (theta : ℝ)
    (htau : tau ≤ deriv (deriv h) theta + R * b theta) :
    (planarHessian (quadraticFillerCartesianPotential R M h b)
      (saddlePolarChart ![R, theta])).det ≤ -M * tau / R ^ 2 := by
  rw [quadraticFillerCartesianPotential_boundary_hessian_det hR M hh hb hhper hbper]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).mpr
  nlinarith [mul_nonneg hM (sub_nonneg.mpr htau),
    sq_nonneg (deriv b theta - deriv h theta / R)]

/-- A single positive trace margin controls every nonnegative coefficient and every angle. -/
theorem quadraticFillerCartesianPotential_boundary_uniform_hessian_margin {R : ℝ}
    (hR : 0 < R) {h b : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hb : ContDiff ℝ ∞ b)
    (hhper : Function.Periodic h (2 * Real.pi))
    (hbper : Function.Periodic b (2 * Real.pi))
    (htrace : ∀ theta, 0 < deriv (deriv h) theta + R * b theta) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ M : ℝ, 0 ≤ M → ∀ theta : ℝ,
      (planarHessian (quadraticFillerCartesianPotential R M h b)
        (saddlePolarChart ![R, theta])).det ≤ -M * tau / R ^ 2 := by
  obtain ⟨tau, htau, hbound⟩ := quadraticDomination_trace_margin hh hb hhper hbper htrace
  exact ⟨tau, htau, fun M hM theta =>
    quadraticFillerCartesianPotential_boundary_hessian_det_bound hR hM hh hb hhper hbper
      theta (hbound theta)⟩

end
end TightVer401
