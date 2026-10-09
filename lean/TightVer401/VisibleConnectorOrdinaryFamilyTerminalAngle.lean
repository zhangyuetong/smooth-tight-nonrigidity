import TightVer401.VisibleConnectorAngularFrame

/-! The terminal angle belongs to the SAME actual radius-R gradient curve.
Its increasing derivative is deduced from the actual angular determinant;
no old undisplaced angle or gradient inverse is substituted. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- A smooth periodic actual radius-R curve with positive angular determinant
and one positive argument turn has its own smooth increasing full-turn angle. -/
theorem visibleConnectorOrdinaryFamilyTerminalAngle_exists
    {Y : ℝ → Coord} {L R : ℝ} (hR : 0 < R)
    (hY : ContDiff ℝ ∞ Y) (hYL : Periodic Y L)
    (hNorm : ∀ s, ‖positiveExitComplexTrace Y s‖ = R)
    (hTurn : HasPositiveArgumentTurn (positiveExitComplexTrace Y) L)
    (hDet : ∀ s, 0 < visibleConnectorDet (Y s) (deriv Y s)) :
    ∃ theta : ℝ → ℝ, ContDiff ℝ ∞ theta ∧
      (∀ s, 0 < deriv theta s) ∧
      (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
      (∀ s, Y s = R • visibleConnectorUnitDirection (theta s)) := by
  have hcomplex : positiveExitComplexPoint = angularDescentComplex := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hc : ContDiff ℝ ∞ (positiveExitComplexTrace Y) := by
    change ContDiff ℝ ∞ (positiveExitComplexPoint ∘ Y)
    rw [hcomplex]
    exact angularDescentComplex_contDiff.comp hY
  have hcp : Periodic (positiveExitComplexTrace Y) L := by
    intro s
    change positiveExitComplexPoint (Y (s + L)) = positiveExitComplexPoint (Y s)
    rw [hYL s]
  have hne (s : ℝ) : positiveExitComplexTrace Y s ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hNorm s]
    exact hR.ne'
  obtain ⟨theta, htheta, hphase, hshift⟩ :=
    positiveExit_actual_positive_argument_lift hc hcp hne hTurn
  have hrep (s : ℝ) : Y s = R • visibleConnectorUnitDirection (theta s) := by
    have he := congrArg Subtype.val (hphase s)
    rw [complexCircleDirection_normalized (hne s), Circle.coe_exp, Complex.exp_mul_I,
      hNorm s] at he
    have hx : R⁻¹ * Y s 0 = Real.cos (theta s) := by
      simpa [positiveExitComplexTrace, positiveExitComplexPoint, Complex.real_smul,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.re he
    have hy : R⁻¹ * Y s 1 = Real.sin (theta s) := by
      simpa [positiveExitComplexTrace, positiveExitComplexPoint, Complex.real_smul,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.im he
    ext i
    fin_cases i
    · change Y s 0 = R * Real.cos (theta s)
      rw [← hx]
      field_simp [hR.ne']
    · change Y s 1 = R * Real.sin (theta s)
      rw [← hy]
      field_simp [hR.ne']
  have hpositive (s : ℝ) : 0 < deriv theta s := by
    have hd := (visibleConnectorUnitDirection_hasDerivAt
      ((htheta.differentiable (by simp) s).hasDerivAt)).const_smul R
    have hd' := hd.congr_of_eventuallyEq (Eventually.of_forall (fun r => hrep r))
    have he : visibleConnectorDet (Y s) (deriv Y s) = R ^ 2 * deriv theta s := by
      rw [hrep s, hd'.deriv]
      simp only [visibleConnectorDet, visibleConnectorJ, visibleConnectorUnitDirection,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (R ^ 2 * deriv theta s) * Real.cos_sq_add_sin_sq (theta s)
    exact pos_of_mul_pos_right (he ▸ hDet s) (sq_nonneg R)
  exact ⟨theta, htheta, hpositive, hshift, hrep⟩

end
end TightVer401
