import TightVer401.VisibleConnectorIncomingParametersChoice
import TightVer401.VisibleConnectorOrdinaryFamilyTerminalAngle
import TightVer401.VisibleConnectorOrdinaryFamilyTerminalActualMargins

/-! Differential terminal facts at the already selected displacement. Actual
C positivity and positive excess determine the angular speed of its OWN unit
direction. No additional displacement or old angular lift is selected. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Smoothness and unit length of the actual Gin rotated direction follow
from its SAME smooth gradient/ruling and actual strict visibility norm margin.
No argument lift or angular derivative sign is assumed. -/
theorem visibleConnectorOrdinaryFamilyActualChoiceTerminal_rotated_direction
    {R eta : ℝ} (hR : 0 < R) {gamma w : ℝ → Coord}
    (hgamma : ContDiff ℝ ∞ gamma) (hw : ContDiff ℝ ∞ w)
    (hActual : w = visibleConnectorGinRotatedRuling R eta gamma)
    (hMargin : ∀ s, R < ‖Complex.I * angularDescentComplex (gamma s)‖) :
    ContDiff ℝ ∞ (visibleConnectorGinRotatedDirection R eta gamma) ∧
      ∀ s, visibleConnectorGinRotatedDirection R eta gamma s ⬝ᵥ
        visibleConnectorGinRotatedDirection R eta gamma s = 1 := by
  have hJ : ContDiff ℝ ∞ visibleConnectorJ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun v : Coord => -(v 1))
      exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
    · change ContDiff ℝ ∞ (fun v : Coord => v 0)
      exact contDiff_apply ℝ ℝ (0 : Fin 2)
  have hRepresentation : visibleConnectorGinRotatedDirection R eta gamma =
      fun s => R⁻¹ • (visibleConnectorJ (gamma s) - w s) := by
    funext s
    rw [hActual]
    unfold visibleConnectorGinRotatedRuling visibleConnectorActualRuling
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hR.ne']
    ring
  constructor
  · rw [hRepresentation]
    exact (contDiff_const (c := R⁻¹)).smul ((hJ.comp hgamma).sub hw)
  · intro s
    let z := corrugatedVisibilityDirection R (Complex.I * angularDescentComplex (gamma s))
    have hn : ‖z‖ = 1 := corrugatedVisibilityDirection_norm hR.le (hMargin s)
    have hu : z.re ^ 2 + z.im ^ 2 = 1 := by
      have hh := Complex.sq_norm z
      simpa only [hn, one_pow, Complex.normSq_apply, pow_two, one_mul] using hh.symm
    change (Real.cos eta • ![z.re, z.im] - Real.sin eta • visibleConnectorJ ![z.re, z.im]) ⬝ᵥ
      (Real.cos eta • ![z.re, z.im] - Real.sin eta • visibleConnectorJ ![z.re, z.im]) = 1
    simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ((Real.cos eta)^2 + (Real.sin eta)^2) * hu + Real.cos_sq_add_sin_sq eta
/-- A smooth unit direction has its actual derivative along its quarter turn.
The angular speed is its actual determinant, rather than a supplied witness. -/
theorem visibleConnectorOrdinaryFamilyActualChoiceTerminal_unit_derivative
    {e : ℝ → Coord} (he : ContDiff ℝ ∞ e) (hUnit : ∀ s, e s ⬝ᵥ e s = 1)
    (s : ℝ) :
    deriv e s = visibleConnectorDet (e s) (deriv e s) • visibleConnectorJ (e s) := by
  have hd := (he.differentiable (by simp) s).hasDerivAt
  have hd0 : HasDerivAt (fun t => e t 0) (deriv e s 0) s := by
    exact (hasDerivAt_pi.mp hd) 0
  have hd1 : HasDerivAt (fun t => e t 1) (deriv e s 1) s := by
    exact (hasDerivAt_pi.mp hd) 1
  have hNormDeriv := (hd0.mul hd0).add (hd1.mul hd1)
  have hIdentity : (((fun t => e t 0) * (fun t => e t 0)) +
      ((fun t => e t 1) * (fun t => e t 1))) = fun _ => (1 : ℝ) := by
    funext t
    simpa only [Pi.add_apply, Pi.mul_apply, dotProduct, Fin.sum_univ_two] using hUnit t
  have hDerivative := hNormDeriv.deriv
  rw [hIdentity, deriv_const] at hDerivative
  have hOrthogonal : e s 0 * deriv e s 0 + e s 1 * deriv e s 1 = 0 := by
    nlinarith
  have hUnit' : (e s 0)^2 + (e s 1)^2 = 1 := by
    simpa only [dotProduct, Fin.sum_univ_two, pow_two] using hUnit s
  ext i
  fin_cases i
  · change deriv e s 0 =
      (e s 0 * deriv e s 1 - e s 1 * deriv e s 0) * (-e s 1)
    linear_combination -(deriv e s 0) * hUnit' + (e s 0) * hOrthogonal
  · change deriv e s 1 =
      (e s 0 * deriv e s 1 - e s 1 * deriv e s 0) * e s 0
    linear_combination -(deriv e s 1) * hUnit' + (e s 1) * hOrthogonal

/-- At one selected actual ruling, positive C and positive excess imply the
OWN angular speed is positive. Retained radial and directional inequalities
then imply actual terminal radial, tangent and angular positivity. -/
theorem visibleConnectorOrdinaryFamilyActualChoiceTerminal_selected_signs
    {R : ℝ} (hR : 0 < R) {p gamma e : ℝ → Coord}
    (hgamma : ContDiff ℝ ∞ gamma) (he : ContDiff ℝ ∞ e)
    (hUnit : ∀ s, e s ⬝ᵥ e s = 1)
    (hA : ∀ s, 0 < visibleConnectorA p (visibleConnectorActualRuling R gamma e) s)
    (hB : ∀ s, 0 < visibleConnectorB gamma (visibleConnectorActualRuling R gamma e) s)
    (hC : ∀ s, 0 < visibleConnectorC gamma (visibleConnectorActualRuling R gamma e) s)
    (hExcess : ∀ s, 0 < visibleConnectorJ (gamma s) ⬝ᵥ e s - R)
    (hRadial : ∀ s, 0 < visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e) s ⬝ᵥ (-visibleConnectorJ (e s)))
    (hDirectional : ∀ s, 0 < deriv (visibleConnectorActualTerminalSource p gamma
      (visibleConnectorActualRuling R gamma e)) s ⬝ᵥ e s) :
    let Y := fun s => -R • visibleConnectorJ (e s)
    let T := visibleConnectorActualTerminalSource p gamma (visibleConnectorActualRuling R gamma e)
    ContDiff ℝ ∞ Y ∧
      (∀ s, visibleConnectorGradient p gamma (visibleConnectorActualRuling R gamma e)
        ![s, visibleConnectorActualTerminalHeight p gamma (visibleConnectorActualRuling R gamma e) s] = Y s) ∧
      (∀ s, ‖positiveExitComplexTrace Y s‖ = R) ∧
      (∀ s, 0 < visibleConnectorDet (e s) (deriv e s)) ∧
      (∀ s, deriv Y s = (R * visibleConnectorDet (e s) (deriv e s)) • e s) ∧
      (∀ s, 0 < T s ⬝ᵥ Y s ∧ 0 < deriv T s ⬝ᵥ deriv Y s ∧
        0 < visibleConnectorDet (Y s) (deriv Y s)) := by
  let beta := fun s => visibleConnectorDet (e s) (deriv e s)
  let Y := fun s => -R • visibleConnectorJ (e s)
  have hJ : ContDiff ℝ ∞ visibleConnectorJ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun v : Coord => -(v 1))
      exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
    · change ContDiff ℝ ∞ (fun v : Coord => v 0)
      exact contDiff_apply ℝ ℝ (0 : Fin 2)
  have hY : ContDiff ℝ ∞ Y := (contDiff_const (c := -R)).smul (hJ.comp he)
  have hde (s : ℝ) : HasDerivAt e (beta s • visibleConnectorJ (e s)) s := by
    have hd := (he.differentiable (by simp) s).hasDerivAt
    rw [visibleConnectorOrdinaryFamilyActualChoiceTerminal_unit_derivative he hUnit s] at hd
    exact hd
  have hBeta (s : ℝ) : 0 < beta s := by
    have hf := visibleConnector_actual_ruling_C_formula (R := R) hgamma (hde s) (hUnit s)
    have hc := hC s
    rw [hf] at hc
    have hprod : 0 < R * beta s := pos_of_mul_pos_left hc (hExcess s).le
    exact pos_of_mul_pos_right hprod hR.le
  have hDY (s : ℝ) : deriv Y s = (R * beta s) • e s := by
    have hd := (visibleConnectorJ_hasDerivAt (hde s)).const_smul (-R)
    change HasDerivAt Y _ s at hd
    rw [hd.deriv]
    ext i
    fin_cases i <;> simp [visibleConnectorJ, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hJet (s : ℝ) := visibleConnector_actual_ruling_circle_terminal hR
    (p := p) (gamma := gamma) (e := e) (hUnit s) (hA s) (hB s) (hC s)
  refine ⟨hY, (fun s => (hJet s).2.2.1), ?_, hBeta, hDY, ?_⟩
  · intro s
    have hsq := (hJet s).2.2.2
    rw [(hJet s).2.2.1] at hsq
    have hn : ‖positiveExitComplexTrace Y s‖ ^ 2 = R ^ 2 := by
      rw [Complex.sq_norm]
      simpa [Y, positiveExitComplexTrace, positiveExitComplexPoint, visibleConnectorJ,
        dotProduct, Fin.sum_univ_two, Complex.normSq_apply, pow_two] using hsq
    nlinarith [norm_nonneg (positiveExitComplexTrace Y s)]
  · intro s
    constructor
    · have heq : Y s = R • (-visibleConnectorJ (e s)) := by
        ext i
        simp [Y]
      change 0 < visibleConnectorActualTerminalSource p gamma (visibleConnectorActualRuling R gamma e) s ⬝ᵥ Y s
      rw [heq, dotProduct_smul]
      exact mul_pos hR (hRadial s)
    constructor
    · change 0 < deriv (visibleConnectorActualTerminalSource p gamma (visibleConnectorActualRuling R gamma e)) s ⬝ᵥ deriv Y s
      rw [hDY s, dotProduct_smul]
      exact mul_pos (mul_pos hR (hBeta s)) (hDirectional s)
    · change 0 < visibleConnectorDet (Y s) (deriv Y s)
      rw [hDY s]
      have hu := hUnit s
      simp only [dotProduct, Fin.sum_univ_two] at hu
      have hdet : visibleConnectorDet (Y s) ((R * beta s) • e s) = R^2 * beta s := by
        simp only [Y, visibleConnectorDet, visibleConnectorJ, Pi.smul_apply, smul_eq_mul,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination (R^2 * beta s) * hu
      rw [hdet]
      exact mul_pos (sq_pos_of_pos hR) (hBeta s)

/-- Apply the differential producer to the already selected SAME Gin family.
All displaced radial/directional/excess facts are retained from C; there is
no replacement rho or undisplaced angular parametrization in this result. -/
theorem visibleConnectorOrdinaryFamilyActualChoiceTerminal_of_choice
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (C : VisibleConnectorIncomingParametersChoice D etaMax) :
    let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
    let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
    let direction := visibleConnectorGinRotatedDirection R C.etaAngle gc
    let Y := fun s => -R • visibleConnectorJ (direction s)
    let T := visibleConnectorActualTerminalSource pc gc wc
    ContDiff ℝ ∞ direction ∧ ContDiff ℝ ∞ Y ∧
      (∀ s, visibleConnectorGradient pc gc wc ![s, visibleConnectorActualTerminalHeight pc gc wc s] = Y s) ∧
      (∀ s, ‖positiveExitComplexTrace Y s‖ = R) ∧
      (∀ s, 0 < T s ⬝ᵥ Y s ∧ 0 < deriv T s ⬝ᵥ deriv Y s ∧
        0 < visibleConnectorDet (Y s) (deriv Y s)) := by
  let pc := fun s => visibleConnectorGinDisplacedPosition D.incoming.p C.w0 (C.rho, s)
  let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
  let wc := fun s => visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0 (C.rho, s)
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖ := by
    have h := (D.visibility s).1
    rw [D.actual_delta] at h
    change R < ‖Complex.I * positiveExitComplexPoint (D.incoming.gamma s)‖ at h
    have heq : positiveExitComplexPoint = angularDescentComplex := by
      funext q
      apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
    simpa only [heq] using h
  have hgamma (s : ℝ) : D.incoming.gamma s = planarGradient Gin (D.incoming.p s) := by
    rw [D.incoming.actual_gradient]
    rfl
  obtain ⟨_, _, hgc, _, hVsub, _, hW, _, _, _, _, _, _⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open D.potential_smooth
      D.incoming.p_smooth C.w0_smooth D.incoming.p_periodic C.w0_periodic
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma hmargin
      (fun s => congrFun C.w0_actual s)
  have hgcs : ContDiff ℝ ∞ gc := contDiffOn_univ.mp
    (hgc.comp ((contDiff_const (c := C.rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => hVsub (C.family_domain s)))
  have hwcs : ContDiff ℝ ∞ wc := contDiffOn_univ.mp
    (hW.comp ((contDiff_const (c := C.rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => C.family_domain s))
  have hwActual : wc = visibleConnectorGinRotatedRuling R C.etaAngle gc := rfl
  have hMarginC (s : ℝ) : R < ‖Complex.I * angularDescentComplex (gc s)‖ :=
    (C.family_domain s).2
  obtain ⟨he, hUnit⟩ := visibleConnectorOrdinaryFamilyActualChoiceTerminal_rotated_direction
    D.radius_pos hgcs hwcs hwActual hMarginC
  have hcoeff : ∀ s, 0 < visibleConnectorA pc wc s ∧
      0 < visibleConnectorB gc wc s ∧ 0 < visibleConnectorC gc wc s := C.coefficients_positive
  obtain ⟨hY, hJet, hNorm, _, _, hSigns⟩ :=
    visibleConnectorOrdinaryFamilyActualChoiceTerminal_selected_signs D.radius_pos hgcs he hUnit
      (fun s => (hcoeff s).1) (fun s => (hcoeff s).2.1) (fun s => (hcoeff s).2.2)
      C.terminal_excess C.terminal_radial C.terminal_directional
  exact ⟨he, hY, hJet, hNorm, hSigns⟩
end
end TightVer401




