import TightVer401.PositiveExitConstructionSelectedHomotopy
import TightVer401.PositiveExitConstructionBalancedTurn
import TightVer401.VisibleConnectorOrdinaryFamilyActualChoiceTerminal

/-! Full turn at the SAME already selected rho follows from the retained
entire homotopy domain. No second C0-small displacement is selected. -/
namespace TightVer401
noncomputable section
open Set Function Filter Metric OAI.SmoothLocal.Geometry
open OAI.CircleDomainRigidity OAI.CircleDomainRigidity.FiniteTransfer
open scoped ContDiff Topology

private theorem ordinaryTerminalHomotopy_direction (z : ℂ) :
    AddCircle.toCircle (normalizedArgument z) = complexCircleDirection z := by
  rw [normalizedArgument_eq, AddCircle.toCircle_apply_mk, div_one]
  have he : 2 * Real.pi * (z.arg / (2 * Real.pi)) = z.arg := by field_simp
  rw [he]
  apply Subtype.ext
  simpa only [Circle.coe_exp] using (complexCircleDirection_coe z).symm

/-- A continuous nonzero family on the ENTIRE retained strip transports the
actual baseline turn to its selected endpoint. Only that endpoint needs scalar
smoothness for the real argument-lift reconstruction. -/
theorem visibleConnectorOrdinaryFamilyTerminalHomotopyTurn_selected
    {F : ℝ × ℝ → ℂ} {rho L : ℝ} (hrho : 0 < rho)
    (hF : ContinuousOn F {z : ℝ × ℝ | |z.1| ≤ rho})
    (hPeriod : ∀ r, Periodic (fun s => F (r, s)) L)
    (hAvoid : ∀ r, |r| ≤ rho → ∀ s, F (r, s) ≠ 0)
    (hEndpoint : ContDiff ℝ ∞ (fun s => F (rho, s)))
    (hTurn0 : HasPositiveArgumentTurn (fun s => F (0, s)) L) :
    HasPositiveArgumentTurn (fun s => F (rho, s)) L := by
  have habs (l : unitInterval) : |(l : ℝ) * rho| ≤ rho := by
    rw [abs_mul, abs_of_nonneg l.property.1, abs_of_pos hrho]
    exact mul_le_of_le_one_left hrho.le l.property.2
  have hSlice (l : unitInterval) : Continuous (fun t : unitInterval => F ((l : ℝ) * rho, L * (t : ℝ))) := by
    apply continuousOn_univ.mp
    apply hF.comp (continuous_const.prodMk (continuous_const.mul continuous_subtype_val)).continuousOn
    intro t ht
    exact habs l
  let path (l : unitInterval) : C(unitInterval, ℂ) := ⟨fun t => F ((l : ℝ) * rho, L * (t : ℝ)), hSlice l⟩
  have hpath : Continuous path := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuousOn_univ.mp
    have hm : Continuous (fun z : unitInterval × unitInterval =>
        ((z.1 : ℝ) * rho, L * (z.2 : ℝ))) :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
    exact hF.comp hm.continuousOn (fun z _ => habs z.1)
  let H : C(unitInterval, C(unitInterval, ℂ)) := ⟨path, hpath⟩
  have havoid (l t : unitInterval) : H l t ≠ 0 := hAvoid _ (habs l) _
  have hclosed (l : unitInterval) : H l 1 = H l 0 := by
    change F ((l : ℝ) * rho, L * 1) = F ((l : ℝ) * rho, L * 0)
    simp only [mul_one, mul_zero]
    exact (show F ((l : ℝ) * rho, L) = F ((l : ℝ) * rho, 0) by
      simpa only [zero_add] using hPeriod ((l : ℝ) * rho) 0)
  let avoiding (l : unitInterval) : AvoidingPathPoint :=
    ⟨(path l, 0), by rintro ⟨t, ht⟩; exact havoid l t ht⟩
  let inc : unitInterval → ℝ := pathArgumentIncrement ∘ avoiding
  have hequal : inc (1 : unitInterval) = inc (0 : unitInterval) :=
    positiveExit_actual_loop_homotopy_increment_eq H 0 havoid hclosed 1 0
  have hTurnNormalized : HasPositiveArgumentTurn (fun t => F (0, L * t)) 1 := by
    obtain ⟨phi, hphi, hproj, hinc⟩ := hTurn0
    refine ⟨fun t => phi (L * t), hphi.comp (continuous_const.mul continuous_id),
      (fun t => hproj (L * t)), ?_⟩
    simpa only [mul_one, mul_zero] using hinc
  obtain ⟨v, hv, hproj, hvinc⟩ := positiveExit_positive_turn_unit_lift hTurnNormalized
  let vI : C(unitInterval, ℝ) := ⟨fun t => v t, hv.comp continuous_subtype_val⟩
  have hinc0 : inc (0 : unitInterval) = 1 := by
    simp only [inc, Function.comp_apply, pathArgumentIncrement]
    rw [circlePathIncrement_eq_lift _ vI (fun t => by
      change (v t : UnitAddCircle) = normalizedArgument (F ((0 : ℝ) * rho, L * (t : ℝ)) - 0)
      simpa only [zero_mul, sub_zero] using hproj t)]
    exact hvinc
  have hinc1 : inc (1 : unitInterval) = 1 := hequal.trans hinc0
  have hne (s : ℝ) : F (rho, s) ≠ 0 := hAvoid rho (by rw [abs_of_pos hrho]) s
  let O : Set ℂ := {z | z ≠ 0}
  have hO : IsOpen O := isClosed_singleton.isOpen_compl
  obtain ⟨u, hu, huproj, _⟩ := annularAngularForm_exists_smooth_lift
    (F := id) (y := 0) hO contDiff_id.contDiffOn (fun z hz => hz) hEndpoint hne
  let uI : C(unitInterval, ℝ) :=
    ⟨fun t => u (L * t), hu.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
  have huinc : u L - u 0 = 1 := by
    simp only [inc, Function.comp_apply, pathArgumentIncrement] at hinc1
    rw [circlePathIncrement_eq_lift _ uI (fun t => by
      change (u (L * t) : UnitAddCircle) = normalizedArgument (F ((1 : ℝ) * rho, L * (t : ℝ)) - 0)
      simpa only [one_mul, id_eq, sub_zero] using huproj (L * t))] at hinc1
    change u (L * 1) - u (L * 0) = 1 at hinc1
    simpa only [mul_one, mul_zero] using hinc1
  refine ⟨fun s => 2 * Real.pi * u s, continuous_const.mul hu.continuous, ?_, ?_⟩
  · intro s
    have he := congrArg AddCircle.toCircle (huproj s)
    simp only [id_eq, sub_zero] at he
    rw [ordinaryTerminalHomotopy_direction, AddCircle.toCircle_apply_mk, div_one] at he
    exact he.symm
  · calc
      2 * Real.pi * u L - 2 * Real.pi * u 0 = 2 * Real.pi * (u L - u 0) := by ring
      _ = 2 * Real.pi := by rw [huinc, mul_one]

/-- The strengthened choice retains the ENTIRE actual Gin homotopy domain.
It transports the baseline actual circle turn to the SAME selected terminal
gradient, using no second displacement threshold. -/
theorem visibleConnectorOrdinaryFamilyTerminalHomotopyTurn_of_choice
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax : ℝ} [Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R)
    (C : VisibleConnectorIncomingParametersChoice D etaMax) :
    let gc := fun s => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, s)
    let Y := fun s => -R • visibleConnectorJ (visibleConnectorGinRotatedDirection R C.etaAngle gc s)
    HasPositiveArgumentTurn (positiveExitComplexTrace Y) L := by
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
  obtain ⟨_, _, hgc, _, hVsub, _, hW, _, hgcL, hWL, _, hgc0, hW0⟩ :=
    visibleConnectorGinDisplacedFamily_properties D.radius_pos D.domain_open D.potential_smooth
      D.incoming.p_smooth C.w0_smooth D.incoming.p_periodic C.w0_periodic
      (fun s => D.incoming.p_in_domain (mem_univ s)) hgamma hmargin
      (fun s => congrFun C.w0_actual s)
  let G := visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0
  let W := visibleConnectorGinDisplacedRuling Gin R C.etaAngle D.incoming.p C.w0
  let Omega := visibleConnectorGinDisplacedVisibilityDomain Gin Uin R D.incoming.p C.w0
  let Y : ℝ × ℝ → Coord := fun z => G z + visibleConnectorJ (W z)
  let F : ℝ × ℝ → ℂ := fun z => positiveExitComplexPoint (Y z)
  have hJ : ContDiff ℝ ∞ visibleConnectorJ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun v : Coord => -(v 1))
      exact (contDiff_apply ℝ ℝ (1 : Fin 2)).neg
    · change ContDiff ℝ ∞ (fun v : Coord => v 0)
      exact contDiff_apply ℝ ℝ (0 : Fin 2)
  have hYs : ContDiffOn ℝ ∞ Y Omega := (hgc.mono hVsub).add (hJ.comp_contDiffOn hW)
  have hComplex : positiveExitComplexPoint = angularDescentComplex := by
    funext q
    apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]
  have hFs : ContDiffOn ℝ ∞ F Omega := by
    change ContDiffOn ℝ ∞ (positiveExitComplexPoint ∘ Y) Omega
    rw [hComplex]
    exact angularDescentComplex_contDiff.comp_contDiffOn hYs
  have hIdentity (r s : ℝ) : Y (r, s) = -R • visibleConnectorJ
      (visibleConnectorGinRotatedDirection R C.etaAngle (fun t => G (r, t)) s) := by
    dsimp [Y, W, visibleConnectorGinDisplacedRuling, visibleConnectorGinRotatedRuling,
      visibleConnectorActualRuling]
    ext i
    fin_cases i <;> simp [visibleConnectorJ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have hNorm (r : ℝ) (hr : |r| ≤ C.rho) (s : ℝ) : ‖F (r, s)‖ = R := by
    have hfull (t : ℝ) := C.family_homotopy_domain r hr t
    have hg : ContDiff ℝ ∞ (fun t => G (r, t)) := contDiffOn_univ.mp
      (hgc.comp ((contDiff_const (c := r)).prodMk contDiff_id).contDiffOn
        (fun t _ => hVsub (hfull t)))
    have hw : ContDiff ℝ ∞ (fun t => W (r, t)) := contDiffOn_univ.mp
      (hW.comp ((contDiff_const (c := r)).prodMk contDiff_id).contDiffOn
        (fun t _ => hfull t))
    obtain ⟨_, hunit⟩ := visibleConnectorOrdinaryFamilyActualChoiceTerminal_rotated_direction
      D.radius_pos hg hw rfl (fun t => (hfull t).2)
    have hu := hunit s
    have hsquare : Y (r, s) ⬝ᵥ Y (r, s) = R ^ 2 := by
      rw [hIdentity r s]
      simp only [visibleConnectorJ, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at hu ⊢
      linear_combination (R^2) * hu
    have hn : ‖F (r, s)‖^2 = R^2 := by
      rw [Complex.sq_norm]
      simpa [F, positiveExitComplexPoint, dotProduct, Fin.sum_univ_two,
        Complex.normSq_apply, pow_two] using hsquare
    nlinarith [norm_nonneg (F (r, s)), D.radius_pos]
  have hFcontinuous : ContinuousOn F {z : ℝ × ℝ | |z.1| ≤ C.rho} :=
    hFs.continuousOn.mono (fun z hz => C.family_homotopy_domain z.1 hz z.2)
  have hFperiod (r : ℝ) : Periodic (fun s => F (r, s)) L := by
    intro s
    have hg : G (r, s + L) = G (r, s) := hgcL r s
    have hw : W (r, s + L) = W (r, s) := hWL r s
    change positiveExitComplexPoint (G (r, s + L) + visibleConnectorJ (W (r, s + L))) =
      positiveExitComplexPoint (G (r, s) + visibleConnectorJ (W (r, s)))
    rw [hg, hw]
  have hFavoid (r : ℝ) (hr : |r| ≤ C.rho) (s : ℝ) : F (r, s) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hNorm r hr s]
    exact D.radius_pos.ne'
  have hFendpoint : ContDiff ℝ ∞ (fun s => F (C.rho, s)) := contDiffOn_univ.mp
    (hFs.comp ((contDiff_const (c := C.rho)).prodMk contDiff_id).contDiffOn
      (fun s _ => C.family_domain s))
  let phi := fun s => C.theta s - C.etaAngle - Real.pi / 2
  have hRep0 (s : ℝ) : Y (0, s) = R • visibleConnectorUnitDirection (phi s) := by
    have hg : G (0, s) = D.incoming.gamma s := hgc0 s
    have hw : W (0, s) = C.w0 s := hW0 s
    have hdir : visibleConnectorGinRotatedDirection R C.etaAngle D.incoming.gamma s =
        visibleConnectorUnitDirection (C.theta s - C.etaAngle) := by
      rw [visibleConnectorGinRotatedDirection, C.theta_actual s]
      ext i
      fin_cases i <;> simp [visibleConnectorJ, visibleConnectorUnitDirection,
        Real.cos_sub, Real.sin_sub] <;> ring
    change G (0, s) + visibleConnectorJ (W (0, s)) = _
    rw [hg, hw, C.w0_actual]
    unfold visibleConnectorGinRotatedRuling visibleConnectorActualRuling
    rw [hdir]
    ext i
    fin_cases i <;> simp [visibleConnectorJ, visibleConnectorUnitDirection, phi,
      Real.cos_sub, Real.sin_sub] <;> ring
  have hTurn0 : HasPositiveArgumentTurn (fun s => F (0, s)) L := by
    refine ⟨phi, (C.theta_smooth.continuous.sub continuous_const).sub continuous_const, ?_, ?_⟩
    · intro s
      apply complexCircleDirection_eq_of_exp (hFavoid 0 (by simp [C.rho_pos.le]) s)
      rw [hNorm 0 (by simp [C.rho_pos.le]) s]
      change Complex.exp ((phi s : ℂ) * Complex.I) = R⁻¹ • positiveExitComplexPoint (Y (0, s))
      rw [hRep0 s]
      apply Complex.ext <;> simp [positiveExitComplexPoint, visibleConnectorUnitDirection,
        Complex.real_smul, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      <;> field_simp [D.radius_pos.ne']
    · change C.theta L - C.etaAngle - Real.pi / 2 -
        (C.theta 0 - C.etaAngle - Real.pi / 2) = 2 * Real.pi
      have hs := C.theta_shift 0
      simp only [zero_add] at hs
      linarith
  have hTurn := visibleConnectorOrdinaryFamilyTerminalHomotopyTurn_selected
    C.rho_pos hFcontinuous hFperiod hFavoid hFendpoint hTurn0
  have hTarget : (fun s => F (C.rho, s)) = positiveExitComplexTrace
      (fun s => -R • visibleConnectorJ (visibleConnectorGinRotatedDirection R C.etaAngle
        (fun t => visibleConnectorGinDisplacedGradient Gin D.incoming.p C.w0 (C.rho, t)) s)) := by
    funext s
    change positiveExitComplexPoint (Y (C.rho, s)) = _
    rw [hIdentity C.rho s]
    rfl
  rw [hTarget] at hTurn
  exact hTurn
end
end TightVer401

