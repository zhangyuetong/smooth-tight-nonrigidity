import TightVer401.VisibleConnectorUniformAngle
import TightVer401.VisibleConnectorAngularFrame
import TightVer401.VisibleConnectorTerminalCircle

/-! A single actual rotation works on every real period representative.
The frame, signs, terminal height and circular terminal gradient are all
constructed from the same visible periodic exit. No global annular inverse
or completed connector is an input or a conclusion of this leaf. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private theorem connectorPeriodic_complex_eq : positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

private theorem connectorPeriodic_coord_deriv {f : ℝ → Coord} {L : ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have htrans : HasDerivAt (fun r => f (r + L)) (deriv f (s + L)) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      ((hf.differentiable (by simp) (s + L)).hasDerivAt).scomp s
        ((hasDerivAt_id s).add_const L)
  have he := htrans.congr_of_eventuallyEq
    (f₁ := f) (Eventually.of_forall (fun r => (hp r).symm))
  exact he.deriv.symm

/-- The full angle shift gives an actual periodic unit direction at every
fixed rotation. This uses the existing shared unit direction definition. -/
theorem visibleConnector_shifted_direction_periodic {theta : ℝ → ℝ} {L : ℝ}
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi) (eta : ℝ) :
    Periodic (visibleConnectorShiftedDirection theta eta) L := by
  intro s
  change visibleConnectorUnitDirection (theta (s + L) - eta) =
    visibleConnectorUnitDirection (theta s - eta)
  rw [hshift s, show theta s + 2 * Real.pi - eta =
    (theta s - eta) + 2 * Real.pi by ring]
  ext i
  fin_cases i <;> simp [visibleConnectorUnitDirection]

private theorem connectorPeriodic_angle_deriv {theta : ℝ → ℝ} {L : ℝ}
    (ht : ContDiff ℝ ∞ theta)
    (hshift : ∀ s, theta (s + L) = theta s + 2 * Real.pi) :
    Periodic (deriv theta) L := by
  intro s
  have hleft : HasDerivAt (fun r => theta (r + L)) (deriv theta (s + L)) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((ht.differentiable (by simp) (s + L)).hasDerivAt).comp s
        ((hasDerivAt_id s).add_const L)
  have he := hleft.congr_of_eventuallyEq
    (f₁ := fun r => theta r + 2 * Real.pi)
    (Eventually.of_forall (fun r => (hshift r).symm))
  exact he.unique (((ht.differentiable (by simp) s).hasDerivAt).add_const _)

/-- Ordinary actual exit data produce one small positive angle, the actual
smooth periodic ruling and terminal height, positive A/B/C everywhere, and
the actual circle terminal formula and closed-segment Jacobian positivity. -/
theorem visibleConnector_exists_uniform_periodic_actual_ruling
    {R L etaMax : ℝ} (hR : 0 < R) (hL : 0 < L) (hetaMax : 0 < etaMax)
    {p gamma : ℝ → Coord} (hp : ContDiff ℝ ∞ p) (hgamma : ContDiff ℝ ∞ gamma)
    (hpperiod : Periodic p L) (hgperiod : Periodic gamma L)
    (hturn : HasPositiveArgumentTurn (positiveExitComplexTrace gamma) L)
    (hvisible : ComplexVisiblePair R (positiveExitComplexTrace p)
      (fun s => Complex.I * positiveExitComplexTrace gamma s)) :
    ∃ theta : ℝ → ℝ, ContDiff ℝ ∞ theta ∧
      (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
      Periodic (deriv theta) L ∧ (∀ s, 0 < deriv theta s) ∧
      ∃ eta > 0, eta < etaMax ∧
        let e := visibleConnectorShiftedDirection theta eta
        let w := visibleConnectorShiftedRuling R gamma theta eta
        let t := visibleConnectorActualTerminalHeight p gamma w
        ContDiff ℝ ∞ e ∧ Periodic e L ∧ (∀ s, e s ⬝ᵥ e s = 1) ∧
        ContDiff ℝ ∞ w ∧ Periodic w L ∧ ContDiff ℝ ∞ t ∧ Periodic t L ∧
        ∀ s, 0 < visibleConnectorA p w s ∧
          0 < visibleConnectorB gamma w s ∧ 0 < visibleConnectorC gamma w s ∧
          0 < t s ∧ (∀ u ∈ Icc (0 : ℝ) (t s), 0 < visibleConnectorDelta p gamma w ![s, u]) ∧
          visibleConnectorGradient p gamma w ![s, t s] = -R • visibleConnectorJ (e s) ∧
          visibleConnectorGradient p gamma w ![s, t s] ⬝ᵥ
            visibleConnectorGradient p gamma w ![s, t s] = R ^ 2 := by
  obtain ⟨theta, kappa, ht, hk, hshift, htpos, hkpos, _, hdir, hdecomp⟩ :=
    visibleConnector_exists_actual_angular_frame hR hgamma hgperiod hturn hvisible
  have hvis : ComplexVisiblePair R (angularDescentComplex ∘ p)
      (fun s => Complex.I * angularDescentComplex (gamma s)) := by
    simpa only [positiveExitComplexTrace, connectorPeriodic_complex_eq, Function.comp_apply] using hvisible
  obtain ⟨_, _, hprops⟩ := visibleConnector_tangent_direction_properties hR hp hgamma hvis
  have hpv (s : ℝ) : 0 < deriv p s ⬝ᵥ visibleConnectorUnitDirection (theta s) := by
    have hh := (hprops s).2.2.2.1
    convert hh using 1 <;>
      simp [visibleConnectorA, visibleConnectorDet, visibleConnectorTangentTransverse,
        hdir s, visibleConnectorJ, dotProduct, Fin.sum_univ_two] <;> ring
  have hgv (s : ℝ) : 0 < visibleConnectorJ (deriv gamma s) ⬝ᵥ
      visibleConnectorUnitDirection (theta s) := by
    have hh := (hprops s).2.2.2.2
    convert hh using 1 <;>
      simp [visibleConnectorB, visibleConnectorTangentTransverse, hdir s,
        visibleConnectorJ, dotProduct, Fin.sum_univ_two] <;> ring
  obtain ⟨eps, heps, hcoeff⟩ := visibleConnector_uniform_positive_actual_coefficients
    hR hp hgamma ht hk (K := Icc (0 : ℝ) L) isCompact_Icc hdecomp
    (fun s _ => hkpos s) (fun s _ => hpv s) (fun s _ => hgv s) (fun s _ => htpos s)
  let eta := min eps etaMax / 2
  have heta : 0 < eta := half_pos (lt_min heps hetaMax)
  have hetaEps : eta < eps := (half_lt_self (lt_min heps hetaMax)).trans_le (min_le_left _ _)
  have hetaBound : eta < etaMax :=
    (half_lt_self (lt_min heps hetaMax)).trans_le (min_le_right _ _)
  let e := visibleConnectorShiftedDirection theta eta
  let w := visibleConnectorShiftedRuling R gamma theta eta
  let t := visibleConnectorActualTerminalHeight p gamma w
  have he : ContDiff ℝ ∞ e :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have heperiod : Periodic e L := visibleConnector_shifted_direction_periodic hshift eta
  have heunit (s : ℝ) : e s ⬝ᵥ e s = 1 := by
    simpa [e, visibleConnectorShiftedDirection, visibleConnectorUnitDirection,
      dotProduct, Fin.sum_univ_two, pow_two] using Real.cos_sq_add_sin_sq (theta s - eta)
  have hw : ContDiff ℝ ∞ w := visibleConnectorActualRuling_contDiff hgamma he
  have hwperiod : Periodic w L := by
    intro s
    change visibleConnectorJ (gamma (s + L)) - R • e (s + L) =
      visibleConnectorJ (gamma s) - R • e s
    rw [hgperiod s, heperiod s]
  have hdp := connectorPeriodic_coord_deriv hp hpperiod
  have hdg := connectorPeriodic_coord_deriv hgamma hgperiod
  have hdw := connectorPeriodic_coord_deriv hw hwperiod
  have hAperiod : Periodic (visibleConnectorA p w) L := by
    intro s
    unfold visibleConnectorA
    rw [hdp s, hwperiod s]
  have hBperiod : Periodic (visibleConnectorB gamma w) L := by
    intro s
    unfold visibleConnectorB
    rw [hdg s, hwperiod s]
  have hCperiod : Periodic (visibleConnectorC gamma w) L := by
    intro s
    unfold visibleConnectorC
    rw [hBperiod s, hdw s, hwperiod s]
  have hsigns (s : ℝ) : 0 < visibleConnectorA p w s ∧
      0 < visibleConnectorB gamma w s ∧ 0 < visibleConnectorC gamma w s := by
    obtain ⟨n, hn, _⟩ := existsUnique_sub_zsmul_mem_Ico hL s 0
    simp only [mem_Ico, zero_add] at hn
    have hh := (hcoeff eta heta hetaEps (s - n • L) ⟨hn.1, hn.2.le⟩).2
    change 0 < visibleConnectorA p w (s - n • L) ∧
      0 < visibleConnectorB gamma w (s - n • L) ∧
      0 < visibleConnectorC gamma w (s - n • L) at hh
    rw [hAperiod.sub_zsmul_eq n, hBperiod.sub_zsmul_eq n, hCperiod.sub_zsmul_eq n] at hh
    exact hh
  have hterminal : ContDiff ℝ ∞ t :=
    visibleConnectorActualTerminalHeight_contDiff hp hgamma hw
      (fun s => (hsigns s).2.2.ne')
  have htperiod : Periodic t L := by
    intro s
    change visibleConnectorA p w (s + L) / visibleConnectorC gamma w (s + L) =
      visibleConnectorA p w s / visibleConnectorC gamma w s
    rw [hAperiod s, hCperiod s]
  refine ⟨theta, ht, hshift, connectorPeriodic_angle_deriv ht hshift, htpos,
    eta, heta, hetaBound, he, heperiod, heunit, hw, hwperiod, hterminal, htperiod, ?_⟩
  intro s
  obtain ⟨hA, hB, hC⟩ := hsigns s
  refine ⟨hA, hB, hC, ?_⟩
  exact visibleConnector_actual_ruling_circle_terminal hR (heunit s) hA hB hC

end
end TightVer401