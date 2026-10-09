import TightVer401.VisibleConnectorIncomingParametersEta
import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.VisibleConnectorUniformPeriodic

/-! The original eta/ruling/terminal choice is constructed from actual incoming
exit data alone. Angular signs, norm margin and gradient agreement are derived
from D; no chosen angle or terminal geometry is supplied as a desired premise.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem incomingParametersFromData_complex_eq :
    positiveExitComplexPoint = angularDescentComplex := by
  funext q
  apply Complex.ext <;> simp [positiveExitComplexPoint, angularDescentComplex]

/-- Incoming data produce the angular frame, then eta, then the ONE actual
ruling. All central and terminal conclusions refer to that literal ruling. -/
theorem visibleConnectorIncomingParameters_exists_original_choice_from_data
    {Gin : Coord → ℝ} {Uin : Set Coord} {L R etaMax M : ℝ} [hL : Fact (0 < L)]
    (D : VisibleConnectorIncomingData Gin Uin L R) (hetaMax : 0 < etaMax) :
    ∃ theta : ℝ → ℝ,
      ContDiff ℝ ∞ theta ∧
      (∀ s, theta (s + L) = theta s + 2 * Real.pi) ∧
      (∀ s, 0 < deriv theta s) ∧
      (∀ s, visibleConnectorTangentDirection R D.incoming.gamma s =
        visibleConnectorUnitDirection (theta s)) ∧
      ∃ eta > 0, eta < etaMax ∧
        let w0 := visibleConnectorShiftedRuling R D.incoming.gamma theta eta
        let T := visibleConnectorActualTerminalSource D.incoming.p D.incoming.gamma w0
        w0 = visibleConnectorGinRotatedRuling R eta D.incoming.gamma ∧
        ContDiff ℝ ∞ w0 ∧ Periodic w0 L ∧
        (∀ s, 0 < visibleConnectorA D.incoming.p w0 s ∧
          0 < visibleConnectorB D.incoming.gamma w0 s ∧
          0 < visibleConnectorC D.incoming.gamma w0 s) ∧
        (∀ s, D.incoming.gamma s = planarGradient Gin (D.incoming.p s)) ∧
        (∀ s, R < ‖Complex.I * angularDescentComplex (D.incoming.gamma s)‖) ∧
        ContDiff ℝ ∞ T ∧ Periodic T L ∧
        (∀ s, positiveExitComplexTrace T s ≠ 0) ∧
        (∀ s, 0 < visibleConnectorDet (T s) (deriv T s)) ∧
        HasPositiveArgumentTurn (positiveExitComplexTrace T) L ∧ InjOn T (Ico 0 L) ∧
        Schoenflies.IsJordanCurve
          (range (jordanComplexCoordinates.symm ∘ positiveExitComplexTrace T)) ∧
        (∀ s, M < ‖positiveExitComplexPoint (T s)‖) ∧
        (∀ s, 0 < T s ⬝ᵥ (-visibleConnectorJ (visibleConnectorShiftedDirection theta eta s))) ∧
        ∃ H : ℂ ≃ₜ ℂ,
          DualRadialCompletionPositiveTrace H (visibleConnectorTerminalNormalizedTrace L T) ∧
          (0 : ℂ) ∈ H '' Metric.ball (0 : ℂ) 1 ∧
          range (positiveExitComplexTrace T) = frontier (H '' Metric.ball (0 : ℂ) 1) := by
  let p := D.incoming.p
  let gamma := D.incoming.gamma
  have hp : ContDiff ℝ ∞ p := D.incoming.p_smooth
  have hg : ContDiff ℝ ∞ gamma := D.incoming.gamma_smooth
  have hvis : ComplexVisiblePair R (positiveExitComplexTrace p)
      (fun s => Complex.I * positiveExitComplexTrace gamma s) := by
    have h := D.visibility
    rw [D.actual_delta] at h
    exact h
  obtain ⟨theta, kappa, ht, hk, hshift, htpos, hkpos, _, hdir, hdecomp⟩ :=
    visibleConnector_exists_actual_angular_frame D.radius_pos hg
      D.incoming.gamma_periodic D.incoming.gradient_turn hvis
  have hvisAngular : ComplexVisiblePair R (angularDescentComplex ∘ p)
      (fun s => Complex.I * angularDescentComplex (gamma s)) := by
    simpa only [positiveExitComplexTrace, incomingParametersFromData_complex_eq,
      Function.comp_apply] using hvis
  obtain ⟨_, _, hprops⟩ :=
    visibleConnector_tangent_direction_properties D.radius_pos hp hg hvisAngular
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
  obtain ⟨eta, heta, hetaBound, hcoeff, hT, hTperiod, hne, hdet, hturn, hi,
      hjordan, hnorm, H, hpositive, h0, hboundary⟩ :=
    visibleConnectorIncomingParameters_exists_eta_original_margins
      (M := M) D.radius_pos hL.out hetaMax hp hg ht hk
      D.incoming.p_periodic D.incoming.gamma_periodic hshift hdecomp hkpos hpv hgv htpos
  let w0 := visibleConnectorShiftedRuling R gamma theta eta
  let T := visibleConnectorActualTerminalSource p gamma w0
  have he : ContDiff ℝ ∞ (visibleConnectorShiftedDirection theta eta) :=
    visibleConnectorUnitDirection_contDiff.comp (ht.sub contDiff_const)
  have heperiod : Periodic (visibleConnectorShiftedDirection theta eta) L :=
    visibleConnector_shifted_direction_periodic hshift eta
  have hw : ContDiff ℝ ∞ w0 := visibleConnectorActualRuling_contDiff hg he
  have hgammaPeriod : Periodic gamma L := D.incoming.gamma_periodic
  have hwperiod : Periodic w0 L := by
    intro s
    change visibleConnectorJ (gamma (s + L)) - R • visibleConnectorShiftedDirection theta eta (s + L) =
      visibleConnectorJ (gamma s) - R • visibleConnectorShiftedDirection theta eta s
    rw [hgammaPeriod s, heperiod s]
  have hwrotated : w0 = visibleConnectorGinRotatedRuling R eta gamma :=
    (visibleConnectorGinRotatedRuling_eq_shifted hdir).symm
  have hgradient (s : ℝ) : gamma s = planarGradient Gin (p s) :=
    congrFun D.incoming.actual_gradient s
  have hmargin (s : ℝ) : R < ‖Complex.I * angularDescentComplex (gamma s)‖ :=
    (hvisAngular s).1
  refine ⟨theta, ht, hshift, htpos, hdir, eta, heta, hetaBound, hwrotated, hw, hwperiod,
    ?_, hgradient, hmargin, hT, hTperiod, hne, hdet, hturn, hi, hjordan, hnorm, ?_,
    H, hpositive, h0, hboundary⟩
  · intro s
    exact ⟨(hcoeff s).1, (hcoeff s).2.1, (hcoeff s).2.2.1⟩
  · intro s
    exact (hcoeff s).2.2.2

end
end TightVer401

