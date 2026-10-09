import TightVer401.VisibleConnectorIncomingParametersCoefficients
import TightVer401.VisibleConnectorTerminalPairing

/-! Actual joint terminal C1 producer from the SAME smooth P/G/W family.
Its literal terminal quotient is smooth on the open nonzero-C domain; actual
longitudinal derivatives are then identified with the joint differential.
No terminal C1 convergence, terminal smoothness or derivative continuity is
assumed. Restricting to C nonzero is a genuine ordinary coefficient bound. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem incomingTerminalQuotient_coordinate_smooth
    {F : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hF : ContDiffOn ℝ ∞ F Omega) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun z => F z i) Omega :=
  (contDiff_apply ℝ ℝ i).contDiffOn.comp hF (fun _ _ => mem_univ _)

/-- Smooth source families produce smooth actual longitudinal derivatives. -/
theorem visibleConnectorIncomingTerminal_familyPhaseDerivative_contDiffOn
    {F : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hF : ContDiffOn ℝ ∞ F Omega) :
    ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyPhaseDerivative F) Omega :=
  (hF.fderiv_of_isOpen hOmega (by simp)).clm_apply contDiffOn_const

/-- The joint A and C used by the terminal are constructed smooth functions,
not assumed terminal coefficients or terminal regularity statements. -/
theorem visibleConnectorIncomingTerminal_familyAC_contDiffOn
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega) :
    ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyA P W) Omega ∧
      ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyC G W) Omega := by
  have hDP := visibleConnectorIncomingTerminal_familyPhaseDerivative_contDiffOn hOmega hP
  have hDG := visibleConnectorIncomingTerminal_familyPhaseDerivative_contDiffOn hOmega hG
  have hDW := visibleConnectorIncomingTerminal_familyPhaseDerivative_contDiffOn hOmega hW
  have hA : ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyA P W) Omega :=
    (((incomingTerminalQuotient_coordinate_smooth hDP 0).mul
      (incomingTerminalQuotient_coordinate_smooth hW 1)).sub
        ((incomingTerminalQuotient_coordinate_smooth hDP 1).mul
          (incomingTerminalQuotient_coordinate_smooth hW 0))).neg
  have hB : ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyB G W) Omega := by
    have he : visibleConnectorIncomingParametersFamilyB G W =
        (fun z => visibleConnectorIncomingParametersFamilyPhaseDerivative G z 0 * W z 0 +
          visibleConnectorIncomingParametersFamilyPhaseDerivative G z 1 * W z 1) := by
      funext z
      simp [visibleConnectorIncomingParametersFamilyB, dotProduct, Fin.sum_univ_two]
    rw [he]
    exact ((incomingTerminalQuotient_coordinate_smooth hDG 0).mul
      (incomingTerminalQuotient_coordinate_smooth hW 0)).add
        ((incomingTerminalQuotient_coordinate_smooth hDG 1).mul
          (incomingTerminalQuotient_coordinate_smooth hW 1))
  have hC : ContDiffOn ℝ ∞ (visibleConnectorIncomingParametersFamilyC G W) Omega :=
    hB.add (((incomingTerminalQuotient_coordinate_smooth hDW 0).mul
      (incomingTerminalQuotient_coordinate_smooth hW 1)).sub
        ((incomingTerminalQuotient_coordinate_smooth hDW 1).mul
          (incomingTerminalQuotient_coordinate_smooth hW 0)))
  exact ⟨hA, hC⟩

def visibleConnectorIncomingTerminalActualFamily (P G W : ℝ × ℝ → Coord)
    (z : ℝ × ℝ) : Coord :=
  visibleConnectorActualTerminalSource (fun s => P (z.1, s))
    (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2

/-- Actual terminal smoothness follows from its literal quotient, on any
open SAME family domain where the actual C coefficient is nonzero. -/
theorem visibleConnectorIncomingTerminal_actualFamily_contDiffOn
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    (hC : ∀ z ∈ Omega, visibleConnectorC
      (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 ≠ 0) :
    ContDiffOn ℝ ∞ (visibleConnectorIncomingTerminalActualFamily P G W) Omega := by
  obtain ⟨hA, hCjoint⟩ := visibleConnectorIncomingTerminal_familyAC_contDiffOn hOmega hP hG hW
  have hCne : ∀ z ∈ Omega, visibleConnectorIncomingParametersFamilyC G W z ≠ 0 := by
    intro z hz
    rw [(visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).2.2]
    exact hC z hz
  have hModel : ContDiffOn ℝ ∞ (fun z => P z +
      (visibleConnectorIncomingParametersFamilyA P W z /
        visibleConnectorIncomingParametersFamilyC G W z) • W z) Omega :=
    hP.add ((hA.div hCjoint hCne).smul hW)
  apply hModel.congr
  intro z hz
  dsimp [visibleConnectorIncomingTerminalActualFamily,
    visibleConnectorActualTerminalSource, visibleConnectorActualTerminalHeight]
  rw [(visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).1,
    (visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).2.2]

/-- The actual fixed-rho terminal derivative is jointly continuous. This is
precisely the C1 input needed by the compact displacement margin producer. -/
theorem visibleConnectorIncomingTerminal_actualFamily_C1
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    (hC : ∀ z ∈ Omega, visibleConnectorC
      (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 ≠ 0) :
    ContinuousOn (visibleConnectorIncomingTerminalActualFamily P G W) Omega ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv
        (fun s => visibleConnectorIncomingTerminalActualFamily P G W (z.1, s)) z.2) Omega := by
  have hT := visibleConnectorIncomingTerminal_actualFamily_contDiffOn hOmega hP hG hW hC
  refine ⟨hT.continuousOn, ?_⟩
  exact (visibleConnectorIncomingParametersFamilyPhaseDerivative_continuousOn hOmega hT).congr
    (fun z hz => visibleConnectorIncomingParametersFamilyPhaseDerivative_actual hOmega hT hz)

end
end TightVer401


