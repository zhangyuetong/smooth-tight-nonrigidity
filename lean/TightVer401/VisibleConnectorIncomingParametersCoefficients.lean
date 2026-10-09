import TightVer401.VisibleConnectorRuledCoordinates
import TightVer401.SeamPeriodicity
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Joint local calculus for the SAME fixed-eta smooth family.  Differentiation
is on the actual open domain only.  The joint derivative is identified with
the actual fixed-rho curve derivative before coefficient continuity is used. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def visibleConnectorIncomingParametersFamilyPhaseDerivative (F : ℝ × ℝ → Coord) (z : ℝ × ℝ) : Coord :=
  fderiv ℝ F z ((0 : ℝ), (1 : ℝ))

def visibleConnectorIncomingParametersFamilyA (P W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  -visibleConnectorDet (visibleConnectorIncomingParametersFamilyPhaseDerivative P z) (W z)

def visibleConnectorIncomingParametersFamilyB (G W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  visibleConnectorIncomingParametersFamilyPhaseDerivative G z ⬝ᵥ W z

def visibleConnectorIncomingParametersFamilyC (G W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  visibleConnectorIncomingParametersFamilyB G W z +
    visibleConnectorDet (visibleConnectorIncomingParametersFamilyPhaseDerivative W z) (W z)

theorem visibleConnectorIncomingParametersFamilyPhaseDerivative_actual {F : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega) (hF : ContDiffOn ℝ ∞ F Omega)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    deriv (fun s => F (z.1, s)) z.2 = visibleConnectorIncomingParametersFamilyPhaseDerivative F z := by
  have hf : DifferentiableAt ℝ F z :=
    ((hF _ hz).contDiffAt (hOmega.mem_nhds hz)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt z.2 hpath).deriv

theorem visibleConnectorIncomingParametersFamilyPhaseDerivative_continuousOn
    {F : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hF : ContDiffOn ℝ ∞ F Omega) :
    ContinuousOn (visibleConnectorIncomingParametersFamilyPhaseDerivative F) Omega :=
  (hF.continuousOn_fderiv_of_isOpen hOmega (by simp)).clm_apply continuousOn_const

private theorem incomingParameters_coordinate_continuous {F : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} (hF : ContinuousOn F Omega) (i : Fin 2) :
    ContinuousOn (fun z => F z i) Omega :=
  (continuous_apply i).continuousOn.comp hF (fun _ _ => mem_univ _)

theorem visibleConnectorIncomingParametersFamily_coefficients_continuousOn
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega) :
    ContinuousOn (visibleConnectorIncomingParametersFamilyA P W) Omega ∧
      ContinuousOn (visibleConnectorIncomingParametersFamilyB G W) Omega ∧
      ContinuousOn (visibleConnectorIncomingParametersFamilyC G W) Omega := by
  have hDP := visibleConnectorIncomingParametersFamilyPhaseDerivative_continuousOn hOmega hP
  have hDG := visibleConnectorIncomingParametersFamilyPhaseDerivative_continuousOn hOmega hG
  have hDW := visibleConnectorIncomingParametersFamilyPhaseDerivative_continuousOn hOmega hW
  have hw := hW.continuousOn
  have hA : ContinuousOn (visibleConnectorIncomingParametersFamilyA P W) Omega :=
    (((incomingParameters_coordinate_continuous hDP 0).mul
      (incomingParameters_coordinate_continuous hw 1)).sub
        ((incomingParameters_coordinate_continuous hDP 1).mul
          (incomingParameters_coordinate_continuous hw 0))).neg
  have hB : ContinuousOn (visibleConnectorIncomingParametersFamilyB G W) Omega := by
    have he : visibleConnectorIncomingParametersFamilyB G W =
        (fun z => visibleConnectorIncomingParametersFamilyPhaseDerivative G z 0 * W z 0 +
          visibleConnectorIncomingParametersFamilyPhaseDerivative G z 1 * W z 1) := by
      funext z
      simp [visibleConnectorIncomingParametersFamilyB, dotProduct, Fin.sum_univ_two]
    rw [he]
    exact ((incomingParameters_coordinate_continuous hDG 0).mul
      (incomingParameters_coordinate_continuous hw 0)).add
        ((incomingParameters_coordinate_continuous hDG 1).mul
          (incomingParameters_coordinate_continuous hw 1))
  have hC : ContinuousOn (visibleConnectorIncomingParametersFamilyC G W) Omega :=
    hB.add (((incomingParameters_coordinate_continuous hDW 0).mul
      (incomingParameters_coordinate_continuous hw 1)).sub
        ((incomingParameters_coordinate_continuous hDW 1).mul
          (incomingParameters_coordinate_continuous hw 0)))
  exact ⟨hA, hB, hC⟩

theorem visibleConnectorIncomingParametersFamily_coefficients_actual
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    visibleConnectorIncomingParametersFamilyA P W z =
      visibleConnectorA (fun s => P (z.1, s)) (fun s => W (z.1, s)) z.2 ∧
    visibleConnectorIncomingParametersFamilyB G W z =
      visibleConnectorB (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 ∧
    visibleConnectorIncomingParametersFamilyC G W z =
      visibleConnectorC (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold visibleConnectorIncomingParametersFamilyA visibleConnectorA
    rw [← visibleConnectorIncomingParametersFamilyPhaseDerivative_actual hOmega hP hz]
  · unfold visibleConnectorIncomingParametersFamilyB visibleConnectorB
    rw [← visibleConnectorIncomingParametersFamilyPhaseDerivative_actual hOmega hG hz]
  · unfold visibleConnectorIncomingParametersFamilyC visibleConnectorIncomingParametersFamilyB
      visibleConnectorC visibleConnectorB
    rw [← visibleConnectorIncomingParametersFamilyPhaseDerivative_actual hOmega hG hz,
      ← visibleConnectorIncomingParametersFamilyPhaseDerivative_actual hOmega hW hz]

/-- Periodicity of actual derivatives needs no smoothness outside Omega. -/
theorem visibleConnectorIncomingParametersFamily_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hp
  rw [← deriv_comp_add_const f L s, he]

/-- Joint continuity of the literal fixed-rho coefficients, identified with
actual curve derivatives on the open family domain. -/
theorem visibleConnectorIncomingParametersFamily_actual_coefficients_continuousOn
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega) :
    ContinuousOn (fun z => visibleConnectorA
      (fun s => P (z.1, s)) (fun s => W (z.1, s)) z.2) Omega ∧
    ContinuousOn (fun z => visibleConnectorB
      (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2) Omega ∧
    ContinuousOn (fun z => visibleConnectorC
      (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2) Omega := by
  obtain ⟨hA, hB, hC⟩ :=
    visibleConnectorIncomingParametersFamily_coefficients_continuousOn hOmega hP hG hW
  exact ⟨hA.congr (fun z hz =>
      (visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).1.symm),
    hB.congr (fun z hz =>
      (visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).2.1.symm),
    hC.congr (fun z hz =>
      (visibleConnectorIncomingParametersFamily_coefficients_actual hOmega hP hG hW hz).2.2.symm)⟩
/-- The literal actual coefficients are periodic even without smoothness
outside the open family domain. -/
theorem visibleConnectorIncomingParametersFamily_actual_coefficients_periodic
    {P G W : ℝ × ℝ → Coord} {L : ℝ}
    (hP : ∀ rho, Periodic (fun s => P (rho, s)) L)
    (hG : ∀ rho, Periodic (fun s => G (rho, s)) L)
    (hW : ∀ rho, Periodic (fun s => W (rho, s)) L) :
    (∀ rho, Periodic (fun s => visibleConnectorA
      (fun t => P (rho, t)) (fun t => W (rho, t)) s) L) ∧
    (∀ rho, Periodic (fun s => visibleConnectorB
      (fun t => G (rho, t)) (fun t => W (rho, t)) s) L) ∧
    (∀ rho, Periodic (fun s => visibleConnectorC
      (fun t => G (rho, t)) (fun t => W (rho, t)) s) L) := by
  have hDP := fun rho => visibleConnectorIncomingParametersFamily_deriv_periodic (hP rho)
  have hDG := fun rho => visibleConnectorIncomingParametersFamily_deriv_periodic (hG rho)
  have hDW := fun rho => visibleConnectorIncomingParametersFamily_deriv_periodic (hW rho)
  refine ⟨?_, ?_, ?_⟩
  · intro rho s
    simp only [visibleConnectorA, hDP rho s, hW rho s]
  · intro rho s
    simp only [visibleConnectorB, hDG rho s, hW rho s]
  · intro rho s
    simp only [visibleConnectorC, visibleConnectorB, hDG rho s, hDW rho s, hW rho s]
end
end TightVer401






