import TightVer401.VisibleConnectorDisplacedSeamGinFamily
import TightVer401.SeamPeriodicity
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Joint local calculus for the SAME fixed-eta Gin family.  Differentiation
is on the actual open domain only.  The joint derivative is identified with
the actual fixed-rho curve derivative before coefficient continuity is used. -/
namespace TightVer401
noncomputable section
open Set Function Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def visibleConnectorIncomingGinFamilyPhaseDerivative (F : ℝ × ℝ → Coord) (z : ℝ × ℝ) : Coord :=
  fderiv ℝ F z ((0 : ℝ), (1 : ℝ))

def visibleConnectorIncomingGinFamilyA (P W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  -visibleConnectorDet (visibleConnectorIncomingGinFamilyPhaseDerivative P z) (W z)

def visibleConnectorIncomingGinFamilyB (G W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  visibleConnectorIncomingGinFamilyPhaseDerivative G z ⬝ᵥ W z

def visibleConnectorIncomingGinFamilyC (G W : ℝ × ℝ → Coord) (z : ℝ × ℝ) : ℝ :=
  visibleConnectorIncomingGinFamilyB G W z +
    visibleConnectorDet (visibleConnectorIncomingGinFamilyPhaseDerivative W z) (W z)

theorem visibleConnectorIncomingGinFamilyPhaseDerivative_actual {F : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega) (hF : ContDiffOn ℝ ∞ F Omega)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    deriv (fun s => F (z.1, s)) z.2 = visibleConnectorIncomingGinFamilyPhaseDerivative F z := by
  have hf : DifferentiableAt ℝ F z :=
    ((hF _ hz).contDiffAt (hOmega.mem_nhds hz)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun s : ℝ => (z.1, s)) ((0 : ℝ), (1 : ℝ)) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt z.2 hpath).deriv

theorem visibleConnectorIncomingGinFamilyPhaseDerivative_continuousOn
    {F : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hF : ContDiffOn ℝ ∞ F Omega) :
    ContinuousOn (visibleConnectorIncomingGinFamilyPhaseDerivative F) Omega :=
  (hF.continuousOn_fderiv_of_isOpen hOmega (by simp)).clm_apply continuousOn_const

private theorem incomingFamily_coordinate_continuous {F : ℝ × ℝ → Coord}
    {Omega : Set (ℝ × ℝ)} (hF : ContinuousOn F Omega) (i : Fin 2) :
    ContinuousOn (fun z => F z i) Omega :=
  (continuous_apply i).continuousOn.comp hF (fun _ _ => mem_univ _)

theorem visibleConnectorIncomingGinFamily_coefficients_continuousOn
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega) :
    ContinuousOn (visibleConnectorIncomingGinFamilyA P W) Omega ∧
      ContinuousOn (visibleConnectorIncomingGinFamilyB G W) Omega ∧
      ContinuousOn (visibleConnectorIncomingGinFamilyC G W) Omega := by
  have hDP := visibleConnectorIncomingGinFamilyPhaseDerivative_continuousOn hOmega hP
  have hDG := visibleConnectorIncomingGinFamilyPhaseDerivative_continuousOn hOmega hG
  have hDW := visibleConnectorIncomingGinFamilyPhaseDerivative_continuousOn hOmega hW
  have hw := hW.continuousOn
  have hA : ContinuousOn (visibleConnectorIncomingGinFamilyA P W) Omega :=
    (((incomingFamily_coordinate_continuous hDP 0).mul
      (incomingFamily_coordinate_continuous hw 1)).sub
        ((incomingFamily_coordinate_continuous hDP 1).mul
          (incomingFamily_coordinate_continuous hw 0))).neg
  have hB : ContinuousOn (visibleConnectorIncomingGinFamilyB G W) Omega := by
    simp only [visibleConnectorIncomingGinFamilyB, dotProduct, Fin.sum_univ_two]
    exact ((incomingFamily_coordinate_continuous hDG 0).mul
      (incomingFamily_coordinate_continuous hw 0)).add
        ((incomingFamily_coordinate_continuous hDG 1).mul
          (incomingFamily_coordinate_continuous hw 1))
  have hC : ContinuousOn (visibleConnectorIncomingGinFamilyC G W) Omega :=
    hB.add (((incomingFamily_coordinate_continuous hDW 0).mul
      (incomingFamily_coordinate_continuous hw 1)).sub
        ((incomingFamily_coordinate_continuous hDW 1).mul
          (incomingFamily_coordinate_continuous hw 0)))
  exact ⟨hA, hB, hC⟩

theorem visibleConnectorIncomingGinFamily_coefficients_actual
    {P G W : ℝ × ℝ → Coord} {Omega : Set (ℝ × ℝ)}
    (hOmega : IsOpen Omega) (hP : ContDiffOn ℝ ∞ P Omega)
    (hG : ContDiffOn ℝ ∞ G Omega) (hW : ContDiffOn ℝ ∞ W Omega)
    {z : ℝ × ℝ} (hz : z ∈ Omega) :
    visibleConnectorIncomingGinFamilyA P W z =
      visibleConnectorA (fun s => P (z.1, s)) (fun s => W (z.1, s)) z.2 ∧
    visibleConnectorIncomingGinFamilyB G W z =
      visibleConnectorB (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 ∧
    visibleConnectorIncomingGinFamilyC G W z =
      visibleConnectorC (fun s => G (z.1, s)) (fun s => W (z.1, s)) z.2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold visibleConnectorIncomingGinFamilyA visibleConnectorA
    rw [← visibleConnectorIncomingGinFamilyPhaseDerivative_actual hOmega hP hz]
  · unfold visibleConnectorIncomingGinFamilyB visibleConnectorB
    rw [← visibleConnectorIncomingGinFamilyPhaseDerivative_actual hOmega hG hz]
  · unfold visibleConnectorIncomingGinFamilyC visibleConnectorIncomingGinFamilyB
      visibleConnectorC visibleConnectorB
    rw [← visibleConnectorIncomingGinFamilyPhaseDerivative_actual hOmega hG hz,
      ← visibleConnectorIncomingGinFamilyPhaseDerivative_actual hOmega hW hz]

/-- Periodicity of actual derivatives needs no smoothness outside Omega. -/
theorem visibleConnectorIncomingGinFamily_deriv_periodic {f : ℝ → Coord} {L : ℝ}
    (hp : Periodic f L) : Periodic (deriv f) L := by
  intro s
  have he : (fun t => f (t + L)) = f := funext hp
  rw [← deriv_comp_add_const f L s, he]

end
end TightVer401
