import TightVer401.DualRadialCompletionPhase
import TightVer401.DualRadialCompletionTerminalPairings
import TightVer401.DualRadialCompletionTraceJets
import TightVer401.QuadraticFillingDomination

/-! The actual terminal collar, with its genuine increasing phase, supplies
all angular filler trace hypotheses. No identity phase is assumed.
-/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix

/-- Convert the physical terminal parametrization through the constructed
smooth phase inverse into the actual smooth periodic positive dual traces. -/
theorem dualRadialCompletion_terminal_traces
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {P : ℝ → Coord} (hP : ContDiff ℝ ∞ P)
    {phase : ℝ → ℝ} (hphase : ContDiff ℝ ∞ phase)
    (hDeriv : ∀ s, 0 < deriv phase s)
    (hShift : ∀ s, phase (s + L) = phase s + 2 * Real.pi)
    (hSource : ∀ s, P s ∈ e.source)
    (hActual : ∀ s, e (P s) = saddlePolarChart ![R, phase s])
    (hRadial : ∀ s, 0 < P s ⬝ᵥ quadraticRadialFillingRadialUnit (phase s))
    (hTangential : ∀ s, 0 < deriv P s ⬝ᵥ
      deriv (fun r => saddlePolarChart ![R, phase r]) s) :
    ContDiff ℝ ∞ (quadraticRadialFillingValueTrace (planarLegendre G e) R) ∧
      ContDiff ℝ ∞ (quadraticRadialFillingRadialTrace (planarLegendre G e) R) ∧
      Function.Periodic (quadraticRadialFillingValueTrace (planarLegendre G e) R) (2 * Real.pi) ∧
      Function.Periodic (quadraticRadialFillingRadialTrace (planarLegendre G e) R) (2 * Real.pi) ∧
      (∀ t, 0 < quadraticRadialFillingRadialTrace (planarLegendre G e) R t) ∧
      (∀ t, 0 < deriv (deriv (quadraticRadialFillingValueTrace (planarLegendre G e) R)) t +
        R * quadraticRadialFillingRadialTrace (planarLegendre G e) R t) := by
  obtain ⟨tau, _htau, _hsmooth, hDtau, hLeft, _hRight, _hTurn⟩ :=
    exists_dualRadialCompletion_phase_inverse hphase hDeriv hL hShift
  have hActualAngle (t : ℝ) : e (P (tau.symm t)) = saddlePolarChart ![R, t] := by
    rw [hActual, hLeft]
  have hCircle (t : ℝ) : saddlePolarChart ![R, t] ∈ e.target := by
    rw [← hActualAngle t]
    exact e.map_source (hSource _)
  have hInverse (t : ℝ) : e.symm (saddlePolarChart ![R, t]) = (P ∘ tau.symm) t := by
    rw [← hActualAngle t]
    exact e.left_inv (hSource _)
  obtain ⟨hRad, hTan⟩ := dualRadialCompletionTerminalPairings_reparametrized_pairings
    hP hphase hDeriv hR hDtau hLeft hRadial hTangential
  obtain ⟨hh, hb, hhper, hbper⟩ :=
    dualRadialCompletionTrace_contDiff_periodic e hG hi hCircle
  obtain ⟨hbpos, htrace⟩ :=
    dualRadialCompletionTrace_positive e hG hi heG hCircle hInverse hR hRad hTan
  exact ⟨hh, hb, hhper, hbper, hbpos, htrace⟩

/-- Arbitrarily large actual angular filler coefficients for the dual of the
physical terminal collar; the trace conditions follow from ordinary actual
collar and phase data. -/
theorem exists_dualRadialCompletion_terminal_filler_coefficient
    {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
    (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (heG : ∀ p ∈ e.source, e p = planarGradient G p)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {P : ℝ → Coord} (hP : ContDiff ℝ ∞ P)
    {phase : ℝ → ℝ} (hphase : ContDiff ℝ ∞ phase)
    (hDeriv : ∀ s, 0 < deriv phase s)
    (hShift : ∀ s, phase (s + L) = phase s + 2 * Real.pi)
    (hSource : ∀ s, P s ∈ e.source)
    (hActual : ∀ s, e (P s) = saddlePolarChart ![R, phase s])
    (hRadial : ∀ s, 0 < P s ⬝ᵥ quadraticRadialFillingRadialUnit (phase s))
    (hTangential : ∀ s, 0 < deriv P s ⬝ᵥ
      deriv (fun r => saddlePolarChart ![R, phase r]) s)
    (M0 : ℝ) :
    ∃ M : ℝ, M0 < M ∧ 0 < M ∧ ∀ p : Coord, 0 < p 0 → p 0 ≤ R →
      coordPartial 0 (coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R)
        (quadraticRadialFillingValueTrace (planarLegendre G e) R)
        (quadraticRadialFillingRadialTrace (planarLegendre G e) R))) p < 0 ∧
      0 < coordPartial 1 (coordPartial 1 (dualQuadraticFiller R M (quadraticDominationCutoff R)
        (quadraticRadialFillingValueTrace (planarLegendre G e) R)
        (quadraticRadialFillingRadialTrace (planarLegendre G e) R))) p +
        p 0 * coordPartial 0 (dualQuadraticFiller R M (quadraticDominationCutoff R)
          (quadraticRadialFillingValueTrace (planarLegendre G e) R)
          (quadraticRadialFillingRadialTrace (planarLegendre G e) R)) p := by
  obtain ⟨hh, hb, hhper, hbper, hbpos, htrace⟩ :=
    dualRadialCompletion_terminal_traces e hG hi heG hR hL hP hphase hDeriv hShift
      hSource hActual hRadial hTangential
  obtain ⟨hchi, hc0, hc1, _⟩ := quadraticDominationCutoff_properties hR
  exact exists_quadratic_filler_coefficient hR hchi hh hb hhper hbper hc0 hc1 hbpos htrace M0

end
end TightVer401
