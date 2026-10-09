import TightVer401.PlanarLegendre
import TightVer401.QuadraticRadialFillingJets

/-! Actual dual traces on a terminal circle contained in an open inverse collar. -/
namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem terminal_circle_hasDerivAt (R theta : ℝ) :
    HasDerivAt (fun t => saddlePolarChart ![R, t])
      (R • quadraticRadialFillingTangentialUnit theta) theta := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [saddlePolarChart, quadraticRadialFillingTangentialUnit,
      Pi.smul_apply, smul_eq_mul, mul_neg, neg_mul] using
      (Real.hasDerivAt_cos theta).const_mul R
  · simpa [saddlePolarChart, quadraticRadialFillingTangentialUnit,
      Pi.smul_apply, smul_eq_mul] using (Real.hasDerivAt_sin theta).const_mul R

section Terminal
variable {G : Coord → ℝ} (e : OpenPartialHomeomorph Coord Coord)
  (hG : ContDiffOn ℝ ∞ G e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
  (heG : ∀ p ∈ e.source, e p = planarGradient G p)
  {R : ℝ} (hCircle : ∀ theta : ℝ, saddlePolarChart ![R, theta] ∈ e.target)
  {P : ℝ → Coord} (hP : ∀ theta : ℝ, e.symm (saddlePolarChart ![R, theta]) = P theta)
include hG hi heG hCircle hP

/-- The actual Cartesian gradient of the dual along the terminal circle
is the actual incoming source seam. -/
theorem dualRadialCompletionTrace_gradient (theta : ℝ) :
    planarGradient (planarLegendre G e) (saddlePolarChart ![R, theta]) = P theta := by
  rw [planarLegendre_gradient e hG hi heG (hCircle theta), hP theta]

/-- Its Hessian is the actual inverse source Hessian, derived from the
ordinary partial inverse and actual gradient equality. -/
theorem dualRadialCompletionTrace_hessian (theta : ℝ) :
    planarHessian (planarLegendre G e) (saddlePolarChart ![R, theta]) =
      (planarHessian G (P theta))⁻¹ := by
  rw [planarLegendre_hessian e hG hi heG (hCircle theta), hP theta]

omit heG hP in
/-- Actual scalar value and radial traces are smooth and 2π-periodic. -/
theorem dualRadialCompletionTrace_contDiff_periodic :
    ContDiff ℝ ∞ (quadraticRadialFillingValueTrace (planarLegendre G e) R) ∧
      ContDiff ℝ ∞ (quadraticRadialFillingRadialTrace (planarLegendre G e) R) ∧
      Function.Periodic (quadraticRadialFillingValueTrace (planarLegendre G e) R)
        (2 * Real.pi) ∧
      Function.Periodic (quadraticRadialFillingRadialTrace (planarLegendre G e) R)
        (2 * Real.pi) := by
  have hL := planarLegendre_contDiffOn e hG hi
  have hs := quadraticRadialFilling_traces_contDiff hL e.open_target hCircle
  exact ⟨hs.1, hs.2, quadraticRadialFilling_valueTrace_periodic _ _,
    quadraticRadialFilling_radialTrace_periodic hL e.open_target hCircle⟩

omit hG heG in
/-- The source seam itself is smooth and periodic as the actual inverse
of the smooth periodic terminal circle. -/
theorem dualRadialCompletionTrace_seam_contDiff_periodic :
    ContDiff ℝ ∞ P ∧ Function.Periodic P (2 * Real.pi) := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => saddlePolarChart ![R, t]) :=
    saddlePolarChart_contDiff.comp (quadraticRadialFilling_parameters_contDiff R)
  have he : (fun t => e.symm (saddlePolarChart ![R, t])) = P := funext hP
  constructor
  · rw [← he]
    exact contDiffOn_univ.mp (hi.comp hc.contDiffOn (fun t _ => hCircle t))
  · intro t
    have hper : saddlePolarChart ![R, t + 2 * Real.pi] = saddlePolarChart ![R, t] :=
      quadraticRadialFilling_polar_circle_periodic R t
    rw [← hP (t + 2 * Real.pi), hper, hP t]

/-- The actual radial trace is the positive radial source-seam pairing. -/
theorem dualRadialCompletionTrace_radial (theta : ℝ) :
    quadraticRadialFillingRadialTrace (planarLegendre G e) R theta =
      P theta ⬝ᵥ quadraticRadialFillingRadialUnit theta := by
  rw [quadraticRadialFilling_radialTrace_eq (planarLegendre_contDiffOn e hG hi)
    e.open_target (hCircle theta),
    dualRadialCompletionTrace_gradient e hG hi heG hCircle hP theta]

/-- Differentiate the actual dual gradient along the terminal circle;
no derivative relation on P is assumed. -/
theorem dualRadialCompletionTrace_seam_deriv (theta : ℝ) :
    deriv P theta = planarHessian (planarLegendre G e) (saddlePolarChart ![R, theta]) *ᵥ
      (R • quadraticRadialFillingTangentialUnit theta) := by
  have hL := planarLegendre_contDiffOn e hG hi
  have hdG := ((planarGradient_contDiffOn hL e.open_target).contDiffAt
    (e.open_target.mem_nhds (hCircle theta))).differentiableAt (by simp)
  have hd := hdG.hasFDerivAt.comp_hasDerivAt theta (terminal_circle_hasDerivAt R theta)
  have he : (fun t => planarGradient (planarLegendre G e) (saddlePolarChart ![R, t])) = P :=
    funext (dualRadialCompletionTrace_gradient e hG hi heG hCircle hP)
  change HasDerivAt (fun t => planarGradient (planarLegendre G e)
    (saddlePolarChart ![R, t])) _ theta at hd
  rw [he] at hd
  rw [hd.deriv]
  exact planarGradient_fderiv_apply hL e.open_target (hCircle theta) _

/-- The actual angular filler quantity is the signed positive terminal-seam
pairing, including its exact radius factor. -/
theorem dualRadialCompletionTrace_tangential (theta : ℝ) :
    deriv (deriv (quadraticRadialFillingValueTrace (planarLegendre G e) R)) theta +
        R * quadraticRadialFillingRadialTrace (planarLegendre G e) R theta =
      R * (deriv P theta ⬝ᵥ quadraticRadialFillingTangentialUnit theta) := by
  rw [quadraticRadialFilling_tangentialTrace_eq (planarLegendre_contDiffOn e hG hi)
    e.open_target hCircle theta,
    dualRadialCompletionTrace_seam_deriv e hG hi heG hCircle hP theta]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  ring

/-- Positive ordinary terminal-seam pairings imply exactly the positivity
hypotheses of the already proved angular domination theorem. -/
theorem dualRadialCompletionTrace_positive (hR : 0 < R)
    (hRadial : ∀ theta, 0 < P theta ⬝ᵥ quadraticRadialFillingRadialUnit theta)
    (hTangential : ∀ theta, 0 < deriv P theta ⬝ᵥ quadraticRadialFillingTangentialUnit theta) :
    (∀ theta, 0 < quadraticRadialFillingRadialTrace (planarLegendre G e) R theta) ∧
      ∀ theta, 0 < deriv (deriv (quadraticRadialFillingValueTrace (planarLegendre G e) R)) theta +
        R * quadraticRadialFillingRadialTrace (planarLegendre G e) R theta := by
  constructor
  · intro theta
    rw [dualRadialCompletionTrace_radial e hG hi heG hCircle hP theta]
    exact hRadial theta
  · intro theta
    rw [dualRadialCompletionTrace_tangential e hG hi heG hCircle hP theta]
    exact mul_pos hR (hTangential theta)

end Terminal
end
end TightVer401
