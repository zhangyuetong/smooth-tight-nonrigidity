import TightVer401.QuadraticRadialFillingTraces

/-! Convert actual physical terminal seam pairings to actual angular pairings
using the separately constructed smooth phase inverse and its actual derivative.
-/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual chain-rule derivative of the physical terminal gradient circle. -/
theorem dualRadialCompletionTerminalPairings_circle_hasDerivAt
    {theta : ℝ → ℝ} (hTheta : ContDiff ℝ ∞ theta) (R s : ℝ) :
    HasDerivAt (fun r => saddlePolarChart ![R, theta r])
      ((R * deriv theta s) • quadraticRadialFillingTangentialUnit (theta s)) s := by
  have ht := (hTheta.differentiable (by simp) s).hasDerivAt
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun r => R * Real.cos (theta r))
      ((R * deriv theta s) * (-Real.sin (theta s))) s
    simpa only [mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm] using
      ht.cos.const_mul R
  · change HasDerivAt (fun r => R * Real.sin (theta r))
      ((R * deriv theta s) * Real.cos (theta s)) s
    simpa only [mul_assoc, mul_comm, mul_left_comm] using ht.sin.const_mul R

theorem dualRadialCompletionTerminalPairings_circle_deriv
    {theta : ℝ → ℝ} (hTheta : ContDiff ℝ ∞ theta) (R s : ℝ) :
    deriv (fun r => saddlePolarChart ![R, theta r]) s =
      (R * deriv theta s) • quadraticRadialFillingTangentialUnit (theta s) :=
  (dualRadialCompletionTerminalPairings_circle_hasDerivAt hTheta R s).deriv

/-- Derive the actual reparametrized seam derivative from the scalar inverse
HasDerivAt produced by the phase-inverse construction. -/
theorem dualRadialCompletionTerminalPairings_reparam_deriv
    {P : ℝ → Coord} {theta tau : ℝ → ℝ} (hP : ContDiff ℝ ∞ P)
    (hDtau : ∀ t, HasDerivAt tau (deriv theta (tau t))⁻¹ t) (t : ℝ) :
    deriv (P ∘ tau) t = (deriv theta (tau t))⁻¹ • deriv P (tau t) :=
  ((hP.differentiable (by simp) (tau t)).hasDerivAt.scomp t (hDtau t)).deriv

/-- Physical positivity gives the exact ordinary angular pairings required
by the terminal dual-trace adapter; neither angular conclusion is an input. -/
theorem dualRadialCompletionTerminalPairings_reparametrized_pairings
    {P : ℝ → Coord} {theta tau : ℝ → ℝ} {R : ℝ}
    (hP : ContDiff ℝ ∞ P) (hTheta : ContDiff ℝ ∞ theta)
    (hDeriv : ∀ s, 0 < deriv theta s) (hR : 0 < R)
    (hDtau : ∀ t, HasDerivAt tau (deriv theta (tau t))⁻¹ t)
    (hPhaseLeft : ∀ t, theta (tau t) = t)
    (hRadial : ∀ s, 0 < P s ⬝ᵥ quadraticRadialFillingRadialUnit (theta s))
    (hTangential : ∀ s, 0 < deriv P s ⬝ᵥ
      deriv (fun r => saddlePolarChart ![R, theta r]) s) :
    (∀ t, 0 < P (tau t) ⬝ᵥ quadraticRadialFillingRadialUnit t) ∧
      ∀ t, 0 < deriv (P ∘ tau) t ⬝ᵥ quadraticRadialFillingTangentialUnit t := by
  constructor
  · intro t
    simpa only [hPhaseLeft t] using hRadial (tau t)
  · intro t
    have hPhysical := hTangential (tau t)
    rw [dualRadialCompletionTerminalPairings_circle_deriv hTheta R (tau t)] at hPhysical
    have hScale : deriv P (tau t) ⬝ᵥ
        ((R * deriv theta (tau t)) • quadraticRadialFillingTangentialUnit (theta (tau t))) =
        (R * deriv theta (tau t)) *
          (deriv P (tau t) ⬝ᵥ quadraticRadialFillingTangentialUnit (theta (tau t))) := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hScale] at hPhysical
    have hPhysicalPositive : 0 < deriv P (tau t) ⬝ᵥ quadraticRadialFillingTangentialUnit t := by
      have hv := (mul_pos_iff_of_pos_left (mul_pos hR (hDeriv (tau t)))).mp hPhysical
      simpa only [hPhaseLeft t] using hv
    rw [dualRadialCompletionTerminalPairings_reparam_deriv hP hDtau t]
    have hInverseScale : ((deriv theta (tau t))⁻¹ • deriv P (tau t)) ⬝ᵥ
        quadraticRadialFillingTangentialUnit t =
        (deriv theta (tau t))⁻¹ * (deriv P (tau t) ⬝ᵥ quadraticRadialFillingTangentialUnit t) := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hInverseScale]
    exact mul_pos (inv_pos.mpr (hDeriv (tau t))) hPhysicalPositive

end
end TightVer401
