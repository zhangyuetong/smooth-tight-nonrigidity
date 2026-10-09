import TightVer401.NormalLoopSpeed

/-! The preceding construction specialized to `deriv ζ` and `deriv (deriv ζ)`;
no independently supplied frame or frame equations are required. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def normalLoopTangent (ζ : ℝ → Ambient) := normalLoopP ζ (deriv ζ)
def normalLoopCurvature (ζ : ℝ → Ambient) := normalLoopKappa ζ (deriv ζ) (deriv (deriv ζ))

theorem normalLoop_derivative_periodic {ζ E : ℝ → Ambient} {L : ℝ}
    (hζL : Function.Periodic ζ L) (hζ : ∀ r, HasDerivAt ζ (E r) r) :
    Function.Periodic E L := by
  intro r
  have hd := (hζ (r + L)).scomp r ((hasDerivAt_id r).add_const L)
  change HasDerivAt (ζ ∘ fun t => t + L) ((1 : ℝ) • E (r + L)) r at hd
  have heq : (ζ ∘ fun r => r + L) = ζ := funext hζL
  rw [heq] at hd
  simpa only [one_smul] using hd.unique (hζ r)

theorem normalLoop_actual_frame {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ)
    (hunit : ∀ r, inner ℝ (ζ r) (ζ r) = 1)
    (hspeed : ∀ r, inner ℝ (deriv ζ r) (deriv ζ r) = 1) (r : ℝ) :
    IsOrthonormalFrame (normalLoopTangent ζ r) (deriv ζ r) (ζ r) ∧
    HasDerivAt (normalLoopTangent ζ) (normalLoopCurvature ζ r • deriv ζ r) r ∧
    deriv (deriv ζ) r = -ζ r - normalLoopCurvature ζ r • normalLoopTangent ζ r := by
  have hz := (contDiff_infty_iff_deriv.mp hζ).1
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hEd := (contDiff_infty_iff_deriv.mp hE).1
  exact ⟨normalLoop_frame (fun t => (hz t).hasDerivAt) hunit hspeed r,
    normalLoop_derivative_P (fun t => (hz t).hasDerivAt) (fun t => (hEd t).hasDerivAt)
      hunit hspeed r,
    normalLoop_second_derivative (fun t => (hz t).hasDerivAt)
      (fun t => (hEd t).hasDerivAt) hunit hspeed r⟩

theorem normalLoop_actual_smooth {ζ : ℝ → Ambient} (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (normalLoopTangent ζ) ∧ ContDiff ℝ ∞ (normalLoopCurvature ζ) := by
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hA := (contDiff_infty_iff_deriv.mp hE).2
  exact ⟨normalLoopP_contDiff hζ hE, normalLoopKappa_contDiff hζ hE hA⟩

theorem normalLoop_actual_periodic {ζ : ℝ → Ambient} {L : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζL : Function.Periodic ζ L) :
    Function.Periodic (normalLoopTangent ζ) L ∧ Function.Periodic (normalLoopCurvature ζ) L := by
  have hz := (contDiff_infty_iff_deriv.mp hζ).1
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hEd := (contDiff_infty_iff_deriv.mp hE).1
  have hEL := normalLoop_derivative_periodic hζL (fun r => (hz r).hasDerivAt)
  have hAL := normalLoop_derivative_periodic hEL (fun r => (hEd r).hasDerivAt)
  refine ⟨normalLoopP_periodic hζL hEL, ?_⟩
  intro r
  simp only [normalLoopCurvature, normalLoopKappa, hAL r,
    normalLoopP_periodic hζL hEL r]

end
end TightVer401
