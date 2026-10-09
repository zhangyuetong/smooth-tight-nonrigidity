import TightVer401.CorrugatedSeedCurvature
import TightVer401.NormalLoopActual

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

def corrugatedHomogeneous (z : ℂ) : Ambient := WithLp.toLp 2 ![z.re, z.im, 1]
def corrugatedHorizontal (z : ℂ) : Ambient := WithLp.toLp 2 ![z.re, z.im, 0]

theorem corrugatedHomogeneous_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => corrugatedHomogeneous (f s)) (corrugatedHorizontal v) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : HasDerivAt (fun s => ![(f s).re, (f s).im, (1 : ℝ)]) ![v.re, v.im, (0 : ℝ)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact hasDerivAt_const t 1
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem corrugatedHorizontal_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => corrugatedHorizontal (f s)) (corrugatedHorizontal v) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : HasDerivAt (fun s => ![(f s).re, (f s).im, (0 : ℝ)]) ![v.re, v.im, (0 : ℝ)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact hasDerivAt_const t 0
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem corrugatedScaledHomogeneous_deriv {a : ℝ → ℝ} {f : ℝ → ℂ}
    (ha : Differentiable ℝ a) (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun s => a s • corrugatedHomogeneous (f s)) t =
      deriv a t • corrugatedHomogeneous (f t) + a t • corrugatedHorizontal (deriv f t) := by
  have h := (ha t).hasDerivAt.smul (corrugatedHomogeneous_hasDerivAt (hf t).hasDerivAt)
  have h' := h.congr_of_eventuallyEq (f₁ := fun s => a s • corrugatedHomogeneous (f s))
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [h'.deriv]
  exact add_comm _ _

theorem corrugatedScaledHomogeneous_second_deriv {a : ℝ → ℝ} {f : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (deriv (fun s => a s • corrugatedHomogeneous (f s))) t =
      deriv (deriv a) t • corrugatedHomogeneous (f t) +
        (2 * deriv a t) • corrugatedHorizontal (deriv f t) +
        a t • corrugatedHorizontal (deriv (deriv f) t) := by
  have had := ha.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have had' := (contDiff_infty_iff_deriv.mp ha).2.differentiable (by simp)
  have hfd' := (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  have he : deriv (fun s => a s • corrugatedHomogeneous (f s)) =
      fun s => deriv a s • corrugatedHomogeneous (f s) + a s • corrugatedHorizontal (deriv f s) :=
    funext (corrugatedScaledHomogeneous_deriv had hfd)
  rw [he]
  have h₁ := (had' t).hasDerivAt.smul (corrugatedHomogeneous_hasDerivAt (hfd t).hasDerivAt)
  have h₂ := (had t).hasDerivAt.smul (corrugatedHorizontal_hasDerivAt (hfd' t).hasDerivAt)
  have hsum := (h₁.add h₂).congr_of_eventuallyEq
    (f₁ := fun s => deriv a s • corrugatedHomogeneous (f s) + a s • corrugatedHorizontal (deriv f s))
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hsum.deriv]
  module

theorem corrugatedScaledHomogeneous_triple (a b c : ℝ) (z v w : ℂ) :
    inner ℝ
      (c • corrugatedHomogeneous z + (2 * b) • corrugatedHorizontal v + a • corrugatedHorizontal w)
      (ambientCross (a • corrugatedHomogeneous z)
        (b • corrugatedHomogeneous z + a • corrugatedHorizontal v)) =
      a^3 * corrugatedSeedPlaneDet v w := by
  rw [ambient_inner_dot]
  simp [dotProduct, Fin.sum_univ_succ, corrugatedHomogeneous, corrugatedHorizontal,
    ambientCross, cross_apply, corrugatedSeedPlaneDet]
  ring

theorem corrugatedScaledHomogeneous_actual_triple {a : ℝ → ℝ} {f : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    inner ℝ (deriv (deriv (fun s => a s • corrugatedHomogeneous (f s))) t)
      (ambientCross (a t • corrugatedHomogeneous (f t))
        (deriv (fun s => a s • corrugatedHomogeneous (f s)) t)) =
      (a t)^3 * corrugatedSeedPlaneDet (deriv f t) (deriv (deriv f) t) := by
  rw [corrugatedScaledHomogeneous_deriv (ha.differentiable (by simp)) (hf.differentiable (by simp)),
    corrugatedScaledHomogeneous_second_deriv ha hf]
  exact corrugatedScaledHomogeneous_triple _ _ _ _ _ _

end
end TightVer401
