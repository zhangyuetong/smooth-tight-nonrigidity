import TightVer401.NormalLoopActual
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Positive speed supplies the inverse arclength coordinate through the
inverse function theorem; its derivative is derived rather than assumed. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem normalLoop_exists_arclength_inverse {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hpos : ∀ r, 0 < a r) (r : ℝ) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      r ∈ e.source ∧ (e : ℝ → ℝ) = rawPrimitive a ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ e.target, HasDerivAt e.symm (a (e.symm s))⁻¹ s := by
  have hf := rawPrimitive_contDiff ha
  have hd := (rawPrimitive_hasDerivAt ha.continuous r).hasFDerivAt_equiv (ne_of_gt (hpos r))
  let e := hf.contDiffAt.toOpenPartialHomeomorph (rawPrimitive a) hd (by simp)
  have hefun : (e : ℝ → ℝ) = rawPrimitive a := rfl
  refine ⟨e, hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp), hefun, ?_, ?_⟩
  · intro s hs
    have hd' := (rawPrimitive_hasDerivAt ha.continuous (e.symm s)).hasFDerivAt_equiv
      (ne_of_gt (hpos (e.symm s)))
    exact (e.contDiffAt_symm hs (f₀' := ContinuousLinearEquiv.unitsEquivAut ℝ
      (Units.mk0 (a (e.symm s)) (ne_of_gt (hpos (e.symm s)))))
      (by rw [hefun]; exact hd') (by rw [hefun]; exact hf.contDiffAt)).contDiffWithinAt
  · intro s hs
    exact e.hasDerivAt_symm hs (ne_of_gt (hpos (e.symm s)))
      (by rw [hefun]; exact rawPrimitive_hasDerivAt ha.continuous (e.symm s))

theorem normalLoop_physical_curve_hasDerivAt {ζ : ℝ → Ambient} {a ψ : ℝ → ℝ} {s : ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (ha : Continuous a) (hpos : 0 < a (ψ s))
    (hψ : HasDerivAt ψ (a (ψ s))⁻¹ s) :
    HasDerivAt (normalLoopCurve a ζ (deriv ζ) ∘ ψ) (normalLoopTangent ζ (ψ s)) s := by
  have hE := (contDiff_infty_iff_deriv.mp hζ).2
  have hd := (normalLoopCurve_hasDerivAt ha hζ hE (ψ s)).scomp s hψ
  simpa only [normalLoopTangent, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul] using hd

end
end TightVer401
