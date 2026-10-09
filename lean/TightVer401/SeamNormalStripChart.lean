import TightVer401.SeamNormalStrip
import OAI.Analysis.CircleDomains.Sobolev.ComplexTangentFrame

namespace TightVer401

/-! An actual smooth local normal chart around each regular curve point. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
open OAI.CircleDomainRigidity

lemma seamCurveNormalStrip_exists_chart {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (t : ℝ) (ht : deriv γ t ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (t,0) ∈ e.source ∧ (∀ p, e p = seamCurveNormalStrip γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (γ t) := by
  let L : (ℝ × ℝ) ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.ofBijective (complexTangentFrame (deriv γ t))
      (LinearMap.ker_eq_bot.mpr (complexTangentFrame_bijective ht).1)
      (LinearMap.range_eq_top.mpr (complexTangentFrame_bijective ht).2)
  have hc := seamCurveNormalStrip_contDiff hγ
  have hdf : fderiv ℝ (seamCurveNormalStrip γ) (t,0) = (L : (ℝ × ℝ) →L[ℝ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro v
    exact seamCurveNormalStrip_fderiv hγ t v
  have hd : HasFDerivAt (seamCurveNormalStrip γ) (L : (ℝ × ℝ) →L[ℝ] ℂ) (t,0) := by
    rw [← hdf]
    exact (hc.differentiable (by simp) (t,0)).hasFDerivAt
  let e := hc.contDiffAt.toOpenPartialHomeomorph (seamCurveNormalStrip γ) hd (by simp)
  have he : ∀ p, e p = seamCurveNormalStrip γ p := fun _ => rfl
  have hp : (t,0) ∈ e.source := hc.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,hp,he,hc,?_⟩
  have hval : e (t,0) = γ t := by simp [he,seamCurveNormalStrip]
  rw [← hval]
  apply e.contDiffAt_symm (e.map_source hp) (f₀' := L)
  · change HasFDerivAt (seamCurveNormalStrip γ) _ (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hd
  · change ContDiffAt ℝ ∞ (seamCurveNormalStrip γ) (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hc.contDiffAt



end

end TightVer401
