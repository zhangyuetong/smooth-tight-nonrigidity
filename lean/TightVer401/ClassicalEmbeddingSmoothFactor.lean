import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-! Smoothness can be recovered through a smooth map with injective differential.
This local Euclidean leaf uses the actual differential, a continuous linear left
inverse, and the ordinary inverse function theorem. -/
namespace TightVer401
noncomputable section
open Filter
open scoped Topology ContDiff

/-- A continuous factor is smooth when its composition with a smooth map having
injective differential is smooth. The finite-dimensional ambient space supplies
a continuous linear left inverse; no embedding or inverse is assumed. -/
theorem classicalEmbedding_contDiffAt_factor
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : G → E} {x : G}
    (hf : ContDiffAt ℝ ∞ f (g x))
    (hinj : Function.Injective (fderiv ℝ f (g x)))
    (hg : ContinuousAt g x)
    (hfg : ContDiffAt ℝ ∞ (f ∘ g) x) :
    ContDiffAt ℝ ∞ g x := by
  obtain ⟨L, hL⟩ :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  have hcomp : L.comp (fderiv ℝ f (g x)) =
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) := by
    ext v
    exact hL v
  have hder : HasFDerivAt (L ∘ f)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (g x) := by
    simpa only [hcomp] using
      L.hasFDerivAt.comp (g x) (hf.differentiableAt (by simp)).hasFDerivAt
  have hLF : ContDiffAt ℝ ∞ (L ∘ f) (g x) :=
    L.contDiff.contDiffAt.comp (g x) hf
  let hi : E → E := hLF.localInverse hder (by simp)
  have hhi : ContDiffAt ℝ ∞ hi (L (f (g x))) :=
    hLF.to_localInverse hder (by simp)
  have hleft : ∀ᶠ z in 𝓝 (g x), hi (L (f z)) = z := by
    simpa only [hi, ContDiffAt.localInverse, Function.comp_apply] using
      (hLF.hasStrictFDerivAt' hder (by simp)).eventually_left_inverse
  have hfactor : ContDiffAt ℝ ∞ (fun y => hi (L (f (g y)))) x := by
    exact hhi.comp x (L.contDiff.contDiffAt.comp x hfg)
  apply hfactor.congr_of_eventuallyEq
  have heq : (fun y => hi (L (f (g y)))) =ᶠ[𝓝 x] g :=
    hg.eventually hleft
  exact heq.symm

end
end TightVer401

