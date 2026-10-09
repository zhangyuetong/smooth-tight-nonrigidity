import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Tactic.NormNum

/-! Necessary second derivative tests for actual local maxima. The scalar proof
uses the ordinary second derivative test and locality of derivatives; the normed
space proof applies it to affine lines and identifies both actual derivatives. -/
namespace TightVer401
noncomputable section
open Filter
open scoped Topology ContDiff

/-- At a continuous real local maximum, the actual second derivative is
nonpositive. No differentiability assumptions are needed because `deriv` takes
its ordinary zero value when the relevant derivative does not exist. -/
theorem localMax_deriv_deriv_nonpos
    {f : ℝ → ℝ} {x : ℝ} (hmax : IsLocalMax f x)
    (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ : ℝ => f x) := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hzero : deriv (deriv f) x = 0 := by
    simpa using heq.deriv.deriv_eq
  exact hpos.ne' hzero

/-- The actual second Fréchet derivative is nonpositive in every repeated
vector direction at a twice continuously differentiable local maximum. -/
theorem localMax_fderiv_fderiv_apply_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E}
    (hmax : IsLocalMax f x) (hf : ContDiffAt ℝ 2 f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let line : ℝ → E := fun t => x + t • v
  let k : ℝ → ℝ := f ∘ line
  have hline : HasDerivAt line v 0 := by
    simpa only [line, one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hline0 : line 0 = x := by simp [line]
  have hmaxLine : IsLocalMax f (line 0) := by
    rw [hline0]
    exact hmax
  have hfLine : ContinuousAt f (line 0) := by
    rw [hline0]
    exact hf.continuousAt
  have hkmax : IsLocalMax k 0 := hmaxLine.comp_continuous hline.continuousAt
  have hkcont : ContinuousAt k 0 := hfLine.comp hline.continuousAt
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (by norm_num)
  have hcder : HasDerivAt (fun t => fderiv ℝ f (line t))
      (fderiv ℝ (fderiv ℝ f) x v) 0 := by
    have hd := (hDf.differentiableAt (by norm_num)).hasFDerivAt
    have hd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (line 0) := by
      simpa only [hline0] using hd
    exact hd'.comp_hasDerivAt 0 hline
  have hsecond : HasDerivAt (fun t => fderiv ℝ f (line t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    simpa using hcder.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (line t) := by
    have hs : ∀ᶠ y in 𝓝 (line 0), ContDiffAt ℝ 2 f y := by
      simpa only [hline0] using hf.eventually (by norm_num)
    exact hline.continuousAt.eventually hs
  have hfirst : deriv k =ᶠ[𝓝 (0 : ℝ)] (fun t => fderiv ℝ f (line t) v) := by
    filter_upwards [hnear] with t ht
    exact (ht.differentiableAt (by norm_num)).deriv_comp_add_smul
  have hvalue : deriv (deriv k) 0 = fderiv ℝ (fderiv ℝ f) x v v :=
    hfirst.deriv_eq.trans hsecond.deriv
  rw [← hvalue]
  exact localMax_deriv_deriv_nonpos hkmax hkcont

end
end TightVer401


