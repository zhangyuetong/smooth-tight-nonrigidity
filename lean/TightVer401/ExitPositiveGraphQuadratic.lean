import TightVer401.ExitPositiveGraphProfile
import TightVer401.ExitPositiveGraphUniform

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix
set_option backward.isDefEq.respectTransparency false

def exitGraphPoint (v : ℝ → ℝ) (p : Coord) : Coord := ![p 0, p 1 * v (p 0)]

def exitGraphQuadratic (ℓ M N : Coord → ℝ) (v : ℝ → ℝ) (p : Coord) : ℝ :=
  ℓ (exitGraphPoint v p) + 2 * (p 1 * deriv v (p 0)) * M (exitGraphPoint v p) +
    (p 1 * deriv v (p 0))^2 * N (exitGraphPoint v p)

theorem exitGraphPoint_contDiff {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (exitGraphPoint v) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact (contDiff_apply ℝ ℝ 1).mul (hv.comp (contDiff_apply ℝ ℝ 0))

theorem exitGraphQuadratic_contDiffOn {ℓ M N : Coord → ℝ} {v : ℝ → ℝ} {U : Set Coord}
    (hℓ : ContDiffOn ℝ ∞ ℓ U) (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hv : ContDiff ℝ ∞ v) :
    ContDiffOn ℝ ∞ (exitGraphQuadratic ℓ M N v) ((exitGraphPoint v) ⁻¹' U) := by
  have hg := exitGraphPoint_contDiff hv
  have hℓg := hℓ.comp hg.contDiffOn (fun _ h => h)
  have hMg := hM.comp hg.contDiffOn (fun _ h => h)
  have hNg := hN.comp hg.contDiffOn (fun _ h => h)
  have hvd := (contDiff_infty_iff_deriv.mp hv).2
  have hs : ContDiff ℝ ∞ (fun p : Coord => p 1 * deriv v (p 0)) :=
    (contDiff_apply ℝ ℝ 1).mul (hvd.comp (contDiff_apply ℝ ℝ 0))
  exact (hℓg.add ((contDiffOn_const.mul hs.contDiffOn).mul hMg)).add
    ((hs.pow 2).contDiffOn.mul hNg)

theorem exitGraphQuadratic_matrix (ℓ M N : Coord → ℝ) (v : ℝ → ℝ) (r δ : ℝ) :
    exitGraphQuadratic ℓ M N v ![r, δ] =
      dotProduct (![1, δ * deriv v r] : Coord)
        (!![ℓ ![r, δ * v r], M ![r, δ * v r];
          M ![r, δ * v r], N ![r, δ * v r]] *ᵥ ![1, δ * deriv v r]) := by
  simp [exitGraphQuadratic, exitGraphPoint, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem exitGraphQuadratic_hasDerivAt_zero {ℓ M N : Coord → ℝ} {v : ℝ → ℝ}
    {U : Set Coord} {r : ℝ} (hU : IsOpen U)
    (hℓ : ContDiffOn ℝ ∞ ℓ U) (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hr : (![r, 0] : Coord) ∈ U) :
    HasDerivAt (fun δ => exitGraphQuadratic ℓ M N v ![r, δ])
      (v r * coordPartial 1 ℓ ![r, 0] + 2 * deriv v r * M ![r, 0]) 0 := by
  have hparam : HasDerivAt (fun δ : ℝ => δ * v r) (v r) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (v r)
  have hr0 : (![r, (0 : ℝ) * v r] : Coord) ∈ U := by simpa using hr
  have hℓ' := (exitGraph_slice_hasDerivAt hU hℓ hr0).comp (0 : ℝ) hparam
  have hM' := (exitGraph_slice_hasDerivAt hU hM hr0).comp (0 : ℝ) hparam
  have hN' := (exitGraph_slice_hasDerivAt hU hN hr0).comp (0 : ℝ) hparam
  have hs : HasDerivAt (fun δ : ℝ => δ * deriv v r) (deriv v r) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (deriv v r)
  have h := hℓ'.add ((hs.const_mul 2).mul hM') |>.add ((hs.pow 2).mul hN')
  convert! h using 1
  simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply, zero_mul, add_zero,
    mul_zero, pow_two, mul_one, zero_add]
  ring

theorem exitGraphQuadratic_seam {ℓ M N : Coord → ℝ} {v : ℝ → ℝ} {r : ℝ}
    (hzero : ℓ ![r, 0] = 0) : exitGraphQuadratic ℓ M N v ![r, 0] = 0 := by
  simpa [exitGraphQuadratic, exitGraphPoint] using hzero

theorem exitGraphQuadratic_transverse_seam {ℓ M N : Coord → ℝ} {v a b : ℝ → ℝ}
    {U : Set Coord} {r m : ℝ} (hU : IsOpen U)
    (hℓ : ContDiffOn ℝ ∞ ℓ U) (hM : ContDiffOn ℝ ∞ M U) (hN : ContDiffOn ℝ ∞ N U)
    (hv : ContDiff ℝ ∞ v) (hr : (![r, 0] : Coord) ∈ U)
    (hMr : M ![r, 0] = a r)
    (hℓt : coordPartial 1 ℓ ![r, 0] = -2 * a r * b r)
    (hode : deriv v r = (b r - m) * v r) :
    coordPartial 1 (exitGraphQuadratic ℓ M N v) ![r, 0] = -2 * a r * m * v r := by
  have hUg : IsOpen ((exitGraphPoint v) ⁻¹' U) := hU.preimage (exitGraphPoint_contDiff hv).continuous
  have hrg : (![r, 0] : Coord) ∈ (exitGraphPoint v) ⁻¹' U := by simpa [exitGraphPoint] using hr
  have hs := exitGraph_slice_hasDerivAt hUg (exitGraphQuadratic_contDiffOn hℓ hM hN hv) hrg
  have ht := exitGraphQuadratic_hasDerivAt_zero (v := v) hU hℓ hM hN hr
  have he := hs.unique ht
  rw [he, hMr, hℓt, hode]
  ring

end
end TightVer401
