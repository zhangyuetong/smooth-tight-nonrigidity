import TightVer401.MomentControlBump
import Mathlib.Analysis.Convex.Deriv

/-! A constructed interior bump makes an even strictly concave meridian
asymmetric while preserving both end collars. The amplitude is obtained from
actual compact bounds on the baseline and bump second derivatives. -/
namespace TightVer401
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

private theorem parabolicConvexClosure_add_bump_second_deriv
    {U : Set ℝ} (hU : IsOpen U) {r b : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r U) (hb : ContDiff ℝ ∞ b) (ε z : ℝ) (hz : z ∈ U) :
    deriv (deriv (fun x => r x + ε * b x)) z =
      deriv (deriv r) z + ε * deriv (deriv b) z := by
  have hr₁ := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hr |>.2
  have hb₁ := contDiff_infty_iff_deriv.mp hb |>.2
  have he : deriv (fun x => r x + ε * b x) =ᶠ[𝓝 z]
      (fun x => deriv r x + ε * deriv b x) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact (((hr.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt.add
      ((hb.differentiable (by simp) x).hasDerivAt.const_mul ε)).deriv
  rw [he.deriv_eq]
  exact (((hr₁.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasDerivAt.add
    ((hb₁.differentiable (by simp) z).hasDerivAt.const_mul ε)).deriv

/-- Construct a nonnegative compactly supported perturbation, with a derived
positive amplitude, preserving actual strict concavity and both end collars.
Evenness is required only on the actual closed meridian interval. -/
theorem exists_parabolicConvexClosure_asymmetric_perturbation
    {h : ℝ} (hh : 0 < h) {r0 : ℝ → ℝ}
    (hc : ContinuousOn r0 (Icc (-h) h))
    (hs : ContDiffOn ℝ ∞ r0 (Ioo (-h) h))
    (hn : ∀ z ∈ Ioo (-h) h, deriv (deriv r0) z < 0)
    (heven : ∀ z ∈ Icc (-h) h, r0 (-z) = r0 z) :
    ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-h) h) ∧
      ContDiffOn ℝ ∞ r (Ioo (-h) h) ∧
      (∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0) ∧
      StrictConcaveOn ℝ (Icc (-h) h) r ∧
      (∀ z, r0 z ≤ r z) ∧
      (∀ z, z ≤ h / 4 ∨ 3 * h / 4 ≤ z → r z = r0 z) ∧
      ∃ z ∈ Ioo 0 h, r (-z) ≠ r z := by
  let β := momentControlBump (h / 2) (h / 4) (by positivity : 0 < h / 4)
  let b : ℝ → ℝ := β
  let K : Set ℝ := Icc (h / 4) (3 * h / 4)
  have hK : IsCompact K := isCompact_Icc
  have hKU : K ⊆ Ioo (-h) h := by
    intro z hz
    dsimp [K] at hz
    constructor <;> linarith [hz.1, hz.2]
  have hb : ContDiff ℝ ∞ b := β.contDiff
  have hb₁ := contDiff_infty_iff_deriv.mp hb |>.2
  have hb₂ := contDiff_infty_iff_deriv.mp hb₁ |>.2
  have hr₁ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hs |>.2
  have hr₂ := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hr₁ |>.2
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le'
    (hr₂.continuousOn.mono hKU).neg (fun z hz => neg_pos.mpr (hn z (hKU hz)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hb₂.continuous.continuousOn
  let D := max C 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ε, hε, hεD⟩ := exists_pos_mul_lt hm D
  let r : ℝ → ℝ := fun z => r0 z + ε * b z
  have hrc : ContinuousOn r (Icc (-h) h) :=
    hc.add (hb.continuous.continuousOn.const_mul ε)
  have hrs : ContDiffOn ℝ ∞ r (Ioo (-h) h) :=
    hs.add ((contDiff_const.mul hb).contDiffOn)
  have hts : tsupport b = K := by
    rw [show tsupport b = closedBall (h / 2) (h / 4) from β.tsupport_eq,
      Real.closedBall_eq_Icc]
    dsimp [K]
    congr 1 <;> ring
  have hrn : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0 := by
    intro z hz
    rw [parabolicConvexClosure_add_bump_second_deriv isOpen_Ioo hs hb ε z hz]
    by_cases hzK : z ∈ K
    · have hbase := hmin z hzK
      change m ≤ -deriv (deriv r0) z at hbase
      have hbound : deriv (deriv b) z ≤ D := by
        have hbnd : |deriv (deriv b) z| ≤ C := by
          simpa only [Real.norm_eq_abs] using hC z hzK
        have hCD : C ≤ D := by dsimp [D]; linarith [le_max_left C 0]
        exact (le_abs_self _).trans (hbnd.trans hCD)
      have hmul := mul_le_mul_of_nonneg_left hbound hε.le
      have hεD' : ε * D < m := by simpa only [mul_comm] using hεD
      linarith
    · have hzts : z ∉ tsupport (deriv b) := by
        intro hmem
        apply hzK
        rw [← hts]
        exact tsupport_deriv_subset hmem
      rw [deriv_of_notMem_tsupport hzts, mul_zero, add_zero]
      exact hn z hz
  have hrconc : StrictConcaveOn ℝ (Icc (-h) h) r := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc (-h) h) hrc
    intro z hz
    have hz' : z ∈ Ioo (-h) h := by simpa only [interior_Icc] using hz
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hrn z hz'
  have hbzero : ∀ z, z ≤ h / 4 ∨ 3 * h / 4 ≤ z → b z = 0 := by
    intro z hz
    apply Function.notMem_support.mp
    rw [show Function.support b = ball (h / 2) (h / 4) from β.support_eq,
      Real.ball_eq_Ioo]
    intro hmem
    rcases hz with hz | hz <;> linarith [hmem.1, hmem.2]
  have heq : ∀ z, z ≤ h / 4 ∨ 3 * h / 4 ≤ z → r z = r0 z := by
    intro z hz
    simp [r, hbzero z hz]
  have hbcenter : b (h / 2) = 1 := β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le)
  have hbneg : b (-(h / 2)) = 0 := hbzero _ (Or.inl (by linarith))
  refine ⟨r, hrc, hrs, hrn, hrconc, ?_, heq, h / 2, ⟨by linarith, by linarith⟩, ?_⟩
  · intro z
    have hbz : 0 ≤ b z := β.nonneg
    dsimp [r]
    exact le_add_of_nonneg_right (mul_nonneg hε.le hbz)
  · have hev := heven (h / 2) ⟨by linarith, by linarith⟩
    dsimp [r]
    rw [hbneg, hbcenter, hev]
    intro he
    linarith

end
end TightVer401
