import TightVer401.RevolutionEndGaussInverse
import OAI.Geometry.WeakMTW.Analysis.IntegralEquation

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem revolutionNormalHeight_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (revolutionNormalHeight q) := by
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have hw : ContDiff ℝ ∞ (fun z => revolutionWeight (deriv q z)) :=
    (contDiff_const.add (hqd.pow 2)).sqrt
      (fun z => ne_of_gt (by positivity : 0 < 1 + deriv q z ^ 2))
  exact hqd.div hw (fun z => ne_of_gt (revolutionWeight_pos _))

theorem revolutionNormalHeight_smooth_local_inverse {q : ℝ → ℝ} {z : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : 0 < deriv (deriv q) z) :
    ∃ (g : ℝ → ℝ) (V : Set ℝ), IsOpen V ∧ revolutionNormalHeight q z ∈ V ∧
      g (revolutionNormalHeight q z) = z ∧ ContDiffOn ℝ ∞ g V ∧
      ∀ y ∈ V, revolutionNormalHeight q (g y) = y := by
  let c := deriv (deriv q) z / revolutionWeight (deriv q z)^3
  have hc' : c ≠ 0 := ne_of_gt (div_pos hc (pow_pos (revolutionWeight_pos _) 3))
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft
    (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 c hc')
  have he : HasFDerivAt (revolutionNormalHeight q) (e : ℝ →L[ℝ] ℝ) z := by
    convert! (revolutionNormalHeight_hasDerivAt hq z).hasFDerivAt using 1
    ext v
    simp [e, c, smul_eq_mul]
  exact OAI.WeakMTWGlobalSupport.SmoothODE.exists_smooth_local_inverse
    (revolutionNormalHeight_contDiff hq) he

theorem revolutionHeightInverse_contDiffAt {q : ℝ → ℝ} {H y : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop)
    (hy : y ∈ Ioo (revolutionNormalHeight q H) 1) :
    ContDiffAt ℝ ∞ (revolutionHeightInverse (H := H) hq hslope) y := by
  let z := revolutionHeightInverse (H := H) hq hslope y
  have hz := revolutionHeightInverse_spec hq hslope ⟨hy.1.le, hy.2⟩
  have hz' : H < z := by
    apply lt_of_le_of_ne hz.1
    intro he
    rw [← he] at hz
    exact (ne_of_lt hy.1) hz.2
  obtain ⟨g, V, hV, hVy, hgy, hg, hright⟩ :=
    revolutionNormalHeight_smooth_local_inverse hq (hc z hz.1)
  rw [hz.2] at hVy hgy
  have hgc : ContinuousAt g y := (hg y hVy).contDiffAt (hV.mem_nhds hVy) |>.continuousAt
  have hge : ∀ᶠ t in 𝓝 y, H < g t := hgc.eventually (by rw [hgy]; exact lt_mem_nhds hz')
  have heq : revolutionHeightInverse (H := H) hq hslope =ᶠ[𝓝 y] g := by
    filter_upwards [hV.mem_nhds hVy, hge, isOpen_Ioo.mem_nhds hy] with t ht hgt hty
    have ht' := revolutionHeightInverse_spec hq hslope ⟨hty.1.le, hty.2⟩
    exact (revolutionNormalHeight_strictMonoOn hq hc).injOn ht'.1 hgt.le
      (ht'.2.trans (hright t ht).symm)
  exact ((hg y hVy).contDiffAt (hV.mem_nhds hVy)).congr_of_eventuallyEq heq

theorem revolutionHeightInverse_contDiffOn {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    ContDiffOn ℝ ∞ (revolutionHeightInverse (H := H) hq hslope)
      (Ioo (revolutionNormalHeight q H) 1) :=
  fun _ hy => (revolutionHeightInverse_contDiffAt hq hc hslope hy).contDiffWithinAt

end
end TightVer401
