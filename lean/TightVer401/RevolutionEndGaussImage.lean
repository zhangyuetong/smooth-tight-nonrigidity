import TightVer401.RevolutionEndGaussSmooth
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem revolutionNormalHeight_exists_preimage {q : ℝ → ℝ} {H y : ℝ}
    (hq : ContDiff ℝ ∞ q) (hslope : Tendsto (deriv q) atTop atTop)
    (hy : y ∈ Ico (revolutionNormalHeight q H) 1) :
    ∃ z ∈ Ici H, revolutionNormalHeight q z = y := by
  have he : ∀ᶠ z in atTop, y < revolutionNormalHeight q z :=
    (revolutionNormalHeight_tendsto hslope).eventually (lt_mem_nhds hy.2)
  obtain ⟨R, hR, hyR⟩ := (he.and (eventually_ge_atTop H)).exists
  have hc : Continuous (revolutionNormalHeight q) :=
    (show Differentiable ℝ (revolutionNormalHeight q) from
      fun z => (revolutionNormalHeight_hasDerivAt hq z).differentiableAt).continuous
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc hyR hc.continuousOn ⟨hy.1, hR.le⟩
  exact ⟨z, hz.1, heq⟩

theorem revolutionNormalHeight_image {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    revolutionNormalHeight q '' Ici H = Ico (revolutionNormalHeight q H) 1 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(revolutionNormalHeight_strictMonoOn hq hc).monotoneOn
      (by simp) hz hz, (revolutionNormalHeight_mem_Ioo (hs z hz)).2⟩
  · exact revolutionNormalHeight_exists_preimage hq hslope

def revolutionEndGaussCap (q : ℝ → ℝ) (H : ℝ) : Set RoundSphere :=
  {n | n.val 2 ∈ Ico (revolutionNormalHeight q H) 1}

theorem revolutionEndGauss_mem_cap {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z) (p : AddCircle (2 * Real.pi) × Ici H) :
    revolutionEndGauss q H p ∈ revolutionEndGaussCap q H := by
  change revolutionEndCircleNormal q (p.1, p.2.val) 2 ∈ Ico _ _
  rw [revolutionEndCircleNormal_height]
  exact ⟨(revolutionNormalHeight_strictMonoOn hq hc).monotoneOn
    (by simp) p.2.property p.2.property,
    (revolutionNormalHeight_mem_Ioo (hs _ p.2.property)).2⟩

theorem revolutionSphere_horizontal_sq (n : RoundSphere) :
    (n.val 0)^2 + (n.val 1)^2 + (n.val 2)^2 = 1 := by
  have hn : ‖n.val‖ = 1 := by simpa using n.property
  have he := EuclideanSpace.real_norm_sq_eq n.val
  simp only [Fin.sum_univ_three] at he
  rw [hn] at he
  nlinarith

def revolutionGaussAngle (n : RoundSphere) : AddCircle (2 * Real.pi) :=
  ((⟨-n.val 0, -n.val 1⟩ : ℂ).arg : Real.Angle)

theorem revolutionEndCircleNormal_angle {q : ℝ → ℝ} (n : RoundSphere)
    (z : ℝ) (hs : 0 < deriv q z) (hz : revolutionNormalHeight q z = n.val 2) :
    revolutionEndCircleNormal q (revolutionGaussAngle n, z) = n.val := by
  let v : ℂ := ⟨-n.val 0, -n.val 1⟩
  let w := revolutionWeight (deriv q z)
  have hw : 0 < w := revolutionWeight_pos _
  have hsq : ‖v‖^2 = 1 / w^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp only [← pow_two]
    change (-n.val 0)^2 + (-n.val 1)^2 = 1 / w^2
    have hn := revolutionSphere_horizontal_sq n
    have hh : n.val 2 = deriv q z / w := hz.symm
    rw [hh] at hn
    have hws : w^2 = 1 + (deriv q z)^2 := revolutionWeight_sq _
    field_simp [ne_of_gt hw] at hn ⊢
    nlinarith
  have hv : ‖v‖ = 1 / w := by
    have hw' : 0 < 1 / w := one_div_pos.mpr hw
    have he : ‖v‖^2 = (1 / w)^2 := by simpa [div_pow] using hsq
    nlinarith [norm_nonneg v]
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; positivity)
  apply PiLp.ext
  intro i
  fin_cases i
  · change (-1 / w) * Real.Angle.cos (v.arg : Real.Angle) +
      revolutionNormalHeight q z * 0 = n.val 0
    rw [Real.Angle.cos_coe, Complex.cos_arg hv0, hv]
    change (-1 / w) * (-n.val 0 / (1 / w)) + _ * 0 = _
    field_simp [ne_of_gt hw]
    simp
  · change (-1 / w) * Real.Angle.sin (v.arg : Real.Angle) +
      revolutionNormalHeight q z * 0 = n.val 1
    rw [Real.Angle.sin_coe, Complex.sin_arg, hv]
    change (-1 / w) * (-n.val 1 / (1 / w)) + _ * 0 = _
    field_simp [ne_of_gt hw]
    simp
  · change (-1 / w) * 0 + revolutionNormalHeight q z * 1 = n.val 2
    simpa using hz

theorem revolutionEndGauss_range {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hc : ∀ z ∈ Ici H, 0 < deriv (deriv q) z)
    (hs : ∀ z ∈ Ici H, 0 < deriv q z)
    (hslope : Tendsto (deriv q) atTop atTop) :
    range (revolutionEndGauss q H) = revolutionEndGaussCap q H := by
  apply Subset.antisymm
  · rintro n ⟨p, rfl⟩
    exact revolutionEndGauss_mem_cap hq hc hs p
  · intro n hn
    obtain ⟨z, hz, he⟩ := revolutionNormalHeight_exists_preimage hq hslope hn
    have hθ := revolutionEndCircleNormal_angle n z (hs z hz) he
    exact ⟨(revolutionGaussAngle n, ⟨z, hz⟩), Subtype.ext hθ⟩

end
end TightVer401
