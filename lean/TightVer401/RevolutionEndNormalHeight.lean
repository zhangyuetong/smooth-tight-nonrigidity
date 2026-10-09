import TightVer401.RevolutionEndGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def revolutionNormalHeight (q : ℝ → ℝ) (z : ℝ) : ℝ := deriv q z / revolutionWeight (deriv q z)

theorem revolutionEndNormal_height (q : ℝ → ℝ) (p : Coord) :
    revolutionEndNormal q p 2 = revolutionNormalHeight q (p 1) := by
  simp [revolutionEndNormal, revolutionRadial, revolutionAxis, revolutionNormalHeight]

theorem revolutionWeight_hasDerivAt (s : ℝ) :
    HasDerivAt revolutionWeight (s / revolutionWeight s) s := by
  have he : 1 + s^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + s^2)
  convert! (((hasDerivAt_id s).pow 2).const_add 1).sqrt he using 1
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one, revolutionWeight]
  field_simp
  <;> ring

theorem revolution_ratio_hasDerivAt (s : ℝ) :
    HasDerivAt (fun t => t / revolutionWeight t) (1 / revolutionWeight s^3) s := by
  have hw := ne_of_gt (revolutionWeight_pos s)
  convert! (hasDerivAt_id s).div (revolutionWeight_hasDerivAt s) hw using 1
  simp only [id_eq]
  field_simp [hw]
  nlinarith [revolutionWeight_sq s]

theorem revolutionNormalHeight_hasDerivAt {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (z : ℝ) :
    HasDerivAt (revolutionNormalHeight q)
      (deriv (deriv q) z / revolutionWeight (deriv q z)^3) z := by
  have hqd := (contDiff_infty_iff_deriv.mp hq).2
  have h := (revolution_ratio_hasDerivAt (deriv q z)).comp z (hqd.differentiable (by simp) z).hasDerivAt
  convert! h using 1
  ring

theorem revolutionNormalHeight_strictMonoOn {q : ℝ → ℝ} {H : ℝ}
    (hq : ContDiff ℝ ∞ q) (hconvex : ∀ z ∈ Ici H, 0 < deriv (deriv q) z) :
    StrictMonoOn (revolutionNormalHeight q) (Ici H) := by
  have hc : Continuous (revolutionNormalHeight q) :=
    (show Differentiable ℝ (revolutionNormalHeight q) from
      fun z => (revolutionNormalHeight_hasDerivAt hq z).differentiableAt).continuous
  apply strictMonoOn_of_deriv_pos (convex_Ici H) hc.continuousOn
  intro z hz
  rw [(revolutionNormalHeight_hasDerivAt hq z).deriv]
  exact div_pos (hconvex z (interior_subset hz)) (pow_pos (revolutionWeight_pos _) 3)

theorem revolution_ratio_tendsto :
    Tendsto (fun s : ℝ => s / revolutionWeight s) atTop (𝓝 1) := by
  have henergy : Tendsto (fun s : ℝ => 1 + s^2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide))
  have hinv : Tendsto (fun s : ℝ => (1 + s^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp henergy
  have hinner : Tendsto (fun s : ℝ => 1 - (1 + s^2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hinner
  have heq : (fun s : ℝ => s / revolutionWeight s) =ᶠ[atTop]
      (fun s => Real.sqrt (1 - (1 + s^2)⁻¹)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hsq : (s / revolutionWeight s)^2 = 1 - (1 + s^2)⁻¹ := by
      rw [div_pow, revolutionWeight_sq]
      field_simp [ne_of_gt (by positivity : 0 < 1 + s^2)]
      ring
    rw [← hsq, Real.sqrt_sq (div_nonneg hs.le (revolutionWeight_pos s).le)]
  simpa using hsqrt.congr' heq.symm

theorem revolutionNormalHeight_tendsto {q : ℝ → ℝ}
    (hslope : Tendsto (deriv q) atTop atTop) :
    Tendsto (revolutionNormalHeight q) atTop (𝓝 1) :=
  revolution_ratio_tendsto.comp hslope

theorem revolutionNormalHeight_mem_Ioo {q : ℝ → ℝ} {z : ℝ} (hslope : 0 < deriv q z) :
    revolutionNormalHeight q z ∈ Ioo 0 1 := by
  have hw := revolutionWeight_pos (deriv q z)
  have hlt : deriv q z < revolutionWeight (deriv q z) := by nlinarith [revolutionWeight_sq (deriv q z)]
  exact ⟨div_pos hslope hw, (div_lt_one hw).mpr hlt⟩

end
end TightVer401
