import TightVer401.ParabolicConvexClosureGeometry
import TightVer401.ParabolicConvexClosureMeridianGerms
import TightVer401.RevolutionEndHeightInverseSmooth
import Mathlib.Topology.Order.MonotoneContinuity

/-! Actual scalar outward Gauss height of a concave parabolic meridian.

Interior smoothness and negative actual second derivative prove strict
monotonicity. Literal upper/lower square-root radius germs prove the two
one-sided height limits by their actual differentiated germs. Intermediate
values then prove the whole open-interval bijection; neither the endpoint
slopes nor surjectivity, inverse, or sphere Gauss conclusions are inputs.
The interval homeomorphism is constructed from this proved bijection.
-/

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

def parabolicConvexClosureGaussHeight (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  -revolutionNormalHeight r z

theorem parabolicConvexClosure_gaussHeight_germ {q r : ℝ → ℝ} {z : ℝ}
    (h : q =ᶠ[𝓝 z] r) :
    parabolicConvexClosureGaussHeight q =ᶠ[𝓝 z] parabolicConvexClosureGaussHeight r := by
  filter_upwards [h.deriv] with x hx
  simp only [parabolicConvexClosureGaussHeight, revolutionNormalHeight, hx]

theorem parabolicConvexClosure_gaussHeight_contDiffOn {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) :
    ContDiffOn ℝ ∞ (parabolicConvexClosureGaussHeight r) U := by
  intro z hz
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hz
  exact (((revolutionNormalHeight_contDiff hq).neg).contDiffAt.congr_of_eventuallyEq
    (parabolicConvexClosure_gaussHeight_germ hg).symm).contDiffWithinAt

theorem parabolicConvexClosure_gaussHeight_hasDerivAt {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) {z : ℝ} (hz : z ∈ U) :
    HasDerivAt (parabolicConvexClosureGaussHeight r)
      (-deriv (deriv r) z / revolutionWeight (deriv r z)^3) z := by
  obtain ⟨q, hq, hg⟩ := parabolicConvexClosure_profile_extension hU hr hz
  have hd := (revolutionNormalHeight_hasDerivAt hq z).neg
  rw [hg.deriv.deriv_eq, hg.deriv_eq] at hd
  simpa only [parabolicConvexClosureGaussHeight, neg_div] using
    hd.congr_of_eventuallyEq (parabolicConvexClosure_gaussHeight_germ hg).symm

theorem parabolicConvexClosure_gaussHeight_deriv {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) {z : ℝ} (hz : z ∈ U) :
    deriv (parabolicConvexClosureGaussHeight r) z =
      -deriv (deriv r) z / revolutionWeight (deriv r z)^3 :=
  (parabolicConvexClosure_gaussHeight_hasDerivAt hU hr hz).deriv

theorem parabolicConvexClosure_gaussHeight_deriv_pos {U : Set ℝ} (hU : IsOpen U)
    {r : ℝ → ℝ} (hr : ContDiffOn ℝ ∞ r U) {z : ℝ} (hz : z ∈ U)
    (hneg : deriv (deriv r) z < 0) :
    0 < deriv (parabolicConvexClosureGaussHeight r) z := by
  rw [parabolicConvexClosure_gaussHeight_deriv hU hr hz]
  exact div_pos (neg_pos.mpr hneg) (pow_pos (revolutionWeight_pos _) 3)

/-- The scalar function is exactly the actual coordinate outward normal's height. -/
theorem parabolicConvexClosureOutwardNormal_height (r : ℝ → ℝ) (p : Coord) :
    parabolicConvexClosureOutwardNormal r p 2 = parabolicConvexClosureGaussHeight r (p 1) := by
  simp [parabolicConvexClosureOutwardNormal, parabolicConvexClosureGaussHeight,
    revolutionEndNormal_height]

theorem parabolicConvexClosure_gaussHeight_strictMonoOn {h : ℝ} {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0) :
    StrictMonoOn (parabolicConvexClosureGaussHeight r) (Ioo (-h) h) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-h) h)
    (parabolicConvexClosure_gaussHeight_contDiffOn isOpen_Ioo hr).continuousOn
  intro z hz
  rw [(parabolicConvexClosure_gaussHeight_hasDerivAt isOpen_Ioo hr (interior_subset hz)).deriv]
  exact div_pos (neg_pos.mpr (hneg z (interior_subset hz)))
    (pow_pos (revolutionWeight_pos _) 3)

/-- Every actual finite meridian slope gives an outward height strictly between the poles. -/
theorem parabolicConvexClosure_gaussHeight_mem (r : ℝ → ℝ) (z : ℝ) :
    parabolicConvexClosureGaussHeight r z ∈ Ioo (-1 : ℝ) 1 := by
  let d := deriv r z
  let w := revolutionWeight d
  have hw : 0 < w := revolutionWeight_pos d
  have hsq : w^2 = 1 + d^2 := revolutionWeight_sq d
  have habs : |d| < w := by nlinarith [sq_abs d, abs_nonneg d]
  have hlt := abs_lt.mp habs
  change -1 < -(d / w) ∧ -(d / w) < 1
  rw [← neg_div]
  constructor
  · apply (lt_div_iff₀ hw).mpr
    nlinarith [hlt.2]
  · apply (div_lt_iff₀ hw).mpr
    nlinarith [hlt.1]

theorem parabolicConvexClosure_gaussHeight_mapsTo (r : ℝ → ℝ) (h : ℝ) :
    MapsTo (parabolicConvexClosureGaussHeight r) (Ioo (-h) h) (Ioo (-1 : ℝ) 1) :=
  fun z _ => parabolicConvexClosure_gaussHeight_mem r z

/-- Actual derivative of the literal upper radius germ. -/
theorem parabolicConvexClosure_upperRadius_deriv (RN mu h : ℝ) (hmu : 0 < mu)
    {z : ℝ} (hz : z < h) :
    deriv (parabolicClosureUpperRadius RN mu h) z =
      -mu / Real.sqrt (2 * mu * (h - z)) := by
  have hdisc : 0 < 2 * mu * (h - z) := mul_pos (by positivity) (sub_pos.mpr hz)
  have hs : Real.sqrt (2 * mu * (h - z)) ≠ 0 := (Real.sqrt_pos.mpr hdisc).ne'
  have hd := (((hasDerivAt_id z).const_sub h).const_mul (2 * mu)).sqrt hdisc.ne'
  have hd' := hd.const_add RN
  have he : HasDerivAt (parabolicClosureUpperRadius RN mu h)
      (-mu / Real.sqrt (2 * mu * (h - z))) z := by
    convert hd' using 1 <;> try rfl
    simp only [id_eq, mul_neg, mul_one]
    field_simp [hs]
    <;> ring
  exact he.deriv

/-- Algebraic normalization of the actual upper slope, retaining its sign. -/
theorem parabolicConvexClosure_upperGaussHeight (RN mu h : ℝ) (hmu : 0 < mu)
    {z : ℝ} (hz : z < h) :
    parabolicConvexClosureGaussHeight (parabolicClosureUpperRadius RN mu h) z =
      mu / Real.sqrt (mu^2 + 2 * mu * (h - z)) := by
  let s := Real.sqrt (2 * mu * (h - z))
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (by positivity) (sub_pos.mpr hz))
  have hss : s^2 = 2 * mu * (h - z) := Real.sq_sqrt (by positivity)
  let w := revolutionWeight (-mu / s)
  have hw : 0 < w := revolutionWeight_pos _
  have hww : w^2 = 1 + (-mu / s)^2 := revolutionWeight_sq _
  have hroot : Real.sqrt (mu^2 + 2 * mu * (h - z)) = s * w := by
    have hp : 0 < mu^2 + 2 * mu * (h - z) := by positivity
    have hpow : (s * w)^2 = mu^2 + 2 * mu * (h - z) := by
      rw [mul_pow, hww, ← hss]
      field_simp [hs.ne']
      <;> ring
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (mu^2 + 2 * mu * (h - z)),
      mul_pos hs hw]
  change -(deriv (parabolicClosureUpperRadius RN mu h) z /
    revolutionWeight (deriv (parabolicClosureUpperRadius RN mu h) z)) = _
  rw [parabolicConvexClosure_upperRadius_deriv RN mu h hmu hz, hroot]
  change -((-mu / s) / w) = mu / (s * w)
  field_simp [hs.ne', hw.ne']
  <;> ring

theorem parabolicConvexClosure_gaussHeight_reflect (r : ℝ → ℝ) (z : ℝ) :
    parabolicConvexClosureGaussHeight (fun x => r (-x)) z =
      -parabolicConvexClosureGaussHeight r (-z) := by
  simp [parabolicConvexClosureGaussHeight, revolutionNormalHeight, deriv_comp_neg,
    revolutionWeight, neg_div]

theorem parabolicConvexClosure_gaussHeight_upper_limit {RN mu h δ : ℝ}
    (hmu : 0 < mu) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hupper : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h)) :
    Tendsto (parabolicConvexClosureGaussHeight r) (𝓝[<] h) (𝓝 1) := by
  have he : parabolicConvexClosureGaussHeight r =ᶠ[𝓝[<] h]
      (fun z => mu / Real.sqrt (mu^2 + 2 * mu * (h - z))) := by
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show h - δ < h by linarith)),
      self_mem_nhdsWithin] with z hzl hzh
    have hg : r =ᶠ[𝓝 z] parabolicClosureUpperRadius RN mu h := by
      filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (h - δ) h from ⟨hzl, hzh⟩)] with x hx
      exact hupper ⟨hx.1.le, hx.2.le⟩
    rw [(parabolicConvexClosure_gaussHeight_germ hg).self_of_nhds]
    exact parabolicConvexClosure_upperGaussHeight RN mu h hmu hzh
  have hc : ContinuousAt (fun z : ℝ => mu / Real.sqrt (mu^2 + 2 * mu * (h - z))) h :=
    continuousAt_const.div (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))))
      (by simp [Real.sqrt_sq_eq_abs, abs_of_pos hmu, hmu.ne'])
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio h))
  simpa [Real.sqrt_sq_eq_abs, abs_of_pos hmu, hmu.ne'] using ht.congr' he.symm

theorem parabolicConvexClosure_gaussHeight_lower_limit {RN mu h δ : ℝ}
    (hmu : 0 < mu) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hlower : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z))
      (Icc (-h) (-h + δ))) :
    Tendsto (parabolicConvexClosureGaussHeight r) (𝓝[>] (-h)) (𝓝 (-1)) := by
  have he : parabolicConvexClosureGaussHeight r =ᶠ[𝓝[>] (-h)]
      (fun z => -(mu / Real.sqrt (mu^2 + 2 * mu * (h + z)))) := by
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds (show -h < -h + δ by linarith)),
      self_mem_nhdsWithin] with z hzu hzl
    change -h < z at hzl
    have hg : r =ᶠ[𝓝 z] (fun x => parabolicClosureUpperRadius RN mu h (-x)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (-h) (-h + δ) from ⟨hzl, hzu⟩)] with x hx
      exact hlower ⟨hx.1.le, hx.2.le⟩
    rw [(parabolicConvexClosure_gaussHeight_germ hg).self_of_nhds,
      parabolicConvexClosure_gaussHeight_reflect,
      parabolicConvexClosure_upperGaussHeight RN mu h hmu (show -z < h by linarith)]
    simp only [sub_neg_eq_add]
  have hc : ContinuousAt (fun z : ℝ => -(mu / Real.sqrt (mu^2 + 2 * mu * (h + z)))) (-h) :=
    (continuousAt_const.div (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add (continuousAt_const.mul (continuousAt_const.add continuousAt_id))))
      (by simp [Real.sqrt_sq_eq_abs, abs_of_pos hmu, hmu.ne'])).neg
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (-h)))
  simpa [Real.sqrt_sq_eq_abs, abs_of_pos hmu, hmu.ne'] using ht.congr' he.symm

/-- Actual interval bijection, derived from the negative acceleration and prescribed germs. -/
theorem parabolicConvexClosure_gaussHeight_bijOn {RN mu h δ : ℝ}
    (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0)
    (hlower : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z))
      (Icc (-h) (-h + δ)))
    (hupper : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h)) :
    BijOn (parabolicConvexClosureGaussHeight r) (Ioo (-h) h) (Ioo (-1 : ℝ) 1) := by
  have hleft : 𝓝[>] (-h) ≤ 𝓟 (Ioo (-h) h) := by
    rw [Filter.le_principal_iff]
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show -h < h by linarith))] with z hzl hzu
    exact ⟨hzl, hzu⟩
  have hright : 𝓝[<] h ≤ 𝓟 (Ioo (-h) h) := by
    rw [Filter.le_principal_iff]
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (show -h < h by linarith))] with z hzu hzl
    exact ⟨hzl, hzu⟩
  refine ⟨parabolicConvexClosure_gaussHeight_mapsTo r h,
    (parabolicConvexClosure_gaussHeight_strictMonoOn hr hneg).injOn, ?_⟩
  exact isPreconnected_Ioo.intermediate_value_Ioo hleft hright
    (parabolicConvexClosure_gaussHeight_contDiffOn isOpen_Ioo hr).continuousOn
    (parabolicConvexClosure_gaussHeight_lower_limit hmu hδ hlower)
    (parabolicConvexClosure_gaussHeight_upper_limit hmu hδ hupper)

/-- The actual scalar interval homeomorphism, constructed from the proved bijection. -/
def parabolicConvexClosureGaussHeightHomeomorph {RN mu h δ : ℝ}
    (hmu : 0 < mu) (hh : 0 < h) (hδ : 0 < δ) {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ ∞ r (Ioo (-h) h))
    (hneg : ∀ z ∈ Ioo (-h) h, deriv (deriv r) z < 0)
    (hlower : EqOn r (fun z => parabolicClosureUpperRadius RN mu h (-z))
      (Icc (-h) (-h + δ)))
    (hupper : EqOn r (parabolicClosureUpperRadius RN mu h) (Icc (h - δ) h)) :
    Ioo (-h) h ≃ₜ Ioo (-1 : ℝ) 1 := by
  let f : Ioo (-h) h → Ioo (-1 : ℝ) 1 := fun z =>
    ⟨parabolicConvexClosureGaussHeight r z, parabolicConvexClosure_gaussHeight_mem r z⟩
  have hm : StrictMono f := fun x y hxy =>
    parabolicConvexClosure_gaussHeight_strictMonoOn hr hneg x.property y.property hxy
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨z, hz, he⟩ :=
      (parabolicConvexClosure_gaussHeight_bijOn hmu hh hδ hr hneg hlower hupper).surjOn y.property
    exact ⟨⟨z, hz⟩, Subtype.ext he⟩
  exact (StrictMono.orderIsoOfSurjective f hm hs).toHomeomorph

end
end TightVer401
