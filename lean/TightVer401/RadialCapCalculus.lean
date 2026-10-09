import TightVer401.PlanarSupportCurvature

namespace TightVer401
noncomputable section
open Set
open scoped ContDiff Topology

def radialCap (C R a r : ℝ) : ℝ := C + Real.sqrt (a ^ 2 - (R - r) ^ 2)

theorem radialCap_contDiffOn (C R a : ℝ) :
    ContDiffOn ℝ ∞ (radialCap C R a) {r | 0 < a ^ 2 - (R - r) ^ 2} := by
  apply contDiffOn_const.add
  apply (contDiff_const.sub ((contDiff_const.sub contDiff_id).pow 2)).contDiffOn.sqrt
  intro r hr
  exact ne_of_gt hr

theorem radialCap_hasDerivAt (C R a : ℝ) {r : ℝ}
    (hr : 0 < a ^ 2 - (R - r) ^ 2) :
    HasDerivAt (radialCap C R a)
      ((R - r) / Real.sqrt (a ^ 2 - (R - r) ^ 2)) r := by
  have hd := ((hasDerivAt_const r (a ^ 2)).sub
    (((hasDerivAt_id r).const_sub R).pow 2)).sqrt (ne_of_gt hr)
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq] at hd
  have hs : Real.sqrt (a ^ 2 - (R - r) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  convert hd.const_add C using 1 <;> try rfl
  field_simp
  <;> ring

theorem radialCap_deriv (C R a : ℝ) {r : ℝ}
    (hr : 0 < a ^ 2 - (R - r) ^ 2) :
    deriv (radialCap C R a) r = (R - r) / Real.sqrt (a ^ 2 - (R - r) ^ 2) :=
  (radialCap_hasDerivAt C R a hr).deriv

theorem radialCap_deriv_hasDerivAt (C R a : ℝ) {r : ℝ}
    (hr : 0 < a ^ 2 - (R - r) ^ 2) :
    HasDerivAt (deriv (radialCap C R a))
      (-(a ^ 2) / (Real.sqrt (a ^ 2 - (R - r) ^ 2)) ^ 3) r := by
  have hs : Real.sqrt (a ^ 2 - (R - r) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hw := ((hasDerivAt_const r (a ^ 2)).sub
    (((hasDerivAt_id r).const_sub R).pow 2)).sqrt (ne_of_gt hr)
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq] at hw
  have hw' : HasDerivAt (fun s => Real.sqrt (a ^ 2 - (R - s) ^ 2))
      ((R - r) / Real.sqrt (a ^ 2 - (R - r) ^ 2)) r := by
    convert hw using 1 <;> try rfl
    field_simp
    <;> ring
  have hd := ((hasDerivAt_id r).const_sub R).div hw' hs
  simp only [id_eq] at hd
  have hnear : ∀ᶠ s in 𝓝 r, 0 < a ^ 2 - (R - s) ^ 2 :=
    (continuous_const.sub ((continuous_const.sub continuous_id).pow 2)).continuousAt.eventually
      (Ioi_mem_nhds hr)
  have heq : deriv (radialCap C R a) =ᶠ[𝓝 r]
      fun s => (R - s) / Real.sqrt (a ^ 2 - (R - s) ^ 2) := by
    filter_upwards [hnear] with s hs using radialCap_deriv C R a hs
  have hsq := Real.sq_sqrt hr.le
  convert hd.congr_of_eventuallyEq heq using 1 <;> try rfl
  field_simp
  nlinarith [hsq]

theorem radialCap_second_deriv (C R a : ℝ) {r : ℝ}
    (hr : 0 < a ^ 2 - (R - r) ^ 2) :
    deriv (deriv (radialCap C R a)) r =
      -(a ^ 2) / (Real.sqrt (a ^ 2 - (R - r) ^ 2)) ^ 3 :=
  (radialCap_deriv_hasDerivAt C R a hr).deriv

end
end TightVer401
