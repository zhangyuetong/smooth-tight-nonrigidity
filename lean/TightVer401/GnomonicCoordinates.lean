import TightVer401.PlanarSupportForms
import TightVer401.SphereSupportManifoldGeometry

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped ContDiff Topology RealInnerProductSpace Matrix Manifold

local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

def gnomonicInverse (u : Ambient) : Coord := ![u 0 / u 2, u 1 / u 2]

def gnomonicPoint (p : Coord) : RoundSphere := ⟨planarUnitNormal p, by
  have h := planarUnitNormal_unit p
  rw [real_inner_self_eq_norm_sq] at h
  have hn : ‖planarUnitNormal p‖ = 1 := by nlinarith [norm_nonneg (planarUnitNormal p)]
  simpa using hn⟩

theorem gnomonicWeight_contDiff : ContDiff ℝ ∞ planarWeight := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hpos : 0 < 1 + p 0 ^ 2 + p 1 ^ 2 := by positivity
  have h0 : ContDiff ℝ ∞ (fun p : Coord => p 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ ∞ (fun p : Coord => p 1) :=
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).contDiff
  have hf : ContDiff ℝ ∞ (fun p : Coord => 1 + p 0 ^ 2 + p 1 ^ 2) :=
    (contDiff_const.add (h0.pow 2)).add (h1.pow 2)
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp p hf.contDiffAt

theorem gnomonicNormal_contDiff : ContDiff ℝ ∞ planarUnitNormal := by
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hh : ContDiff ℝ ∞ (fun p : Coord => ![p 0 / planarWeight p,
      p 1 / planarWeight p, 1 / planarWeight p]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) : Coord →L[ℝ] ℝ).contDiff.div
        gnomonicWeight_contDiff (fun p => ne_of_gt (planarWeight_pos p))
    · exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) : Coord →L[ℝ] ℝ).contDiff.div
        gnomonicWeight_contDiff (fun p => ne_of_gt (planarWeight_pos p))
    · exact contDiff_const.div gnomonicWeight_contDiff (fun p => ne_of_gt (planarWeight_pos p))
  exact E.contDiff.comp hh

theorem gnomonicPoint_contMDiff : ContMDiff 𝓘(ℝ, Coord) (𝓡 2) ∞ gnomonicPoint :=
  gnomonicNormal_contDiff.contMDiff.codRestrict_sphere (fun p => (gnomonicPoint p).property)

theorem gnomonicInverse_contDiffAt {u : Ambient} (hu : u 2 ≠ 0) :
    ContDiffAt ℝ ∞ gnomonicInverse u := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).contDiff.contDiffAt.div
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).contDiff.contDiffAt hu
  · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)).contDiff.contDiffAt.div
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).contDiff.contDiffAt hu

theorem gnomonicPoint_north (p : Coord) : 0 < (gnomonicPoint p).val 2 :=
  one_div_pos.mpr (planarWeight_pos p)

theorem gnomonic_left_inverse (p : Coord) : gnomonicInverse (planarUnitNormal p) = p := by
  have hw := ne_of_gt (planarWeight_pos p)
  ext i
  fin_cases i <;> simp [gnomonicInverse, planarUnitNormal] <;> field_simp

theorem gnomonic_right_inverse {q : RoundSphere} (hq : 0 < q.val 2) :
    gnomonicPoint (gnomonicInverse q.val) = q := by
  have hq2 : q.val 2 ≠ 0 := ne_of_gt hq
  have hs : q.val 0 ^ 2 + q.val 1 ^ 2 + q.val 2 ^ 2 = 1 := by
    have h : inner ℝ q.val q.val = 1 := by rw [real_inner_self_eq_norm_sq, roundSphere_norm, one_pow]
    rw [PiLp.inner_apply] at h
    simp [Fin.sum_univ_succ, pow_two] at h
    nlinarith [h]
  have hw : planarWeight (gnomonicInverse q.val) = 1 / q.val 2 := by
    have hsq := planarWeight_sq (gnomonicInverse q.val)
    change planarWeight (gnomonicInverse q.val) ^ 2 =
      1 + (q.val 0 / q.val 2) ^ 2 + (q.val 1 / q.val 2) ^ 2 at hsq
    have hmul : planarWeight (gnomonicInverse q.val) ^ 2 * q.val 2 ^ 2 = 1 := by
      field_simp [hq2] at hsq
      nlinarith [hs, hsq]
    have hp := planarWeight_pos (gnomonicInverse q.val)
    have hpr : planarWeight (gnomonicInverse q.val) * q.val 2 = 1 := by
      nlinarith [mul_pos hp hq]
    apply (eq_div_iff hq2).mpr
    exact hpr
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp only [gnomonicPoint, planarUnitNormal, WithLp.ofLp_toLp] <;>
    rw [hw] <;> simp [gnomonicInverse] <;> field_simp [hq2]

def gnomonicChart : OpenPartialHomeomorph Coord RoundSphere where
  toFun := gnomonicPoint
  invFun := fun q => gnomonicInverse q.val
  source := univ
  target := {q | 0 < q.val 2}
  map_source' := fun p _ => gnomonicPoint_north p
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun p _ => gnomonic_left_inverse p
  right_inv' := fun _ hq => gnomonic_right_inverse hq
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuous.comp continuous_subtype_val)
  continuousOn_toFun := gnomonicPoint_contMDiff.continuous.continuousOn
  continuousOn_invFun := by
    intro q hq
    exact ((gnomonicInverse_contDiffAt (ne_of_gt hq)).continuousAt.comp
      continuous_subtype_val.continuousAt).continuousWithinAt

theorem gnomonicNormal_differential_injective (p : Coord) :
    Function.Injective (fderiv ℝ planarUnitNormal p) := by
  have hi := gnomonicInverse_contDiffAt (u := planarUnitNormal p)
    (ne_of_gt (gnomonicPoint_north p))
  have hc := hi.differentiableAt (by simp) |>.hasFDerivAt.comp p
    (gnomonicNormal_contDiff.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have he : (fun p => gnomonicInverse (planarUnitNormal p)) = id := funext gnomonic_left_inverse
  change HasFDerivAt (fun p => gnomonicInverse (planarUnitNormal p)) _ p at hc
  rw [he] at hc
  have hd : (fderiv ℝ gnomonicInverse (planarUnitNormal p)).comp
      (fderiv ℝ planarUnitNormal p) = ContinuousLinearMap.id ℝ Coord := by
    rw [← hc.fderiv]
    exact (hasFDerivAt_id p).fderiv
  intro v z hvz
  have h := congrArg (fderiv ℝ gnomonicInverse (planarUnitNormal p)) hvz
  change ((fderiv ℝ gnomonicInverse (planarUnitNormal p)).comp (fderiv ℝ planarUnitNormal p)) v =
    ((fderiv ℝ gnomonicInverse (planarUnitNormal p)).comp (fderiv ℝ planarUnitNormal p)) z at h
  simpa only [hd, ContinuousLinearMap.id_apply] using h

theorem gnomonicInverse_contMDiffAt {q : RoundSphere} (hq : 0 < q.val 2) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, Coord) ∞ (fun q : RoundSphere => gnomonicInverse q.val) q :=
  (gnomonicInverse_contDiffAt (ne_of_gt hq)).contMDiffAt.comp q (contMDiff_coe_sphere q)

end
end TightVer401
