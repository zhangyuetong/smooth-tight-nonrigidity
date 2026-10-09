import TightVer401.RevolutionEndGaussImage
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TightVer401
noncomputable section
open Set Filter OAI.SmoothLocal.Geometry
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (Module.finrank ℝ Ambient = 2 + 1) := ⟨by simp [Ambient]⟩

theorem revolutionComplexArg_contDiffAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z :=
    (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have h := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using h

theorem revolutionComplexAngle_contMDiffAt {z : ℂ} (hz : z ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun x : ℂ => periodProjection (2 * Real.pi) x.arg) z := by
  by_cases hs : z ∈ Complex.slitPlane
  · exact (periodProjection_contMDiff (2 * Real.pi) z.arg).comp z
      (revolutionComplexArg_contDiffAt hs).contMDiffAt
  · have hs' : -z ∈ Complex.slitPlane := by
      replace hs := Complex.mem_slitPlane_iff.mpr.mt hs
      push Not at hs
      apply Or.inl
      rw [Complex.neg_re, neg_pos]
      exact hs.1.lt_of_ne fun h0 => hz (Complex.ext h0 hs.2)
    have harg : ContDiffAt ℝ ∞ (fun x : ℂ => (-x).arg - Real.pi) z :=
      ((revolutionComplexArg_contDiffAt hs').comp z contDiffAt_id.neg).sub contDiffAt_const
    have hproj : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
        (fun x : ℂ => periodProjection (2 * Real.pi) ((-x).arg - Real.pi)) z :=
      (periodProjection_contMDiff (2 * Real.pi) ((-z).arg - Real.pi)).comp z harg.contMDiffAt
    apply hproj.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with x hx
    change (x.arg : Real.Angle) = (((-x).arg - Real.pi : ℝ) : Real.Angle)
    rw [Real.Angle.coe_sub]
    exact eq_sub_iff_add_eq.mpr (Complex.arg_neg_coe_angle hx).symm

def revolutionGaussHorizontal (n : Ambient) : ℂ :=
  ⟨-n 0, -n 1⟩

theorem revolutionGaussHorizontal_contDiff :
    ContDiff ℝ ∞ revolutionGaussHorizontal := by
  let A : Ambient →L[ℝ] ℂ :=
    -(Complex.ofRealCLM.comp (EuclideanSpace.proj 0)) -
      Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj 1))
  have he : (A : Ambient → ℂ) = revolutionGaussHorizontal := by
    funext n
    apply Complex.ext <;> simp [A, revolutionGaussHorizontal]
  rw [← he]
  exact A.contDiff

theorem revolutionGaussHorizontal_ne_zero (n : RoundSphere)
    (hn : n.val 2 ∈ Ioo (0 : ℝ) 1) : revolutionGaussHorizontal n.val ≠ 0 := by
  intro he
  have h0 := congrArg Complex.re he
  have h1 := congrArg Complex.im he
  change -n.val 0 = 0 at h0
  change -n.val 1 = 0 at h1
  have hsq := revolutionSphere_horizontal_sq n
  have h00 := neg_eq_zero.mp h0
  have h11 := neg_eq_zero.mp h1
  rw [h00, h11] at hsq
  nlinarith [hn.1, hn.2]

theorem revolutionGaussAngle_contMDiffAt (n : RoundSphere)
    (hn : n.val 2 ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ revolutionGaussAngle n := by
  have hh : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞
      (fun s : RoundSphere => revolutionGaussHorizontal s.val) n :=
    revolutionGaussHorizontal_contDiff.contMDiff.contMDiffAt.comp n (contMDiff_coe_sphere n)
  have harg := revolutionComplexAngle_contMDiffAt (revolutionGaussHorizontal_ne_zero n hn)
  have h : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun s : RoundSphere => periodProjection (2 * Real.pi)
        (revolutionGaussHorizontal s.val).arg) n :=
    ContMDiffAt.comp (f := fun s : RoundSphere => revolutionGaussHorizontal s.val)
      (g := fun z : ℂ => periodProjection (2 * Real.pi) z.arg) n harg hh
  exact h

end
end TightVer401
