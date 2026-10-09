import TightVer401.PeriodicRuledFrame
import TightVer401.FrameDecomposition
import TightVer401.RuledTransverseStrain

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def frameCoefficient (Y : Coord → Ambient) (V : ℝ → Ambient) : Coord → ℝ :=
  fun p => inner ℝ (Y p) (V (p 0))

theorem frameCoefficient_contDiff {Y : Coord → Ambient} {V : ℝ → Ambient}
    (hY : ContDiff ℝ ∞ Y) (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (frameCoefficient Y V) :=
  hY.inner ℝ (hV.comp (contDiff_apply ℝ ℝ (0 : Fin 2)))

theorem frameCoefficient_full_decomposition {Y : Coord → Ambient} {T E n : ℝ → Ambient}
    (hf : ∀ s, IsOrthonormalFrame (T s) (E s) (n s)) :
    ruledFullBending (frameCoefficient Y T) (frameCoefficient Y E) (frameCoefficient Y n) T E n = Y := by
  funext p
  have h := orthonormal_frame_decomposition (hf (p 0)) (Y p)
  dsimp only [ruledFullBending, ruledBending, frameCoefficient]
  calc
    _ = (inner ℝ (Y p) (T (p 0))) • T (p 0) +
        (inner ℝ (Y p) (E (p 0))) • E (p 0) +
        (inner ℝ (Y p) (n (p 0))) • n (p 0) := by module
    _ = Y p := h.symm

theorem supported_ruled_vector_transverse_zero {L : ℝ} (d : PeriodicRuledFrame L)
    {Y : Coord → Ambient} {lower : ℝ} (hY : ContDiff ℝ ∞ Y) (hlower : 0 < lower)
    (hstrain : ∀ p : Coord, 0 < p 1 → strain (ruledMap d.γ d.E) Y p 1 1 = 0)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ p 1) (p : Coord) (hp : 0 < p 1) :
    frameCoefficient Y d.E p = 0 := by
  let α := frameCoefficient Y d.T
  let χ := frameCoefficient Y d.E
  let β := frameCoefficient Y d.n
  have hfull : ruledFullBending α χ β d.T d.E d.n = Y :=
    frameCoefficient_full_decomposition d.orthonormal
  have hα := frameCoefficient_contDiff hY d.smooth_T
  have hχ := frameCoefficient_contDiff hY d.smooth_E
  have hβ := frameCoefficient_contDiff hY d.smooth_n
  have he : (![p 0, p 1] : Coord) = p := by ext i; fin_cases i <;> rfl
  have h := supported_ruled_transverse_component_zero hlower
    (show lower < p 1 + lower + 1 by linarith)
    d.deriv_γ d.deriv_E d.deriv_T d.deriv_n
    (fun q _ => hα.differentiable (by simp) q)
    (fun q _ => hχ.differentiable (by simp) q)
    (fun q _ => hβ.differentiable (by simp) q)
    (fun q => d.orthonormal (q 0))
    (fun q hq => by rw [hfull]; exact hstrain q hq.1)
    (fun q hq => hsupport q (by rwa [hfull] at hq)) (p 0) (p 1)
    (show p 1 ∈ Set.Ioo 0 (p 1 + lower + 1) by constructor <;> linarith)
  simpa only [he] using h

theorem supported_ruled_vector_reduced {L : ℝ} (d : PeriodicRuledFrame L)
    {Y : Coord → Ambient} {lower : ℝ} (hY : ContDiff ℝ ∞ Y) (hlower : 0 < lower)
    (hstrain : ∀ p : Coord, 0 < p 1 → strain (ruledMap d.γ d.E) Y p 1 1 = 0)
    (hsupport : ∀ p ∈ tsupport Y, lower ≤ p 1) (p : Coord) (hp : 0 < p 1) :
    Y p = ruledBending (frameCoefficient Y d.T) (frameCoefficient Y d.n) d.T d.n p := by
  have he := congrFun (frameCoefficient_full_decomposition (Y := Y) d.orthonormal) p
  have hz := supported_ruled_vector_transverse_zero d hY hlower hstrain hsupport p hp
  simpa only [ruledFullBending, hz, zero_smul, add_zero] using he.symm

end
end TightVer401
