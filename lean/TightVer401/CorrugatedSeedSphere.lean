import TightVer401.CorrugatedSeedCurvature
import TightVer401.CorrugatedSeedAnalytic
import TightVer401.GnomonicCoordinates

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Manifold

def corrugatedComplexCoord (z : ℂ) : Coord := ![z.re, z.im]
def corrugatedComplexSphere (z : ℂ) : RoundSphere := gnomonicPoint (corrugatedComplexCoord z)
def corrugatedSeedSphere (N : ℝ) (t : ℝ) : Ambient :=
  planarUnitNormal (corrugatedComplexCoord (corrugatedSeedBeta N t))
def corrugatedSeedSpherePoint (N : ℝ) (t : ℝ) : RoundSphere :=
  corrugatedComplexSphere (corrugatedSeedBeta N t)

theorem corrugatedComplexCoord_contDiff : ContDiff ℝ ∞ corrugatedComplexCoord := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Complex.reCLM.contDiff
  · exact Complex.imCLM.contDiff

theorem corrugatedComplexCoord_injective : Function.Injective corrugatedComplexCoord := by
  intro z w h
  apply Complex.ext
  · exact congrFun h 0
  · exact congrFun h 1

theorem corrugatedComplexCoord_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => corrugatedComplexCoord (f s)) (corrugatedComplexCoord v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf

theorem corrugatedSeedSphere_contDiff (N : ℝ) : ContDiff ℝ ∞ (corrugatedSeedSphere N) :=
  gnomonicNormal_contDiff.comp (corrugatedComplexCoord_contDiff.comp (corrugatedSeedBeta_contDiff N))

theorem corrugatedSeedSpherePoint_contMDiff (N : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (corrugatedSeedSpherePoint N) :=
  gnomonicPoint_contMDiff.comp
    (corrugatedComplexCoord_contDiff.comp (corrugatedSeedBeta_contDiff N)).contMDiff

theorem corrugatedSeedSphere_unit (N t : ℝ) : ‖corrugatedSeedSphere N t‖ = 1 := by
  have h := planarUnitNormal_unit (corrugatedComplexCoord (corrugatedSeedBeta N t))
  rw [real_inner_self_eq_norm_sq] at h
  change ‖corrugatedSeedSphere N t‖^2 = 1 at h
  nlinarith [norm_nonneg (corrugatedSeedSphere N t)]

theorem corrugatedSeedSphere_north (N t : ℝ) : 0 < corrugatedSeedSphere N t 2 :=
  gnomonicPoint_north _

theorem corrugatedSeedSphere_periodic {N : ℕ} (hN : 2 ≤ N) :
    Function.Periodic (corrugatedSeedSphere (N : ℝ)) (2 * Real.pi) := by
  intro t
  unfold corrugatedSeedSphere
  rw [corrugatedSeedBeta_periodic hN t]

theorem corrugatedSeedSpherePoint_periodic {N : ℕ} (hN : 2 ≤ N) :
    Function.Periodic (corrugatedSeedSpherePoint (N : ℝ)) (2 * Real.pi) := by
  intro t
  unfold corrugatedSeedSpherePoint
  rw [corrugatedSeedBeta_periodic hN t]

theorem corrugatedSeedSphere_injOn {N : ℝ} (hN : 1 < N) :
    InjOn (corrugatedSeedSphere N) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  have hp := congrArg gnomonicInverse h
  simp only [corrugatedSeedSphere, gnomonic_left_inverse] at hp
  exact corrugatedSeedBeta_injOn hN hs ht (corrugatedComplexCoord_injective hp)

theorem corrugatedSeedSphere_deriv_ne_zero {N : ℝ} (hN : 1 < N) (t : ℝ) :
    deriv (corrugatedSeedSphere N) t ≠ 0 := by
  have hNz : N ≠ 0 := ne_of_gt (by linarith)
  have hp := corrugatedComplexCoord_hasDerivAt (corrugatedSeedBeta_hasDerivAt hNz t)
  have h : DifferentiableAt ℝ planarUnitNormal
      (corrugatedComplexCoord (corrugatedSeedBeta N t)) :=
    gnomonicNormal_contDiff.contDiffAt.differentiableAt (by simp)
  have hd := h.hasFDerivAt.comp_hasDerivAt t hp
  have hd' := hd.congr_of_eventuallyEq (f₁ := corrugatedSeedSphere N)
    (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hd'.deriv]
  intro hz
  have he : corrugatedComplexCoord (corrugatedSeedBetaVelocity N t) = 0 :=
    gnomonicNormal_differential_injective _ (by simpa only [map_zero] using hz)
  have hv : corrugatedSeedBetaVelocity N t = 0 := by
    apply Complex.ext
    · exact congrFun he 0
    · exact congrFun he 1
  exact corrugatedSeedBetaVelocity_ne_zero hN t hv

end
end TightVer401
