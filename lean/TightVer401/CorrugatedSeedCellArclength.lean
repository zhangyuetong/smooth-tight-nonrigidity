import TightVer401.CorrugatedSeedSphereArclength

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff RealInnerProductSpace

def corrugatedAmbientRotation (ξ : ℂ) (u : Ambient) : Ambient := WithLp.toLp 2
  ![ξ.re * u 0 - ξ.im * u 1, ξ.im * u 0 + ξ.re * u 1, u 2]
def corrugatedSeedSphericalSpeed (N t : ℝ) : ℝ := ‖deriv (corrugatedSeedSphere N) t‖
def corrugatedSeedArcMap (N : ℝ) : ℝ → ℝ := rawPrimitive (corrugatedSeedSphericalSpeed N)
def corrugatedSeedArcCell (N : ℝ) : ℝ := corrugatedSeedArcMap N (corrugatedSeedCell N)

theorem corrugatedAmbientRotation_norm {ξ : ℂ} (hξ : ‖ξ‖ = 1) (u : Ambient) :
    ‖corrugatedAmbientRotation ξ u‖ = ‖u‖ := by
  have hξsq : ξ.re^2 + ξ.im^2 = 1 := by
    have h := Complex.sq_norm ξ
    rw [hξ, one_pow, Complex.normSq_apply] at h
    nlinarith
  have hn : ‖corrugatedAmbientRotation ξ u‖^2 = ‖u‖^2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ambient_inner_dot, ambient_inner_dot]
    simp [dotProduct, Fin.sum_univ_succ, corrugatedAmbientRotation]
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  nlinarith [norm_nonneg (corrugatedAmbientRotation ξ u), norm_nonneg u]

theorem corrugatedAmbientRotation_hasDerivAt {f : ℝ → Ambient} {v : Ambient} {t : ℝ}
    (hf : HasDerivAt f v t) (ξ : ℂ) :
    HasDerivAt (fun s => corrugatedAmbientRotation ξ (f s)) (corrugatedAmbientRotation ξ v) t := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hcoord (i : Fin 3) := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt t hf
  have hp : HasDerivAt (fun s =>
      ![ξ.re * f s 0 - ξ.im * f s 1, ξ.im * f s 0 + ξ.re * f s 1, f s 2])
      ![ξ.re * v 0 - ξ.im * v 1, ξ.im * v 0 + ξ.re * v 1, v 2] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((hcoord 0).const_mul ξ.re).sub ((hcoord 1).const_mul ξ.im)
    · exact ((hcoord 0).const_mul ξ.im).add ((hcoord 1).const_mul ξ.re)
    · exact hcoord 2
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem corrugatedComplexCoord_weight (z : ℂ) :
    planarWeight (corrugatedComplexCoord z) = Real.sqrt (1 + ‖z‖^2) := by
  simp only [planarWeight, corrugatedComplexCoord, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.sq_norm, Complex.normSq_apply]
  congr 1
  ring

theorem corrugatedComplexSphere_rotation {ξ : ℂ} (hξ : ‖ξ‖ = 1) (z : ℂ) :
    planarUnitNormal (corrugatedComplexCoord (ξ * z)) =
      corrugatedAmbientRotation ξ (planarUnitNormal (corrugatedComplexCoord z)) := by
  have hw : planarWeight (corrugatedComplexCoord (ξ * z)) = planarWeight (corrugatedComplexCoord z) := by
    rw [corrugatedComplexCoord_weight, corrugatedComplexCoord_weight, norm_mul, hξ, one_mul]
  unfold planarUnitNormal
  rw [hw]
  ext i
  fin_cases i <;>
    simp [corrugatedComplexCoord, corrugatedAmbientRotation,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem corrugatedSeedSphere_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    corrugatedSeedSphere N (t + corrugatedSeedCell N) =
      corrugatedAmbientRotation (corrugatedSeedRotation N) (corrugatedSeedSphere N t) := by
  unfold corrugatedSeedSphere
  rw [corrugatedSeedBeta_cell hN]
  exact corrugatedComplexSphere_rotation (by
    simp only [corrugatedSeedRotation, Complex.norm_exp_ofReal_mul_I]) _

theorem corrugatedSeedSphere_deriv_cell {N : ℝ} (hN : N ≠ 0) (t : ℝ) :
    deriv (corrugatedSeedSphere N) (t + corrugatedSeedCell N) =
      corrugatedAmbientRotation (corrugatedSeedRotation N) (deriv (corrugatedSeedSphere N) t) := by
  have hd := (corrugatedSeedSphere_contDiff N).differentiable (by simp)
  have hs := (hd (t + corrugatedSeedCell N)).hasDerivAt.scomp t
    ((hasDerivAt_id t).add_const (corrugatedSeedCell N))
  have hr := corrugatedAmbientRotation_hasDerivAt (hd t).hasDerivAt (corrugatedSeedRotation N)
  have he := hs.congr_of_eventuallyEq
    (f₁ := fun s => corrugatedAmbientRotation (corrugatedSeedRotation N) (corrugatedSeedSphere N s))
    (Filter.Eventually.of_forall (fun s => (corrugatedSeedSphere_cell hN s).symm))
  simpa only [one_smul] using he.unique hr

theorem corrugatedSeedSphericalSpeed_contDiff {N : ℝ} (hN : 1 < N) :
    ContDiff ℝ ∞ (corrugatedSeedSphericalSpeed N) :=
  (contDiff_infty_iff_deriv.mp (corrugatedSeedSphere_contDiff N)).2.norm ℝ
    (fun t => corrugatedSeedSphere_deriv_ne_zero hN t)

theorem corrugatedSeedSphericalSpeed_pos {N : ℝ} (hN : 1 < N) (t : ℝ) :
    0 < corrugatedSeedSphericalSpeed N t := norm_pos_iff.mpr (corrugatedSeedSphere_deriv_ne_zero hN t)

theorem corrugatedSeedSphericalSpeed_periodic {N : ℝ} (hN : N ≠ 0) :
    Function.Periodic (corrugatedSeedSphericalSpeed N) (corrugatedSeedCell N) := by
  intro t
  unfold corrugatedSeedSphericalSpeed
  rw [corrugatedSeedSphere_deriv_cell hN]
  exact corrugatedAmbientRotation_norm (by
    simp only [corrugatedSeedRotation, Complex.norm_exp_ofReal_mul_I]) _

theorem corrugatedSeedArcMap_shift {N : ℝ} (hN : 1 < N) (t : ℝ) :
    corrugatedSeedArcMap N (t + corrugatedSeedCell N) =
      corrugatedSeedArcMap N t + corrugatedSeedArcCell N :=
  normalLoop_arclength_shift (corrugatedSeedSphericalSpeed_contDiff hN).continuous
    (corrugatedSeedSphericalSpeed_periodic (ne_of_gt (by linarith))) t

theorem corrugatedSeedArcCell_pos {N : ℝ} (hN : 1 < N) : 0 < corrugatedSeedArcCell N :=
  normalLoop_arclength_period_pos (corrugatedSeedSphericalSpeed_contDiff hN).continuous
    (corrugatedSeedSphericalSpeed_pos hN) (by unfold corrugatedSeedCell; positivity)

theorem corrugatedSeedArcMap_full_period {N : ℕ} (hN : 2 ≤ N) :
    corrugatedSeedArcMap (N : ℝ) (2 * Real.pi) = (N : ℝ) * corrugatedSeedArcCell (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hp := corrugatedSeedSphericalSpeed_periodic (ne_of_gt (by linarith : (0 : ℝ) < N))
  have hi := hp.intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (fun a b => (corrugatedSeedSphericalSpeed_contDiff hNr).continuous.intervalIntegrable a b)
  have he : (N : ℤ) • corrugatedSeedCell (N : ℝ) = 2 * Real.pi := by
    simp only [zsmul_eq_mul, Int.cast_natCast, corrugatedSeedCell]
    field_simp
  simpa only [corrugatedSeedArcMap, corrugatedSeedArcCell, rawPrimitive, zero_add,
    he, zsmul_eq_mul, Int.cast_natCast] using hi

theorem corrugatedSeedArcInverse_cell {N : ℝ} (hN : 1 < N) (e : ℝ ≃ₜ ℝ)
    (he : (e : ℝ → ℝ) = corrugatedSeedArcMap N) (r : ℝ) :
    e.symm (r + corrugatedSeedArcCell N) = e.symm r + corrugatedSeedCell N := by
  apply e.injective
  rw [e.apply_symm_apply, he, corrugatedSeedArcMap_shift hN, ← he, e.apply_symm_apply]

end
end TightVer401
