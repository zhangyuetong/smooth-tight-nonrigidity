import TightVer401.CorrugatedSeedSphere
import TightVer401.CorrugatedSeedSphereLift

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff RealInnerProductSpace

def corrugatedSeedSphereScale (N t : ℝ) : ℝ :=
  (planarWeight (corrugatedComplexCoord (corrugatedSeedBeta N t)))⁻¹

/-- Signed curvature of an arbitrary regular spherical parametrization.
Its numerator is the actual normal-loop curvature, and the denominator
is the cube of the actual speed. The unit-speed compatibility is below. -/
def sphericalCurveGeodesicCurvature (ζ : ℝ → Ambient) (t : ℝ) : ℝ :=
  normalLoopCurvature ζ t / ‖deriv ζ t‖^3

theorem sphericalCurveGeodesicCurvature_unit_speed {ζ : ℝ → Ambient} {t : ℝ}
    (ht : ‖deriv ζ t‖ = 1) :
    sphericalCurveGeodesicCurvature ζ t = normalLoopCurvature ζ t := by
  simp only [sphericalCurveGeodesicCurvature, ht, one_pow, div_one]

theorem corrugatedSeedSphereScale_pos (N t : ℝ) : 0 < corrugatedSeedSphereScale N t :=
  inv_pos.mpr (planarWeight_pos _)

theorem corrugatedSeedSphereScale_contDiff (N : ℝ) :
    ContDiff ℝ ∞ (corrugatedSeedSphereScale N) := by
  have h := gnomonicWeight_contDiff.comp
    (corrugatedComplexCoord_contDiff.comp (corrugatedSeedBeta_contDiff N))
  exact h.inv (fun _ => ne_of_gt (planarWeight_pos _))

theorem corrugatedSeedSphere_eq_scaled (N t : ℝ) :
    corrugatedSeedSphere N t = corrugatedSeedSphereScale N t •
      corrugatedHomogeneous (corrugatedSeedBeta N t) := by
  ext i
  fin_cases i <;>
    simp [corrugatedSeedSphere, corrugatedSeedSphereScale, planarUnitNormal,
      corrugatedComplexCoord, corrugatedHomogeneous, div_eq_mul_inv, mul_comm]

theorem corrugatedSeedSphere_curvature_numerator (N t : ℝ) :
    normalLoopCurvature (corrugatedSeedSphere N) t =
      (corrugatedSeedSphereScale N t)^3 *
        corrugatedSeedPlaneDet (deriv (corrugatedSeedBeta N) t)
          (deriv (deriv (corrugatedSeedBeta N)) t) := by
  have he : corrugatedSeedSphere N =
      fun s => corrugatedSeedSphereScale N s • corrugatedHomogeneous (corrugatedSeedBeta N s) :=
    funext (corrugatedSeedSphere_eq_scaled N)
  unfold normalLoopCurvature normalLoopKappa normalLoopP
  rw [inner_neg_right, neg_neg, he]
  exact corrugatedScaledHomogeneous_actual_triple (corrugatedSeedSphereScale_contDiff N)
    (corrugatedSeedBeta_contDiff N) t

theorem corrugatedSeedSphere_geodesic_curvature (N t : ℝ) :
    sphericalCurveGeodesicCurvature (corrugatedSeedSphere N) t =
      (corrugatedSeedSphereScale N t)^3 *
        corrugatedSeedPlaneDet (deriv (corrugatedSeedBeta N) t)
          (deriv (deriv (corrugatedSeedBeta N)) t) / ‖deriv (corrugatedSeedSphere N) t‖^3 := by
  rw [sphericalCurveGeodesicCurvature, corrugatedSeedSphere_curvature_numerator]

theorem corrugatedSeedSphere_curvature_positive {N : ℝ} (hN : 1 < N) :
    0 < sphericalCurveGeodesicCurvature (corrugatedSeedSphere N) 0 := by
  rw [corrugatedSeedSphere_geodesic_curvature,
    corrugatedSeedBeta_curvature_at_zero (ne_of_gt (by linarith : 0 < N))]
  exact div_pos (mul_pos (pow_pos (corrugatedSeedSphereScale_pos N 0) _) (by norm_num))
    (pow_pos (norm_pos_iff.mpr (corrugatedSeedSphere_deriv_ne_zero hN 0)) _)

theorem corrugatedSeedSphere_curvature_negative {N : ℝ} (hN : 1 < N) :
    sphericalCurveGeodesicCurvature (corrugatedSeedSphere N) (Real.pi / N) < 0 := by
  rw [corrugatedSeedSphere_geodesic_curvature,
    corrugatedSeedBeta_curvature_at_half_cell (ne_of_gt (by linarith : 0 < N))]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (pow_pos (corrugatedSeedSphereScale_pos N _) _) (by norm_num))
    (pow_pos (norm_pos_iff.mpr (corrugatedSeedSphere_deriv_ne_zero hN _)) _)

end
end TightVer401
