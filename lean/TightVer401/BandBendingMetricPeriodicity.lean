import TightVer401.SmoothingSeamPeriodicity
import TightVer401.SurfaceMetric
import OAI.Geometry.IsometricImmersion.Metrics.MetricSmoothness

/-! Periodicity of the actual induced intrinsic curvature.
Translation has actual derivative equal to the identity. Its chain rule
transfers periodicity to metric coefficients and their spatial derivatives. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual vector-valued differential is unchanged by a period translation. -/
theorem bandBending_fderiv_shift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Coord → V} (hX : ContDiff ℝ ∞ X) (L : ℝ)
    (hperiod : ∀ p, X (smoothingSeamShift L p) = X p) (p : Coord) :
    fderiv ℝ X (smoothingSeamShift L p) = fderiv ℝ X p := by
  have hc : HasFDerivAt (fun q => X (smoothingSeamShift L q))
      ((fderiv ℝ X (smoothingSeamShift L p)).comp (ContinuousLinearMap.id ℝ Coord)) p := by
    simpa only [Function.comp_def] using
      (hX.differentiable (by simp) (smoothingSeamShift L p)).hasFDerivAt.comp p
        (smoothingSeamShift_hasFDerivAt L p)
  have he : (fun q => X (smoothingSeamShift L q)) = X := funext hperiod
  rw [he] at hc
  simpa only [ContinuousLinearMap.comp_id] using hc.fderiv.symm

/-- Actual coordinate vector partials retain the period. -/
theorem bandBending_coordPartial_shift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Coord → V} (hX : ContDiff ℝ ∞ X) (L : ℝ)
    (hperiod : ∀ p, X (smoothingSeamShift L p) = X p) (p : Coord) (i : Fin 2) :
    coordPartial i X (smoothingSeamShift L p) = coordPartial i X p := by
  unfold coordPartial
  rw [bandBending_fderiv_shift hX L hperiod]

/-- The whole actual induced metric matrix retains the period. -/
theorem bandBending_inducedMetric_shift {X : Coord → Ambient}
    (hX : ContDiff ℝ ∞ X) (L : ℝ)
    (hperiod : ∀ p, X (smoothingSeamShift L p) = X p) (p : Coord) :
    inducedMetric X (smoothingSeamShift L p) = inducedMetric X p := by
  ext i j
  unfold inducedMetric
  rw [bandBending_coordPartial_shift hX L hperiod p i,
    bandBending_coordPartial_shift hX L hperiod p j]

section Metric
variable {g : MetricField} (hg : SmoothPositiveOn g univ) (L : ℝ)
    (hperiod : ∀ p, g (smoothingSeamShift L p) = g p)
include hg hperiod

/-- Spatial metric-entry partials retain their actual period. -/
theorem bandBending_metric_partial_shift (p : Coord) (i j d : Fin 2) :
    coordPartial d (fun q => g q i j) (smoothingSeamShift L p) =
      coordPartial d (fun q => g q i j) p := by
  exact smoothing_seam_partial_periodic (contDiffOn_univ.mp (hg.1 i j)) L
    (fun q => congrFun (congrFun (hperiod q) i) j) p d

/-- The actual inverse metric retains the same period. -/
theorem bandBending_metric_inverse_shift (p : Coord) :
    inverseMetric g (smoothingSeamShift L p) = inverseMetric g p := by
  unfold inverseMetric
  rw [hperiod p]

/-- Periodicity of the actual Christoffel symbols, using actual spatial partials. -/
theorem bandBending_metric_christoffel_shift (p : Coord) (k i j : Fin 2) :
    christoffel g k i j (smoothingSeamShift L p) = christoffel g k i j p := by
  unfold christoffel
  simp only [bandBending_metric_inverse_shift hg L hperiod,
    bandBending_metric_partial_shift hg L hperiod]

/-- Christoffel derivatives retain the period because the actual symbols are smooth. -/
theorem bandBending_metric_christoffelPartial_shift
    (p : Coord) (k i j d : Fin 2) :
    coordPartial d (christoffel g k i j) (smoothingSeamShift L p) =
      coordPartial d (christoffel g k i j) p := by
  exact smoothing_seam_partial_periodic
    (contDiffOn_univ.mp (christoffel_contDiffOn hg isOpen_univ k i j)) L
    (fun q => bandBending_metric_christoffel_shift hg L hperiod q k i j) p d

/-- Periodicity of the actual Riemann curvature components. -/
theorem bandBending_metric_riemann_shift (p : Coord) (l k i j : Fin 2) :
    riemann g l k i j (smoothingSeamShift L p) = riemann g l k i j p := by
  unfold riemann
  simp only [bandBending_metric_christoffelPartial_shift hg L hperiod,
    bandBending_metric_christoffel_shift hg L hperiod]

/-- Periodicity of the pinned intrinsic Gaussian curvature formula. -/
theorem bandBending_metric_curvature_shift (p : Coord) :
    gaussianCurvature g (smoothingSeamShift L p) = gaussianCurvature g p := by
  unfold gaussianCurvature
  simp only [hperiod p, bandBending_metric_riemann_shift hg L hperiod]

end Metric

/-- Actual intrinsic curvature of a globally smooth periodic immersion
is periodic in the longitudinal coordinate at every fixed height. -/
theorem bandBending_actual_curvature_periodic {X : Coord → Ambient} {L : ℝ}
    (hX : ContDiff ℝ ∞ X)
    (hperiod : ∀ p, X (smoothingSeamShift L p) = X p)
    (himm : ∀ p, Function.Injective (fderiv ℝ X p)) (u : ℝ) :
    Function.Periodic
      (fun s => gaussianCurvature (inducedMetric X) (![s, u] : Coord)) L := by
  have hg : SmoothPositiveOn (inducedMetric X) univ :=
    inducedMetric_smoothPositiveOn hX.contDiffOn isOpen_univ (fun p _ => himm p)
  intro s
  exact bandBending_metric_curvature_shift hg L
    (bandBending_inducedMetric_shift hX L hperiod) (![s, u] : Coord)

end
end TightVer401

