import TightVer401.SmoothingSeamPeriodicity
import TightVer401.SurfaceMetric
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Covariance of actual intrinsic curvature under longitude translation.
The pinned affine-translation derivative theorem holds for arbitrary functions,
so this identity requires neither positivity nor a supplied curvature relation. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical longitude shift is an actual affine translation. -/
theorem bandBending_longitudeShift_eq_add (s : ℝ) (p : Coord) :
    smoothingSeamShift s p = p + (![s, 0] : Coord) := by
  ext i
  fin_cases i <;> simp [smoothingSeamShift]

/-- Actual derivatives commute with affine translation, including at nonsmooth points. -/
theorem bandBending_fderiv_translation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Coord → V) (s : ℝ) (p : Coord) :
    fderiv ℝ (fun q => f (smoothingSeamShift s q)) p =
      fderiv ℝ f (smoothingSeamShift s p) := by
  simpa only [bandBending_longitudeShift_eq_add] using
    (fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := p) (![s, 0] : Coord))

/-- Actual coordinate partials commute with the longitude shift. -/
theorem bandBending_coordPartial_translation {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Coord → V) (s : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (fun q => f (smoothingSeamShift s q)) p =
      coordPartial i f (smoothingSeamShift s p) := by
  unfold coordPartial
  rw [bandBending_fderiv_translation]

/-- The actual induced metric of the shifted map is the shifted metric. -/
theorem bandBending_inducedMetric_translation (F : Coord → Ambient) (s : ℝ) (p : Coord) :
    inducedMetric (fun q => F (smoothingSeamShift s q)) p =
      inducedMetric F (smoothingSeamShift s p) := by
  ext i j
  unfold inducedMetric
  rw [bandBending_coordPartial_translation F s p i,
    bandBending_coordPartial_translation F s p j]

/-- Pointwise actual inverse metric covariance under the physical translation. -/
theorem bandBending_metric_inverse_translation (g : MetricField) (s : ℝ) (p : Coord) :
    inverseMetric (fun q => g (smoothingSeamShift s q)) p =
      inverseMetric g (smoothingSeamShift s p) := rfl

/-- Actual Christoffel symbols commute with this affine translation. -/
theorem bandBending_metric_christoffel_translation
    (g : MetricField) (s : ℝ) (p : Coord) (k i j : Fin 2) :
    christoffel (fun q => g (smoothingSeamShift s q)) k i j p =
      christoffel g k i j (smoothingSeamShift s p) := by
  have hpartial (a b c : Fin 2) :
      coordPartial a (fun q => g (smoothingSeamShift s q) b c) p =
        coordPartial a (fun q => g q b c) (smoothingSeamShift s p) :=
    bandBending_coordPartial_translation (fun q => g q b c) s p a
  simp only [christoffel, inverseMetric, hpartial]

/-- Actual Riemann curvature components commute with the translation. -/
theorem bandBending_metric_riemann_translation
    (g : MetricField) (s : ℝ) (p : Coord) (l k i j : Fin 2) :
    riemann (fun q => g (smoothingSeamShift s q)) l k i j p =
      riemann g l k i j (smoothingSeamShift s p) := by
  have hC (a b c : Fin 2) :
      christoffel (fun q => g (smoothingSeamShift s q)) a b c =
        (fun q => christoffel g a b c (smoothingSeamShift s q)) := by
    funext q
    exact bandBending_metric_christoffel_translation g s q a b c
  simp only [riemann, hC, bandBending_coordPartial_translation]

/-- The pinned intrinsic Gaussian curvature formula commutes with translation. -/
theorem bandBending_metric_curvature_translation
    (g : MetricField) (s : ℝ) (p : Coord) :
    gaussianCurvature (fun q => g (smoothingSeamShift s q)) p =
      gaussianCurvature g (smoothingSeamShift s p) := by
  simp only [gaussianCurvature, bandBending_metric_riemann_translation]

/-- Actual intrinsic curvature of the translated map equals the original
actual intrinsic curvature at the translated point. No period or curvature
correspondence is assumed; the identity also holds without immersion. -/
theorem bandBending_actual_curvature_translation
    (F : Coord → Ambient) (s : ℝ) (p : Coord) :
    gaussianCurvature (inducedMetric (fun q => F (smoothingSeamShift s q))) p =
      gaussianCurvature (inducedMetric F) (smoothingSeamShift s p) := by
  have hM : inducedMetric (fun q => F (smoothingSeamShift s q)) =
      (fun q => inducedMetric F (smoothingSeamShift s q)) := by
    funext q
    exact bandBending_inducedMetric_translation F s q
  rw [hM]
  exact bandBending_metric_curvature_translation (inducedMetric F) s p

end
end TightVer401

