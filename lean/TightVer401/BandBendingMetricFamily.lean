import TightVer401.BandBendingMetricParameter
import OAI.Geometry.IsometricImmersion.Metrics.MetricSmoothness

/-! Joint smoothness of the actual intrinsic curvature of a metric family.
This extends the pinned coordinate metric smoothness proof to a parameter
without changing inverseMetric, christoffel, riemann or gaussianCurvature. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff BigOperators Matrix

variable {G : ℝ → MetricField} {W : Set (ℝ × Coord)}

/-- Actual positive definiteness ensures the joint determinant never vanishes. -/
theorem bandBending_metricFamily_det_ne_zero
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) {z : ℝ × Coord} (hz : z ∈ W) :
    (G z.1 z.2).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (hpos z hz).isUnit).ne_zero

/-- Joint smoothness of the actual determinant, by the two-coordinate formula. -/
theorem bandBending_metricFamily_det_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => (G z.1 z.2).det) W := by
  simpa only [Matrix.det_fin_two] using
    ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))

/-- Joint smoothness of the entries of the actual adjugate. -/
theorem bandBending_metricFamily_adjugate_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => (G z.1 z.2).adjugate i j) W := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hG 1 1
  · simpa [Matrix.adjugate_fin_two] using (hG 0 1).neg
  · simpa [Matrix.adjugate_fin_two] using (hG 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using hG 0 0

/-- Joint smoothness of the pinned inverse metric coefficients. -/
theorem bandBending_metricFamily_inverse_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => inverseMetric (G z.1) z.2 i j) W := by
  have hi : ContDiffOn ℝ ∞ (fun z : ℝ × Coord => ((G z.1 z.2).det)⁻¹) W :=
    (bandBending_metricFamily_det_contDiffOn hG).inv
      (fun z hz => bandBending_metricFamily_det_ne_zero hpos hz)
  have ha := bandBending_metricFamily_adjugate_contDiffOn hG i j
  simpa [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hi.mul ha

/-- Actual spatial derivatives of the metric entries are jointly smooth. -/
theorem bandBending_metricFamily_partial_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hW : IsOpen W) (i j k : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Coord => coordPartial k (fun q => G z.1 q i j) z.2) W := by
  exact bandBending_sliceCoordPartial_contDiffOn (hG i j) hW k

/-- Joint smoothness of the actual pinned Christoffel symbols. -/
theorem bandBending_metricFamily_christoffel_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) (hW : IsOpen W) (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => christoffel (G z.1) k i j z.2) W := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Coord => ∑ l,
      inverseMetric (G z.1) z.2 k l *
        (coordPartial i (fun q => G z.1 q j l) z.2 +
          coordPartial j (fun q => G z.1 q i l) z.2 -
          coordPartial l (fun q => G z.1 q i j) z.2)) W := by
    apply ContDiffOn.sum
    intro l hl
    exact (bandBending_metricFamily_inverse_contDiffOn hG hpos k l).mul
      (((bandBending_metricFamily_partial_contDiffOn hG hW j l i).add
        (bandBending_metricFamily_partial_contDiffOn hG hW i l j)).sub
        (bandBending_metricFamily_partial_contDiffOn hG hW i j l))
  exact contDiffOn_const.mul hs

/-- Joint smoothness of spatial derivatives of the actual Christoffel symbols. -/
theorem bandBending_metricFamily_christoffelPartial_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) (hW : IsOpen W)
    (k i j d : Fin 2) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Coord => coordPartial d (christoffel (G z.1) k i j) z.2) W := by
  exact bandBending_sliceCoordPartial_contDiffOn
    (bandBending_metricFamily_christoffel_contDiffOn hG hpos hW k i j) hW d

/-- Joint smoothness of the actual pinned Riemann curvature components. -/
theorem bandBending_metricFamily_riemann_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) (hW : IsOpen W)
    (l k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => riemann (G z.1) l k i j z.2) W := by
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Coord => ∑ m,
      (christoffel (G z.1) m j k z.2 * christoffel (G z.1) l i m z.2 -
        christoffel (G z.1) m i k z.2 * christoffel (G z.1) l j m z.2)) W := by
    apply ContDiffOn.sum
    intro m hm
    exact ((bandBending_metricFamily_christoffel_contDiffOn hG hpos hW m j k).mul
      (bandBending_metricFamily_christoffel_contDiffOn hG hpos hW l i m)).sub
        ((bandBending_metricFamily_christoffel_contDiffOn hG hpos hW m i k).mul
          (bandBending_metricFamily_christoffel_contDiffOn hG hpos hW l j m))
  exact ((bandBending_metricFamily_christoffelPartial_contDiffOn hG hpos hW l j k i).sub
    (bandBending_metricFamily_christoffelPartial_contDiffOn hG hpos hW l i k j)).add hs

/-- Intrinsic Gaussian curvature is jointly smooth in the parameter and actual
spatial coordinates, with no derivative-correspondence input hypothesis. -/
theorem bandBending_metricFamily_curvature_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z : ℝ × Coord => G z.1 z.2 i j) W)
    (hpos : ∀ z ∈ W, (G z.1 z.2).PosDef) (hW : IsOpen W) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Coord => gaussianCurvature (G z.1) z.2) W := by
  have hn : ContDiffOn ℝ ∞ (fun z : ℝ × Coord =>
      ∑ l, G z.1 z.2 0 l * riemann (G z.1) l 1 0 1 z.2) W := by
    apply ContDiffOn.sum
    intro l hl
    exact (hG 0 l).mul (bandBending_metricFamily_riemann_contDiffOn hG hpos hW l 1 0 1)
  exact hn.div (bandBending_metricFamily_det_contDiffOn hG)
    (fun z hz => bandBending_metricFamily_det_ne_zero hpos hz)

end
end TightVer401
