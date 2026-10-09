import TightVer401.ProtectedTorusPositiveGaussCurvatureCharts

/-! Exact actual preferred-chart transport from a real cylinder to the
literal protected torus. The cylinder's real second coordinate has center
u; the torus's second circle coordinate has center zero. Their local
representatives therefore differ by the explicit translation ![0,u].

The translation identities below concern the actual pinned induced metric,
Christoffel symbols and curvature. They follow from Mathlib's all-map
fderiv_comp_add_left, including its derivative defaults. No smoothness,
normal, metric compatibility or curvature conclusion is a premise.
-/
open scoped Manifold ContDiff Topology Matrix
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance actualGraphPeriod : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem actualGraph_partial_translate (f : Coord → ℝ) (a x : Coord) (i : Fin 2) :
    coordPartial i (fun q => f (a + q)) x = coordPartial i f (a + x) := by
  simp only [coordPartial, fderiv_comp_add_left]

/-- Actual pinned Gaussian curvature commutes with coordinate translation. -/
theorem protectedTorusPositiveGauss_metric_curvature_translate
    (g : MetricField) (a x : Coord) :
    gaussianCurvature (fun q => g (a + q)) x = gaussianCurvature g (a + x) := by
  have hc (k i j : Fin 2) :
      christoffel (fun q => g (a + q)) k i j =
        (fun q => christoffel g k i j (a + q)) := by
    funext q
    simp only [christoffel, inverseMetric]
    apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    apply Finset.sum_congr rfl
    intro m _
    rw [actualGraph_partial_translate (fun z => g z j m) a q i,
      actualGraph_partial_translate (fun z => g z i m) a q j,
      actualGraph_partial_translate (fun z => g z i j) a q m]
  have hr (l k i j : Fin 2) :
      riemann (fun q => g (a + q)) l k i j x = riemann g l k i j (a + x) := by
    simp only [riemann, hc, actualGraph_partial_translate]
  simp only [gaussianCurvature, hr]

/-- The metric is explicitly translated, rather than identified with an
unchanged metric field. -/
theorem protectedTorusPositiveGauss_inducedMetric_translate
    (F : Coord → Ambient) (a : Coord) :
    inducedMetric (fun q => F (a + q)) = (fun q => inducedMetric F (a + q)) := by
  funext q
  ext i j
  simp only [inducedMetric, coordPartial, fderiv_comp_add_left]

theorem protectedTorusPositiveGauss_map_curvature_translate
    (F : Coord → Ambient) (a x : Coord) :
    gaussianCurvature (inducedMetric (fun q => F (a + q))) x =
      gaussianCurvature (inducedMetric F) (a + x) := by
  rw [protectedTorusPositiveGauss_inducedMetric_translate]
  exact protectedTorusPositiveGauss_metric_curvature_translate (inducedMetric F) a x

private theorem actualGraph_cylinder_chart (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (q : AddCircle (2 * Real.pi)) (u : ℝ) (x : Coord) :
    nativeProductCoordinateMap S (q,u) x =
      S (q + periodProjection (2 * Real.pi) (x 0), x 1) := by
  unfold nativeProductCoordinateMap
  congr 1
  apply Prod.ext
  · change (OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) q).symm (x 0) = _
    simpa [periodChart, periodProjection] using
      OAI.RawQuotientLie.addLeftChart_symm_apply (periodChart (2 * Real.pi)) q (x 0)
  · rfl

/-- Exact cylinder-to-torus preferred-chart curvature transport on the
literal saddle phase. The radius r remains arbitrary in this local bridge. -/
theorem protectedTorusPositiveGauss_saddle_chart_curvature_transport
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    (p : NonrigidTorusSource)
    (hphase : (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo (0 : ℝ) Real.pi) :
    nativeTorusChartCurvature (protectedTorusMap S r h) p =
      gaussianCurvature (inducedMetric (nativeProductCoordinateMap S
        (p.1, (AddCircle.equivIco (2 * Real.pi) 0 p.2).val)))
        (![0, (AddCircle.equivIco (2 * Real.pi) 0 p.2).val] : Coord) := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  have hu : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
  let a : Coord := ![0,u]
  have hg := protectedTorusPositiveGauss_saddle_chart_germ S r h p s u hs hu hphase
  have he : (fun q : Coord => S (periodProjection (2 * Real.pi) (s + q 0), u + q 1)) =
      (fun q : Coord => nativeProductCoordinateMap S (p.1,u) (a + q)) := by
    funext q
    rw [actualGraph_cylinder_chart]
    simp only [a, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
    rw [← hs]
    change S (periodProjection (2 * Real.pi) (s + q 0), u + q 1) =
      S (periodProjection (2 * Real.pi) s + periodProjection (2 * Real.pi) (q 0), u + q 1)
    rw [map_add]
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center,
    gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq hg), he,
    protectedTorusPositiveGauss_map_curvature_translate]
  simp only [add_zero]
  rfl

end
end TightVer401
