import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.ProtectedTorusPositiveGaussCurvatureSupport
import TightVer401.ClassicalExternal

/-! Preferred native quotient charts of the literal protected torus map.
Saddle smoothing owns the ordinary sphere-support germ producer below. This
leaf derives the actual negative preferred-chart curvature from it; it takes
no curvature sign or region equality as a premise.
-/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance positiveGaussChartsPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual quotient charts are centered at the zero physical Coord vector. -/
theorem protectedTorusPositiveGauss_chart_center (p : NonrigidTorusSource) :
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
      (chartAt (ModelProd ℝ ℝ) p p) = (0 : Coord) := by
  have hz (q : AddCircle (2 * Real.pi)) : chartAt ℝ q q = (0 : ℝ) := by
    change (periodChart (2 * Real.pi)).symm (-q + q) = 0
    rw [neg_add_cancel]
    have hp : periodChart (2 * Real.pi) (0 : ℝ) = 0 := rfl
    rw [← hp, (periodChart (2 * Real.pi)).left_inv (periodChart_zero_source _)]
  change (![chartAt ℝ p.1 p.1, chartAt ℝ p.2 p.2] : Coord) = 0
  rw [hz p.1, hz p.2]
  ext i
  fin_cases i <;> rfl

/-- The actual preferred inverse charts have their literal affine quotient
representatives, without identifying Coord and ModelProd definitionally. -/
theorem protectedTorusPositiveGauss_chart_lift (F : NonrigidTorusSource → Ambient)
    (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) :
    nativeProductCoordinateMap F p = fun q : Coord =>
      F (periodProjection (2 * Real.pi) (s + q 0),
        periodProjection (2 * Real.pi) (u + q 1)) := by
  have hc (a : AddCircle (2 * Real.pi)) (v w : ℝ)
      (ha : periodProjection (2 * Real.pi) v = a) :
      (chartAt ℝ a).symm w = periodProjection (2 * Real.pi) (v + w) := by
    change (OAI.RawQuotientLie.addLeftChart (periodChart (2 * Real.pi)) a).symm w = _
    rw [OAI.RawQuotientLie.addLeftChart_symm_apply, ← ha]
    exact (map_add (periodProjection (2 * Real.pi)) v w).symm
  funext q
  change F ((chartAt ℝ p.1).symm (q 0), (chartAt ℝ p.2).symm (q 1)) = _
  rw [hc p.1 s (q 0) hs, hc p.2 u (q 1) hu]

private theorem real_representative (S : AddCircle (2 * Real.pi) × ℝ → Ambient)
    (r : ℝ → ℝ) (h s u : ℝ) (hu : u ∈ Ico (0 : ℝ) (2 * Real.pi)) :
    protectedTorusMap S r h (periodProjection (2 * Real.pi) s,
      periodProjection (2 * Real.pi) u) =
      if u ≤ Real.pi then S (periodProjection (2 * Real.pi) s, u)
      else protectedTorusConvexCylinder r h (periodProjection (2 * Real.pi) s, u) := by
  have he : (AddCircle.equivIco (2 * Real.pi) 0
      (periodProjection (2 * Real.pi) u)).val = u :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hu))
  simp only [protectedTorusMap, he]

/-- Literal saddle phase matches the actual translated cylinder germ. -/
theorem protectedTorusPositiveGauss_saddle_chart_germ
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    (p : NonrigidTorusSource) (s u : ℝ)
    (hs : periodProjection (2 * Real.pi) s = p.1)
    (hu : periodProjection (2 * Real.pi) u = p.2) (hphase : u ∈ Ioo (0 : ℝ) Real.pi) :
    nativeProductCoordinateMap (protectedTorusMap S r h) p =ᶠ[𝓝 (0 : Coord)]
      (fun q : Coord => S (periodProjection (2 * Real.pi) (s + q 0), u + q 1)) := by
  rw [protectedTorusPositiveGauss_chart_lift _ p s u hs hu]
  have hn : ∀ᶠ q : Coord in 𝓝 0, u + q 1 ∈ Ioo (0 : ℝ) Real.pi :=
    (continuous_const.add (continuous_apply 1)).continuousAt
      (by simpa using Ioo_mem_nhds hphase.1 hphase.2)
  filter_upwards [hn] with q hq
  rw [real_representative _ _ _ _ _ ⟨hq.1.le, by linarith [hq.2, Real.pi_pos]⟩,
    if_pos hq.2.le]

/-- A precise ordinary producer obligation for the open saddle cylinder.
Each witness consists only of actual potential, metric, normal coordinates,
tensor determinant negativity and map agreement. No inhabitant is granted.
Its producer belongs to saddle/core-support smoothing. -/
def ProtectedTorusSaddleSphereSupportGerms
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) : Prop :=
  ∀ s u : ℝ, u ∈ Ioo (0 : ℝ) Real.pi → Nonempty
    (ProtectedTorusSphereSupportGerm
      (fun q : Coord => S (periodProjection (2 * Real.pi) (q 0), q 1))
      (![s, u] : Coord))

/-- The actual native preferred-chart curvature is negative throughout the
literal saddle phase, derived from the ordinary support producer. -/
theorem protectedTorusPositiveGauss_saddle_curvature_neg
    (S : AddCircle (2 * Real.pi) × ℝ → Ambient) (r : ℝ → ℝ) (h : ℝ)
    (hS : ProtectedTorusSaddleSphereSupportGerms S) (p : NonrigidTorusSource)
    (hphase : (AddCircle.equivIco (2 * Real.pi) 0 p.2).val ∈ Ioo (0 : ℝ) Real.pi) :
    nativeTorusChartCurvature (protectedTorusMap S r h) p < 0 := by
  obtain ⟨s, hs⟩ := QuotientAddGroup.mk_surjective p.1
  let u := (AddCircle.equivIco (2 * Real.pi) 0 p.2).val
  have hu : periodProjection (2 * Real.pi) u = p.2 := AddCircle.coe_equivIco
  obtain ⟨dg⟩ := hS s u hphase
  have hK := protectedTorus_sphereSupportGerm_translated_curvature_neg dg
  have he := protectedTorusPositiveGauss_saddle_chart_germ S r h p s u hs hu hphase
  have hcurv := gaussianCurvature_eq_of_eventuallyEq (inducedMetric_eventuallyEq he)
  rw [nativeTorusChartCurvature, protectedTorusPositiveGauss_chart_center, hcurv]
  change gaussianCurvature (inducedMetric
    (fun q : Coord => S (periodProjection (2 * Real.pi) (s + q 0), u + q 1))) 0 < 0 at hK
  exact hK

end
end TightVer401
