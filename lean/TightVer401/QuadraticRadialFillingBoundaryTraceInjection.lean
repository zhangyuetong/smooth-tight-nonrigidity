import TightVer401.QuadraticRadialFillingGradientBoundary
import TightVer401.QuadraticRadialFillingBoundaryRadial

/-! Cartesian circle injectivity from the actual quotient gradient trace. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped Topology

/-- Injectivity of the actual once-traversed quotient gradient trace gives
ordinary Cartesian gradient injectivity on the actual source radius level. -/
theorem quadraticRadialFillingGradient_injOn_of_trace_lift_injective
    {F : Coord → ℝ} {R : ℝ} (hR : 0 < R)
    (hinj : Function.Injective
      (quadraticRadialFillingGradientTrace_periodic F R).lift) :
    InjOn (planarGradient F) (quadraticRadialFillingRadiusLevel R) := by
  intro x hx y hy he
  obtain ⟨s, hs⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hx
  obtain ⟨t, ht⟩ := quadraticRadialFilling_radiusLevel_exists_polar hR hy
  have heTrace : quadraticRadialFillingGradientTrace F R s =
      quadraticRadialFillingGradientTrace F R t := by
    change planarGradient F (saddlePolarChart ![R, s]) =
      planarGradient F (saddlePolarChart ![R, t])
    rw [hs, ht]
    exact he
  have hst : (s : AddCircle (2 * Real.pi)) = (t : AddCircle (2 * Real.pi)) :=
    hinj (by simpa only [(quadraticRadialFillingGradientTrace_periodic F R).lift_coe]
      using heTrace)
  have heCircle : (quadraticRadialFillingCircle_periodic R).lift
      (s : AddCircle (2 * Real.pi)) =
      (quadraticRadialFillingCircle_periodic R).lift
        (t : AddCircle (2 * Real.pi)) :=
    congrArg (quadraticRadialFillingCircle_periodic R).lift hst
  have hCircle : quadraticRadialFillingCircle R s = quadraticRadialFillingCircle R t := by
    simpa only [(quadraticRadialFillingCircle_periodic R).lift_coe] using heCircle
  have hPolar : saddlePolarChart ![R, s] = saddlePolarChart ![R, t] := by
    simpa only [quadraticRadialFillingCircle_coord] using congrArg seamComplexCoord hCircle
  exact hs.symm.trans (hPolar.trans ht)

/-- Conversely, ordinary Cartesian circle injectivity gives injectivity of
the actual quotient gradient trace, using the retained source-circle lift. -/
theorem quadraticRadialFillingGradientTrace_lift_injective_of_injOn
    {F : Coord → ℝ} {R : ℝ} (hR : 0 < R)
    (hinj : InjOn (planarGradient F) (quadraticRadialFillingRadiusLevel R)) :
    Function.Injective (quadraticRadialFillingGradientTrace_periodic F R).lift := by
  intro q q' he
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q'
  have heTrace : quadraticRadialFillingGradientTrace F R s =
      quadraticRadialFillingGradientTrace F R t := by
    simpa only [(quadraticRadialFillingGradientTrace_periodic F R).lift_coe] using he
  have hPolar : saddlePolarChart ![R, s] = saddlePolarChart ![R, t] :=
    hinj (quadraticRadialFilling_radiusLevel_polar hR s)
      (quadraticRadialFilling_radiusLevel_polar hR t) heTrace
  apply quadraticRadialFillingCircle_lift_injective hR
  simp only [(quadraticRadialFillingCircle_periodic R).lift_coe]
  apply seamComplexCoord.injective
  simpa only [quadraticRadialFillingCircle_coord] using hPolar

theorem quadraticRadialFillingGradient_injOn_iff_trace_lift_injective
    {F : Coord → ℝ} {R : ℝ} (hR : 0 < R) :
    InjOn (planarGradient F) (quadraticRadialFillingRadiusLevel R) ↔
      Function.Injective (quadraticRadialFillingGradientTrace_periodic F R).lift :=
  ⟨quadraticRadialFillingGradientTrace_lift_injective_of_injOn hR,
    quadraticRadialFillingGradient_injOn_of_trace_lift_injective hR⟩

end
end TightVer401
