import TightVer401.QuadraticRadialFillingGradientJordan
import TightVer401.CircleDiskWinding
import TightVer401.QuadraticRadialFillingTraces

namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

theorem quadraticRadialFillingGradientComplexTrace_locally_injective
    {F : Coord → ℝ} {R : ℝ} {U : Set Coord}
    (hR : 0 < R) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = R} ⊆ U)
    (hdet : ∀ x, planarRadius x = R → (planarHessian F x).det < 0) :
    IsLocallyInjective (quadraticRadialFillingGradientComplexTrace F R) := by
  have hExp := Circle.isCoveringMap_exp.isLocalHomeomorph.isLocallyInjective
  have hc : Continuous (fun t : ℝ => saddlePolarChart ![R,t]) :=
    saddlePolarChart_contDiff.continuous.comp
      (quadraticRadialFilling_parameters_contDiff R).continuous
  intro s
  obtain ⟨I,hI,hsI,hInj⟩ := hExp s
  have hs : planarRadius (saddlePolarChart ![R,s]) = R :=
    angularDescent_radius_polar (show (0 : ℝ) < (![R,s] : Coord) 0 from hR)
  obtain ⟨e,he,_heU,hef,_hei⟩ := planarGradient_exists_smooth_local_inverse_at
    hF hU (hCircleU hs) (ne_of_lt (hdet _ hs))
  refine ⟨I ∩ (fun t : ℝ => saddlePolarChart ![R,t]) ⁻¹' e.source,
    hI.inter (e.open_source.preimage hc), ⟨hsI,he⟩, ?_⟩
  intro t ht v hv hEq
  apply hInj ht.1 hv.1
  have hGrad : planarGradient F (saddlePolarChart ![R,t]) =
      planarGradient F (saddlePolarChart ![R,v]) :=
    quadraticRadialFillingComplex_injective hEq
  have hPolar : saddlePolarChart ![R,t] = saddlePolarChart ![R,v] := by
    apply e.injOn ht.2 hv.2
    rw [hef]
    exact hGrad
  have hCircle : quadraticRadialFillingCircle R t = quadraticRadialFillingCircle R v := by
    apply seamComplexCoord.injective
    simpa only [quadraticRadialFillingCircle_coord] using hPolar
  apply Subtype.ext
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne')
  simpa only [quadraticRadialFillingCircle, circleMap, zero_add,
    Circle.coe_exp, Complex.real_smul] using hCircle

end
end TightVer401
