import TightVer401.QuadraticRadialFillingTraces

namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Matrix BigOperators

/-- The incoming Cartesian first jet is recovered from its actual circle
value and radial traces by inverting the physical polar differential. -/
theorem quadraticRadialFilling_cartesian_gradient
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R,θ] ∈ U) (θ : ℝ) :
    coordPartial 0 F (saddlePolarChart ![R,θ]) =
        quadraticRadialFillingRadialTrace F R θ * Real.cos θ -
          (deriv (quadraticRadialFillingValueTrace F R) θ / R) * Real.sin θ ∧
      coordPartial 1 F (saddlePolarChart ![R,θ]) =
        quadraticRadialFillingRadialTrace F R θ * Real.sin θ +
          (deriv (quadraticRadialFillingValueTrace F R) θ / R) * Real.cos θ := by
  have hdiff := (hF.contDiffAt (hU.mem_nhds (hCircle θ))).differentiableAt (by simp)
  have hradial := polarLocal_coordPartial_comp hdiff saddlePolarChart_contDiff
    (i := 0)
  have hangular := polarLocal_coordPartial_comp hdiff saddlePolarChart_contDiff
    (i := 1)
  have hr : quadraticRadialFillingRadialTrace F R θ =
      coordPartial 0 F (saddlePolarChart ![R,θ]) * Real.cos θ +
        coordPartial 1 F (saddlePolarChart ![R,θ]) * Real.sin θ := by
    simpa [quadraticRadialFillingRadialTrace, Fin.sum_univ_two,
      saddlePolarChart_coordPartial] using hradial
  have ha : deriv (quadraticRadialFillingValueTrace F R) θ =
      coordPartial 0 F (saddlePolarChart ![R,θ]) * (-R * Real.sin θ) +
        coordPartial 1 F (saddlePolarChart ![R,θ]) * (R * Real.cos θ) := by
    rw [quadraticRadialFilling_valueTrace_deriv hF hU (hCircle θ)]
    simpa [Fin.sum_univ_two, saddlePolarChart_coordPartial] using hangular
  have hadiv : deriv (quadraticRadialFillingValueTrace F R) θ / R =
      -coordPartial 0 F (saddlePolarChart ![R,θ]) * Real.sin θ +
        coordPartial 1 F (saddlePolarChart ![R,θ]) * Real.cos θ := by
    apply (div_eq_iff hR.ne').mpr
    rw [ha]
    ring
  constructor
  · rw [hr, hadiv]
    linear_combination -coordPartial 0 F (saddlePolarChart ![R,θ]) *
      Real.sin_sq_add_cos_sq θ
  · rw [hr, hadiv]
    linear_combination -coordPartial 1 F (saddlePolarChart ![R,θ]) *
      Real.sin_sq_add_cos_sq θ

end
end TightVer401
