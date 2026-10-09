import TightVer401.PolarSaddleSignOn
import TightVer401.ExitPositiveGraphUniform

/-! Actual incoming circle traces for the ver500 quadratic filling. -/
namespace TightVer401
noncomputable section
open Set OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

def quadraticRadialFillingValueTrace (F : Coord → ℝ) (R θ : ℝ) : ℝ :=
  F (saddlePolarChart ![R, θ])

def quadraticRadialFillingRadialTrace (F : Coord → ℝ) (R θ : ℝ) : ℝ :=
  coordPartial 0 (fun q => F (saddlePolarChart q)) ![R, θ]

def quadraticRadialFillingRadialUnit (θ : ℝ) : Coord :=
  ![Real.cos θ, Real.sin θ]

def quadraticRadialFillingTangentialUnit (θ : ℝ) : Coord :=
  ![-Real.sin θ, Real.cos θ]

theorem quadraticRadialFilling_parameters_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (fun θ : ℝ => (![R, θ] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

theorem quadraticRadialFilling_polar_circle_periodic (R : ℝ) :
    Function.Periodic (fun θ => saddlePolarChart ![R, θ]) (2 * Real.pi) := by
  intro θ
  ext i
  fin_cases i <;> simp [saddlePolarChart, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Both boundary functions are actual smooth traces, even when the incoming
potential is only smooth on its open domain near the circle. -/
theorem quadraticRadialFilling_traces_contDiff {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {R : ℝ}
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R, θ] ∈ U) :
    ContDiff ℝ ∞ (quadraticRadialFillingValueTrace F R) ∧
      ContDiff ℝ ∞ (quadraticRadialFillingRadialTrace F R) := by
  have hpre : IsOpen (saddlePolarChart ⁻¹' U) :=
    hU.preimage saddlePolarChart_contDiff.continuous
  have hcomp : ContDiffOn ℝ ∞ (fun q => F (saddlePolarChart q))
      (saddlePolarChart ⁻¹' U) :=
    hF.comp saddlePolarChart_contDiff.contDiffOn (fun _ hq => hq)
  have hmap : MapsTo (fun θ : ℝ => (![R, θ] : Coord)) univ
      (saddlePolarChart ⁻¹' U) := fun θ _ => hCircle θ
  constructor
  · exact contDiffOn_univ.mp
      (hcomp.comp (quadraticRadialFilling_parameters_contDiff R).contDiffOn hmap)
  · exact contDiffOn_univ.mp
      ((partial_contDiffOn hcomp hpre 0).comp
        (quadraticRadialFilling_parameters_contDiff R).contDiffOn hmap)

/-- Actual radial boundary derivative is the Cartesian gradient paired with
the physical outward unit radial vector. -/
theorem quadraticRadialFilling_radialTrace_eq {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {R θ : ℝ}
    (hθ : saddlePolarChart ![R, θ] ∈ U) :
    quadraticRadialFillingRadialTrace F R θ =
      planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ
        quadraticRadialFillingRadialUnit θ := by
  unfold quadraticRadialFillingRadialTrace
  rw [polarLocal_coordPartial_comp
    ((hF.contDiffAt (hU.mem_nhds hθ)).differentiableAt (by simp))
    saddlePolarChart_contDiff]
  simp [saddlePolarChart_coordPartial, quadraticRadialFillingRadialUnit,
    planarGradient, dotProduct, Fin.sum_univ_two]

theorem quadraticRadialFilling_valueTrace_periodic (F : Coord → ℝ) (R : ℝ) :
    Function.Periodic (quadraticRadialFillingValueTrace F R) (2 * Real.pi) := by
  intro θ
  unfold quadraticRadialFillingValueTrace
  exact congrArg F (quadraticRadialFilling_polar_circle_periodic R θ)

theorem quadraticRadialFilling_radialTrace_periodic {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {R : ℝ}
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R, θ] ∈ U) :
    Function.Periodic (quadraticRadialFillingRadialTrace F R) (2 * Real.pi) := by
  intro θ
  rw [quadraticRadialFilling_radialTrace_eq hF hU (hCircle (θ + 2 * Real.pi)),
    quadraticRadialFilling_radialTrace_eq hF hU (hCircle θ)]
  have hc : saddlePolarChart ![R, θ + 2 * Real.pi] = saddlePolarChart ![R, θ] :=
    quadraticRadialFilling_polar_circle_periodic R θ
  rw [hc]
  simp [quadraticRadialFillingRadialUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The angular cylinder derivative equals the derivative of the actual value
trace; it is not supplied as independent boundary data. -/
theorem quadraticRadialFilling_valueTrace_deriv {F : Coord → ℝ} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {R θ : ℝ}
    (hθ : saddlePolarChart ![R, θ] ∈ U) :
    deriv (quadraticRadialFillingValueTrace F R) θ =
      coordPartial 1 (fun q => F (saddlePolarChart q)) ![R, θ] := by
  have hpre : IsOpen (saddlePolarChart ⁻¹' U) :=
    hU.preimage saddlePolarChart_contDiff.continuous
  have hcomp : ContDiffOn ℝ ∞ (fun q => F (saddlePolarChart q))
      (saddlePolarChart ⁻¹' U) :=
    hF.comp saddlePolarChart_contDiff.contDiffOn (fun _ hq => hq)
  exact (exitGraph_slice_hasDerivAt hpre hcomp hθ).deriv

/-- The complete actual incoming cylinder first jet, in the orientation used
by the existing filler boundary-jet theorem. -/
theorem quadraticRadialFilling_boundary_first_jet
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R θ : ℝ} (hθ : saddlePolarChart ![R, θ] ∈ U) :
    F (saddlePolarChart ![R, θ]) = quadraticRadialFillingValueTrace F R θ ∧
      coordPartial 0 (fun q => F (saddlePolarChart q)) ![R, θ] =
        quadraticRadialFillingRadialTrace F R θ ∧
      coordPartial 1 (fun q => F (saddlePolarChart q)) ![R, θ] =
        deriv (quadraticRadialFillingValueTrace F R) θ := by
  exact ⟨rfl, rfl, (quadraticRadialFilling_valueTrace_deriv hF hU hθ).symm⟩

theorem quadraticRadialFilling_valueTrace_second_deriv
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ}
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R, θ] ∈ U) (θ : ℝ) :
    deriv (deriv (quadraticRadialFillingValueTrace F R)) θ =
      planarHessian (fun q => F (saddlePolarChart q)) ![R, θ] 1 1 := by
  have hpre : IsOpen (saddlePolarChart ⁻¹' U) :=
    hU.preimage saddlePolarChart_contDiff.continuous
  have hcomp : ContDiffOn ℝ ∞ (fun q => F (saddlePolarChart q))
      (saddlePolarChart ⁻¹' U) :=
    hF.comp saddlePolarChart_contDiff.contDiffOn (fun _ hq => hq)
  have he : deriv (quadraticRadialFillingValueTrace F R) =
      fun s => coordPartial 1 (fun q => F (saddlePolarChart q)) ![R, s] := by
    funext s
    exact quadraticRadialFilling_valueTrace_deriv hF hU (hCircle s)
  rw [he]
  exact (exitGraph_slice_hasDerivAt hpre
    (partial_contDiffOn hcomp hpre 1) (hCircle θ)).deriv

/-- The polar-coordinate curvature correction converts the angular boundary
quantity to the actual Cartesian tangential Hessian. -/
theorem quadraticRadialFilling_tangentialTrace_eq
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ}
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R, θ] ∈ U) (θ : ℝ) :
    deriv (deriv (quadraticRadialFillingValueTrace F R)) θ +
        R * quadraticRadialFillingRadialTrace F R θ =
      R ^ 2 * (quadraticRadialFillingTangentialUnit θ ⬝ᵥ
        (planarHessian F (saddlePolarChart ![R, θ]) *ᵥ
          quadraticRadialFillingTangentialUnit θ)) := by
  rw [quadraticRadialFilling_valueTrace_second_deriv hF hU hCircle θ,
    quadraticRadialFilling_radialTrace_eq hF hU (hCircle θ),
    polarLocal_planarHessian_comp hF hU saddlePolarChart_contDiff (hCircle θ)]
  simp [saddlePolarChart_jacobian, saddlePolarChart_hessian,
    quadraticRadialFillingRadialUnit, quadraticRadialFillingTangentialUnit,
    planarGradient, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The exact positivity assumptions needed by angular domination follow from
the positive physical radial gradient and Cartesian tangential Hessian. No
radial concavity assumption on the incoming potential is needed. -/
theorem quadraticRadialFilling_traces_positive
    {F : Coord → ℝ} {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {R : ℝ} (hR : 0 < R)
    (hCircle : ∀ θ : ℝ, saddlePolarChart ![R, θ] ∈ U)
    (hRadial : ∀ θ : ℝ, 0 <
      planarGradient F (saddlePolarChart ![R, θ]) ⬝ᵥ
        quadraticRadialFillingRadialUnit θ)
    (hTangential : ∀ θ : ℝ, 0 < quadraticRadialFillingTangentialUnit θ ⬝ᵥ
      (planarHessian F (saddlePolarChart ![R, θ]) *ᵥ
        quadraticRadialFillingTangentialUnit θ)) :
    (∀ θ : ℝ, 0 < quadraticRadialFillingRadialTrace F R θ) ∧
      ∀ θ : ℝ, 0 < deriv (deriv (quadraticRadialFillingValueTrace F R)) θ +
        R * quadraticRadialFillingRadialTrace F R θ := by
  constructor
  · intro θ
    rw [quadraticRadialFilling_radialTrace_eq hF hU (hCircle θ)]
    exact hRadial θ
  · intro θ
    rw [quadraticRadialFilling_tangentialTrace_eq hF hU hCircle θ]
    exact mul_pos (sq_pos_of_pos hR) (hTangential θ)

end
end TightVer401
