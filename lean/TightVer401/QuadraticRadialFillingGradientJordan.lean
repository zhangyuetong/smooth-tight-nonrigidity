import TightVer401.QuadraticRadialFillingGradientBoundary
import TightVer401.PeriodicPlanarSchoenflies

/-! Actual nearby gradient circles in an injective collar are Jordan curves.
This supplies their Schoenflies fillings, without a winding or origin claim. -/
namespace TightVer401
noncomputable section
open Set Function OAI.SmoothLocal.Geometry
open scoped ContDiff Topology

/-- The actual complex coordinate of the gradient along a round source circle. -/
def quadraticRadialFillingGradientComplexTrace (F : Coord → ℝ) (S : ℝ) : ℝ → ℂ :=
  fun s => angularDescentComplex (quadraticRadialFillingGradientTrace F S s)

theorem quadraticRadialFillingComplex_injective : Function.Injective angularDescentComplex := by
  have hl : Function.LeftInverse seamComplexCoord angularDescentComplex :=
    quadraticRadialFillingCoord_complex
  exact hl.injective

theorem quadraticRadialFillingGradientComplexTrace_periodic (F : Coord → ℝ) (S : ℝ) :
    Function.Periodic (quadraticRadialFillingGradientComplexTrace F S) (2 * Real.pi) := by
  intro s
  exact congrArg angularDescentComplex (quadraticRadialFillingGradientTrace_periodic F S s)

theorem quadraticRadialFillingGradientComplexTrace_contDiff
    {F : Coord → ℝ} {S : ℝ} {U : Set Coord}
    (hS : 0 < S) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = S} ⊆ U) :
    ContDiff ℝ ∞ (quadraticRadialFillingGradientComplexTrace F S) :=
  angularDescentComplex_contDiff.comp
    (quadraticRadialFillingGradientTrace_contDiff hS hU hF hCircleU)

/-- The ordinary injectivity on a collar gives an injective once-traversed
actual gradient boundary; no Jordan conclusion is an input. -/
theorem quadraticRadialFillingGradientComplexTrace_injOn
    {F : Coord → ℝ} {S : ℝ} {W : Set Coord}
    (hS : 0 < S) (hCircleW : {x : Coord | planarRadius x = S} ⊆ W)
    (hinj : InjOn (planarGradient F) W) :
    InjOn (quadraticRadialFillingGradientComplexTrace F S) (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht he
  have hst : saddlePolarChart ![S,s] = saddlePolarChart ![S,t] := by
    apply hinj (hCircleW (angularDescent_radius_polar (q := ![S,s]) hS))
      (hCircleW (angularDescent_radius_polar (q := ![S,t]) hS))
    exact quadraticRadialFillingComplex_injective he
  apply quadraticRadialFillingCircle_injOn hS hs ht
  apply seamComplexCoord.injective
  simpa only [quadraticRadialFillingCircle_coord] using hst

theorem quadraticRadialFillingGradientComplexTrace_isJordanCurve
    {F : Coord → ℝ} {S : ℝ} {U W : Set Coord}
    (hS : 0 < S) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = S} ⊆ U)
    (hCircleW : {x : Coord | planarRadius x = S} ⊆ W)
    (hinj : InjOn (planarGradient F) W) :
    Schoenflies.IsJordanCurve (range
      (jordanComplexCoordinates.symm ∘ quadraticRadialFillingGradientComplexTrace F S)) := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  exact periodicComplexCurve_isJordanCurve
    (quadraticRadialFillingGradientComplexTrace_contDiff hS hU hF hCircleU)
    (quadraticRadialFillingGradientComplexTrace_periodic F S)
    (quadraticRadialFillingGradientComplexTrace_injOn hS hCircleW hinj)

/-- A genuine complex homeomorphism filling of the actual nearby gradient
circle, in the same source model used by the annular degree theorem. -/
theorem quadraticRadialFillingGradientComplexTrace_exists_filling
    {F : Coord → ℝ} {S : ℝ} {U W : Set Coord}
    (hS : 0 < S) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hCircleU : {x : Coord | planarRadius x = S} ⊆ U)
    (hCircleW : {x : Coord | planarRadius x = S} ⊆ W)
    (hinj : InjOn (planarGradient F) W) :
    ∃ H : ℂ ≃ₜ ℂ, range (quadraticRadialFillingGradientComplexTrace F S) =
      H '' Metric.sphere (0 : ℂ) 1 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  exact periodicComplexCurve_exists_filling
    (quadraticRadialFillingGradientComplexTrace_contDiff hS hU hF hCircleU)
    (quadraticRadialFillingGradientComplexTrace_periodic F S)
    (quadraticRadialFillingGradientComplexTrace_injOn hS hCircleW hinj)

end
end TightVer401
