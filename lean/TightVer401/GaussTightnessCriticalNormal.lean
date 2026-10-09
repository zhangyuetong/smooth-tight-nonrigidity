import TightVer401.SurfaceMetric
import OAI.Geometry.IsometricImmersion.Immersions.NormalSpace
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Critical height directions in the actual ambient three-space.
The final consumer is the generic-height route to
`classicalPositiveGaussTightness_proved`: the tangents, normal and height
in these lemmas are all those of the SAME coordinate representative.
No orientation or curvature hypothesis is inserted. -/

namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped RealInnerProductSpace Topology

/-- Two unit vectors perpendicular to the same independent tangent pair
differ by a sign. -/
theorem gaussTightness_unit_normal_eq_or_neg
    (t : Fin 2 → Ambient) (ht : LinearIndependent ℝ t)
    (n w : Ambient) (hn : inner ℝ n n = 1) (hw : inner ℝ w w = 1)
    (hnt : ∀ i, inner ℝ (t i) n = 0)
    (hwt : ∀ i, inner ℝ (t i) w = 0) :
    w = n ∨ w = -n := by
  have heq := normal_eq_inner_smul_of_independent_tangents t ht n w hn hnt hwt
  have hsquare : (inner ℝ n w) ^ 2 = 1 := by
    calc
      (inner ℝ n w) ^ 2 = inner ℝ ((inner ℝ n w) • n) ((inner ℝ n w) • n) := by
        simp only [real_inner_smul_left, real_inner_smul_right, hn]
        ring
      _ = inner ℝ w w := by rw [← heq]
      _ = 1 := hw
  have hsign : inner ℝ n w = 1 ∨ inner ℝ n w = -1 := by
    have hproduct : (inner ℝ n w - 1) * (inner ℝ n w + 1) = 0 := by
      nlinarith [hsquare]
    rcases mul_eq_zero.mp hproduct with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hsign with h | h
  · left
    simpa only [h, one_smul] using heq
  · right
    simpa only [h, neg_one_smul] using heq

/-- At a local height maximum, its direction annihilates the actual
coordinate differential. -/
theorem gaussTightness_localMax_height_orthogonal
    {F : Coord → Ambient} {p : Coord} (hF : DifferentiableAt ℝ F p)
    (w : Ambient) (hmax : IsLocalMax (height F w) p) (v : Coord) :
    inner ℝ (fderiv ℝ F p v) w = 0 := by
  have hz := congrArg (fun L : Coord →L[ℝ] ℝ => L v) hmax.fderiv_eq_zero
  change fderiv ℝ (fun q => inner ℝ (F q) w) p v = 0 at hz
  rw [fderiv_inner_apply ℝ hF (differentiableAt_const (c := w))] at hz
  simpa using hz

/-- A unit height direction at a local maximum is one of the two signs
of any given actual unit normal at that point. -/
theorem gaussTightness_localMax_height_normal_eq_or_neg
    {F : Coord → Ambient} {p : Coord} (hF : DifferentiableAt ℝ F p)
    (ht : LinearIndependent ℝ (fun i : Fin 2 => coordPartial i F p))
    (n w : Ambient) (hn : IsUnitNormalAt F n p)
    (hw : inner ℝ w w = 1) (hmax : IsLocalMax (height F w) p) :
    w = n ∨ w = -n := by
  apply gaussTightness_unit_normal_eq_or_neg
    (fun i : Fin 2 => coordPartial i F p) ht n w hn.1 hw
  · intro i
    exact hn.2 (Pi.single i 1)
  · intro i
    exact gaussTightness_localMax_height_orthogonal hF w hmax (Pi.single i 1)

/-- The same critical-normal statement with immersion expressed directly
as injectivity of the actual coordinate differential. -/
theorem gaussTightness_localMax_height_normal_eq_or_neg_of_injective
    {F : Coord → Ambient} {p : Coord} (hF : DifferentiableAt ℝ F p)
    (hi : Function.Injective (fderiv ℝ F p))
    (n w : Ambient) (hn : IsUnitNormalAt F n p)
    (hw : inner ℝ w w = 1) (hmax : IsLocalMax (height F w) p) :
    w = n ∨ w = -n := by
  have ht : LinearIndependent ℝ (fun i : Fin 2 => coordPartial i F p) := by
    simpa only [Function.comp_def, Pi.basisFun_apply, coordPartial,
      ContinuousLinearMap.coe_coe] using
      (Pi.basisFun ℝ (Fin 2)).linearIndependent.map' (fderiv ℝ F p).toLinearMap
        (LinearMap.ker_eq_bot_of_injective hi)
  exact gaussTightness_localMax_height_normal_eq_or_neg hF ht n w hn hw hmax

end
end TightVer401
