import TightVer401.DualRadialNeckCalculus
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Literal endpoint radius germs and the matching central quadratic for
ver500 convex closure. The square-root germ is continuous at its endpoint,
but smoothness is asserted only on the open side of that endpoint. -/
namespace TightVer401
noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal upper parabolic radius from the pinned manuscript. -/
def parabolicClosureUpperRadius (RN mu h z : ℝ) : ℝ :=
  RN + Real.sqrt (2 * mu * (h - z))

/-- Reuse the retained square-root neck with its actual calculus. -/
theorem parabolicClosureUpperRadius_eq_neck (RN mu h : ℝ) :
    parabolicClosureUpperRadius RN mu h =
      fun z => dualRadialNeck RN (mu / 2) (-h) (-z) := by
  funext z
  unfold parabolicClosureUpperRadius dualRadialNeck
  congr 1
  calc
    Real.sqrt (2 * mu * (h - z)) =
        Real.sqrt (4 * (mu / 2 * (-z - -h))) := by congr 1 <;> ring
    _ = Real.sqrt 4 * Real.sqrt (mu / 2 * (-z - -h)) :=
      Real.sqrt_mul (by norm_num) _
    _ = 2 * Real.sqrt (mu / 2 * (-z - -h)) := by norm_num

/-- Reflection twice cancels its derivative sign, with the standard default derivatives. -/
theorem parabolicClosure_secondDeriv_reflect (f : ℝ → ℝ) (z : ℝ) :
    deriv (deriv (fun x => f (-x))) z = deriv (deriv f) (-z) := by
  have he : deriv (fun x => f (-x)) = fun x => -deriv f (-x) :=
    funext (fun x => deriv_comp_neg f x)
  rw [he]
  change deriv (-(fun x => deriv f (-x))) z = deriv (deriv f) (-z)
  rw [deriv.neg, deriv_comp_neg, neg_neg]

 theorem parabolicClosureUpperRadius_continuous (RN mu h : ℝ) :
    Continuous (parabolicClosureUpperRadius RN mu h) :=
  continuous_const.add
    (Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id)))

 theorem parabolicClosureUpperRadius_contDiffOn (RN mu h : ℝ) (hmu : 0 < mu) :
    ContDiffOn ℝ ∞ (parabolicClosureUpperRadius RN mu h) (Iio h) := by
  rw [parabolicClosureUpperRadius_eq_neck]
  apply (dualRadialNeck_contDiffOn RN (-h) (half_pos hmu)).comp contDiffOn_id.neg
  intro z hz
  change z < h at hz
  change -h < -z
  linarith

 theorem parabolicClosureUpperRadius_deriv_neg (RN mu h : ℝ) (hmu : 0 < mu)
    {z : ℝ} (hz : z < h) :
    deriv (parabolicClosureUpperRadius RN mu h) z < 0 := by
  rw [parabolicClosureUpperRadius_eq_neck, deriv_comp_neg]
  exact neg_neg_of_pos
    (dualRadialNeck_strict_derivative_signs RN (-h) (half_pos hmu)
      (show -h < -z by linarith)).1

 theorem parabolicClosureUpperRadius_second_neg (RN mu h : ℝ) (hmu : 0 < mu)
    {z : ℝ} (hz : z < h) :
    deriv (deriv (parabolicClosureUpperRadius RN mu h)) z < 0 := by
  rw [parabolicClosureUpperRadius_eq_neck, parabolicClosure_secondDeriv_reflect]
  exact (dualRadialNeck_strict_derivative_signs RN (-h) (half_pos hmu)
    (show -h < -z by linarith)).2

@[simp] theorem parabolicClosureUpperRadius_endpoint (RN mu h : ℝ) :
    parabolicClosureUpperRadius RN mu h h = RN := by
  simp [parabolicClosureUpperRadius]

/-- An even quadratic with prescribed value at j and negative acceleration. -/
def parabolicClosureJetQuadratic (j value k z : ℝ) : ℝ :=
  value + k / 2 * (j ^ 2 - z ^ 2)

 theorem parabolicClosureJetQuadratic_contDiff (j value k : ℝ) :
    ContDiff ℝ ∞ (parabolicClosureJetQuadratic j value k) :=
  contDiff_const.add (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2)))

 theorem parabolicClosureJetQuadratic_hasDerivAt (j value k z : ℝ) :
    HasDerivAt (parabolicClosureJetQuadratic j value k) (-k * z) z := by
  have hd := (((hasDerivAt_id z).pow 2).const_sub (j ^ 2)).const_mul (k / 2)
  convert hd.const_add value using 1 <;> first | rfl | (simp only [id_eq]; ring)

 theorem parabolicClosureJetQuadratic_deriv (j value k z : ℝ) :
    deriv (parabolicClosureJetQuadratic j value k) z = -k * z :=
  (parabolicClosureJetQuadratic_hasDerivAt j value k z).deriv

 theorem parabolicClosureJetQuadratic_second (j value k z : ℝ) :
    deriv (deriv (parabolicClosureJetQuadratic j value k)) z = -k := by
  have he : deriv (parabolicClosureJetQuadratic j value k) = fun x => -k * x :=
    funext (parabolicClosureJetQuadratic_deriv j value k)
  rw [he]
  simpa using ((hasDerivAt_id z).const_mul (-k)).deriv

@[simp] theorem parabolicClosureJetQuadratic_even (j value k z : ℝ) :
    parabolicClosureJetQuadratic j value k (-z) =
      parabolicClosureJetQuadratic j value k z := by
  simp [parabolicClosureJetQuadratic]

/-- The central quadratic matches the actual upper germ in its first jet. -/
theorem parabolicClosure_quadratic_firstJet {RN mu h j : ℝ} (hj : 0 < j) :
    let g := parabolicClosureUpperRadius RN mu h
    let k := -deriv g j / j
    parabolicClosureJetQuadratic j (g j) k j = g j ∧
      deriv (parabolicClosureJetQuadratic j (g j) k) j = deriv g j := by
  dsimp only
  constructor
  · simp [parabolicClosureJetQuadratic]
  · rw [parabolicClosureJetQuadratic_deriv]
    field_simp [hj.ne']

end
end TightVer401



