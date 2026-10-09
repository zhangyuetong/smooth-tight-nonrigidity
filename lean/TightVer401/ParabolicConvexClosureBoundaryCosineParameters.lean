import TightVer401.ParabolicConvexClosureBoundaryCosineCalculus
import TightVer401.ProtectedTorusMapDefinitions
import TightVer401.ParabolicConvexClosureBodyAnnulus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The exact coordinator map and its genuine parabolic transverse coordinates.
The upper and lower coordinates have nonzero derivative at the appropriate
endpoint, while cosine height has zero derivative there. -/
open scoped Manifold ContDiff Topology
namespace TightVer401
noncomputable section
open Set Filter _root_.Manifold OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false
local instance boundaryCosineParametersPeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def parabolicConvexClosureCosineHeight (h t : ℝ) : ℝ := h * Real.cos (Real.pi * t)

def parabolicConvexClosureBoundaryCosineMap (r : ℝ → ℝ) (h : ℝ)
    (p : AddCircle (2 * Real.pi) × unitInterval) : Ambient :=
  protectedTorusConvexCylinder r h (p.1, Real.pi + Real.pi * (p.2 : ℝ))

theorem parabolicConvexClosureBoundaryCosineMap_eq (r : ℝ → ℝ) (h : ℝ)
    (p : AddCircle (2 * Real.pi) × unitInterval) :
    parabolicConvexClosureBoundaryCosineMap r h p =
      revolutionEndCircleFull r (p.1, parabolicConvexClosureCosineHeight h p.2) := by
  simp [parabolicConvexClosureBoundaryCosineMap, protectedTorusConvexCylinder,
    parabolicConvexClosureCosineHeight, Real.cos_add]

def parabolicConvexClosureCosineUpper (mu h t : ℝ) : ℝ :=
  protectedTorusCollarScale h mu * Real.sin (Real.pi * t / 2)

def parabolicConvexClosureCosineLower (mu h t : ℝ) : ℝ :=
  protectedTorusCollarScale h mu * Real.cos (Real.pi * t / 2)

theorem parabolicConvexClosure_cosineScale_pos {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h) :
    0 < protectedTorusCollarScale h mu := by
  unfold protectedTorusCollarScale
  positivity

theorem parabolicConvexClosure_cosineScale_sq {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h) :
    mu * (protectedTorusCollarScale h mu)^2 / 2 = 2 * h := by
  have hs := Real.sq_sqrt (div_nonneg hh.le hmu.le)
  unfold protectedTorusCollarScale
  rw [show (2 * Real.sqrt (h / mu))^2 = 4 * (Real.sqrt (h / mu))^2 by ring, hs]
  field_simp
  ring

theorem parabolicConvexClosureCosineUpper_height {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h) (t : ℝ) :
    h - mu * (parabolicConvexClosureCosineUpper mu h t)^2 / 2 =
      parabolicConvexClosureCosineHeight h t := by
  have hs := parabolicConvexClosure_cosineScale_sq hmu hh
  have hc := Real.cos_two_mul (Real.pi * t / 2)
  have htr := Real.sin_sq_add_cos_sq (Real.pi * t / 2)
  rw [show 2 * (Real.pi * t / 2) = Real.pi * t by ring] at hc
  unfold parabolicConvexClosureCosineUpper parabolicConvexClosureCosineHeight
  rw [show mu * (protectedTorusCollarScale h mu * Real.sin (Real.pi * t / 2))^2 / 2 =
    (mu * (protectedTorusCollarScale h mu)^2 / 2) * (Real.sin (Real.pi * t / 2))^2 by ring, hs]
  nlinarith [congrArg (fun x : ℝ => h * x) hc, congrArg (fun x : ℝ => h * x) htr]

theorem parabolicConvexClosureCosineLower_height {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h) (t : ℝ) :
    -h + mu * (parabolicConvexClosureCosineLower mu h t)^2 / 2 =
      parabolicConvexClosureCosineHeight h t := by
  have hs := parabolicConvexClosure_cosineScale_sq hmu hh
  have hc := Real.cos_two_mul (Real.pi * t / 2)
  rw [show 2 * (Real.pi * t / 2) = Real.pi * t by ring] at hc
  unfold parabolicConvexClosureCosineLower parabolicConvexClosureCosineHeight
  rw [show mu * (protectedTorusCollarScale h mu * Real.cos (Real.pi * t / 2))^2 / 2 =
    (mu * (protectedTorusCollarScale h mu)^2 / 2) * (Real.cos (Real.pi * t / 2))^2 by ring, hs]
  nlinarith [congrArg (fun x : ℝ => h * x) hc]

theorem parabolicConvexClosureCosineUpper_nonneg {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h)
    (t : unitInterval) : 0 ≤ parabolicConvexClosureCosineUpper mu h t := by
  apply mul_nonneg (parabolicConvexClosure_cosineScale_pos hmu hh).le
  apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [Real.pi_pos, t.property.1, t.property.2]

theorem parabolicConvexClosureCosineLower_nonneg {mu h : ℝ} (hmu : 0 < mu) (hh : 0 < h)
    (t : unitInterval) : 0 ≤ parabolicConvexClosureCosineLower mu h t := by
  apply mul_nonneg (parabolicConvexClosure_cosineScale_pos hmu hh).le
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [Real.pi_pos, t.property.1, t.property.2]

theorem parabolicConvexClosureCosineHeight_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (parabolicConvexClosureCosineHeight h) := by
  unfold parabolicConvexClosureCosineHeight
  fun_prop

theorem parabolicConvexClosureCosineUpper_contDiff (mu h : ℝ) :
    ContDiff ℝ ∞ (parabolicConvexClosureCosineUpper mu h) := by
  unfold parabolicConvexClosureCosineUpper
  fun_prop

theorem parabolicConvexClosureCosineLower_contDiff (mu h : ℝ) :
    ContDiff ℝ ∞ (parabolicConvexClosureCosineLower mu h) := by
  unfold parabolicConvexClosureCosineLower
  fun_prop

theorem parabolicConvexClosureCosineHeight_hasDerivAt (h t : ℝ) :
    HasDerivAt (parabolicConvexClosureCosineHeight h)
      (-h * Real.pi * Real.sin (Real.pi * t)) t := by
  convert! (((hasDerivAt_id t).const_mul Real.pi).cos.const_mul h) using 1 <;> try rfl
  simp only [id_eq, mul_one]
  ring

theorem parabolicConvexClosureCosineUpper_hasDerivAt (mu h t : ℝ) :
    HasDerivAt (parabolicConvexClosureCosineUpper mu h)
      (protectedTorusCollarScale h mu * (Real.pi / 2) * Real.cos (Real.pi * t / 2)) t := by
  convert! ((((hasDerivAt_id t).const_mul Real.pi).div_const 2).sin.const_mul
    (protectedTorusCollarScale h mu)) using 1 <;> try rfl
  simp only [id_eq, mul_one]
  ring

theorem parabolicConvexClosureCosineLower_hasDerivAt (mu h t : ℝ) :
    HasDerivAt (parabolicConvexClosureCosineLower mu h)
      (-protectedTorusCollarScale h mu * (Real.pi / 2) * Real.sin (Real.pi * t / 2)) t := by
  convert! ((((hasDerivAt_id t).const_mul Real.pi).div_const 2).cos.const_mul
    (protectedTorusCollarScale h mu)) using 1 <;> try rfl
  simp only [id_eq, mul_one]
  ring

theorem parabolicConvexClosureCosineHeight_mem {h : ℝ} (hh : 0 < h) (t : unitInterval) :
    parabolicConvexClosureCosineHeight h t ∈ Icc (-h) h := by
  unfold parabolicConvexClosureCosineHeight
  constructor <;> nlinarith [Real.neg_one_le_cos (Real.pi * (t : ℝ)), Real.cos_le_one (Real.pi * (t : ℝ))]

theorem parabolicConvexClosureCosineHeight_mem_interior {h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Ioo (0 : ℝ) 1) : parabolicConvexClosureCosineHeight h t ∈ Ioo (-h) h := by
  have h0 : 0 < Real.pi * t := mul_pos Real.pi_pos ht.1
  have h1 : Real.pi * t < Real.pi := by nlinarith [Real.pi_pos, ht.2]
  have hupper := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0.le, h1.le⟩ h0
  have hlower := Real.strictAntiOn_cos ⟨h0.le, h1.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ h1
  simp only [Real.cos_zero, Real.cos_pi] at hupper hlower
  unfold parabolicConvexClosureCosineHeight
  constructor <;> nlinarith

end
end TightVer401
