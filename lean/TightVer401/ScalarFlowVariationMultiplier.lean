import TightVer401.ScalarFlowVariation
import TightVer401.ScalarFlowVariationLinearODE

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open OAI.ClosedSurfaceR4.PeriodicPrimitive
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem scalarFlow_return_hasDerivAt {u f : Coord → ℝ} {V W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hV : IsOpen V) (hW : IsOpen W)
    (hu : ContDiffOn ℝ ∞ u V) (hf : ContDiffOn ℝ ∞ f W)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0)
    (hinitial : (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    HasDerivAt (fun x : ℝ => u ![P, x])
      (Real.exp (∫ r in 0..P, scalarFlowLinearCoefficient f r)) 0 := by
  have hWseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ W := by
    intro r hr
    simpa only [Matrix.cons_val_zero, hzero r hr] using himage ![r, 0] (hseam r hr)
  have hb := scalarFlowLinearCoefficient_continuousOn hW hf hWseam
  have hj : ∀ r ∈ Icc (0 : ℝ) P, HasDerivAt (scalarFlowJacobian u)
      (scalarFlowLinearCoefficient f r * scalarFlowJacobian u r) r :=
    fun r hr => scalarFlow_variation_hasDerivAt hV hW hu hf himage hode (hseam r hr) (hzero r hr)
  have hj0 := scalarFlowJacobian_initial hV hu (hseam 0 ⟨le_rfl, hP⟩) hinitial
  have he := scalarLinearODE_endpoint hP hb hj hj0
  have hd := exitGraph_slice_hasDerivAt hV hu (hseam P ⟨hP, le_rfl⟩)
  change HasDerivAt (fun x : ℝ => u ![P, x]) (scalarFlowJacobian u P) 0 at hd
  rwa [he] at hd

theorem scalarFlow_return_deriv {u f : Coord → ℝ} {V W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hV : IsOpen V) (hW : IsOpen W)
    (hu : ContDiffOn ℝ ∞ u V) (hf : ContDiffOn ℝ ∞ f W)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0)
    (hinitial : (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    deriv (fun x : ℝ => u ![P, x]) 0 = Real.exp (∫ r in 0..P, scalarFlowLinearCoefficient f r) :=
  (scalarFlow_return_hasDerivAt hP hV hW hu hf himage hode hseam hzero hinitial).deriv

theorem scalarFlow_return_identity_integral_zero {u f : Coord → ℝ} {V W : Set Coord} {P : ℝ}
    (hP : 0 ≤ P) (hV : IsOpen V) (hW : IsOpen W)
    (hu : ContDiffOn ℝ ∞ u V) (hf : ContDiffOn ℝ ∞ f W)
    (himage : ∀ q ∈ V, (![q 0, u q] : Coord) ∈ W)
    (hode : ∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q])
    (hseam : ∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V)
    (hzero : ∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0)
    (hinitial : (fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id)
    (hreturn : (fun x : ℝ => u ![P, x]) =ᶠ[𝓝 (0 : ℝ)] id) :
    (∫ r in 0..P, scalarFlowLinearCoefficient f r) = 0 := by
  have hd := scalarFlow_return_hasDerivAt hP hV hW hu hf himage hode hseam hzero hinitial
  have he := hd.unique ((hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hreturn)
  have hl := congrArg Real.log he
  simpa only [Real.log_exp, Real.log_one] using hl

end
end TightVer401
