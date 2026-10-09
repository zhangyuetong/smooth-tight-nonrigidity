import TightVer401.ScalarFlowPeriodFamily
import TightVer401.ScalarFlowVariationMultiplier

namespace TightVer401
noncomputable section
open Set Filter MeasureTheory OAI.SmoothLocal.Geometry
open scoped ContDiff Topology Matrix
set_option backward.isDefEq.respectTransparency false

/-- The return multiplier belongs to a constructed actual full-period solution family. -/
theorem exists_scalarFlowPeriod_return_family {f : Coord → ℝ} {W : Set Coord} {P : ℝ}
    (hP : 0 < P) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W)
    (hseam : ∀ r : ℝ, (![r, 0] : Coord) ∈ W)
    (hfzero : ∀ r : ℝ, f ![r, 0] = 0) :
    ∃ (V : Set Coord) (u : Coord → ℝ), IsOpen V ∧ ContDiffOn ℝ ∞ u V ∧
      (∀ q ∈ V, (![q 0, u q] : Coord) ∈ W) ∧
      (∀ q ∈ V, coordPartial 0 u q = f ![q 0, u q]) ∧
      (∀ r ∈ Icc (0 : ℝ) P, (![r, 0] : Coord) ∈ V) ∧
      (∀ r ∈ Icc (0 : ℝ) P, u ![r, 0] = 0) ∧
      ((fun x : ℝ => u ![0, x]) =ᶠ[𝓝 (0 : ℝ)] id) ∧
      HasDerivAt (fun x : ℝ => u ![P, x])
        (Real.exp (∫ r in 0..P, scalarFlowLinearCoefficient f r)) 0 := by
  obtain ⟨V, u, hV, hu, himage, hode, hvseam, hzero, hi⟩ :=
    exists_scalarFlowPeriod_family hP hW hf hseam hfzero
  exact ⟨V, u, hV, hu, himage, hode, hvseam, hzero, hi,
    scalarFlow_return_hasDerivAt hP.le hV hW hu hf himage hode hvseam hzero hi⟩

end
end TightVer401
