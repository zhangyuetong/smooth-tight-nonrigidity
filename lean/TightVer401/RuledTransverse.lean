import TightVer401.RuledStrain
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.MeanValue

/-! The zero transverse-component support argument on the lifted ruled band.
These are actual scalar coordinate derivatives, not formal jet variables. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

theorem transverse_slice_hasDerivAt {χ : Coord → ℝ} {s u : ℝ}
    (hχ : DifferentiableAt ℝ χ (![s, u] : Coord)) :
    HasDerivAt (fun v => χ (![s, v] : Coord)) (coordPartial 1 χ (![s, u] : Coord)) u := by
  have he : (fun v => (![s, v] : Coord)) = Function.update (![s, 0] : Coord) 1 := by
    funext v i
    fin_cases i <;> simp
  have hd : HasDerivAt (fun v => (![s, v] : Coord)) (Pi.single 1 (1 : ℝ) : Coord) u := by
    rw [he]
    exact hasDerivAt_update _ _ _
  convert! hχ.hasFDerivAt.comp_hasDerivAt u hd using 1

theorem transverse_component_zero_of_support
    {χ : Coord → ℝ} {b lower : ℝ} (hlower : 0 < lower) (hband : lower < b)
    (hχ : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b → DifferentiableAt ℝ χ p)
    (hzero : ∀ p : Coord, p 1 ∈ Set.Ioo 0 b → coordPartial 1 χ p = 0)
    (hsupp : ∀ p ∈ tsupport χ, lower ≤ p 1)
    (s u : ℝ) (hu : u ∈ Set.Ioo 0 b) : χ (![s, u] : Coord) = 0 := by
  have hd (v : ℝ) (hv : v ∈ Set.Ioo 0 b) : HasDerivAt (fun r => χ (![s, r] : Coord)) 0 v := by
    have hp : (![s, v] : Coord) 1 ∈ Set.Ioo 0 b := by simpa using hv
    simpa only [hzero _ hp] using transverse_slice_hasDerivAt (hχ _ hp)
  have hm : lower / 2 ∈ Set.Ioo 0 b := by constructor <;> linarith
  have hn : (![s, lower / 2] : Coord) ∉ tsupport χ := by
    intro h
    have hh := hsupp _ h
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hh
    linarith
  have hbase : χ (![s, lower / 2] : Coord) = 0 := image_eq_zero_of_notMem_tsupport hn
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) b).isPreconnected
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hd v hv).deriv) hu hm
  exact he.trans hbase

end
end TightVer401
