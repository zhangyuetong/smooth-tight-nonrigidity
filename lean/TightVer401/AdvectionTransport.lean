import TightVer401.RuledCharacteristics
import TightVer401.CompactTransport

/-! Global transport in the reciprocal coordinate is integrated along an
explicit complete curve. No flow-existence or characteristic-constancy grant
is used. Its period obstruction follows from actual compact support. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
set_option backward.isDefEq.respectTransparency false

theorem fderiv_two_scalar_coordinates (f : Coord → ℝ) (p v : Coord) :
    fderiv ℝ f p v = v 0 * coordPartial 0 f p + v 1 * coordPartial 1 f p := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp [coordPartial, smul_eq_mul]

theorem advection_characteristic_hasDerivAt {f : Coord → ℝ} {W a : ℝ → ℝ} {c s : ℝ}
    (hf : DifferentiableAt ℝ f (![s, c + W s] : Coord)) (hW : HasDerivAt W (a s) s)
    (hpde : coordPartial 0 f (![s, c + W s] : Coord) +
      a s * coordPartial 1 f (![s, c + W s] : Coord) = 0) :
    HasDerivAt (fun r => f (![r, c + W r] : Coord)) 0 s := by
  have hline := ruled_graph_hasDerivAt (hW.const_add c)
  have hd := hf.hasFDerivAt.comp_hasDerivAt s hline
  have hv : fderiv ℝ f (![s, c + W s] : Coord) (![1, a s] : Coord) = 0 := by
    rw [fderiv_two_scalar_coordinates]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul] using hpde
  convert! hd using 1
  exact hv.symm

theorem advection_first_integral_formula {f : Coord → ℝ} {W a : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hW : ∀ s, HasDerivAt W (a s) s) (hW0 : W 0 = 0)
    (hpde : ∀ p : Coord, coordPartial 0 f p + a (p 0) * coordPartial 1 f p = 0)
    (s r : ℝ) : f (![s, r] : Coord) = f (![0, r - W s] : Coord) := by
  let c := r - W s
  have hd (t : ℝ) : HasDerivAt (fun q => f (![q, c + W q] : Coord)) 0 t :=
    advection_characteristic_hasDerivAt (hf _) (hW t) (hpde _)
  have he := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t _ => (hd t).deriv) (Set.mem_univ s) (Set.mem_univ (0 : ℝ))
  simpa only [c, sub_add_cancel, hW0, add_zero] using he

theorem advection_period_zero_of_compact_support {f : Coord → ℝ} {W a : ℝ → ℝ} {L I : ℝ}
    (hf : Differentiable ℝ f) (hW : ∀ s, HasDerivAt W (a s) s) (hW0 : W 0 = 0)
    (hWL : W L = I)
    (hpde : ∀ p : Coord, coordPartial 0 f p + a (p 0) * coordPartial 1 f p = 0)
    (hperiod : ∀ s r, f (![s + L, r] : Coord) = f (![s, r] : Coord))
    (hcompact : HasCompactSupport (fun r => f (![0, r] : Coord))) (hne : f ≠ 0) : I = 0 := by
  let F : ℝ → ℝ := fun r => f (![0, r] : Coord)
  have hform := advection_first_integral_formula hf hW hW0 hpde
  have hFp : Function.Periodic F I := by
    intro r
    have h := hperiod 0 (r + I)
    simp only [zero_add] at h
    rw [hform L (r + I), hWL] at h
    simpa only [add_sub_cancel_right, F] using h.symm
  have hFn : F ≠ 0 := by
    intro hz
    apply hne
    funext p
    have he : p = (![p 0, p 1] : Coord) := by ext i; fin_cases i <;> simp
    rw [he, hform]
    exact congrFun hz (p 1 - W (p 0))
  exact period_zero_of_nonzero_compact_support hcompact hFp hFn

end
end TightVer401
