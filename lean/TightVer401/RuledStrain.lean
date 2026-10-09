import TightVer401.RuledNormal
import TightVer401.MetricBranching

/-! Reduction of the actual linearized metric equation on the ruled band.
The transverse frame component has been set to zero; the support argument
forcing that component to vanish is a separate analytic step. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

def ruledBending (α β : Coord → ℝ) (T n : ℝ → Ambient) : Coord → Ambient :=
  fun p => α p • T (p 0) + β p • n (p 0)

theorem ruledBending_partial
    {α β : Coord → ℝ} {T E n : ℝ → Ambient} {p : Coord} {k τ : ℝ}
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p)
    (hT : HasDerivAt T (k • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ • E (p 0)) (p 0)) (i : Fin 2) :
    coordPartial i (ruledBending α β T n) p =
      coordPartial i α p • T (p 0) + coordPartial i β p • n (p 0) +
        (((Pi.single i (1 : ℝ) : Coord) 0) * (k * α p - τ * β p)) • E (p 0) := by
  have hTc := hT.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hnc := hn.hasFDerivAt.comp p (ContinuousLinearMap.proj (R := ℝ) 0).hasFDerivAt
  have hdT : DifferentiableAt ℝ (fun q : Coord => T (q 0)) p := hTc.differentiableAt
  have hdn : DifferentiableAt ℝ (fun q : Coord => n (q 0)) p := hnc.differentiableAt
  have hdαT : DifferentiableAt ℝ (fun q : Coord => α q • T (q 0)) p := hα.smul hdT
  have hdβn : DifferentiableAt ℝ (fun q : Coord => β q • n (q 0)) p := hβ.smul hdn
  change coordPartial i (fun q => α q • T (q 0) + β q • n (q 0)) p = _
  have hadd : coordPartial i (fun q => α q • T (q 0) + β q • n (q 0)) p =
      coordPartial i (fun q => α q • T (q 0)) p +
        coordPartial i (fun q => β q • n (q 0)) p := by
    simp only [coordPartial, fderiv_fun_add hdαT hdβn, add_apply]
  rw [hadd, coordPartial_scalar_vector hα hdT, coordPartial_scalar_vector hβ hdn,
    coordPartial_curve hT i, coordPartial_curve hn i]
  module

theorem ruled_strain_equations
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {α β : Coord → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hα : DifferentiableAt ℝ α p) (hβ : DifferentiableAt ℝ β p)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    strain (ruledMap γ E) (ruledBending α β T n) p 0 0 =
      2 * ((1 - k (p 0) * p 1) * coordPartial 0 α p +
        τ (p 0) * p 1 * coordPartial 0 β p) ∧
    strain (ruledMap γ E) (ruledBending α β T n) p 0 1 =
      (1 - k (p 0) * p 1) * coordPartial 1 α p +
        τ (p 0) * p 1 * coordPartial 1 β p + k (p 0) * α p - τ (p 0) * β p ∧
    strain (ruledMap γ E) (ruledBending α β T n) p 1 1 = 0 := by
  rcases hf with ⟨hTT, hEE, hnn, hTE, hTn, hEn⟩
  have hET : inner ℝ (E (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTE]
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  have hnE : inner ℝ (n (p 0)) (E (p 0)) = 0 := by rw [real_inner_comm, hEn]
  simp only [strain, ruled_partial_s hγ hE, ruled_partial_u hγ hE,
    ruledBending_partial hα hβ hT hn, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    one_mul, zero_mul, zero_smul, add_zero, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hTT, hEE, hnn, hTE, hTn, hEn,
    hET, hnT, hnE, mul_zero, mul_one, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · ring
  · ring
  · trivial

end
end TightVer401
