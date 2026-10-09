import TightVer401.RuledBand

/-! The unit normal and the ruling/mixed second-form coefficients are proved
from the actual ruled map, frame orthogonality and frame derivatives. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry

theorem fderiv_two_coordinates (F : Coord → Ambient) (p v : Coord) :
    fderiv ℝ F p v = v 0 • coordPartial 0 F p + v 1 • coordPartial 1 F p := by
  have hv : v = v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord) := by
    ext i
    fin_cases i <;> simp
  calc
    fderiv ℝ F p v = fderiv ℝ F p
      (v 0 • (Pi.single 0 1 : Coord) + v 1 • (Pi.single 1 1 : Coord)) := congrArg _ hv
    _ = _ := by simp [coordPartial]

def ruledNormal (T n : Ambient) (k τ u : ℝ) : Ambient :=
  (-τ * u / Real.sqrt (ruledEnergy k τ u)) • T +
    ((1 - k * u) / Real.sqrt (ruledEnergy k τ u)) • n

theorem ruledNormal_unit {T E n : Ambient} {k τ u : ℝ}
    (hf : IsOrthonormalFrame T E n) (hτ : τ ≠ 0) :
    inner ℝ (ruledNormal T n k τ u) (ruledNormal T n k τ u) = 1 := by
  rcases hf with ⟨hTT, _, hnn, _, hTn, _⟩
  have hnT : inner ℝ n T = 0 := by rw [real_inner_comm, hTn]
  have hp := ruledEnergy_pos (k := k) (u := u) hτ
  have hsq := Real.sq_sqrt hp.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  simp only [ruledNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hTT, hnn, hTn, hnT,
    mul_zero, mul_one, add_zero, zero_add]
  field_simp
  change Real.sqrt (ruledEnergy k τ u)^2 = (1 - k * u)^2 + τ^2 * u^2 at hsq
  nlinarith [hsq]

theorem ruledNormal_orthogonal {T E n : Ambient} {k τ u : ℝ}
    (hf : IsOrthonormalFrame T E n) :
    inner ℝ ((1 - k * u) • T + (τ * u) • n) (ruledNormal T n k τ u) = 0 ∧
    inner ℝ E (ruledNormal T n k τ u) = 0 := by
  rcases hf with ⟨hTT, _, hnn, hTE, hTn, hEn⟩
  have hnT : inner ℝ n T = 0 := by rw [real_inner_comm, hTn]
  have hET : inner ℝ E T = 0 := by rw [real_inner_comm, hTE]
  simp only [ruledNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hTT, hnn, hTn, hnT,
    hET, hEn, mul_zero, mul_one, add_zero, zero_add, div_eq_mul_inv]
  constructor
  · ring
  · trivial

theorem ruled_isUnitNormal {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : HasDerivAt γ (T (p 0)) (p 0))
    (hE : HasDerivAt E (-k (p 0) • T (p 0) + τ (p 0) • n (p 0)) (p 0))
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0)))
    (hτ : τ (p 0) ≠ 0) :
    IsUnitNormalAt (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p := by
  refine ⟨ruledNormal_unit hf hτ, ?_⟩
  intro v
  rw [fderiv_two_coordinates, ruled_partial_s hγ hE, ruled_partial_u hγ hE]
  obtain ⟨hs, hu⟩ := ruledNormal_orthogonal (k := k (p 0)) (τ := τ (p 0)) (u := p 1) hf
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hs, hu]
  simp

theorem ruled_mixed_and_ruling_second_form
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) :
    secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p 0 1 =
        τ (p 0) / Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) ∧
    secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p 1 1 = 0 := by
  have he : coordPartial 1 (ruledMap γ E) = fun q => E (q 0) := by
    funext q
    exact ruled_partial_u (hγ (q 0)) (hE (q 0))
  rcases hf with ⟨hTT, _, hnn, _, hTn, _⟩
  have hnT : inner ℝ (n (p 0)) (T (p 0)) = 0 := by rw [real_inner_comm, hTn]
  simp only [secondFundamental, he, coordPartial_curve (hE (p 0)),
    Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), one_smul, zero_smul,
    inner_zero_left, ruledNormal, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hTT, hnn, hTn, hnT,
    mul_zero, mul_one, add_zero, zero_add, div_eq_mul_inv]
  constructor
  · ring
  · trivial

end
end TightVer401
