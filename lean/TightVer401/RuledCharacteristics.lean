import TightVer401.RuledSecondForm
import TightVer401.CharacteristicTransport
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! The nonruling characteristic ODE is derived from the quadratic form
of the actual second fundamental form, not assumed as a geometric interface. -/
namespace TightVer401
noncomputable section
open OAI.SmoothLocal.Geometry
open scoped ContDiff

theorem ruled_graph_hasDerivAt {u : ℝ → ℝ} {s w : ℝ} (hu : HasDerivAt u w s) :
    HasDerivAt (fun r => (![r, u r] : Coord)) (![1, w] : Coord) s := by
  have h1 := (hasDerivAt_single (1 : Fin 2) (u s)).hasFDerivAt.comp_hasDerivAt s hu
  convert! (hasDerivAt_single (0 : Fin 2) s).add h1 using 1
  · funext r i
    fin_cases i <;> simp
  · ext i
    fin_cases i <;> simp

theorem ruled_asymptotic_slope
    {γ T E n : ℝ → Ambient} {k τ : ℝ → ℝ} {p : Coord} {ks τs w : ℝ}
    {U : Set Coord}
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hE : ∀ s, HasDerivAt E (-k s • T s + τ s • n s) s)
    (hT : HasDerivAt T (k (p 0) • E (p 0)) (p 0))
    (hn : HasDerivAt n (-τ (p 0) • E (p 0)) (p 0))
    (hk : HasDerivAt k ks (p 0)) (hτ : HasDerivAt τ τs (p 0))
    (hX : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U) (hp : p ∈ U)
    (hf : IsOrthonormalFrame (T (p 0)) (E (p 0)) (n (p 0))) (hτ0 : τ (p 0) ≠ 0) :
    dotProduct (![1, w] : Coord)
      ((secondFundamental (ruledMap γ E)
        (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p).mulVec ![1, w]) = 0 ↔
      w = -(p 1 / 2) * (τs / τ (p 0) + p 1 * (ks - k (p 0) * (τs / τ (p 0)))) := by
  have h00 := ruled_second_form_ss hγ hE hT hn hk hτ hf hτ0
  obtain ⟨h01, h11⟩ := ruled_mixed_and_ruling_second_form hγ hE hf
  have h10 : secondFundamental (ruledMap γ E)
      (ruledNormal (T (p 0)) (n (p 0)) (k (p 0)) (τ (p 0)) (p 1)) p 1 0 =
      τ (p 0) / Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) := by
    rw [secondFundamental, coordPartial_comm hX hU hp 1 0]
    exact h01
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, h00, h01, h10, h11,
    one_mul, mul_one, zero_mul, mul_zero, add_zero]
  have hroot : Real.sqrt (ruledEnergy (k (p 0)) (τ (p 0)) (p 1)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (ruledEnergy_pos hτ0))
  constructor
  · intro hz
    field_simp at hz ⊢
    nlinarith
  · intro hw
    rw [hw]
    field_simp
    <;> ring

theorem ruled_characteristic_derivative_of_asymptotic
    {γ T E n : ℝ → Ambient} {k τ u : ℝ → ℝ} {s ks τs w : ℝ} {U : Set Coord}
    (hγ : ∀ r, HasDerivAt γ (T r) r)
    (hE : ∀ r, HasDerivAt E (-k r • T r + τ r • n r) r)
    (hT : HasDerivAt T (k s • E s) s) (hn : HasDerivAt n (-τ s • E s) s)
    (hk : HasDerivAt k ks s) (hτ : HasDerivAt τ τs s) (hu : HasDerivAt u w s)
    (hX : ContDiffOn ℝ ∞ (ruledMap γ E) U) (hU : IsOpen U) (hp : (![s, u s] : Coord) ∈ U)
    (hf : IsOrthonormalFrame (T s) (E s) (n s)) (hτ0 : τ s ≠ 0)
    (hasym : dotProduct (deriv (fun r => (![r, u r] : Coord)) s)
      ((secondFundamental (ruledMap γ E) (ruledNormal (T s) (n s) (k s) (τ s) (u s))
        (![s, u s] : Coord)).mulVec (deriv (fun r => (![r, u r] : Coord)) s)) = 0) :
    HasDerivAt u (-(u s / 2) * (τs / τ s + u s * (ks - k s * (τs / τ s)))) s := by
  rw [(ruled_graph_hasDerivAt hu).deriv] at hasym
  have hT' : HasDerivAt T (k ((![s, u s] : Coord) 0) • E ((![s, u s] : Coord) 0))
      ((![s, u s] : Coord) 0) := by simpa using hT
  have hn' : HasDerivAt n (-τ ((![s, u s] : Coord) 0) • E ((![s, u s] : Coord) 0))
      ((![s, u s] : Coord) 0) := by simpa using hn
  have hk' : HasDerivAt k ks ((![s, u s] : Coord) 0) := by simpa using hk
  have hτ' : HasDerivAt τ τs ((![s, u s] : Coord) 0) := by simpa using hτ
  have hf' : IsOrthonormalFrame (T ((![s, u s] : Coord) 0))
      (E ((![s, u s] : Coord) 0)) (n ((![s, u s] : Coord) 0)) := by simpa using hf
  have hτ0' : τ ((![s, u s] : Coord) 0) ≠ 0 := by simpa using hτ0
  have he := (ruled_asymptotic_slope hγ hE hT' hn' hk' hτ' hX hU hp hf' hτ0').mp hasym
  simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hu

end
end TightVer401
